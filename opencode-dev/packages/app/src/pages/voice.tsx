import { createSignal, onMount, Show, For } from "solid-js";
import { MicrophoneButton } from "@/components/voice/MicrophoneButton";
import { AudioVisualizer } from "@/components/voice/AudioVisualizer";
import { TranscriptView, type TranscriptMessage } from "@/components/voice/TranscriptView";
import { VoiceSelector } from "@/components/voice/VoiceSelector";
import { sendVoiceMessage, sendTextMessage, listVoices, type VoiceChatResponse } from "@/api/voice";
import { Button } from "@opencode-ai/ui/button";
import { Icon } from "@opencode-ai/ui/icon";
import { type Maybe, just, none, isJust, isNone, fromMaybe, mapMaybe } from "@/utils/maybe";

export default function VoiceChatPage() {
  const [isListening, setIsListening] = createSignal(false);
  const [isProcessing, setIsProcessing] = createSignal(false);
  const [isSpeaking, setIsSpeaking] = createSignal(false);
  const [audioLevel, setAudioLevel] = createSignal(0);
  const [messages, setMessages] = createSignal<TranscriptMessage[]>([]);
  const [voices, setVoices] = createSignal<string[]>([]);
  const [selectedVoice, setSelectedVoice] = createSignal('Ryan');
  const [conversationId] = createSignal('default');
  const [error, setError] = createSignal<Maybe<string>>(none());
  const [mediaRecorder, setMediaRecorder] = createSignal<Maybe<MediaRecorder>>(none());
  const [audioChunks, setAudioChunks] = createSignal<Blob[]>([]);

  // Load available voices on mount
  onMount(async () => {
    try {
      const availableVoices = await listVoices();
      setVoices(availableVoices);
      if (availableVoices.length > 0 && !availableVoices.includes(selectedVoice())) {
        setSelectedVoice(availableVoices[0]);
      }
    } catch (err) {
      console.error('Failed to load voices:', err);
      const errorMessage = err instanceof Error ? err.message : 'Failed to load voices';
      setError(just(errorMessage));
    }
  });

  const handleStartRecording = async () => {
    try {
      setError(none<string>());
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      
      // Create audio context for visualization (with proper type guard)
      interface WindowWithWebkitAudio extends Window {
        webkitAudioContext?: typeof AudioContext;
      }
      
      const getAudioContext = (): AudioContext => {
        if (window.AudioContext) {
          return new AudioContext();
        }
        const win = window as WindowWithWebkitAudio;
        if (win.webkitAudioContext) {
          return new win.webkitAudioContext();
        }
        throw new Error('AudioContext not supported in this browser');
      };
      
      const audioContext = getAudioContext();
      const analyser = audioContext.createAnalyser();
      const microphone = audioContext.createMediaStreamSource(stream);
      
      analyser.smoothingTimeConstant = 0.8;
      analyser.fftSize = 256;
      microphone.connect(analyser);
      
      // Start visualization loop
      const dataArray = new Uint8Array(analyser.frequencyBinCount);
      let animationFrameId: Maybe<number> = none();
      const updateLevel = () => {
        if (!isListening()) {
          if (isJust(animationFrameId)) {
            cancelAnimationFrame(animationFrameId.value);
            animationFrameId = none();
          }
          return;
        }
        
        analyser.getByteFrequencyData(dataArray);
        let sum = 0;
        for (let i = 0; i < dataArray.length; i++) {
          sum += dataArray[i];
        }
        const average = sum / dataArray.length / 255;
        setAudioLevel(average);
        
        if (isListening()) {
          animationFrameId = just(requestAnimationFrame(updateLevel));
        }
      };
      updateLevel();
      
      // Create MediaRecorder
      const recorder = new MediaRecorder(stream, {
        mimeType: 'audio/webm;codecs=opus',
      });
      
      const chunks: Blob[] = [];
      recorder.ondataavailable = (event) => {
        if (event.data.size > 0) {
          chunks.push(event.data);
        }
      };
      
      recorder.onstop = async () => {
        const blob = new Blob(chunks, { type: 'audio/webm' });
        await handleVoiceMessage(blob);
        stream.getTracks().forEach(track => track.stop());
        audioContext.close();
        const frameId = animationFrameId;
        if (isJust(frameId)) {
          cancelAnimationFrame(frameId.value);
        }
      };
      
      setMediaRecorder(just(recorder));
      setAudioChunks([]);
      recorder.start();
      setIsListening(true);
    } catch (err) {
      console.error('Failed to start recording:', err);
      const errorMessage = err instanceof Error ? err.message : 'Failed to access microphone';
      setError(just(errorMessage));
      alert('Failed to access microphone. Please check permissions.');
    }
  };

  const handleStopRecording = () => {
    const recorderMaybe = mediaRecorder();
    if (isJust(recorderMaybe) && recorderMaybe.value.state !== 'inactive') {
      recorderMaybe.value.stop();
    }
    setIsListening(false);
    setAudioLevel(0);
  };

  const handleVoiceMessage = async (audioBlob: Blob) => {
    setIsProcessing(true);
    setError(none<string>());
    
    try {
      // Add user message placeholder
      const userMessage: TranscriptMessage = {
        id: `user-${Date.now()}`,
        role: 'user',
        text: '...',
        timestamp: new Date(),
        audioUrl: none(),
      };
      setMessages(prev => [...prev, userMessage]);
      
      // Send to API
      const response: VoiceChatResponse = await sendVoiceMessage(
        audioBlob,
        conversationId(),
        selectedVoice(),
        'en'
      );
      
      // Update user message with transcript
      setMessages(prev => {
        const updated = [...prev];
        const lastIndex = updated.length - 1;
        if (updated[lastIndex]?.role === 'user') {
          updated[lastIndex] = {
            ...updated[lastIndex],
            text: response.user_transcript,
          };
        }
        return updated;
      });
      
      // Add assistant message
      if (response.assistant_text) {
        // Explicit check for audio URL using Maybe pattern
        const audioUrlMaybe: Maybe<string> = 
          response.assistant_audio && response.assistant_audio_format
            ? just(`data:audio/${response.assistant_audio_format};base64,${response.assistant_audio}`)
            : none();
        
        const assistantMessage: TranscriptMessage = {
          id: `assistant-${Date.now()}`,
          role: 'assistant',
          text: response.assistant_text,
          timestamp: new Date(),
          audioUrl: audioUrlMaybe,
        };
        setMessages(prev => [...prev, assistantMessage]);
        
        // Play audio if available (explicit check)
        if (response.assistant_audio && response.assistant_audio_format) {
          setIsSpeaking(true);
          const audioUrl = `data:audio/${response.assistant_audio_format};base64,${response.assistant_audio}`;
          const audio = new Audio(audioUrl);
          audio.onended = () => setIsSpeaking(false);
          audio.onerror = () => setIsSpeaking(false);
          audio.play().catch((err: unknown) => {
            const errorMessage = err instanceof Error ? err.message : 'Failed to play audio';
            console.error('Failed to play audio:', errorMessage);
            setIsSpeaking(false);
          });
        }
      }
      
      // Handle errors
      if (response.stt_error) {
        setError(just(`STT Error: ${response.stt_error}`));
      }
      if (response.chat_error) {
        setError(just(`Chat Error: ${response.chat_error}`));
      }
      if (response.tts_error) {
        setError(just(`TTS Error: ${response.tts_error}`));
      }
    } catch (err) {
      console.error('Voice message failed:', err);
      const errorMessage = err instanceof Error ? err.message : 'Failed to process voice message';
      setError(just(errorMessage));
      
      // Remove placeholder message on error
      setMessages(prev => prev.filter(m => m.id !== `user-${Date.now()}`));
    } finally {
      setIsProcessing(false);
    }
  };

  return (
    <div class="flex flex-col h-full">
      {/* Header */}
      <div class="flex items-center justify-between p-4 border-b">
        <h1 class="text-xl font-semibold">Voice Chat</h1>
        <VoiceSelector
          voices={voices()}
          selectedVoice={selectedVoice()}
          onVoiceChange={setSelectedVoice}
          disabled={isListening() || isProcessing()}
        />
      </div>

      {/* Error Display */}
      <Show when={isJust(error())}>
        <div class="bg-destructive/10 text-destructive px-4 py-2 text-sm">
          {fromMaybe(error(), '')}
        </div>
      </Show>

      {/* Main Content */}
      <div class="flex-1 flex flex-col items-center justify-center gap-8 p-8">
        {/* Audio Visualizer */}
        <AudioVisualizer
          audioLevel={audioLevel()}
          isActive={isListening() || isSpeaking()}
        />

        {/* Microphone Button */}
        <MicrophoneButton
          isListening={isListening()}
          isProcessing={isProcessing()}
          audioLevel={audioLevel()}
          onStart={handleStartRecording}
          onStop={handleStopRecording}
          disabled={isSpeaking()}
        />

        {/* Status Text */}
        <div class="text-center text-muted-foreground">
          <Show
            when={isListening()}
            fallback={
              <Show
                when={isProcessing()}
                fallback={
                  <Show
                    when={isSpeaking()}
                    fallback="Click the microphone to start speaking"
                  >
                    Assistant is speaking...
                  </Show>
                }
              >
                Processing your message...
              </Show>
            }
          >
            Listening... Speak now
          </Show>
        </div>
      </div>

      {/* Transcript */}
      <div class="border-t h-64">
        <TranscriptView messages={messages()} />
      </div>
    </div>
  );
}
