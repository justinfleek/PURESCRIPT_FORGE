import { createSignal, onCleanup } from "solid-js"

export interface VoiceConfig {
  onTranscript: (text: string) => void
  onError?: (error: string) => void
  language?: string
}

export function useVoice(config: VoiceConfig) {
  const [recording, setRecording] = createSignal(false)
  const [processing, setProcessing] = createSignal(false)
  
  let mediaRecorder: MediaRecorder | null = null
  let audioChunks: Blob[] = []

  const startRecording = async () => {
    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true })
      mediaRecorder = new MediaRecorder(stream, { mimeType: "audio/webm" })
      audioChunks = []

      mediaRecorder.ondataavailable = (event) => {
        if (event.data.size > 0) {
          audioChunks.push(event.data)
        }
      }

      mediaRecorder.onstop = async () => {
        setRecording(false)
        setProcessing(true)
        
        const audioBlob = new Blob(audioChunks, { type: "audio/webm" })
        
        try {
          const transcript = await transcribeAudio(audioBlob, config.language)
          config.onTranscript(transcript)
        } catch (err) {
          config.onError?.(err instanceof Error ? err.message : "Transcription failed")
        } finally {
          setProcessing(false)
        }
        
        stream.getTracks().forEach(track => track.stop())
      }

      mediaRecorder.start()
      setRecording(true)
    } catch (err) {
      config.onError?.(err instanceof Error ? err.message : "Failed to access microphone")
    }
  }

  const stopRecording = () => {
    if (mediaRecorder && mediaRecorder.state === "recording") {
      mediaRecorder.stop()
    }
  }

  const toggleRecording = () => {
    if (recording()) {
      stopRecording()
    } else {
      startRecording()
    }
  }

  onCleanup(() => {
    if (mediaRecorder && mediaRecorder.state === "recording") {
      mediaRecorder.stop()
    }
  })

  return {
    recording,
    processing,
    startRecording,
    stopRecording,
    toggleRecording,
  }
}

async function transcribeAudio(audioBlob: Blob, language = "en"): Promise<string> {
  // Check for Qwen/OpenAI-compatible whisper endpoint
  // This can be configured via environment or settings
  const endpoint = getWhisperEndpoint()
  
  if (!endpoint) {
    // Fallback to Web Speech API if available
    return transcribeWithWebSpeech(audioBlob, language)
  }

  const formData = new FormData()
  formData.append("file", audioBlob, "audio.webm")
  formData.append("model", "whisper-1")
  formData.append("language", language)

  const response = await fetch(`${endpoint}/v1/audio/transcriptions`, {
    method: "POST",
    body: formData,
  })

  if (!response.ok) {
    throw new Error(`Transcription failed: ${response.statusText}`)
  }

  const result = await response.json()
  return result.text || ""
}

function getWhisperEndpoint(): string | null {
  // Check localStorage for configured endpoint
  const stored = localStorage.getItem("forge-voice-endpoint")
  if (stored) return stored
  
  // Check common local endpoints
  // Qwen typically runs on these ports
  return null
}

async function transcribeWithWebSpeech(audioBlob: Blob, language: string): Promise<string> {
  return new Promise((resolve, reject) => {
    if (!("webkitSpeechRecognition" in window) && !("SpeechRecognition" in window)) {
      reject(new Error("Speech recognition not supported in this browser"))
      return
    }

    const SpeechRecognition = (window as any).SpeechRecognition || (window as any).webkitSpeechRecognition
    const recognition = new SpeechRecognition()
    
    recognition.lang = language
    recognition.interimResults = false
    recognition.maxAlternatives = 1

    let resolved = false

    recognition.onresult = (event: any) => {
      if (resolved) return
      resolved = true
      const transcript = event.results[0][0].transcript
      resolve(transcript)
    }

    recognition.onerror = (event: any) => {
      if (resolved) return
      resolved = true
      reject(new Error(event.error))
    }

    recognition.onend = () => {
      if (!resolved) {
        resolved = true
        resolve("")
      }
    }

    // For Web Speech API, we need to start fresh recognition
    // The audioBlob approach doesn't work directly, so we'll use live recognition
    recognition.start()
    
    // Auto-stop after 10 seconds
    setTimeout(() => {
      if (!resolved) {
        recognition.stop()
      }
    }, 10000)
  })
}

// Text-to-Speech using Qwen TTS
export async function speakText(text: string, voice = "default"): Promise<void> {
  const endpoint = getTTSEndpoint()
  
  if (!endpoint) {
    // Fallback to browser TTS
    return speakWithBrowserTTS(text)
  }

  const response = await fetch(`${endpoint}/v1/audio/speech`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({
      model: "tts-1",
      input: text,
      voice,
    }),
  })

  if (!response.ok) {
    throw new Error(`TTS failed: ${response.statusText}`)
  }

  const audioBlob = await response.blob()
  const audioUrl = URL.createObjectURL(audioBlob)
  const audio = new Audio(audioUrl)
  
  return new Promise((resolve, reject) => {
    audio.onended = () => {
      URL.revokeObjectURL(audioUrl)
      resolve()
    }
    audio.onerror = () => {
      URL.revokeObjectURL(audioUrl)
      reject(new Error("Audio playback failed"))
    }
    audio.play()
  })
}

function getTTSEndpoint(): string | null {
  const stored = localStorage.getItem("forge-tts-endpoint")
  return stored || null
}

function speakWithBrowserTTS(text: string): Promise<void> {
  return new Promise((resolve, reject) => {
    if (!("speechSynthesis" in window)) {
      reject(new Error("Speech synthesis not supported"))
      return
    }

    const utterance = new SpeechSynthesisUtterance(text)
    utterance.onend = () => resolve()
    utterance.onerror = () => reject(new Error("Speech synthesis failed"))
    
    window.speechSynthesis.speak(utterance)
  })
}
