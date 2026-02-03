import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';

// Mock realistic user scenarios
describe('Voice Chat Integration', () => {
  it('user starts recording, speaks, stops, sees transcript', async () => {
    const onStart = vi.fn();
    const onStop = vi.fn();
    const onVoiceChange = vi.fn();

    render(() => (
      <div>
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice', 'Bob']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={[]} />
      </div>
    ));

    // User clicks microphone
    const micButton = screen.getByRole('button');
    fireEvent.click(micButton);
    expect(onStart).toHaveBeenCalled();

    // Simulate recording state
    const { rerender } = render(() => (
      <div>
        <MicrophoneButton
          isListening={true}
          isProcessing={false}
          audioLevel={0.7}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice', 'Bob']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={[]} />
      </div>
    ));

    // User stops recording
    const stopButton = screen.getByRole('button');
    fireEvent.click(stopButton);
    expect(onStop).toHaveBeenCalled();

    // User sees transcript
    const messages: TranscriptMessage[] = [
      {
        id: '1',
        role: 'user',
        text: 'Hello, how are you?',
        timestamp: new Date(),
        audioUrl: null,
      },
      {
        id: '2',
        role: 'assistant',
        text: 'I am doing well, thank you!',
        timestamp: new Date(),
        audioUrl: 'https://example.com/audio.mp3',
      },
    ];

    rerender(() => (
      <div>
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice', 'Bob']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={messages} />
      </div>
    ));

    await waitFor(() => {
      expect(screen.getByText('Hello, how are you?')).toBeInTheDocument();
      expect(screen.getByText('I am doing well, thank you!')).toBeInTheDocument();
    });
  });

  it('user changes voice during conversation', async () => {
    const onVoiceChange = vi.fn();
    const { rerender } = render(() => (
      <VoiceSelector
        voices={['Ryan', 'Alice', 'Bob']}
        selectedVoice="Ryan"
        onVoiceChange={onVoiceChange}
      />
    ));

    const button = screen.getByRole('button');
    fireEvent.click(button);

    await waitFor(() => {
      const aliceOption = screen.getByText('Alice');
      fireEvent.click(aliceOption);
    });

    expect(onVoiceChange).toHaveBeenCalledWith('Alice');
  });
});
