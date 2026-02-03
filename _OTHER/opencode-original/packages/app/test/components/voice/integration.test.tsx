import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';

describe('Voice Components - Real User Flows', () => {
  it('complete voice chat flow', async () => {
    const onStart = vi.fn();
    const onStop = vi.fn();
    const onVoiceChange = vi.fn();

    const { rerender } = render(() => (
      <>
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={[]} />
      </>
    ));

    // Start recording
    fireEvent.click(screen.getAllByRole('button')[0]);
    expect(onStart).toHaveBeenCalled();

    // Recording state
    rerender(() => (
      <>
        <MicrophoneButton
          isListening={true}
          isProcessing={false}
          audioLevel={0.5}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={[]} />
      </>
    ));

    // Stop recording
    fireEvent.click(screen.getAllByRole('button')[0]);
    expect(onStop).toHaveBeenCalled();

    // Show transcript
    const messages: TranscriptMessage[] = [
      {
        id: '1',
        role: 'user',
        text: 'Hello',
        timestamp: new Date(),
        audioUrl: null,
      },
    ];

    rerender(() => (
      <>
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={onStart}
          onStop={onStop}
        />
        <VoiceSelector
          voices={['Ryan', 'Alice']}
          selectedVoice="Ryan"
          onVoiceChange={onVoiceChange}
        />
        <TranscriptView messages={messages} />
      </>
    ));

    await waitFor(() => {
      expect(screen.getByText('Hello')).toBeInTheDocument();
    });
  });
});
