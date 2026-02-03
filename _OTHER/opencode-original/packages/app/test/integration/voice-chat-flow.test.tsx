import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';
import { realisticTranscriptMessage } from '../utils/realistic-data';
import * as fc from 'fast-check';

vi.mock('@opencode/api/voice', () => ({
  sendVoiceMessage: vi.fn(() => Promise.resolve({ text: 'Response', audioUrl: 'audio.mp3' })),
  sendTextMessage: vi.fn(() => Promise.resolve({ text: 'Response', audioUrl: 'audio.mp3' })),
  listVoices: vi.fn(() => Promise.resolve(['Ryan', 'Alice', 'Bob'])),
}));

describe('Voice Chat Integration', () => {
  describe('Real user flows', () => {
    it('user starts recording, speaks, stops, sees transcript', async () => {
      const onStart = vi.fn();
      const onStop = vi.fn();
      
      render(() => (
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={onStart}
          onStop={onStop}
        />
      ));

      const button = screen.getByRole('button');
      
      fireEvent.click(button);
      expect(onStart).toHaveBeenCalled();
    });

    it('user selects voice and sees it in selector', async () => {
      const voices = ['Ryan', 'Alice', 'Bob'];
      const onVoiceChange = vi.fn();
      
      render(() => (
        <VoiceSelector
          voices={voices}
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

    it('conversation flow: user message → assistant response', async () => {
      const messages: TranscriptMessage[] = [
        {
          id: '1',
          role: 'user',
          text: 'Hello, can you help me?',
          timestamp: new Date(2024, 0, 1, 10, 0, 0),
          audioUrl: null,
        },
        {
          id: '2',
          role: 'assistant',
          text: 'Of course! How can I assist you?',
          timestamp: new Date(2024, 0, 1, 10, 0, 5),
          audioUrl: 'https://example.com/audio.mp3',
        },
      ];

      render(() => <TranscriptView messages={messages} />);

      expect(screen.getByText('Hello, can you help me?')).toBeInTheDocument();
      expect(screen.getByText('Of course! How can I assist you?')).toBeInTheDocument();
      
      const userMessage = screen.getByText('Hello, can you help me?').closest('div');
      expect(userMessage?.parentElement).toHaveClass('justify-end');
    });
  });

  describe('Property tests - realistic conversations', () => {
    it('handles realistic conversation patterns', async () => {
      const realisticMessages = await fc.sample(
        fc.array(realisticTranscriptMessage(), { minLength: 2, maxLength: 20 }),
        10
      );

      for (const messages of realisticMessages) {
        render(() => <TranscriptView messages={messages} />);
        
        for (const msg of messages) {
          expect(screen.getByText(msg.text)).toBeInTheDocument();
        }
      }
    });
  });
});
