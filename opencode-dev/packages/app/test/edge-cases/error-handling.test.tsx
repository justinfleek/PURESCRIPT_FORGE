import { describe, it, expect, vi } from 'vitest';
import { render } from '../utils/render';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';
import { VoiceSelector } from '@/components/voice/VoiceSelector';

describe('Error Handling', () => {
  describe('TranscriptView', () => {
    it('handles malformed messages gracefully', () => {
      const malformedMessages = [
        {
          id: '1',
          role: 'user' as const,
          text: '',
          timestamp: new Date(),
          audioUrl: null,
        },
        {
          id: '2',
          role: 'assistant' as const,
          text: null as any,
          timestamp: new Date(),
          audioUrl: null,
        },
      ];

      expect(() => {
        render(() => <TranscriptView messages={malformedMessages as any} />);
      }).not.toThrow();
    });

    it('handles empty messages array', () => {
      expect(() => {
        render(() => <TranscriptView messages={[]} />);
      }).not.toThrow();
    });

    it('handles very long messages', () => {
      const longMessage: TranscriptMessage = {
        id: '1',
        role: 'assistant',
        text: 'x'.repeat(10000),
        timestamp: new Date(),
        audioUrl: null,
      };

      expect(() => {
        render(() => <TranscriptView messages={[longMessage]} />);
      }).not.toThrow();
    });
  });

  describe('VoiceSelector', () => {
    it('handles empty voices array', () => {
      expect(() => {
        render(() => (
          <VoiceSelector
            voices={[]}
            selectedVoice=""
            onVoiceChange={() => {}}
          />
        ));
      }).not.toThrow();
    });

    it('handles selectedVoice not in voices array', () => {
      expect(() => {
        render(() => (
          <VoiceSelector
            voices={['Alice', 'Bob']}
            selectedVoice="NotInList"
            onVoiceChange={() => {}}
          />
        ));
      }).not.toThrow();
    });
  });
});
