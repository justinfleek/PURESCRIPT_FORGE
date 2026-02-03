import { describe, it, expect } from 'vitest';
import { measureRender, measureUpdate, assertPerformance } from '../utils/performance';
import { render } from '../utils/render';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { realisticTranscriptMessage, realisticVoiceName } from '../utils/realistic-data';
import * as fc from 'fast-check';

/**
 * Performance benchmarks with realistic data distributions
 * Tests actual usage patterns, not edge cases
 */

describe('Realistic Performance Benchmarks', () => {
  describe('TranscriptView - Real conversation patterns', () => {
    it('handles typical conversation (5-10 messages)', async () => {
      const messages: TranscriptMessage[] = Array.from({ length: 8 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: i % 2 === 0 
          ? `User message ${i}: Can you help with this?`
          : `Assistant response ${i}: Sure, I can help!`,
        timestamp: new Date(2024, 0, 1, 10, 0, i),
        audioUrl: i % 2 === 1 ? 'https://example.com/audio.mp3' : null,
      }));

      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={messages} />);
      }, 50);

      assertPerformance(metrics, {
        maxRenderTime: 25,
      });
    });

    it('handles long conversation (50+ messages)', async () => {
      const messages: TranscriptMessage[] = Array.from({ length: 50 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: `Message ${i}: ${'x'.repeat(50)}`,
        timestamp: new Date(2024, 0, 1, 10, 0, i),
        audioUrl: null,
      }));

      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={messages} />);
      }, 20);

      assertPerformance(metrics, {
        maxRenderTime: 80,
      });
    });
  });

  describe('VoiceSelector - Real voice lists', () => {
    it('handles typical voice list (5-15 voices)', async () => {
      const voices = ['Ryan', 'Alice', 'Bob', 'Charlie', 'Diana', 'Eve', 'Frank', 'Grace'];
      
      const metrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={voices}
            selectedVoice="Ryan"
            onVoiceChange={() => {}}
          />
        ));
      }, 50);

      assertPerformance(metrics, {
        maxRenderTime: 15,
      });
    });

    it('handles large voice list (50+ voices)', async () => {
      const voices = Array.from({ length: 50 }, (_, i) => `Voice${i}`);
      
      const metrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={voices}
            selectedVoice="Voice0"
            onVoiceChange={() => {}}
          />
        ));
      }, 20);

      assertPerformance(metrics, {
        maxRenderTime: 50,
      });
    });
  });

  describe('Property-based performance', () => {
    it('performance scales reasonably with message count', async () => {
      const results = await Promise.all(
        [5, 10, 20, 50].map(async (count) => {
          const messages: TranscriptMessage[] = Array.from({ length: count }, (_, i) => ({
            id: `msg-${i}`,
            role: i % 2 === 0 ? 'user' : 'assistant',
            text: `Message ${i}`,
            timestamp: new Date(2024, 0, 1, 10, 0, i),
            audioUrl: null,
          }));

          const metrics = await measureRender(() => {
            render(() => <TranscriptView messages={messages} />);
          }, 10);

          return { count, renderTime: metrics.renderTime };
        })
      );

      const ratio5to50 = results[3].renderTime / results[0].renderTime;
      expect(ratio5to50).toBeLessThan(15);
    });
  });
});
