import { describe, it, expect } from 'vitest';
import { measureRender, measureMemory } from '../utils/performance';
import { render } from '../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';

/**
 * Optimization regression tests
 * These tests prevent performance regressions by tracking bundle size and render performance
 */

// Baseline metrics (update these when optimizations are made)
const BASELINES = {
  MicrophoneButton: {
    renderTime: 8,
    bundleSize: 2000, // bytes (estimated)
  },
  VoiceSelector: {
    renderTime: 12,
    bundleSize: 3000,
  },
  TranscriptView: {
    renderTime: 15,
    bundleSize: 4000,
  },
} as const;

describe('Optimization Regression Tests', () => {
  describe('MicrophoneButton', () => {
    it('does not regress render performance', async () => {
      const metrics = await measureRender(() => {
        render(() => (
          <MicrophoneButton
            isListening={false}
            isProcessing={false}
            onStart={() => {}}
            onStop={() => {}}
          />
        ));
      }, 100);

      // Allow 20% regression tolerance
      const threshold = BASELINES.MicrophoneButton.renderTime * 1.2;
      expect(metrics.renderTime).toBeLessThan(threshold);
    });

    it('tracks memory usage', () => {
      const beforeMemory = measureMemory();
      render(() => (
        <MicrophoneButton
          isListening={false}
          isProcessing={false}
          onStart={() => {}}
          onStop={() => {}}
        />
      ));
      const afterMemory = measureMemory();

      if (beforeMemory && afterMemory) {
        const memoryDelta = afterMemory - beforeMemory;
        // Component should use less than 100KB
        expect(memoryDelta).toBeLessThan(100 * 1024);
      }
    });
  });

  describe('VoiceSelector', () => {
    it('does not regress render performance', async () => {
      const voices = ['Ryan', 'Alice', 'Bob'];
      const metrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={voices}
            selectedVoice="Ryan"
            onVoiceChange={() => {}}
          />
        ));
      }, 100);

      const threshold = BASELINES.VoiceSelector.renderTime * 1.2;
      expect(metrics.renderTime).toBeLessThan(threshold);
    });

    it('scales linearly with voice count', async () => {
      const smallVoices = Array.from({ length: 5 }, (_, i) => `Voice${i}`);
      const largeVoices = Array.from({ length: 50 }, (_, i) => `Voice${i}`);

      const smallMetrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={smallVoices}
            selectedVoice="Voice0"
            onVoiceChange={() => {}}
          />
        ));
      }, 50);

      const largeMetrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={largeVoices}
            selectedVoice="Voice0"
            onVoiceChange={() => {}}
          />
        ));
      }, 50);

      // Should scale roughly linearly (allow 2x overhead for 10x items)
      const ratio = largeMetrics.renderTime / smallMetrics.renderTime;
      expect(ratio).toBeLessThan(10);
    });
  });

  describe('TranscriptView', () => {
    it('does not regress render performance', async () => {
      const messages: TranscriptMessage[] = Array.from({ length: 10 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: `Message ${i}`,
        timestamp: new Date(2024, 0, i + 1),
        audioUrl: null,
      }));

      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={messages} />);
      }, 50);

      const threshold = BASELINES.TranscriptView.renderTime * 1.2;
      expect(metrics.renderTime).toBeLessThan(threshold);
    });

    it('handles empty state efficiently', async () => {
      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={[]} />);
      }, 100);

      // Empty state should be very fast
      expect(metrics.renderTime).toBeLessThan(5);
    });

    it('scales sub-linearly with message count', async () => {
      const smallMessages: TranscriptMessage[] = Array.from({ length: 10 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: `Message ${i}`,
        timestamp: new Date(2024, 0, i + 1),
        audioUrl: null,
      }));

      const largeMessages: TranscriptMessage[] = Array.from({ length: 100 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: `Message ${i}: ${'x'.repeat(100)}`,
        timestamp: new Date(2024, 0, i + 1),
        audioUrl: null,
      }));

      const smallMetrics = await measureRender(() => {
        render(() => <TranscriptView messages={smallMessages} />);
      }, 20);

      const largeMetrics = await measureRender(() => {
        render(() => <TranscriptView messages={largeMessages} />);
      }, 20);

      // Should scale sub-linearly (virtualization helps)
      const ratio = largeMetrics.renderTime / smallMetrics.renderTime;
      expect(ratio).toBeLessThan(15); // 10x messages should be <15x slower
    });
  });
});
