import { describe, it, expect } from 'vitest';
import { measureRender, measureUpdate, assertPerformance } from '../utils/performance';
import { render } from '../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';
import { AudioVisualizer } from '@/components/voice/AudioVisualizer';

/**
 * Performance benchmarks for UI components
 * These tests ensure components meet performance targets
 */

describe('Performance Benchmarks', () => {
  describe('MicrophoneButton', () => {
    it('meets render time target (<10ms)', async () => {
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

      assertPerformance(metrics, {
        maxRenderTime: 10,
      });
    });

    it('meets update time target (<5ms)', async () => {
      let isListening = false;
      const { rerender } = render(() => (
        <MicrophoneButton
          isListening={isListening}
          isProcessing={false}
          onStart={() => {}}
          onStop={() => {}}
        />
      ));

      const updateTime = await measureUpdate(() => {
        isListening = !isListening;
        rerender(() => (
          <MicrophoneButton
            isListening={isListening}
            isProcessing={false}
            onStart={() => {}}
            onStop={() => {}}
          />
        ));
      }, 100);

      expect(updateTime).toBeLessThan(5);
    });
  });

  describe('VoiceSelector', () => {
    it('meets render time target (<15ms)', async () => {
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

      assertPerformance(metrics, {
        maxRenderTime: 15,
      });
    });

    it('scales well with many voices (<50ms for 100 voices)', async () => {
      const voices = Array.from({ length: 100 }, (_, i) => `Voice${i}`);
      const metrics = await measureRender(() => {
        render(() => (
          <VoiceSelector
            voices={voices}
            selectedVoice="Voice0"
            onVoiceChange={() => {}}
          />
        ));
      }, 50);

      assertPerformance(metrics, {
        maxRenderTime: 50,
      });
    });
  });

  describe('TranscriptView', () => {
    it('meets render time target for empty state (<5ms)', async () => {
      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={[]} />);
      }, 100);

      assertPerformance(metrics, {
        maxRenderTime: 5,
      });
    });

    it('meets render time target for 10 messages (<20ms)', async () => {
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

      assertPerformance(metrics, {
        maxRenderTime: 20,
      });
    });

    it('handles large message lists efficiently (<100ms for 100 messages)', async () => {
      const messages: TranscriptMessage[] = Array.from({ length: 100 }, (_, i) => ({
        id: `msg-${i}`,
        role: i % 2 === 0 ? 'user' : 'assistant',
        text: `Message ${i}: ${'x'.repeat(100)}`,
        timestamp: new Date(2024, 0, i + 1),
        audioUrl: null,
      }));

      const metrics = await measureRender(() => {
        render(() => <TranscriptView messages={messages} />);
      }, 20);

      assertPerformance(metrics, {
        maxRenderTime: 100,
      });
    });
  });

  describe('AudioVisualizer', () => {
    it('meets render time target (<5ms)', async () => {
      const metrics = await measureRender(() => {
        render(() => <AudioVisualizer audioLevel={0.5} isActive={true} />);
      }, 100);

      assertPerformance(metrics, {
        maxRenderTime: 5,
      });
    });

    it('handles rapid updates efficiently (<2ms per update)', async () => {
      let audioLevel = 0.5;
      const { rerender } = render(() => (
        <AudioVisualizer audioLevel={audioLevel} isActive={true} />
      ));

      const updateTime = await measureUpdate(() => {
        audioLevel = Math.random();
        rerender(() => <AudioVisualizer audioLevel={audioLevel} isActive={true} />);
      }, 100);

      expect(updateTime).toBeLessThan(2);
    });
  });
});
