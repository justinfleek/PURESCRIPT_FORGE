import { describe, it, expect } from 'vitest';
import { measureRender } from '../utils/performance';
import { render } from '../utils/render';
import { TranscriptView, type TranscriptMessage } from '@/components/voice/TranscriptView';

/**
 * Performance tests with realistic data distributions
 * Based on actual user behavior patterns
 */

describe('Realistic Performance Tests', () => {
  // Typical conversation: 5-15 messages
  it('typical conversation (10 messages) renders fast', async () => {
    const messages: TranscriptMessage[] = Array.from({ length: 10 }, (_, i) => ({
      id: `msg-${i}`,
      role: i % 2 === 0 ? 'user' : 'assistant',
      text: `Message ${i}: ${'x'.repeat(50)}`, // Typical message length
      timestamp: new Date(2024, 0, i + 1),
      audioUrl: i % 3 === 0 ? `https://example.com/audio${i}.mp3` : null,
    }));

    const metrics = await measureRender(() => {
      render(() => <TranscriptView messages={messages} />);
    }, 50);

    expect(metrics.renderTime).toBeLessThan(30);
  });

  // Long conversation: 50+ messages (rare but happens)
  it('long conversation (50 messages) still performs', async () => {
    const messages: TranscriptMessage[] = Array.from({ length: 50 }, (_, i) => ({
      id: `msg-${i}`,
      role: i % 2 === 0 ? 'user' : 'assistant',
      text: `Message ${i}: ${'x'.repeat(100)}`,
      timestamp: new Date(2024, 0, i + 1),
      audioUrl: null,
    }));

    const metrics = await measureRender(() => {
      render(() => <TranscriptView messages={messages} />);
    }, 20);

    expect(metrics.renderTime).toBeLessThan(150);
  });

  // Empty state (common on first load)
  it('empty state renders instantly', async () => {
    const metrics = await measureRender(() => {
      render(() => <TranscriptView messages={[]} />);
    }, 100);

    expect(metrics.renderTime).toBeLessThan(5);
  });
});
