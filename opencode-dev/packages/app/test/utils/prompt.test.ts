import { describe, it, expect } from 'vitest';
import { extractPromptFromParts } from '@/utils/prompt';
import type { Part } from '@opencode-ai/sdk/v2';

describe('prompt utilities', () => {
  it('extracts text from simple message', () => {
    const parts: Part[] = [
      { type: 'text', text: 'Hello world', synthetic: false, ignored: false },
    ];
    const prompt = extractPromptFromParts(parts);
    expect(prompt.length).toBe(1);
    expect(prompt[0].type).toBe('text');
    if (prompt[0].type === 'text') {
      expect(prompt[0].content).toBe('Hello world');
    }
  });

  it('extracts file references', () => {
    const parts: Part[] = [
      { type: 'text', text: 'Check @file.ts', synthetic: false, ignored: false },
      {
        type: 'file',
        id: 'f1',
        filename: 'file.ts',
        url: 'file:///path/to/file.ts?start=1&end=10',
        source: {
          text: { value: '@file.ts', start: 6, end: 14 },
          path: '/path/to/file.ts',
        },
      },
    ];
    const prompt = extractPromptFromParts(parts, { directory: '/path/to' });
    expect(prompt.some(p => p.type === 'file')).toBe(true);
  });

  it('handles empty parts', () => {
    const prompt = extractPromptFromParts([]);
    expect(prompt.length).toBe(1);
    expect(prompt[0].type).toBe('text');
    if (prompt[0].type === 'text') {
      expect(prompt[0].content).toBe('');
    }
  });

  it('extracts images from data URLs', () => {
    const parts: Part[] = [
      {
        type: 'file',
        id: 'img1',
        filename: 'image.png',
        url: 'data:image/png;base64,iVBORw0KGgo=',
        mime: 'image/png',
      },
    ];
    const prompt = extractPromptFromParts(parts);
    expect(prompt.some(p => p.type === 'image')).toBe(true);
  });
});
