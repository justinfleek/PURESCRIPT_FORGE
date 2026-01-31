import { describe, it, expect, vi, beforeEach } from 'vitest';
import { createRoot } from 'solid-js';
import { isPromptEqual, DEFAULT_PROMPT, type Prompt } from '@/context/prompt';
import * as fc from 'fast-check';
import { realisticPrompt } from '../utils/realistic-data';

describe('Prompt context', () => {
  describe('isPromptEqual', () => {
    it('returns true for identical prompts', () => {
      const prompt: Prompt = [
        { type: 'text', content: 'Hello', start: 0, end: 5 },
      ];
      expect(isPromptEqual(prompt, prompt)).toBe(true);
    });

    it('returns false for different content', () => {
      const prompt1: Prompt = [
        { type: 'text', content: 'Hello', start: 0, end: 5 },
      ];
      const prompt2: Prompt = [
        { type: 'text', content: 'World', start: 0, end: 5 },
      ];
      expect(isPromptEqual(prompt1, prompt2)).toBe(false);
    });

    it('returns false for different lengths', () => {
      const prompt1: Prompt = [
        { type: 'text', content: 'Hello', start: 0, end: 5 },
      ];
      const prompt2: Prompt = [
        { type: 'text', content: 'Hello', start: 0, end: 5 },
        { type: 'text', content: ' World', start: 5, end: 11 },
      ];
      expect(isPromptEqual(prompt1, prompt2)).toBe(false);
    });

    it('compares file parts correctly', () => {
      const prompt1: Prompt = [
        { type: 'file', path: 'test.ts', content: '@test.ts', start: 0, end: 8 },
      ];
      const prompt2: Prompt = [
        { type: 'file', path: 'test.ts', content: '@test.ts', start: 0, end: 8 },
      ];
      expect(isPromptEqual(prompt1, prompt2)).toBe(true);
    });

    it('compares file parts with different selections', () => {
      const prompt1: Prompt = [
        {
          type: 'file',
          path: 'test.ts',
          content: '@test.ts',
          start: 0,
          end: 8,
          selection: { startLine: 1, startChar: 0, endLine: 5, endChar: 0 },
        },
      ];
      const prompt2: Prompt = [
        {
          type: 'file',
          path: 'test.ts',
          content: '@test.ts',
          start: 0,
          end: 8,
          selection: { startLine: 1, startChar: 0, endLine: 10, endChar: 0 },
        },
      ];
      expect(isPromptEqual(prompt1, prompt2)).toBe(false);
    });
  });

  describe('Property tests - realistic prompts', () => {
    it('isPromptEqual is reflexive', async () => {
      await fc.assert(
        fc.asyncProperty(
          realisticPrompt(),
          async (prompt) => {
            return isPromptEqual(prompt as Prompt, prompt as Prompt) === true;
          }
        ),
        { numRuns: 50 }
      );
    });

    it('isPromptEqual is symmetric', async () => {
      await fc.assert(
        fc.asyncProperty(
          realisticPrompt(),
          realisticPrompt(),
          async (a, b) => {
            return isPromptEqual(a as Prompt, b as Prompt) === 
                   isPromptEqual(b as Prompt, a as Prompt);
          }
        ),
        { numRuns: 50 }
      );
    });

    it('detects content differences', async () => {
      await fc.assert(
        fc.asyncProperty(
          realisticPrompt(),
          async (prompt) => {
            if (prompt.length === 0) return true;
            
            const modified = [...prompt];
            if (modified[0] && 'content' in modified[0]) {
              modified[0] = { ...modified[0], content: modified[0].content + 'X' };
            }
            
            return isPromptEqual(prompt as Prompt, modified as Prompt) === false;
          }
        ),
        { numRuns: 50 }
      );
    });
  });
});
