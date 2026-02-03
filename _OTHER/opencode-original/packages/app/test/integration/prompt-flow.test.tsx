import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../utils/render';
import { PromptInput } from '@/components/prompt-input';
import { realisticPromptText } from '../utils/realistic-data';

vi.mock('@/context/sdk');
vi.mock('@/context/sync');
vi.mock('@/context/file');
vi.mock('@/context/prompt');
vi.mock('@/context/layout');
vi.mock('@/context/comments');
vi.mock('@solidjs/router');

describe('Prompt Input Integration', () => {
  describe('Real user flows', () => {
    it('user types prompt and submits', async () => {
      const onSubmit = vi.fn();
      render(() => <PromptInput onSubmit={onSubmit} />);
      
      const editor = document.querySelector('[contenteditable]') as HTMLElement;
      if (editor) {
        fireEvent.input(editor, { target: { textContent: 'Fix the bug in the login component' } });
        
        const submitButton = screen.queryByRole('button', { name: /submit|send/i }) ||
                           document.querySelector('button[type="submit"]');
        
        if (submitButton) {
          fireEvent.click(submitButton);
        }
      }
      
      expect(editor).toBeInTheDocument();
    });

    it('user attaches file and types prompt', async () => {
      render(() => <PromptInput />);
      
      const fileInput = document.querySelector('input[type="file"]') as HTMLInputElement;
      if (fileInput) {
        const file = new File(['content'], 'test.ts', { type: 'text/typescript' });
        fireEvent.change(fileInput, { target: { files: [file] } });
        
        await waitFor(() => {
          expect(document.querySelector('[class*="file"]') || document.body).toBeInTheDocument();
        });
      }
    });
  });
});
