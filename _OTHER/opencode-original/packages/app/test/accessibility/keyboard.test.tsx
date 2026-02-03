import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../utils/render';
import { MicrophoneButton } from '@/components/voice/MicrophoneButton';
import { VoiceSelector } from '@/components/voice/VoiceSelector';

describe('Keyboard Accessibility', () => {
  describe('MicrophoneButton', () => {
    it('is keyboard accessible', () => {
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
      
      button.focus();
      expect(document.activeElement).toBe(button);
      
      fireEvent.keyDown(button, { key: 'Enter', code: 'Enter' });
      fireEvent.keyUp(button, { key: 'Enter', code: 'Enter' });
      
      fireEvent.keyDown(button, { key: ' ', code: 'Space' });
      fireEvent.keyUp(button, { key: ' ', code: 'Space' });
    });

    it('shows disabled state to screen readers', () => {
      render(() => (
        <MicrophoneButton
          isListening={false}
          isProcessing={true}
          onStart={() => {}}
          onStop={() => {}}
        />
      ));

      const button = screen.getByRole('button');
      expect(button).toBeDisabled();
      expect(button).toHaveAttribute('aria-disabled', 'true');
    });
  });

  describe('VoiceSelector', () => {
    it('keyboard navigation works', async () => {
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
      
      button.focus();
      fireEvent.keyDown(button, { key: 'Enter' });
      
      await waitFor(() => {
        expect(screen.getByText('Alice')).toBeInTheDocument();
      });
    });
  });
});
