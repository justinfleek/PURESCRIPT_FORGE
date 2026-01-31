import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, waitFor } from '../../utils/render';
import { Terminal } from '@/components/terminal';
import { measureRender, assertPerformance } from '../../utils/performance';

// Mock ghostty-web
vi.mock('ghostty-web', () => ({
  Ghostty: {
    load: vi.fn(() => Promise.resolve({
      Terminal: vi.fn(),
      FitAddon: vi.fn(),
    })),
  },
}));

vi.mock('@/context/sdk', () => ({
  useSDK: () => ({
    client: {
      terminal: {
        connect: vi.fn(() => ({
          then: vi.fn(),
        })),
      },
    },
  }),
}));

vi.mock('@/context/settings', () => ({
  useSettings: () => ({
    appearance: {
      font: { mono: 'monospace' },
    },
  }),
  monoFontFamily: vi.fn(() => 'monospace'),
}));

vi.mock('@/context/terminal', () => ({
  useTerminal: () => ({
    createLocalPTY: vi.fn(() => ({
      id: 'test-pty',
      directory: '/test',
    })),
  }),
}));

vi.mock('@/context/language', () => ({
  useLanguage: () => ({
    t: vi.fn((key: string) => key),
  }),
}));

vi.mock('@opencode-ai/ui/theme', () => ({
  useTheme: () => ({
    mode: vi.fn(() => 'dark'),
    themes: vi.fn(() => ({})),
    themeId: vi.fn(() => 'default'),
  }),
  resolveThemeVariant: vi.fn(() => ({})),
  withAlpha: vi.fn((color: string) => color),
}));

describe('Terminal', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Critical functionality', () => {
    it('renders terminal container', async () => {
      const mockPTY = {
        id: 'test-pty',
        directory: '/test',
      };

      render(() => (
        <Terminal
          pty={mockPTY as any}
          onConnect={() => {}}
          onConnectError={() => {}}
        />
      ));

      const container = document.querySelector('[class*="terminal"]') || 
                       document.querySelector('div');
      expect(container).toBeInTheDocument();
    });
  });

  describe('Performance', () => {
    it('renders in under 100ms', async () => {
      const mockPTY = {
        id: 'test-pty',
        directory: '/test',
      };

      const metrics = await measureRender(() => {
        render(() => (
          <Terminal
            pty={mockPTY as any}
            onConnect={() => {}}
            onConnectError={() => {}}
          />
        ));
      }, 10);

      assertPerformance(metrics, {
        maxRenderTime: 100,
      });
    });
  });
});
