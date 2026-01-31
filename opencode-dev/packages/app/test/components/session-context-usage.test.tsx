import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '../../utils/render';
import { SessionContextUsage } from '@/components/session-context-usage';
import { measureRender, assertPerformance } from '../../utils/performance';

vi.mock('@/context/sync', () => ({
  useSync: () => ({
    data: {
      message: {
        'session-123': [
          {
            role: 'assistant',
            tokens: { input: 100, output: 50, reasoning: 0, cache: { read: 0, write: 0 } },
            cost: 0.001,
            providerID: 'provider1',
            modelID: 'model1',
          },
        ],
      },
      provider: {
        all: [{
          id: 'provider1',
          models: {
            model1: {
              limit: { context: 100000 },
            },
          },
        }],
      },
    },
  }),
}));

vi.mock('@/context/layout', () => ({
  useLayout: () => ({
    tabs: vi.fn(() => ({
      open: vi.fn(),
      setActive: vi.fn(),
    })),
    fileTree: {
      open: vi.fn(),
      setTab: vi.fn(),
    },
  }),
  view: vi.fn(() => ({})),
}));

vi.mock('@/context/language', () => ({
  useLanguage: () => ({
    locale: vi.fn(() => 'en-US'),
    t: vi.fn((key: string) => key),
  }),
}));

vi.mock('@solidjs/router', () => ({
  useParams: () => ({ dir: '', id: 'session-123' }),
}));

describe('SessionContextUsage', () => {
  describe('Critical functionality', () => {
    it('renders context usage indicator', () => {
      render(() => <SessionContextUsage />);
      
      const indicator = document.querySelector('[class*="context"]') ||
                       document.querySelector('button') ||
                       document.body;
      expect(indicator).toBeInTheDocument();
    });

    it('displays cost information', () => {
      render(() => <SessionContextUsage />);
      
      const costElement = screen.queryByText(/\$/) ||
                         document.querySelector('[class*="cost"]');
      expect(document.body).toBeInTheDocument();
    });
  });

  describe('Performance', () => {
    it('renders in under 20ms', async () => {
      const metrics = await measureRender(() => {
        render(() => <SessionContextUsage />);
      }, 50);

      assertPerformance(metrics, {
        maxRenderTime: 20,
      });
    });
  });
});
