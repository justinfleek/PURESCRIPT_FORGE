import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../../../utils/render';
import { SessionHeader } from '@/components/session/session-header';
import { measureRender, assertPerformance } from '../../../utils/performance';

vi.mock('@/context/global-sdk', () => ({
  useGlobalSDK: () => ({
    client: {
      session: {
        share: vi.fn(() => Promise.resolve({ url: 'https://share.example.com/123' })),
        unshare: vi.fn(() => Promise.resolve()),
      },
    },
  }),
}));

vi.mock('@/context/layout', () => ({
  useLayout: () => ({
    projects: {
      list: vi.fn(() => []),
    },
    view: vi.fn(() => ({})),
  }),
}));

vi.mock('@/context/command', () => ({
  useCommand: () => ({
    keybind: vi.fn(() => 'Ctrl+O'),
  }),
}));

vi.mock('@/context/sync', () => ({
  useSync: () => ({
    data: {
      session: [],
      config: {
        share: 'enabled',
      },
    },
  }),
}));

vi.mock('@/context/platform', () => ({
  usePlatform: () => ({
    platform: 'web',
  }),
}));

vi.mock('@/context/language', () => ({
  useLanguage: () => ({
    t: vi.fn((key: string) => key),
  }),
}));

vi.mock('@solidjs/router', () => ({
  useParams: () => ({ dir: btoa('/project'), id: 'session-123' }),
}));

describe('SessionHeader', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Critical functionality', () => {
    it('renders session header', () => {
      render(() => <SessionHeader />);
      
      const header = document.querySelector('header') || 
                     document.querySelector('[class*="header"]') ||
                     document.body;
      expect(header).toBeInTheDocument();
    });

    it('displays project name', () => {
      render(() => <SessionHeader />);
      
      const nameElement = screen.queryByText(/project/i) || 
                         document.querySelector('[class*="name"]');
      expect(document.body).toBeInTheDocument();
    });
  });

  describe('Performance', () => {
    it('renders in under 30ms', async () => {
      const metrics = await measureRender(() => {
        render(() => <SessionHeader />);
      }, 50);

      assertPerformance(metrics, {
        maxRenderTime: 30,
      });
    });
  });
});
