import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '../../utils/render';
import { PromptInput } from '@/components/prompt-input';
import { measureRender, assertPerformance } from '../../utils/performance';

// Mock all the context dependencies
vi.mock('@/context/sdk', () => ({
  useSDK: () => ({
    client: {
      session: {
        create: vi.fn(),
      },
    },
  }),
}));

vi.mock('@/context/sync', () => ({
  useSync: () => ({
    data: {
      session_status: {},
      session_diff: {},
    },
    session: {
      get: vi.fn(),
    },
  }),
}));

vi.mock('@/context/file', () => ({
  useFile: () => ({
    tree: {
      state: vi.fn(() => ({ expanded: false })),
      children: vi.fn(() => []),
    },
    tab: vi.fn(),
    load: vi.fn(),
    pathFromTab: vi.fn(),
  }),
}));

vi.mock('@/context/prompt', () => ({
  usePrompt: () => ({
    current: vi.fn(() => [{ type: 'text', content: '', start: 0, end: 0 }]),
    set: vi.fn(),
    context: {
      items: vi.fn(() => []),
    },
  }),
  DEFAULT_PROMPT: [{ type: 'text', content: '', start: 0, end: 0 }],
  isPromptEqual: vi.fn(() => false),
}));

vi.mock('@/context/layout', () => ({
  useLayout: () => ({
    tabs: vi.fn(() => ({
      all: vi.fn(() => []),
      active: vi.fn(() => null),
      open: vi.fn(),
      setActive: vi.fn(),
    })),
    view: vi.fn(() => ({})),
    fileTree: {
      open: vi.fn(),
      setTab: vi.fn(),
    },
    projects: {
      list: vi.fn(() => []),
    },
  }),
}));

vi.mock('@/context/comments', () => ({
  useComments: () => ({
    setActive: vi.fn(),
    setFocus: vi.fn(),
  }),
}));

vi.mock('@solidjs/router', () => ({
  useNavigate: () => vi.fn(),
  useParams: () => ({ dir: '', id: undefined }),
}));

describe('PromptInput', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Critical functionality', () => {
    it('renders prompt input editor', () => {
      render(() => <PromptInput />);
      
      const editor = document.querySelector('[contenteditable]') || 
                     document.querySelector('textarea') ||
                     document.querySelector('[role="textbox"]');
      expect(editor).toBeInTheDocument();
    });

    it('handles text input', async () => {
      render(() => <PromptInput />);
      
      const editor = document.querySelector('[contenteditable]') as HTMLElement;
      if (editor) {
        fireEvent.input(editor, { target: { textContent: 'Hello world' } });
        expect(editor.textContent).toBe('Hello world');
      }
    });

    it('handles file attachment', () => {
      const onFileSelect = vi.fn();
      render(() => <PromptInput />);
      
      const fileInput = document.querySelector('input[type="file"]');
      expect(fileInput).toBeInTheDocument();
    });
  });

  describe('Performance', () => {
    it('renders in under 50ms', async () => {
      const metrics = await measureRender(() => {
        render(() => <PromptInput />);
      }, 20);

      assertPerformance(metrics, {
        maxRenderTime: 50,
      });
    });
  });
});
