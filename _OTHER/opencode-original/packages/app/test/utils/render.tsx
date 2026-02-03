import { render as solidRender, type JSX } from 'solid-js/web';
import { render as rtlRender } from '@testing-library/solid';
import { Router } from '@solidjs/router';
import { ThemeProvider } from '@opencode-ai/ui/theme';
import { DialogProvider } from '@opencode-ai/ui/context/dialog';
import { ErrorBoundary } from 'solid-js';

/**
 * Render SolidJS component with all necessary providers
 */
export function renderWithProviders(
  ui: () => JSX.Element,
  options: {
    initialEntries?: string[];
    theme?: 'light' | 'dark';
  } = {}
) {
  const { initialEntries = ['/'], theme = 'light' } = options;

  const Wrapper = (props: { children: JSX.Element }) => (
    <ErrorBoundary fallback={(err) => <div>Error: {err}</div>}>
      <ThemeProvider theme={theme}>
        <DialogProvider>
          <Router initialEntries={initialEntries}>
            {props.children}
          </Router>
        </DialogProvider>
      </ThemeProvider>
    </ErrorBoundary>
  );

  return rtlRender(ui, {
    wrapper: Wrapper,
  });
}

/**
 * Simple render without providers (for isolated component tests)
 */
export function render(ui: () => JSX.Element) {
  return rtlRender(ui);
}

export * from '@testing-library/solid';
