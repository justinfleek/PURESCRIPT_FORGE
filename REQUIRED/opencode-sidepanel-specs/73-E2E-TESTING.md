# 73-E2E-TESTING: End-to-End Tests with Playwright

## Overview

End-to-end tests verify the complete system from user interaction to visual output. We use Playwright for cross-browser testing of the sidepanel UI.

---

## Test Philosophy

| Layer | What It Tests | Tools |
|-------|---------------|-------|
| Unit | Pure functions, reducers | PureScript spec, Vitest |
| Integration | Component interactions, API contracts | Vitest, WebSocket mocks |
| **E2E** | **Full user journeys, visual output** | **Playwright** |

E2E tests are slow but catch issues that unit/integration tests miss:
- CSS rendering issues
- Animation/transition bugs
- Keyboard navigation
- Cross-browser compatibility

---

## Test Structure

```
e2e/
├── fixtures/
│   ├── test-bridge.ts      # Mock bridge server
│   ├── mock-opencode.ts    # OpenCode simulator
│   └── test-data.ts        # Sample sessions, messages
├── pages/
│   ├── dashboard.page.ts   # Page object for dashboard
│   ├── session.page.ts     # Page object for session
│   ├── search.page.ts      # Page object for search
│   └── settings.page.ts    # Page object for settings
├── tests/
│   ├── dashboard.spec.ts
│   ├── session.spec.ts
│   ├── balance.spec.ts
│   ├── keyboard.spec.ts
│   └── visual.spec.ts
└── playwright.config.ts
```

---

## Playwright Configuration

```typescript
// e2e/playwright.config.ts
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests',
  timeout: 30000,
  expect: {
    timeout: 5000
  },
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [
    ['html', { outputFolder: 'playwright-report' }],
    ['junit', { outputFile: 'results.xml' }]
  ],
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
    video: 'retain-on-failure'
  },
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] }
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] }
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] }
    }
  ],
  webServer: {
    command: 'pnpm run dev',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI
  }
});
```

---

## Page Objects

### Dashboard Page

```typescript
// e2e/pages/dashboard.page.ts
import { Page, Locator, expect } from '@playwright/test';

export class DashboardPage {
  readonly page: Page;
  readonly diemBalance: Locator;
  readonly countdownTimer: Locator;
  readonly tokenChart: Locator;
  readonly sessionCards: Locator;
  readonly navSidebar: Locator;
  
  constructor(page: Page) {
    this.page = page;
    this.diemBalance = page.locator('[data-testid="diem-balance"]');
    this.countdownTimer = page.locator('[data-testid="countdown-timer"]');
    this.tokenChart = page.locator('[data-testid="token-chart"]');
    this.sessionCards = page.locator('[data-testid="session-card"]');
    this.navSidebar = page.locator('[data-testid="nav-sidebar"]');
  }
  
  async goto() {
    await this.page.goto('/');
    await this.page.waitForLoadState('networkidle');
  }
  
  async waitForConnection() {
    await expect(this.page.locator('[data-testid="connection-status"]')).toHaveText(/Connected/);
  }
  
  async getDiemValue(): Promise<number> {
    const text = await this.diemBalance.locator('.diem-value').textContent();
    return parseFloat(text ?? '0');
  }
  
  async getCountdownTime(): Promise<string> {
    return await this.countdownTimer.locator('.countdown-value').textContent() ?? '';
  }
  
  async navigateToSession(index: number = 0) {
    await this.sessionCards.nth(index).click();
    await this.page.waitForURL(/\/session\//);
  }
  
  async navigateViaKeyboard(key: string) {
    await this.page.keyboard.press(key);
  }
  
  async openCommandPalette() {
    await this.page.keyboard.press('Control+Shift+P');
    await expect(this.page.locator('[data-testid="command-palette"]')).toBeVisible();
  }
}
```

### Session Page

```typescript
// e2e/pages/session.page.ts
import { Page, Locator, expect } from '@playwright/test';

export class SessionPage {
  readonly page: Page;
  readonly messageList: Locator;
  readonly toolCalls: Locator;
  readonly tokenCount: Locator;
  readonly costDisplay: Locator;
  readonly branchButton: Locator;
  readonly exportButton: Locator;
  
  constructor(page: Page) {
    this.page = page;
    this.messageList = page.locator('[data-testid="message-list"]');
    this.toolCalls = page.locator('[data-testid="tool-call"]');
    this.tokenCount = page.locator('[data-testid="token-count"]');
    this.costDisplay = page.locator('[data-testid="session-cost"]');
    this.branchButton = page.locator('[data-testid="branch-button"]');
    this.exportButton = page.locator('[data-testid="export-button"]');
  }
  
  async goto(sessionId: string) {
    await this.page.goto(`/session/${sessionId}`);
    await this.page.waitForLoadState('networkidle');
  }
  
  async getMessageCount(): Promise<number> {
    return await this.messageList.locator('.message').count();
  }
  
  async getMessage(index: number): Promise<{ role: string; content: string }> {
    const msg = this.messageList.locator('.message').nth(index);
    const role = await msg.getAttribute('data-role') ?? '';
    const content = await msg.locator('.message-content').textContent() ?? '';
    return { role, content };
  }
  
  async expandToolCall(index: number) {
    await this.toolCalls.nth(index).click();
    await expect(this.toolCalls.nth(index).locator('.tool-card__expanded')).toBeVisible();
  }
  
  async createBranch(description: string) {
    await this.branchButton.click();
    await this.page.fill('[data-testid="branch-description"]', description);
    await this.page.click('[data-testid="create-branch-button"]');
    await this.page.waitForURL(/\/session\//);
  }
  
  async exportSession(format: 'json' | 'markdown') {
    await this.exportButton.click();
    await this.page.click(`[data-testid="export-${format}"]`);
    const download = await this.page.waitForEvent('download');
    return download;
  }
}
```

---

## Test Suites

### Dashboard Tests

```typescript
// e2e/tests/dashboard.spec.ts
import { test, expect } from '@playwright/test';
import { DashboardPage } from '../pages/dashboard.page';
import { TestBridge } from '../fixtures/test-bridge';

test.describe('Dashboard', () => {
  let bridge: TestBridge;
  let dashboard: DashboardPage;
  
  test.beforeAll(async () => {
    bridge = new TestBridge();
    await bridge.start();
  });
  
  test.afterAll(async () => {
    await bridge.stop();
  });
  
  test.beforeEach(async ({ page }) => {
    dashboard = new DashboardPage(page);
    await dashboard.goto();
    await dashboard.waitForConnection();
  });
  
  test('displays Diem balance', async () => {
    bridge.setBalance({ diem: 42.5, usd: 10.0 });
    
    await expect(dashboard.diemBalance).toContainText('42.5');
  });
  
  test('updates balance in real-time', async () => {
    bridge.setBalance({ diem: 50.0, usd: 10.0 });
    await expect(dashboard.diemBalance).toContainText('50');
    
    bridge.setBalance({ diem: 45.0, usd: 10.0 });
    await expect(dashboard.diemBalance).toContainText('45');
  });
  
  test('shows countdown timer', async () => {
    const time = await dashboard.getCountdownTime();
    expect(time).toMatch(/\d+h \d+m \d+s/);
  });
  
  test('displays active sessions', async () => {
    bridge.createSession({ title: 'Test Session', model: 'llama-3.3-70b' });
    
    await expect(dashboard.sessionCards).toHaveCount(1);
    await expect(dashboard.sessionCards.first()).toContainText('Test Session');
  });
  
  test('navigates to session on click', async () => {
    bridge.createSession({ id: 'sess_123', title: 'Test Session' });
    
    await dashboard.navigateToSession(0);
    
    expect(dashboard.page.url()).toContain('/session/sess_123');
  });
  
  test('shows warning when balance is low', async () => {
    bridge.setBalance({ diem: 3.0, usd: 0 });
    
    await expect(dashboard.diemBalance.locator('.alert-badge')).toBeVisible();
    await expect(dashboard.page.locator('[data-testid="alert"]')).toContainText('Low Diem');
  });
});
```

### Balance Tests

```typescript
// e2e/tests/balance.spec.ts
import { test, expect } from '@playwright/test';
import { DashboardPage } from '../pages/dashboard.page';
import { TestBridge } from '../fixtures/test-bridge';

test.describe('Balance Tracking', () => {
  let bridge: TestBridge;
  let dashboard: DashboardPage;
  
  test.beforeAll(async () => {
    bridge = new TestBridge();
    await bridge.start();
  });
  
  test.afterAll(async () => {
    await bridge.stop();
  });
  
  test.beforeEach(async ({ page }) => {
    dashboard = new DashboardPage(page);
    await dashboard.goto();
    await dashboard.waitForConnection();
  });
  
  test('tracks balance consumption', async () => {
    bridge.setBalance({ diem: 50.0 });
    await expect(dashboard.diemBalance).toContainText('50');
    
    // Simulate AI usage
    bridge.simulateMessage({
      usage: { promptTokens: 1000, completionTokens: 500 }
    });
    bridge.setBalance({ diem: 48.5 });
    
    await expect(dashboard.diemBalance).toContainText('48.5');
  });
  
  test('calculates consumption rate', async ({ page }) => {
    // Set up balance history
    bridge.setBalanceHistory([
      { timestamp: Date.now() - 3600000, diem: 55 },
      { timestamp: Date.now() - 1800000, diem: 52 },
      { timestamp: Date.now(), diem: 50 }
    ]);
    
    const burnRate = page.locator('[data-testid="burn-rate"]');
    await expect(burnRate).toContainText(/\d+\.?\d*\/hr/);
  });
  
  test('shows time to depletion', async ({ page }) => {
    bridge.setBalance({ diem: 10.0 });
    bridge.setConsumptionRate(2.5); // 2.5 Diem/hr
    
    const timeToEmpty = page.locator('[data-testid="time-to-empty"]');
    await expect(timeToEmpty).toContainText('~4h');
  });
  
  test('alert levels update correctly', async ({ page }) => {
    const alertIndicator = page.locator('[data-testid="balance-alert"]');
    
    // Normal
    bridge.setBalance({ diem: 50.0 });
    await expect(alertIndicator).toHaveAttribute('data-level', 'normal');
    
    // Warning
    bridge.setBalance({ diem: 5.0 });
    await expect(alertIndicator).toHaveAttribute('data-level', 'warning');
    
    // Critical
    bridge.setBalance({ diem: 0.5 });
    await expect(alertIndicator).toHaveAttribute('data-level', 'critical');
  });
});
```

### Keyboard Navigation Tests

```typescript
// e2e/tests/keyboard.spec.ts
import { test, expect } from '@playwright/test';
import { DashboardPage } from '../pages/dashboard.page';

test.describe('Keyboard Navigation', () => {
  let dashboard: DashboardPage;
  
  test.beforeEach(async ({ page }) => {
    dashboard = new DashboardPage(page);
    await dashboard.goto();
    await dashboard.waitForConnection();
  });
  
  test('switches panels with number keys', async ({ page }) => {
    // Press 1 for dashboard (already there)
    await page.keyboard.press('1');
    await expect(page).toHaveURL(/\/?$/);
    
    // Press 2 for sessions
    await page.keyboard.press('2');
    await expect(page).toHaveURL(/\/sessions/);
    
    // Press 3 for proofs
    await page.keyboard.press('3');
    await expect(page).toHaveURL(/\/proofs/);
  });
  
  test('vim navigation works', async ({ page }) => {
    await page.keyboard.press('2'); // Go to sessions
    
    // j to move down
    await page.keyboard.press('j');
    await expect(page.locator('.session-item:nth-child(2)')).toHaveClass(/selected/);
    
    // k to move up
    await page.keyboard.press('k');
    await expect(page.locator('.session-item:nth-child(1)')).toHaveClass(/selected/);
    
    // Enter to open
    await page.keyboard.press('Enter');
    await expect(page).toHaveURL(/\/session\//);
  });
  
  test('command palette opens with Ctrl+Shift+P', async ({ page }) => {
    await page.keyboard.press('Control+Shift+P');
    
    const palette = page.locator('[data-testid="command-palette"]');
    await expect(palette).toBeVisible();
    
    // Type to filter
    await page.keyboard.type('balance');
    await expect(palette.locator('.command-item')).toContainText(/balance/i);
    
    // Escape to close
    await page.keyboard.press('Escape');
    await expect(palette).not.toBeVisible();
  });
  
  test('gg/G navigation', async ({ page }) => {
    await page.keyboard.press('2'); // Sessions
    
    // G to go to bottom
    await page.keyboard.press('Shift+G');
    await expect(page.locator('.session-item:last-child')).toHaveClass(/selected/);
    
    // gg to go to top
    await page.keyboard.press('g');
    await page.keyboard.press('g');
    await expect(page.locator('.session-item:first-child')).toHaveClass(/selected/);
  });
  
  test('sidebar collapse with [', async ({ page }) => {
    const sidebar = page.locator('[data-testid="nav-sidebar"]');
    
    await expect(sidebar).toHaveAttribute('data-collapsed', 'false');
    
    await page.keyboard.press('[');
    await expect(sidebar).toHaveAttribute('data-collapsed', 'true');
    
    await page.keyboard.press('[');
    await expect(sidebar).toHaveAttribute('data-collapsed', 'false');
  });
});
```

### Visual Regression Tests

```typescript
// e2e/tests/visual.spec.ts
import { test, expect } from '@playwright/test';
import { DashboardPage } from '../pages/dashboard.page';
import { TestBridge } from '../fixtures/test-bridge';

test.describe('Visual Regression', () => {
  let bridge: TestBridge;
  
  test.beforeAll(async () => {
    bridge = new TestBridge();
    await bridge.start();
  });
  
  test.afterAll(async () => {
    await bridge.stop();
  });
  
  test('dashboard renders correctly', async ({ page }) => {
    const dashboard = new DashboardPage(page);
    await dashboard.goto();
    await dashboard.waitForConnection();
    
    // Set predictable state
    bridge.setBalance({ diem: 42.5, usd: 10.0 });
    bridge.createSession({ title: 'Test Session' });
    
    await expect(page).toHaveScreenshot('dashboard.png', {
      maxDiffPixels: 100
    });
  });
  
  test('session view renders correctly', async ({ page }) => {
    bridge.createSession({ id: 'sess_visual' });
    bridge.addMessage({
      sessionId: 'sess_visual',
      role: 'user',
      content: 'Hello AI'
    });
    bridge.addMessage({
      sessionId: 'sess_visual',
      role: 'assistant',
      content: 'Hello! How can I help you today?'
    });
    
    await page.goto('/session/sess_visual');
    
    await expect(page).toHaveScreenshot('session.png', {
      maxDiffPixels: 100
    });
  });
  
  test('alert states render correctly', async ({ page }) => {
    const dashboard = new DashboardPage(page);
    await dashboard.goto();
    
    // Warning state
    bridge.setBalance({ diem: 5.0 });
    await expect(page.locator('[data-testid="diem-tracker"]')).toHaveScreenshot('diem-warning.png');
    
    // Critical state
    bridge.setBalance({ diem: 0.5 });
    await expect(page.locator('[data-testid="diem-tracker"]')).toHaveScreenshot('diem-critical.png');
  });
  
  test('dark theme is consistent', async ({ page }) => {
    await page.goto('/');
    
    // Check multiple components
    await expect(page.locator('[data-testid="nav-sidebar"]')).toHaveScreenshot('sidebar-dark.png');
    await expect(page.locator('[data-testid="header"]')).toHaveScreenshot('header-dark.png');
  });
});
```

---

## Running E2E Tests

```bash
# Run all E2E tests
just test-e2e

# Run with UI mode
pnpm exec playwright test --ui

# Run specific test file
pnpm exec playwright test tests/dashboard.spec.ts

# Update screenshots
pnpm exec playwright test --update-snapshots

# Show report
pnpm exec playwright show-report
```

---

## CI Integration

```yaml
# In .github/workflows/ci.yml
test-e2e:
  name: E2E Tests
  runs-on: ubuntu-latest
  needs: [build]
  steps:
    - uses: actions/checkout@v4
    
    - uses: actions/setup-node@v4
      with:
        node-version: '20'
    
    - name: Install dependencies
      run: pnpm install
    
    - name: Install Playwright
      run: pnpm exec playwright install --with-deps chromium
    
    - name: Run E2E tests
      run: pnpm exec playwright test --project=chromium
    
    - name: Upload test results
      if: always()
      uses: actions/upload-artifact@v3
      with:
        name: playwright-report
        path: e2e/playwright-report
```

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Overall strategy
- `71-UNIT-TESTING.md` - Unit tests
- `72-INTEGRATION-TESTING.md` - Integration tests

---

*"E2E tests are the final gatekeepers. Trust them."*
