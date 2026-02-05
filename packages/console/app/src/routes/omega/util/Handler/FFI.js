// Omega Handler FFI
// Database operations, HTTP fetch, and framework boundaries
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
// Migrated: 2026-02-04

import { Database } from "@opencode-ai/console-core/drizzle/index.js";
import { KeyTable } from "@opencode-ai/console-core/schema/key.sql.js";
import { BillingTable, SubscriptionTable, UsageTable } from "@opencode-ai/console-core/schema/billing.sql.js";
import { UserTable } from "@opencode-ai/console-core/schema/user.sql.js";
import { ProviderTable } from "@opencode-ai/console-core/schema/provider.sql.js";
import { ModelTable } from "@opencode-ai/console-core/schema/model.sql.js";
import { WorkspaceTable } from "@opencode-ai/console-core/schema/workspace.sql.js";
import { eq, and, isNull, lt, sql } from "@opencode-ai/console-core/drizzle/index.js";
import { OmegaData } from "@opencode-ai/console-core/model.js";
import { Black } from "@opencode-ai/console-core/black.js";
import { Billing } from "@opencode-ai/console-core/billing.js";
import { Actor } from "@opencode-ai/console-core/actor.js";
import { Identifier } from "@opencode-ai/console-core/identifier.js";
import { centsToMicroCents } from "@opencode-ai/console-core/util/price.js";
import { getWeekBounds } from "@opencode-ai/console-core/util/date.js";

// Query authentication data from database
export async function queryAuthData(apiKey, modelId, byokProvider) {
  return Database.use((tx) =>
    tx
      .select({
        apiKey: KeyTable.id,
        workspaceID: KeyTable.workspaceID,
        billing: {
          balance: BillingTable.balance,
          paymentMethodID: BillingTable.paymentMethodID,
          monthlyLimit: BillingTable.monthlyLimit,
          monthlyUsage: BillingTable.monthlyUsage,
          timeMonthlyUsageUpdated: BillingTable.timeMonthlyUsageUpdated,
          reloadTrigger: BillingTable.reloadTrigger,
          timeReloadLockedTill: BillingTable.timeReloadLockedTill,
          subscription: BillingTable.subscription,
        },
        user: {
          id: UserTable.id,
          monthlyLimit: UserTable.monthlyLimit,
          monthlyUsage: UserTable.monthlyUsage,
          timeMonthlyUsageUpdated: UserTable.timeMonthlyUsageUpdated,
        },
        subscription: {
          id: SubscriptionTable.id,
          rollingUsage: SubscriptionTable.rollingUsage,
          fixedUsage: SubscriptionTable.fixedUsage,
          timeRollingUpdated: SubscriptionTable.timeRollingUpdated,
          timeFixedUpdated: SubscriptionTable.timeFixedUpdated,
        },
        provider: {
          credentials: ProviderTable.credentials,
        },
        timeDisabled: ModelTable.timeCreated,
      })
      .from(KeyTable)
      .innerJoin(WorkspaceTable, eq(WorkspaceTable.id, KeyTable.workspaceID))
      .innerJoin(BillingTable, eq(BillingTable.workspaceID, KeyTable.workspaceID))
      .innerJoin(UserTable, and(eq(UserTable.workspaceID, KeyTable.workspaceID), eq(UserTable.id, KeyTable.userID)))
      .leftJoin(ModelTable, and(eq(ModelTable.workspaceID, KeyTable.workspaceID), eq(ModelTable.model, modelId)))
      .leftJoin(
        ProviderTable,
        byokProvider
          ? and(
              eq(ProviderTable.workspaceID, KeyTable.workspaceID),
              eq(ProviderTable.provider, byokProvider),
            )
          : sql`false`,
      )
      .leftJoin(
        SubscriptionTable,
        and(
          eq(SubscriptionTable.workspaceID, KeyTable.workspaceID),
          eq(SubscriptionTable.userID, KeyTable.userID),
          isNull(SubscriptionTable.timeDeleted),
        ),
      )
      .where(and(eq(KeyTable.key, apiKey), isNull(KeyTable.timeDeleted)))
      .then((rows) => rows[0])
  );
}

// Analyze weekly usage (calls Black.analyzeWeeklyUsage)
export function analyzeWeeklyUsage(plan, usage, timeUpdated) {
  return Black.analyzeWeeklyUsage({ plan, usage, timeUpdated });
}

// Analyze rolling usage (calls Black.analyzeRollingUsage)
export function analyzeRollingUsage(plan, usage, timeUpdated) {
  return Black.analyzeRollingUsage({ plan, usage, timeUpdated });
}

// Check if date is in current month
export function isCurrentMonth(date) {
  const now = new Date();
  return (
    date.getUTCFullYear() === now.getUTCFullYear() &&
    date.getUTCMonth() === now.getUTCMonth()
  );
}

// Check if date is in future
export function isDateInFuture(date) {
  return date > new Date();
}

// Acquire reload lock
export async function acquireReloadLock(authInfo) {
  const reloadTrigger = centsToMicroCents(
    (authInfo.billing.reloadTrigger ?? Billing.RELOAD_TRIGGER) * 100
  );
  
  const lock = await Database.use((tx) =>
    tx
      .update(BillingTable)
      .set({
        timeReloadLockedTill: sql`now() + interval 1 minute`,
      })
      .where(
        and(
          eq(BillingTable.workspaceID, authInfo.workspaceID),
          eq(BillingTable.reload, true),
          lt(BillingTable.balance, reloadTrigger),
          or(
            isNull(BillingTable.timeReloadLockedTill),
            lt(BillingTable.timeReloadLockedTill, sql`now()`)
          ),
        ),
      )
  );
  
  return lock.rowsAffected > 0;
}

// Trigger reload
export async function triggerReload(workspaceID) {
  await Actor.provide("system", { workspaceID }, async () => {
    await Billing.reload();
  });
}

// Track usage in database
export async function trackUsage(authInfo, modelInfo, providerInfo, billingSource, usageInfo) {
  // Cost calculation is done in PureScript (Handler.Cost)
  // This FFI handles database updates only
  const cost = authInfo.provider?.credentials ? 0 : usageInfo.costInMicroCents;
  
  await Database.use((db) =>
    Promise.all([
      db.insert(UsageTable).values({
        workspaceID: authInfo.workspaceID,
        id: Identifier.create("usage"),
        model: modelInfo.id,
        provider: providerInfo.id,
        inputTokens: usageInfo.inputTokens,
        outputTokens: usageInfo.outputTokens,
        reasoningTokens: usageInfo.reasoningTokens,
        cacheReadTokens: usageInfo.cacheReadTokens,
        cacheWrite5mTokens: usageInfo.cacheWrite5mTokens,
        cacheWrite1hTokens: usageInfo.cacheWrite1hTokens,
        cost,
        keyID: authInfo.apiKeyId,
        enrichment: billingSource === "subscription" ? { plan: "sub" } : undefined,
      }),
      db
        .update(KeyTable)
        .set({ timeUsed: sql`now()` })
        .where(and(eq(KeyTable.workspaceID, authInfo.workspaceID), eq(KeyTable.id, authInfo.apiKeyId))),
      ...(billingSource === "subscription"
        ? updateSubscriptionUsage(db, authInfo, cost)
        : updateBalanceUsage(db, authInfo, cost)),
    ])
  );
  
  return { costInMicroCents: cost };
}

// Update subscription usage
function updateSubscriptionUsage(db, authInfo, cost) {
  const plan = authInfo.billing.subscription.plan;
  const black = BlackData.getLimits({ plan });
  const week = getWeekBounds(new Date());
  const rollingWindowSeconds = black.rollingWindow * 3600;
  
  return [
    db
      .update(SubscriptionTable)
      .set({
        fixedUsage: sql`
          CASE
            WHEN ${SubscriptionTable.timeFixedUpdated} >= ${week.start} THEN ${SubscriptionTable.fixedUsage} + ${cost}
            ELSE ${cost}
          END
        `,
        timeFixedUpdated: sql`now()`,
        rollingUsage: sql`
          CASE
            WHEN UNIX_TIMESTAMP(${SubscriptionTable.timeRollingUpdated}) >= UNIX_TIMESTAMP(now()) - ${rollingWindowSeconds} THEN ${SubscriptionTable.rollingUsage} + ${cost}
            ELSE ${cost}
          END
        `,
        timeRollingUpdated: sql`
          CASE
            WHEN UNIX_TIMESTAMP(${SubscriptionTable.timeRollingUpdated}) >= UNIX_TIMESTAMP(now()) - ${rollingWindowSeconds} THEN ${SubscriptionTable.timeRollingUpdated}
            ELSE now()
          END
        `,
      })
      .where(
        and(
          eq(SubscriptionTable.workspaceID, authInfo.workspaceID),
          eq(SubscriptionTable.userID, authInfo.user.id),
        ),
      ),
  ];
}

// Update balance usage
function updateBalanceUsage(db, authInfo, cost) {
  return [
    db
      .update(BillingTable)
      .set({
        balance: authInfo.isFree
          ? sql`${BillingTable.balance} - ${0}`
          : sql`${BillingTable.balance} - ${cost}`,
        monthlyUsage: sql`
          CASE
            WHEN MONTH(${BillingTable.timeMonthlyUsageUpdated}) = MONTH(now()) AND YEAR(${BillingTable.timeMonthlyUsageUpdated}) = YEAR(now()) THEN ${BillingTable.monthlyUsage} + ${cost}
            ELSE ${cost}
          END
        `,
        timeMonthlyUsageUpdated: sql`now()`,
      })
      .where(eq(BillingTable.workspaceID, authInfo.workspaceID)),
    db
      .update(UserTable)
      .set({
        monthlyUsage: sql`
          CASE
            WHEN MONTH(${UserTable.timeMonthlyUsageUpdated}) = MONTH(now()) AND YEAR(${UserTable.timeMonthlyUsageUpdated}) = YEAR(now()) THEN ${UserTable.monthlyUsage} + ${cost}
            ELSE ${cost}
          END
        `,
        timeMonthlyUsageUpdated: sql`now()`,
      })
      .where(and(eq(UserTable.workspaceID, authInfo.workspaceID), eq(UserTable.id, authInfo.user.id))),
  ];
}
