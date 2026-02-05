// Stripe Webhook FFI
// Stripe API calls and database operations
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
// Migrated: 2026-02-04

import { Billing } from "@opencode-ai/console-core/billing.js";
import { Database } from "@opencode-ai/console-core/drizzle/index.js";
import { BillingTable, PaymentTable, SubscriptionTable } from "@opencode-ai/console-core/schema/billing.sql.js";
import { UserTable } from "@opencode-ai/console-core/schema/user.sql.js";
import { AuthTable } from "@opencode-ai/console-core/schema/auth.sql.js";
import { Identifier } from "@opencode-ai/console-core/identifier.js";
import { centsToMicroCents } from "@opencode-ai/console-core/util/price.js";
import { Actor } from "@opencode-ai/console-core/actor.js";
import { Resource } from "@opencode-ai/console-resource";
import { eq, and, isNull, sql } from "@opencode-ai/console-core/drizzle/index.js";

// Construct Stripe event from API event
export async function constructStripeEvent(event) {
  const body = await Billing.stripe().webhooks.constructEventAsync(
    await event.request.text(),
    event.request.headers.get("stripe-signature"),
    Resource.STRIPE_WEBHOOK_SECRET.value,
  );
  return {
    type: body.type,
    data: JSON.stringify(body.data.object),
    created: body.created,
  };
}

// Log Stripe event
export async function logStripeEvent(eventType, eventDataJson) {
  console.log(eventType, eventDataJson);
}

// Create success response
export async function createSuccessResponse(message) {
  return Response.json({ message: message ?? "done" }, { status: 200 });
}

// Create error response
export async function createErrorResponse(errorMessage) {
  return Response.json({ message: errorMessage }, { status: 500 });
}

// Customer handlers
export async function retrievePaymentMethod(paymentMethodID) {
  const paymentMethod = await Billing.stripe().paymentMethods.retrieve(paymentMethodID);
  return {
    id: paymentMethod.id,
    last4: paymentMethod.card?.last4 ?? null,
    type: paymentMethod.type,
  };
}

export async function updateBillingPaymentMethod(customerID, paymentMethod) {
  await Database.use(async (tx) => {
    await tx
      .update(BillingTable)
      .set({
        paymentMethodID: paymentMethod.id,
        paymentMethodLast4: paymentMethod.last4,
        paymentMethodType: paymentMethod.type,
      })
      .where(eq(BillingTable.customerID, customerID));
  });
}

// Checkout handlers
export async function verifyCustomerID(workspaceID, customerID) {
  const customer = await Billing.get();
  return customer?.customerID === customerID;
}

export async function updateCustomerMetadata(customerID, workspaceID) {
  await Billing.stripe().customers.update(customerID, {
    metadata: {
      workspaceID,
    },
  });
}

export async function retrievePaymentMethodFromIntent(paymentID) {
  const paymentIntent = await Billing.stripe().paymentIntents.retrieve(paymentID, {
    expand: ["payment_method"],
  });
  const paymentMethod = paymentIntent.payment_method;
  if (!paymentMethod || typeof paymentMethod === "string") {
    throw new Error("Payment method not expanded");
  }
  return {
    id: paymentMethod.id,
    last4: paymentMethod.card?.last4 ?? null,
    type: paymentMethod.type,
  };
}

export async function updateBillingAndCreatePayment(
  workspaceID,
  amountInCents,
  customerID,
  paymentID,
  invoiceID,
  paymentMethod,
  isFirstTime,
) {
  await Actor.provide("system", { workspaceID }, async () => {
    await Database.transaction(async (tx) => {
      await tx
        .update(BillingTable)
        .set({
          balance: sql`${BillingTable.balance} + ${centsToMicroCents(amountInCents)}`,
          customerID,
          paymentMethodID: paymentMethod.id,
          paymentMethodLast4: paymentMethod.last4,
          paymentMethodType: paymentMethod.type,
          ...(isFirstTime
            ? {
                reloadError: null,
                timeReloadError: null,
              }
            : {}),
        })
        .where(eq(BillingTable.workspaceID, workspaceID));
      await tx.insert(PaymentTable).values({
        workspaceID,
        id: Identifier.create("payment"),
        amount: centsToMicroCents(amountInCents),
        paymentID,
        invoiceID,
        customerID,
      });
    });
  });
}

export async function getPaymentIDFromInvoice(invoiceID) {
  const invoice = await Billing.stripe().invoices.retrieve(invoiceID, {
    expand: ["payments"],
  });
  return invoice.payments?.data[0].payment.payment_intent;
}

export async function getCouponIDFromPromoCode(promoCode) {
  if (!promoCode) return null;
  const coupon = await Billing.stripe().promotionCodes.retrieve(promoCode);
  const couponID = coupon.coupon.id;
  if (!couponID) throw new Error("Coupon not found for promotion code");
  return couponID;
}

export async function findUserByEmail(workspaceID, customerEmail) {
  const users = await Database.use((tx) =>
    tx
      .select({ id: UserTable.id, email: AuthTable.subject })
      .from(UserTable)
      .innerJoin(AuthTable, and(eq(AuthTable.accountID, UserTable.accountID), eq(AuthTable.provider, "email")))
      .where(and(eq(UserTable.workspaceID, workspaceID), isNull(UserTable.timeDeleted))),
  );
  const user = users.find((u) => u.email === customerEmail) ?? users[0];
  if (!user) {
    console.error(`Error: User with email ${customerEmail} not found in workspace ${workspaceID}`);
    process.exit(1);
  }
  return user.id;
}

export async function updateBillingAndCreateSubscription(
  workspaceID,
  customerID,
  subscriptionID,
  paymentMethod,
  couponID,
  userID,
  amountInCents,
  paymentID,
  invoiceID,
) {
  await Actor.provide("system", { workspaceID }, async () => {
    await Database.transaction(async (tx) => {
      await tx
        .update(BillingTable)
        .set({
          customerID,
          subscriptionID,
          subscription: {
            status: "subscribed",
            coupon: couponID,
            seats: 1,
            plan: "200",
          },
          paymentMethodID: paymentMethod.id,
          paymentMethodLast4: paymentMethod.last4,
          paymentMethodType: paymentMethod.type,
        })
        .where(eq(BillingTable.workspaceID, workspaceID));

      await tx.insert(SubscriptionTable).values({
        workspaceID,
        id: Identifier.create("subscription"),
        userID,
      });

      await tx.insert(PaymentTable).values({
        workspaceID,
        id: Identifier.create("payment"),
        amount: centsToMicroCents(amountInCents),
        paymentID,
        invoiceID,
        customerID,
        enrichment: {
          type: "subscription",
          couponID,
        },
      });
    });
  });
}

// Subscription handlers
export async function unsubscribe(subscriptionID) {
  await Billing.unsubscribe({ subscriptionID });
}

// Invoice handlers
export async function getCouponIDFromSubscription(subscriptionID) {
  const subscriptionData = await Billing.stripe().subscriptions.retrieve(subscriptionID, {
    expand: ["discounts"],
  });
  const couponID =
    typeof subscriptionData.discounts[0] === "string"
      ? subscriptionData.discounts[0]
      : subscriptionData.discounts[0]?.coupon?.id;
  return couponID ?? null;
}

export async function getWorkspaceIDFromCustomer(customerID) {
  const workspaceID = await Database.use((tx) =>
    tx
      .select({ workspaceID: BillingTable.workspaceID })
      .from(BillingTable)
      .where(eq(BillingTable.customerID, customerID))
      .then((rows) => rows[0]?.workspaceID),
  );
  if (!workspaceID) throw new Error("Workspace ID not found for customer");
  return workspaceID;
}

export async function createSubscriptionPayment(
  workspaceID,
  amountPaid,
  paymentID,
  invoiceID,
  customerID,
  couponID,
) {
  await Database.use((tx) =>
    tx.insert(PaymentTable).values({
      workspaceID,
      id: Identifier.create("payment"),
      amount: centsToMicroCents(amountPaid),
      paymentID: paymentID ?? null,
      invoiceID,
      customerID,
      enrichment: {
        type: "subscription",
        couponID: couponID ?? null,
      },
    }),
  );
}

export async function updateBillingBalanceAndCreatePayment(
  workspaceID,
  amountInCents,
  invoiceID,
  paymentID,
  customerID,
) {
  await Actor.provide("system", { workspaceID }, async () => {
    const invoice = await Billing.stripe().invoices.retrieve(invoiceID, {
      expand: ["payments"],
    });
    await Database.transaction(async (tx) => {
      await tx
        .update(BillingTable)
        .set({
          balance: sql`${BillingTable.balance} + ${centsToMicroCents(amountInCents)}`,
          reloadError: null,
          timeReloadError: null,
        })
        .where(eq(BillingTable.workspaceID, Actor.workspace()));
      await tx.insert(PaymentTable).values({
        workspaceID: Actor.workspace(),
        id: Identifier.create("payment"),
        amount: centsToMicroCents(amountInCents),
        invoiceID,
        paymentID: paymentID ?? invoice.payments?.data[0].payment.payment_intent,
        customerID,
      });
    });
  });
}

export async function getPaymentIntentErrorMessage(invoiceID) {
  const paymentIntent = await Billing.stripe().paymentIntents.retrieve(invoiceID);
  const errorMessage =
    typeof paymentIntent === "object" && paymentIntent !== null
      ? paymentIntent.last_payment_error?.message
      : undefined;
  return errorMessage ?? null;
}

export async function updateBillingPaymentError(workspaceID, errorMessage) {
  await Actor.provide("system", { workspaceID }, async () => {
    await Database.use((tx) =>
      tx
        .update(BillingTable)
        .set({
          reload: false,
          reloadError: errorMessage ?? "Payment failed.",
          timeReloadError: sql`now()`,
        })
        .where(eq(BillingTable.workspaceID, Actor.workspace())),
    );
  });
}

// Charge handlers
export async function getPaymentAmount(workspaceID, paymentIntentID) {
  const amount = await Database.use((tx) =>
    tx
      .select({
        amount: PaymentTable.amount,
      })
      .from(PaymentTable)
      .where(and(eq(PaymentTable.paymentID, paymentIntentID), eq(PaymentTable.workspaceID, workspaceID)))
      .then((rows) => rows[0]?.amount),
  );
  if (!amount) throw new Error("Payment not found");
  return amount;
}

// Parse event data helpers
export async function parseCustomerUpdatedData(json) {
  const data = JSON.parse(json);
  return {
    customerID: data.id,
    paymentMethodID: data.invoice_settings?.default_payment_method ?? null,
    previousAttributes: data.previous_attributes ? {
      invoiceSettings: data.previous_attributes.invoice_settings ? {
        defaultPaymentMethod: data.previous_attributes.invoice_settings.default_payment_method ?? null,
      } : null,
    } : null,
  };
}

export async function parseCheckoutSessionData(json) {
  const data = JSON.parse(json);
  return {
    mode: data.mode,
    workspaceID: data.metadata?.workspaceID ?? (data.custom_fields?.find((f) => f.key === "workspaceid")?.text?.value ?? null),
    amountInCents: data.metadata?.amount ? parseInt(data.metadata.amount) : (data.amount_total ?? null),
    customerID: data.customer ?? null,
    customerEmail: data.customer_details?.email ?? null,
    paymentID: data.payment_intent ?? null,
    invoiceID: data.invoice ?? null,
    subscriptionID: data.subscription ?? null,
    promoCode: data.discounts?.[0]?.promotion_code ?? null,
    customFields: (data.custom_fields ?? []).map((f) => ({
      key: f.key,
      text: f.text ? { value: f.text.value } : null,
    })),
  };
}

export async function parseSubscriptionData(json) {
  const data = JSON.parse(json);
  return {
    subscriptionID: data.id,
    status: data.status ?? null,
  };
}

export async function parseInvoiceData(json) {
  const data = JSON.parse(json);
  return {
    invoiceID: data.id,
    customerID: data.customer ?? null,
    workspaceID: data.metadata?.workspaceID ?? null,
    amountInCents: data.metadata?.amount ? parseInt(data.metadata.amount) : null,
    amountPaid: data.amount_paid ?? null,
    billingReason: data.billing_reason ?? null,
    subscriptionID: data.parent?.subscription_details?.subscription ?? null,
    metadata: data.metadata ? {
      workspaceID: data.metadata.workspaceID ?? null,
      amount: data.metadata.amount ?? null,
    } : null,
  };
}

export async function parseChargeData(json, created) {
  const data = JSON.parse(json);
  return {
    customerID: data.customer,
    paymentIntentID: data.payment_intent,
    created: created,
  };
}

export async function updatePaymentAndBillingForRefund(workspaceID, paymentIntentID, created, amount) {
  await Database.transaction(async (tx) => {
    await tx
      .update(PaymentTable)
      .set({
        timeRefunded: new Date(created * 1000),
      })
      .where(and(eq(PaymentTable.paymentID, paymentIntentID), eq(PaymentTable.workspaceID, workspaceID)));

    await tx
      .update(BillingTable)
      .set({
        balance: sql`${BillingTable.balance} - ${amount}`,
      })
      .where(eq(BillingTable.workspaceID, workspaceID));
  });
}
