import { domain } from "./stage"
import { EMAILOCTOPUS_API_KEY } from "./app"

////////////////
// DATABASE
////////////////

const cluster = planetscale.getDatabaseOutput({
  name: "forge",
  organization: "forge-ai",
})

const branch =
  $app.stage === "production"
    ? planetscale.getBranchOutput({
        name: "production",
        organization: cluster.organization,
        database: cluster.name,
      })
    : new planetscale.Branch("DatabaseBranch", {
        database: cluster.name,
        organization: cluster.organization,
        name: $app.stage,
        parentBranch: "production",
      })
const password = new planetscale.Password("DatabasePassword", {
  name: $app.stage,
  database: cluster.name,
  organization: cluster.organization,
  branch: branch.name,
})

export const database = new sst.Linkable("Database", {
  properties: {
    host: password.accessHostUrl,
    database: cluster.name,
    username: password.username,
    password: password.plaintext,
    port: 3306,
  },
})

new sst.x.DevCommand("Studio", {
  link: [database],
  dev: {
    command: "bun db studio",
    directory: "packages/console/core",
    autostart: true,
  },
})

////////////////
// AUTH
////////////////

const GITHUB_CLIENT_ID_CONSOLE = new sst.Secret("GITHUB_CLIENT_ID_CONSOLE")
const GITHUB_CLIENT_SECRET_CONSOLE = new sst.Secret("GITHUB_CLIENT_SECRET_CONSOLE")
const GOOGLE_CLIENT_ID = new sst.Secret("GOOGLE_CLIENT_ID")
const authStorage = new sst.cloudflare.Kv("AuthStorage")
export const auth = new sst.cloudflare.Worker("AuthApi", {
  domain: `auth.${domain}`,
  handler: "packages/console/function/src/auth.ts",
  url: true,
  link: [database, authStorage, GITHUB_CLIENT_ID_CONSOLE, GITHUB_CLIENT_SECRET_CONSOLE, GOOGLE_CLIENT_ID],
})

////////////////
// GATEWAY
////////////////

export const stripeWebhook = new stripe.WebhookEndpoint("StripeWebhookEndpoint", {
  url: $interpolate`https://${domain}/stripe/webhook`,
  enabledEvents: [
    "checkout.session.async_payment_failed",
    "checkout.session.async_payment_succeeded",
    "checkout.session.completed",
    "checkout.session.expired",
    "charge.refunded",
    "invoice.payment_succeeded",
    "invoice.payment_failed",
    "invoice.payment_action_required",
    "customer.created",
    "customer.deleted",
    "customer.updated",
    "customer.discount.created",
    "customer.discount.deleted",
    "customer.discount.updated",
    "customer.source.created",
    "customer.source.deleted",
    "customer.source.expiring",
    "customer.source.updated",
    "customer.subscription.created",
    "customer.subscription.deleted",
    "customer.subscription.paused",
    "customer.subscription.pending_update_applied",
    "customer.subscription.pending_update_expired",
    "customer.subscription.resumed",
    "customer.subscription.trial_will_end",
    "customer.subscription.updated",
  ],
})

const coreProduct = new stripe.Product("CoreBlack", {
  name: "Forge Black",
})
const corePriceProps = {
  product: coreProduct.id,
  currency: "usd",
  recurring: {
    interval: "month",
    intervalCount: 1,
  },
}
const corePrice200 = new stripe.Price("CoreBlackPrice", { ...corePriceProps, unitAmount: 20000 })
const corePrice100 = new stripe.Price("CoreBlack100Price", { ...corePriceProps, unitAmount: 10000 })
const corePrice20 = new stripe.Price("CoreBlack20Price", { ...corePriceProps, unitAmount: 2000 })
const CORE_BLACK_PRICE = new sst.Linkable("CORE_BLACK_PRICE", {
  properties: {
    product: coreProduct.id,
    plan200: corePrice200.id,
    plan100: corePrice100.id,
    plan20: corePrice20.id,
  },
})
const CORE_BLACK_LIMITS = new sst.Secret("CORE_BLACK_LIMITS")

const CORE_MODELS = [
  new sst.Secret("CORE_MODELS1"),
  new sst.Secret("CORE_MODELS2"),
  new sst.Secret("CORE_MODELS3"),
  new sst.Secret("CORE_MODELS4"),
  new sst.Secret("CORE_MODELS5"),
  new sst.Secret("CORE_MODELS6"),
  new sst.Secret("CORE_MODELS7"),
  new sst.Secret("CORE_MODELS8"),
  new sst.Secret("CORE_MODELS9"),
  new sst.Secret("CORE_MODELS10"),
]
const STRIPE_SECRET_KEY = new sst.Secret("STRIPE_SECRET_KEY")
const STRIPE_PUBLISHABLE_KEY = new sst.Secret("STRIPE_PUBLISHABLE_KEY")
const AUTH_API_URL = new sst.Linkable("AUTH_API_URL", {
  properties: { value: auth.url.apply((url) => url!) },
})
const STRIPE_WEBHOOK_SECRET = new sst.Linkable("STRIPE_WEBHOOK_SECRET", {
  properties: { value: stripeWebhook.secret },
})
const gatewayKv = new sst.cloudflare.Kv("GatewayKv")

////////////////
// CONSOLE
////////////////

const bucket = new sst.cloudflare.Bucket("CoreData")
const bucketNew = new sst.cloudflare.Bucket("CoreDataNew")

const AWS_SES_ACCESS_KEY_ID = new sst.Secret("AWS_SES_ACCESS_KEY_ID")
const AWS_SES_SECRET_ACCESS_KEY = new sst.Secret("AWS_SES_SECRET_ACCESS_KEY")

let logProcessor
if ($app.stage === "production" || $app.stage === "frank") {
  const HONEYCOMB_API_KEY = new sst.Secret("HONEYCOMB_API_KEY")
  logProcessor = new sst.cloudflare.Worker("LogProcessor", {
    handler: "packages/console/function/src/log-processor.ts",
    link: [HONEYCOMB_API_KEY],
  })
}

new sst.cloudflare.x.SolidStart("Console", {
  domain,
  path: "packages/console/app",
  link: [
    bucket,
    bucketNew,
    database,
    AUTH_API_URL,
    STRIPE_WEBHOOK_SECRET,
    STRIPE_SECRET_KEY,
    EMAILOCTOPUS_API_KEY,
    AWS_SES_ACCESS_KEY_ID,
    AWS_SES_SECRET_ACCESS_KEY,
    CORE_BLACK_PRICE,
    CORE_BLACK_LIMITS,
    new sst.Secret("CORE_SESSION_SECRET"),
    ...CORE_MODELS,
    ...($dev
      ? [
          new sst.Secret("CLOUDFLARE_DEFAULT_ACCOUNT_ID", process.env.CLOUDFLARE_DEFAULT_ACCOUNT_ID!),
          new sst.Secret("CLOUDFLARE_API_TOKEN", process.env.CLOUDFLARE_API_TOKEN!),
        ]
      : []),
    gatewayKv,
  ],
  environment: {
    VITE_AUTH_URL: auth.url.apply((url) => url!),
    VITE_STRIPE_PUBLISHABLE_KEY: STRIPE_PUBLISHABLE_KEY.value,
  },
  transform: {
    server: {
      transform: {
        worker: {
          placement: { mode: "smart" },
          tailConsumers: logProcessor ? [{ service: logProcessor.nodes.worker.scriptName }] : [],
        },
      },
    },
  },
})
