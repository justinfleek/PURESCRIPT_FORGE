const stage = process.env.SST_STAGE || "dev"

export default {
  url: stage === "production" ? "https://forge.ai" : `https://${stage}.forge.ai`,
  console: stage === "production" ? "https://forge.ai/auth" : `https://${stage}.forge.ai/auth`,
  email: "contact@anoma.ly",
  socialCard: "https://social-cards.sst.dev",
  github: "https://github.com/forge-ai/forge",
  discord: "https://forge.ai/discord",
  headerLinks: [
    { name: "Home", url: "/" },
    { name: "Docs", url: "/docs/" },
  ],
}
