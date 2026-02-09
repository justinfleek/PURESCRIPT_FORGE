export const domain = (() => {
  if ($app.stage === "production") return "forge.ai"
  if ($app.stage === "dev") return "dev.forge.ai"
  return `${$app.stage}.dev.forge.ai`
})()

export const zoneID = "430ba34c138cfb5360826c4909f99be8"

new cloudflare.RegionalHostname("RegionalHostname", {
  hostname: domain,
  regionKey: "us",
  zoneId: zoneID,
})

export const shortDomain = (() => {
  if ($app.stage === "production") return "frg.ai"
  if ($app.stage === "dev") return "dev.frg.ai"
  return `${$app.stage}.dev.frg.ai`
})()
