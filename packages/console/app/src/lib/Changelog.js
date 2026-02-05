// Changelog FFI
// Fetches changelog data from GitHub API

const changelogApiUrl = "https://api.github.com/repos/anomalyco/opencode/releases?per_page=20";

export const loadChangelog = async () => {
  try {
    const response = await fetch(changelogApiUrl, {
      headers: {
        Accept: "application/vnd.github.v3+json",
        "User-Agent": "OpenCode-Console",
      },
    });
    
    if (!response.ok) {
      return { ok: false, releases: [] };
    }
    
    const releases = await response.json();
    return { ok: true, releases };
  } catch (error) {
    return { ok: false, releases: [] };
  }
};
