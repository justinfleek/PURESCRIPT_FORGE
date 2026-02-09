// FFI for Forge.Util.Archive
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/archive.ts

import { $ } from "bun";
import path from "path";

export const extractZip = (zipPath) => (destDir) => async () => {
  if (process.platform === "win32") {
    const winZipPath = path.resolve(zipPath);
    const winDestDir = path.resolve(destDir);
    // $global:ProgressPreference suppresses PowerShell's blue progress bar popup
    const cmd = `$global:ProgressPreference = 'SilentlyContinue'; Expand-Archive -Path '${winZipPath}' -DestinationPath '${winDestDir}' -Force`;
    await $`powershell -NoProfile -NonInteractive -Command ${cmd}`.quiet();
  } else {
    await $`unzip -o -q ${zipPath} -d ${destDir}`.quiet();
  }
};
