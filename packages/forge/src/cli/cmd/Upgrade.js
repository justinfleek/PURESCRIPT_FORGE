// Forge.CLI.Cmd.Upgrade FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

export const upgradeFFI = (versionOpt) => (force) => (checkOnly) => async () => {
  try {
    const response = await fetch('https://registry.npmjs.org/forge-cli/latest');
    const latestVersion = response.ok ? (await response.json()).version || '0.0.0' : '0.0.0';
    const targetVersion = versionOpt || latestVersion;

    if (checkOnly) {
      console.log('Latest version: ' + latestVersion);
      console.log('Target version: ' + targetVersion);
      return { tag: 'Right', value: {} };
    }

    if (!force && targetVersion === latestVersion) {
      console.log('Already up to date: ' + latestVersion);
      return { tag: 'Right', value: {} };
    }

    console.log('Upgrading to version ' + targetVersion + '...');
    await execAsync('npm install -g forge-cli@' + targetVersion);
    console.log('Successfully upgraded to ' + targetVersion);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
