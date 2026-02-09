// Forge.CLI.Cmd.Debug.Scrap FFI

export const debugScrapFFI = async () => {
  try {
    const info = {
      pid: process.pid,
      platform: process.platform,
      arch: process.arch,
      nodeVersion: process.version,
      uptime: process.uptime(),
      memoryUsage: process.memoryUsage(),
      cwd: process.cwd(),
      env: {
        HOME: process.env.HOME || process.env.USERPROFILE || '',
        SHELL: process.env.SHELL || '',
        TERM: process.env.TERM || '',
        NODE_ENV: process.env.NODE_ENV || ''
      }
    };
    console.log(JSON.stringify(info, null, 2));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
