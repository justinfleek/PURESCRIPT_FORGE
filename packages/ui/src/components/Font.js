// Font FFI - Document head font injection

/**
 * Install font face definitions into document head
 * @returns {() => void}
 */
export const installFonts = () => {
  const head = document.head;
  
  // Check if already installed
  if (head.querySelector('style[data-forge-fonts]')) {
    return;
  }
  
  // Font paths (would be bundled assets in production)
  const interPath = '/fonts/inter.woff2';
  const ibmPlexMonoRegular = '/fonts/ibm-plex-mono.woff2';
  const ibmPlexMonoMedium = '/fonts/ibm-plex-mono-medium.woff2';
  const ibmPlexMonoBold = '/fonts/ibm-plex-mono-bold.woff2';
  
  // Nerd fonts
  const nerdFonts = [
    { family: 'JetBrains Mono Nerd Font', regular: '/fonts/jetbrains-mono-nerd-font.woff2', bold: '/fonts/jetbrains-mono-nerd-font-bold.woff2' },
    { family: 'Fira Code Nerd Font', regular: '/fonts/fira-code-nerd-font.woff2', bold: '/fonts/fira-code-nerd-font-bold.woff2' },
    { family: 'Cascadia Code Nerd Font', regular: '/fonts/cascadia-code-nerd-font.woff2', bold: '/fonts/cascadia-code-nerd-font-bold.woff2' },
    { family: 'Hack Nerd Font', regular: '/fonts/hack-nerd-font.woff2', bold: '/fonts/hack-nerd-font-bold.woff2' },
    { family: 'Source Code Pro Nerd Font', regular: '/fonts/source-code-pro-nerd-font.woff2', bold: '/fonts/source-code-pro-nerd-font-bold.woff2' },
    { family: 'Inconsolata Nerd Font', regular: '/fonts/inconsolata-nerd-font.woff2', bold: '/fonts/inconsolata-nerd-font-bold.woff2' },
    { family: 'Roboto Mono Nerd Font', regular: '/fonts/roboto-mono-nerd-font.woff2', bold: '/fonts/roboto-mono-nerd-font-bold.woff2' },
    { family: 'Ubuntu Mono Nerd Font', regular: '/fonts/ubuntu-mono-nerd-font.woff2', bold: '/fonts/ubuntu-mono-nerd-font-bold.woff2' },
    { family: 'Intel One Mono Nerd Font', regular: '/fonts/intel-one-mono-nerd-font.woff2', bold: '/fonts/intel-one-mono-nerd-font-bold.woff2' },
    { family: 'Meslo LGS Nerd Font', regular: '/fonts/meslo-lgs-nerd-font.woff2', bold: '/fonts/meslo-lgs-nerd-font-bold.woff2' },
    { family: 'Iosevka Nerd Font', regular: '/fonts/iosevka-nerd-font.woff2', bold: '/fonts/iosevka-nerd-font-bold.woff2' },
  ];
  
  // Generate nerd font CSS
  const nerdFontCss = nerdFonts.map(font => `
    @font-face {
      font-family: "${font.family}";
      src: url("${font.regular}") format("woff2");
      font-display: swap;
      font-style: normal;
      font-weight: 400;
    }
    @font-face {
      font-family: "${font.family}";
      src: url("${font.bold}") format("woff2");
      font-display: swap;
      font-style: normal;
      font-weight: 700;
    }
  `).join('');
  
  // Create style element with all font definitions
  const css = `
    @font-face {
      font-family: "Inter";
      src: url("${interPath}") format("woff2-variations");
      font-display: swap;
      font-style: normal;
      font-weight: 100 900;
    }
    @font-face {
      font-family: "Inter Fallback";
      src: local("Arial");
      size-adjust: 100%;
      ascent-override: 97%;
      descent-override: 25%;
      line-gap-override: 1%;
    }
    @font-face {
      font-family: "IBM Plex Mono";
      src: url("${ibmPlexMonoRegular}") format("woff2");
      font-display: swap;
      font-style: normal;
      font-weight: 400;
    }
    @font-face {
      font-family: "IBM Plex Mono";
      src: url("${ibmPlexMonoMedium}") format("woff2");
      font-display: swap;
      font-style: normal;
      font-weight: 500;
    }
    @font-face {
      font-family: "IBM Plex Mono";
      src: url("${ibmPlexMonoBold}") format("woff2");
      font-display: swap;
      font-style: normal;
      font-weight: 700;
    }
    @font-face {
      font-family: "IBM Plex Mono Fallback";
      src: local("Courier New");
      size-adjust: 100%;
      ascent-override: 97%;
      descent-override: 25%;
      line-gap-override: 1%;
    }
    ${nerdFontCss}
  `;
  
  const style = document.createElement('style');
  style.setAttribute('data-forge-fonts', 'true');
  style.textContent = css;
  head.appendChild(style);
  
  // Add preload links for primary fonts
  const preloads = [
    { href: interPath, type: 'font/woff2' },
    { href: ibmPlexMonoRegular, type: 'font/woff2' },
  ];
  
  for (const { href, type } of preloads) {
    const link = document.createElement('link');
    link.setAttribute('rel', 'preload');
    link.setAttribute('href', href);
    link.setAttribute('as', 'font');
    link.setAttribute('type', type);
    link.setAttribute('crossorigin', 'anonymous');
    link.setAttribute('data-forge-fonts', 'true');
    head.appendChild(link);
  }
};
