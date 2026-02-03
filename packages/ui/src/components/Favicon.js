// Favicon FFI - Document head manipulation

/**
 * Install favicon links and meta tags into document head
 * @returns {() => void}
 */
export const installFavicon = () => {
  const head = document.head;
  
  // Check if already installed
  if (head.querySelector('link[rel="icon"][data-forge]')) {
    return;
  }
  
  // Create and append link elements
  const links = [
    { rel: 'icon', type: 'image/png', href: '/favicon-96x96-v3.png', sizes: '96x96' },
    { rel: 'shortcut icon', href: '/favicon-v3.ico' },
    { rel: 'apple-touch-icon', href: '/apple-touch-icon-v3.png', sizes: '180x180' },
    { rel: 'manifest', href: '/site.webmanifest' },
  ];
  
  for (const attrs of links) {
    const link = document.createElement('link');
    link.setAttribute('data-forge', 'true');
    for (const [key, value] of Object.entries(attrs)) {
      link.setAttribute(key, value);
    }
    head.appendChild(link);
  }
  
  // Create meta tag for apple-mobile-web-app-title
  const meta = document.createElement('meta');
  meta.setAttribute('name', 'apple-mobile-web-app-title');
  meta.setAttribute('content', 'Forge');
  meta.setAttribute('data-forge', 'true');
  head.appendChild(meta);
};
