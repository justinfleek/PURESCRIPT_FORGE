// Markdown FFI
// Markdown parsing, sanitization, and code copy functionality

// LRU cache for parsed markdown
const MAX_CACHE_SIZE = 200;
const cache = new Map();

// Simple checksum for cache keys
const checksum = (str) => {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return hash.toString(16);
};

// Touch cache entry (move to end for LRU)
const touch = (key, value) => {
  cache.delete(key);
  cache.set(key, value);
  
  if (cache.size <= MAX_CACHE_SIZE) return;
  
  const first = cache.keys().next().value;
  if (first) cache.delete(first);
};

// Parse markdown to HTML
// Returns an Aff (async effect)
export const parseMarkdown = (markdown) => () => {
  return new Promise((resolve, reject) => {
    try {
      // Check if marked is available globally
      if (typeof marked !== 'undefined' && marked.parse) {
        resolve(marked.parse(markdown));
      } else {
        // Basic markdown parsing fallback
        let html = markdown
          // Headers
          .replace(/^### (.*$)/gm, '<h3>$1</h3>')
          .replace(/^## (.*$)/gm, '<h2>$1</h2>')
          .replace(/^# (.*$)/gm, '<h1>$1</h1>')
          // Bold
          .replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>')
          // Italic
          .replace(/\*(.*?)\*/g, '<em>$1</em>')
          // Code blocks
          .replace(/```(\w*)\n([\s\S]*?)```/g, '<pre><code class="language-$1">$2</code></pre>')
          // Inline code
          .replace(/`([^`]+)`/g, '<code>$1</code>')
          // Links
          .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2" target="_blank">$1</a>')
          // Paragraphs
          .replace(/\n\n/g, '</p><p>')
          // Line breaks
          .replace(/\n/g, '<br>');
        
        html = '<p>' + html + '</p>';
        resolve(html);
      }
    } catch (e) {
      reject(e);
    }
  });
};

// Sanitize HTML
export const sanitize = (html) => () => {
  // Check if DOMPurify is available
  if (typeof DOMPurify !== 'undefined' && DOMPurify.sanitize) {
    return DOMPurify.sanitize(html, {
      USE_PROFILES: { html: true, mathMl: true },
      SANITIZE_NAMED_PROPS: true,
      FORBID_TAGS: ['style'],
      FORBID_CONTENTS: ['style', 'script'],
    });
  }
  
  // Basic sanitization fallback
  const div = document.createElement('div');
  div.innerHTML = html;
  
  // Remove script tags
  const scripts = div.querySelectorAll('script');
  scripts.forEach(s => s.remove());
  
  // Remove style tags
  const styles = div.querySelectorAll('style');
  styles.forEach(s => s.remove());
  
  // Remove onclick and other event handlers
  const all = div.querySelectorAll('*');
  all.forEach(el => {
    const attrs = Array.from(el.attributes);
    attrs.forEach(attr => {
      if (attr.name.startsWith('on')) {
        el.removeAttribute(attr.name);
      }
    });
  });
  
  // Add rel to external links
  const links = div.querySelectorAll('a[target="_blank"]');
  links.forEach(link => {
    link.setAttribute('rel', 'noopener noreferrer');
  });
  
  return div.innerHTML;
};

// Get cached HTML
export const getCached = (key) => () => {
  const hash = checksum(key);
  const entry = cache.get(hash);
  if (entry) {
    touch(hash, entry);
    return entry.html;
  }
  return null;
};

// Set cached HTML
export const setCached = (key) => (html) => () => {
  const hash = checksum(key);
  touch(hash, { hash, html });
};

// Set innerHTML on element
export const setInnerHtml = (element) => (html) => () => {
  element.innerHTML = html;
};

// Icon SVG paths
const iconPaths = {
  copy: '<path d="M6.2513 6.24935V2.91602H17.0846V13.7493H13.7513M13.7513 6.24935V17.0827H2.91797V6.24935H13.7513Z" stroke="currentColor" stroke-linecap="round"/>',
  check: '<path d="M5 11.9657L8.37838 14.7529L15 5.83398" stroke="currentColor" stroke-linecap="square"/>',
};

// Create icon element
const createIcon = (path, slot) => {
  const icon = document.createElement('div');
  icon.setAttribute('data-component', 'icon');
  icon.setAttribute('data-size', 'small');
  icon.setAttribute('data-slot', slot);
  
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('data-slot', 'icon-svg');
  svg.setAttribute('fill', 'none');
  svg.setAttribute('viewBox', '0 0 20 20');
  svg.setAttribute('aria-hidden', 'true');
  svg.innerHTML = path;
  
  icon.appendChild(svg);
  return icon;
};

// Create copy button
const createCopyButton = () => {
  const button = document.createElement('button');
  button.type = 'button';
  button.setAttribute('data-component', 'icon-button');
  button.setAttribute('data-variant', 'secondary');
  button.setAttribute('data-size', 'normal');
  button.setAttribute('data-slot', 'markdown-copy-button');
  button.setAttribute('aria-label', 'Copy code');
  button.setAttribute('title', 'Copy code');
  
  button.appendChild(createIcon(iconPaths.copy, 'copy-icon'));
  button.appendChild(createIcon(iconPaths.check, 'check-icon'));
  
  return button;
};

// Setup code copy buttons
export const setupCodeCopy = (root) => () => {
  const timeouts = new Map();
  
  // Wrap pre blocks with copy button
  const blocks = Array.from(root.querySelectorAll('pre'));
  for (const block of blocks) {
    const parent = block.parentElement;
    if (!parent) continue;
    
    // Check if already wrapped
    if (parent.getAttribute('data-component') === 'markdown-code') continue;
    
    // Create wrapper
    const wrapper = document.createElement('div');
    wrapper.setAttribute('data-component', 'markdown-code');
    parent.replaceChild(wrapper, block);
    wrapper.appendChild(block);
    wrapper.appendChild(createCopyButton());
  }
  
  // Handle copy clicks
  const handleClick = async (event) => {
    const target = event.target;
    if (!(target instanceof Element)) return;
    
    const button = target.closest('[data-slot="markdown-copy-button"]');
    if (!(button instanceof HTMLButtonElement)) return;
    
    const code = button.closest('[data-component="markdown-code"]')?.querySelector('code');
    const content = code?.textContent ?? '';
    if (!content) return;
    
    try {
      await navigator.clipboard.writeText(content);
      
      // Show copied state
      button.setAttribute('data-copied', 'true');
      button.setAttribute('aria-label', 'Copied!');
      button.setAttribute('title', 'Copied!');
      
      // Clear existing timeout
      const existing = timeouts.get(button);
      if (existing) clearTimeout(existing);
      
      // Reset after 2 seconds
      const timeout = setTimeout(() => {
        button.removeAttribute('data-copied');
        button.setAttribute('aria-label', 'Copy code');
        button.setAttribute('title', 'Copy code');
      }, 2000);
      
      timeouts.set(button, timeout);
    } catch (e) {
      console.error('Failed to copy:', e);
    }
  };
  
  root.addEventListener('click', handleClick);
  
  // Return cleanup function (not used in PureScript but good practice)
  return () => {
    root.removeEventListener('click', handleClick);
    for (const timeout of timeouts.values()) {
      clearTimeout(timeout);
    }
  };
};
