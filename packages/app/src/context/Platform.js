// App.Context.Platform FFI
// Web platform implementations for browser environment

// Open a URL in a new browser tab
export const openLinkImpl = (url) => () => {
  if (typeof window !== 'undefined' && window.open) {
    window.open(url, '_blank');
  }
};

// Reload the page (web platform restart)
export const restartImpl = () => {
  return new Promise((resolve) => {
    if (typeof window !== 'undefined' && window.location) {
      window.location.reload();
    }
    resolve();
  });
};

// Navigate back in browser history
export const backImpl = () => {
  if (typeof window !== 'undefined' && window.history) {
    window.history.back();
  }
};

// Navigate forward in browser history
export const forwardImpl = () => {
  if (typeof window !== 'undefined' && window.history) {
    window.history.forward();
  }
};

// Send a system notification with optional body and click-through URL
export const notifyImpl = (title) => (body) => (href) => () => {
  return new Promise((resolve) => {
    try {
      if (typeof window !== 'undefined' && typeof Notification !== 'undefined') {
        var doNotify = function() {
          var opts = {};
          if (body) {
            opts.body = body;
          }
          var n = new Notification(title, opts);
          if (href) {
            n.onclick = function() { window.open(href, '_blank'); };
          }
        };

        if (Notification.permission === 'granted') {
          doNotify();
          resolve();
        } else if (Notification.permission !== 'denied') {
          Notification.requestPermission().then(function(perm) {
            if (perm === 'granted') {
              doNotify();
            }
            resolve();
          }).catch(function() {
            resolve();
          });
          return;
        } else {
          resolve();
          return;
        }
      }
      resolve();
    } catch (_err) {
      // Notifications not supported in this environment
      resolve();
    }
  });
};
