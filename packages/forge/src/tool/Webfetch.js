// FFI bindings for Tool.Webfetch PureScript module

// Fetch URL content
export const fetchUrlFFI = (url) => (timeout) => (userAgent) => () => {
  return new Promise(async (resolve) => {
    try {
      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), timeout);
      
      const response = await fetch(url, {
        method: "GET",
        headers: {
          "User-Agent": userAgent,
          "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        },
        signal: controller.signal
      });
      
      clearTimeout(timeoutId);
      
      const content = await response.text();
      const contentType = response.headers.get("content-type") || "text/html";
      
      resolve({
        tag: "Right",
        value: {
          content,
          statusCode: response.status,
          contentType
        }
      });
    } catch (e) {
      if (e.name === "AbortError") {
        resolve({ tag: "Left", value: "Request timed out" });
      } else {
        resolve({ tag: "Left", value: `Fetch failed: ${e.message}` });
      }
    }
  });
};

// Convert HTML to Markdown (simplified)
export const convertToMarkdownFFI = (html) => {
  // Simple HTML to Markdown conversion
  // In production, would use turndown library
  let md = html;
  
  // Remove script and style elements
  md = md.replace(/<script[^>]*>[\s\S]*?<\/script>/gi, "");
  md = md.replace(/<style[^>]*>[\s\S]*?<\/style>/gi, "");
  
  // Convert headings
  md = md.replace(/<h1[^>]*>([\s\S]*?)<\/h1>/gi, "# $1\n\n");
  md = md.replace(/<h2[^>]*>([\s\S]*?)<\/h2>/gi, "## $1\n\n");
  md = md.replace(/<h3[^>]*>([\s\S]*?)<\/h3>/gi, "### $1\n\n");
  md = md.replace(/<h4[^>]*>([\s\S]*?)<\/h4>/gi, "#### $1\n\n");
  md = md.replace(/<h5[^>]*>([\s\S]*?)<\/h5>/gi, "##### $1\n\n");
  md = md.replace(/<h6[^>]*>([\s\S]*?)<\/h6>/gi, "###### $1\n\n");
  
  // Convert paragraphs
  md = md.replace(/<p[^>]*>([\s\S]*?)<\/p>/gi, "$1\n\n");
  
  // Convert links
  md = md.replace(/<a[^>]*href="([^"]*)"[^>]*>([\s\S]*?)<\/a>/gi, "[$2]($1)");
  
  // Convert emphasis
  md = md.replace(/<(strong|b)[^>]*>([\s\S]*?)<\/(strong|b)>/gi, "**$2**");
  md = md.replace(/<(em|i)[^>]*>([\s\S]*?)<\/(em|i)>/gi, "*$2*");
  
  // Convert code
  md = md.replace(/<code[^>]*>([\s\S]*?)<\/code>/gi, "`$1`");
  md = md.replace(/<pre[^>]*>([\s\S]*?)<\/pre>/gi, "```\n$1\n```\n\n");
  
  // Convert lists
  md = md.replace(/<li[^>]*>([\s\S]*?)<\/li>/gi, "- $1\n");
  md = md.replace(/<\/?[uo]l[^>]*>/gi, "\n");
  
  // Convert line breaks
  md = md.replace(/<br\s*\/?>/gi, "\n");
  
  // Remove remaining HTML tags
  md = md.replace(/<[^>]+>/g, "");
  
  // Clean up whitespace
  md = md.replace(/\n{3,}/g, "\n\n");
  md = md.trim();
  
  // Decode HTML entities
  md = md.replace(/&nbsp;/g, " ");
  md = md.replace(/&amp;/g, "&");
  md = md.replace(/&lt;/g, "<");
  md = md.replace(/&gt;/g, ">");
  md = md.replace(/&quot;/g, '"');
  md = md.replace(/&#39;/g, "'");
  
  return md;
};

// Extract plain text from HTML
export const extractTextFFI = (html) => {
  // Remove script and style elements
  let text = html;
  text = text.replace(/<script[^>]*>[\s\S]*?<\/script>/gi, "");
  text = text.replace(/<style[^>]*>[\s\S]*?<\/style>/gi, "");
  text = text.replace(/<noscript[^>]*>[\s\S]*?<\/noscript>/gi, "");
  
  // Remove all HTML tags
  text = text.replace(/<[^>]+>/g, " ");
  
  // Clean up whitespace
  text = text.replace(/\s+/g, " ");
  text = text.trim();
  
  // Decode HTML entities
  text = text.replace(/&nbsp;/g, " ");
  text = text.replace(/&amp;/g, "&");
  text = text.replace(/&lt;/g, "<");
  text = text.replace(/&gt;/g, ">");
  text = text.replace(/&quot;/g, '"');
  text = text.replace(/&#39;/g, "'");
  
  return text;
};
