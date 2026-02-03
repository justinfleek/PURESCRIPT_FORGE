// FFI for Marked Context
// Provides markdown parsing with syntax highlighting and math rendering

import { marked } from "marked";
import markedKatex from "marked-katex-extension";
import markedShiki from "marked-shiki";
import katex from "katex";
import { bundledLanguages } from "shiki";
import { getSharedHighlighter, registerCustomTheme } from "@pierre/diffs";

// Register the Forge syntax theme
registerCustomTheme("Forge", () => {
  return Promise.resolve({
    name: "Forge",
    colors: {
      "editor.background": "transparent",
      "editor.foreground": "var(--text-base)",
      "gitDecoration.addedResourceForeground": "var(--syntax-diff-add)",
      "gitDecoration.deletedResourceForeground": "var(--syntax-diff-delete)",
    },
    tokenColors: [
      {
        scope: ["comment", "punctuation.definition.comment", "string.comment"],
        settings: { foreground: "var(--syntax-comment)" },
      },
      {
        scope: ["entity.other.attribute-name"],
        settings: { foreground: "var(--syntax-property)" },
      },
      {
        scope: ["constant", "entity.name.constant", "variable.other.constant", "variable.language", "entity"],
        settings: { foreground: "var(--syntax-constant)" },
      },
      {
        scope: ["entity.name", "meta.export.default", "meta.definition.variable"],
        settings: { foreground: "var(--syntax-type)" },
      },
      {
        scope: ["entity.name.function", "support.type.primitive"],
        settings: { foreground: "var(--syntax-primitive)" },
      },
      {
        scope: "keyword",
        settings: { foreground: "var(--syntax-keyword)" },
      },
      {
        scope: ["storage", "storage.type"],
        settings: { foreground: "var(--syntax-keyword)" },
      },
      {
        scope: ["string", "punctuation.definition.string", "entity.name.tag"],
        settings: { foreground: "var(--syntax-string)" },
      },
      {
        scope: "variable",
        settings: { foreground: "var(--syntax-variable)" },
      },
    ],
    semanticTokenColors: {
      comment: "var(--syntax-comment)",
      string: "var(--syntax-string)",
      number: "var(--syntax-constant)",
      keyword: "var(--syntax-keyword)",
      variable: "var(--syntax-variable)",
      function: "var(--syntax-primitive)",
      type: "var(--syntax-type)",
    },
  });
});

// Render math in text using KaTeX
function renderMathInText(text) {
  let result = text;

  // Display math: $$...$$
  const displayMathRegex = /\$\$([\s\S]*?)\$\$/g;
  result = result.replace(displayMathRegex, (_, math) => {
    try {
      return katex.renderToString(math, {
        displayMode: true,
        throwOnError: false,
      });
    } catch {
      return `$$${math}$$`;
    }
  });

  // Inline math: $...$
  const inlineMathRegex = /(?<!\$)\$(?!\$)((?:[^$\\]|\\.)+?)\$(?!\$)/g;
  result = result.replace(inlineMathRegex, (_, math) => {
    try {
      return katex.renderToString(math, {
        displayMode: false,
        throwOnError: false,
      });
    } catch {
      return `$${math}$`;
    }
  });

  return result;
}

// Export for PureScript FFI
export const renderMathExpressions = (html) => {
  // Split on code/pre/kbd tags to avoid processing their contents
  const codeBlockPattern = /(<(?:pre|code|kbd)[^>]*>[\s\S]*?<\/(?:pre|code|kbd)>)/gi;
  const parts = html.split(codeBlockPattern);

  return parts
    .map((part, i) => {
      // Odd indices are the captured code blocks - leave them alone
      if (i % 2 === 1) return part;
      // Process math only in non-code parts
      return renderMathInText(part);
    })
    .join("");
};

// Highlight code blocks using Shiki
export const highlightCodeBlocks = (html) => async () => {
  const codeBlockRegex = /<pre><code(?:\s+class="language-([^"]*)")?>([\s\S]*?)<\/code><\/pre>/g;
  const matches = [...html.matchAll(codeBlockRegex)];
  if (matches.length === 0) return html;

  const highlighter = await getSharedHighlighter({ themes: ["Forge"], langs: [] });

  let result = html;
  for (const match of matches) {
    const [fullMatch, lang, escapedCode] = match;
    const code = escapedCode
      .replace(/&lt;/g, "<")
      .replace(/&gt;/g, ">")
      .replace(/&amp;/g, "&")
      .replace(/&quot;/g, '"')
      .replace(/&#39;/g, "'");

    let language = lang || "text";
    if (!(language in bundledLanguages)) {
      language = "text";
    }
    if (!highlighter.getLoadedLanguages().includes(language)) {
      await highlighter.loadLanguage(language);
    }

    const highlighted = highlighter.codeToHtml(code, {
      lang: language,
      theme: "Forge",
      tabindex: false,
    });
    result = result.replace(fullMatch, () => highlighted);
  }

  return result;
};

// Configure marked with extensions
const jsParser = marked.use(
  {
    renderer: {
      link({ href, title, text }) {
        const titleAttr = title ? ` title="${title}"` : "";
        return `<a href="${href}"${titleAttr} class="external-link" target="_blank" rel="noopener noreferrer">${text}</a>`;
      },
    },
  },
  markedKatex({
    throwOnError: false,
    nonStandard: true,
  }),
  markedShiki({
    async highlight(code, lang) {
      const highlighter = await getSharedHighlighter({ themes: ["Forge"], langs: [] });
      if (!(lang in bundledLanguages)) {
        lang = "text";
      }
      if (!highlighter.getLoadedLanguages().includes(lang)) {
        await highlighter.loadLanguage(lang);
      }
      return highlighter.codeToHtml(code, {
        lang: lang || "text",
        theme: "Forge",
        tabindex: false,
      });
    },
  })
);

// Parse markdown implementation
export const parseMarkdownImpl = (markdown) => async () => {
  return jsParser.parse(markdown);
};

// Context reference placeholder
export const markedContextRef = { current: null };
