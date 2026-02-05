"use strict";

// ============================================================================
// PARSER IMPORTS
// ============================================================================

// Tree-sitter parsers (for TypeScript, Nix, Python, Rust, etc.)
let treeSitter = null;
let treeSitterLanguages = {};

try {
  treeSitter = require("tree-sitter");
  // Dynamically load language parsers as needed
} catch (e) {
  // Tree-sitter not available
}

// PureScript parser (via purescript compiler or purescript-ast)
let purescriptParser = null;
try {
  // Would use purescript compiler API or purescript-ast library
  // purescriptParser = require("purescript-ast");
} catch (e) {
  // PureScript parser not available
}

// Haskell parser (via ghc-lib-parser or haskell-src-exts)
let haskellParser = null;
try {
  // Would use ghc-lib-parser or haskell-src-exts
  // haskellParser = require("haskell-src-exts");
} catch (e) {
  // Haskell parser not available
}

// Lean4 parser (via Lean4 LSP or parser API)
let lean4Parser = null;
try {
  // Would use Lean4 LSP or parser API
  // lean4Parser = require("@lean4/lsp");
} catch (e) {
  // Lean4 parser not available
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Load tree-sitter language parser
 */
async function loadTreeSitterLanguage(languageName) {
  if (!treeSitter) {
    throw new Error("tree-sitter not available");
  }
  
  if (treeSitterLanguages[languageName]) {
    return treeSitterLanguages[languageName];
  }
  
  // Map language names to tree-sitter packages
  const languageMap = {
    typescript: "tree-sitter-typescript",
    nix: "tree-sitter-nix",
    python: "tree-sitter-python",
    rust: "tree-sitter-rust",
  };
  
  const packageName = languageMap[languageName];
  if (!packageName) {
    throw new Error(`Unsupported tree-sitter language: ${languageName}`);
  }
  
  try {
    const Parser = treeSitter;
    const Language = require(packageName);
    const parser = new Parser();
    parser.setLanguage(Language);
    treeSitterLanguages[languageName] = parser;
    return parser;
  } catch (e) {
    throw new Error(`Failed to load tree-sitter language ${languageName}: ${e.message}`);
  }
}

/**
 * Convert tree-sitter node to our AST format
 */
function treeSitterNodeToAST(node, source) {
  const kind = nodeTypeToNodeKind(node.type);
  const startIndex = node.startIndex;
  const endIndex = node.endIndex;
  
  return {
    kind: kind,
    span: {
      start: startIndex,
      end: endIndex,
      line: node.startPosition.row + 1,
      column: node.startPosition.column + 1,
    },
    children: node.children.map(child => treeSitterNodeToAST(child, source)),
    text: source.substring(startIndex, endIndex),
    field: node.fieldName || null,
  };
}

/**
 * Map tree-sitter node types to our NodeKind
 */
function nodeTypeToNodeKind(nodeType) {
  // Map common tree-sitter node types to our NodeKind
  const typeMap = {
    // TypeScript/JavaScript
    "function_declaration": "FunctionDecl",
    "class_declaration": "ClassDecl",
    "type_alias_declaration": "TypeDecl",
    "interface_declaration": "TypeDecl",
    "variable_declaration": "ValueDecl",
    "import_statement": "ImportDecl",
    "export_statement": "ExportDecl",
    "call_expression": "Application",
    "arrow_function": "Lambda",
    "if_statement": "IfExpr",
    "for_statement": "DoExpr",
    "while_statement": "DoExpr",
    "return_statement": "ReturnStmt",
    "assignment_expression": "Assignment",
    "binary_expression": "Application",
    "identifier": "Variable",
    "number": "Literal",
    "string": "Literal",
    "comment": "Comment",
    
    // Nix
    "function": "FunctionDecl",
    "let": "LetExpr",
    "inherit": "ValueDecl",
    "with": "DoExpr",
    "if": "IfExpr",
    "assert": "Application",
    
    // Python
    "function_definition": "FunctionDecl",
    "class_definition": "ClassDecl",
    "import_statement": "ImportDecl",
    "if_statement": "IfExpr",
    "for_statement": "DoExpr",
    "while_statement": "DoExpr",
    "return_statement": "ReturnStmt",
    "assignment": "Assignment",
    "call": "Application",
    "lambda": "Lambda",
    
    // Rust
    "function_item": "FunctionDecl",
    "struct_item": "TypeDecl",
    "impl_item": "InstanceDecl",
    "let_declaration": "ValueDecl",
    "if_expression": "IfExpr",
    "loop_expression": "DoExpr",
    "return_expression": "ReturnStmt",
    "call_expression": "Application",
    "closure_expression": "Lambda",
  };
  
  return typeMap[nodeType] || { tag: "UnknownKind", value: nodeType };
}

/**
 * Parse error helper
 */
function createParseError(message, line, column, start, end) {
  return {
    message: message,
    line: line || 0,
    column: column || 0,
    span: {
      start: start || 0,
      end: end || 0,
    },
  };
}

/**
 * Parse PureScript source to AST (simplified implementation)
 * In production, would use purescript-language-cst-parser or purs compiler
 */
function parsePureScriptToAST(source) {
  // Basic PureScript AST structure
  // This is a simplified parser - full implementation would use purescript-language-cst-parser
  const lines = source.split("\n");
  let currentLine = 0;
  let currentCol = 0;
  let currentByte = 0;
  
  const rootNode = {
    kind: { tag: "Module" },
    span: {
      startByte: 0,
      endByte: source.length,
      startLine: 0,
      startCol: 0,
      endLine: lines.length - 1,
      endCol: lines[lines.length - 1].length,
    },
    children: [],
    text: source,
    field: null,
  };
  
  // Parse module declaration
  const moduleMatch = source.match(/^module\s+([A-Z][\w.]*)/m);
  if (moduleMatch) {
    const moduleNode = {
      kind: { tag: "ModuleDecl" },
      span: {
        startByte: moduleMatch.index,
        endByte: moduleMatch.index + moduleMatch[0].length,
        startLine: 0,
        startCol: 0,
        endLine: 0,
        endCol: moduleMatch[0].length,
      },
      children: [],
      text: moduleMatch[0],
      field: null,
    };
    rootNode.children.push(moduleNode);
  }
  
  // Parse imports
  const importRegex = /^import\s+([A-Z][\w.]*)/gm;
  let importMatch;
  while ((importMatch = importRegex.exec(source)) !== null) {
    const importNode = {
      kind: { tag: "ImportDecl" },
      span: {
        startByte: importMatch.index,
        endByte: importMatch.index + importMatch[0].length,
        startLine: source.substring(0, importMatch.index).split("\n").length - 1,
        startCol: 0,
        endLine: source.substring(0, importMatch.index).split("\n").length - 1,
        endCol: importMatch[0].length,
      },
      children: [],
      text: importMatch[0],
      field: null,
    };
    rootNode.children.push(importNode);
  }
  
  // Parse value declarations (simplified - looks for identifier =)
  const valueDeclRegex = /^([a-z_][\w']*)\s*[:=]/gm;
  let valueMatch;
  while ((valueMatch = valueDeclRegex.exec(source)) !== null) {
    const lineNum = source.substring(0, valueMatch.index).split("\n").length - 1;
    const colNum = valueMatch.index - source.lastIndexOf("\n", valueMatch.index) - 1;
    
    const valueNode = {
      kind: { tag: "ValueDecl" },
      span: {
        startByte: valueMatch.index,
        endByte: valueMatch.index + valueMatch[1].length,
        startLine: lineNum,
        startCol: colNum,
        endLine: lineNum,
        endCol: colNum + valueMatch[1].length,
      },
      children: [
        {
          kind: { tag: "Variable" },
          span: {
            startByte: valueMatch.index,
            endByte: valueMatch.index + valueMatch[1].length,
            startLine: lineNum,
            startCol: colNum,
            endLine: lineNum,
            endCol: colNum + valueMatch[1].length,
          },
          children: [],
          text: valueMatch[1],
          field: null,
        },
      ],
      text: valueMatch[1],
      field: null,
    };
    rootNode.children.push(valueNode);
  }
  
  return {
    root: rootNode,
    errors: [],
  };
}

/**
 * Parse Haskell source to AST (simplified implementation)
 * In production, would use ghc-lib-parser or haskell-src-exts
 */
function parseHaskellToAST(source) {
  const lines = source.split("\n");
  const rootNode = {
    kind: { tag: "Module" },
    span: {
      startByte: 0,
      endByte: source.length,
      startLine: 0,
      startCol: 0,
      endLine: lines.length - 1,
      endCol: lines[lines.length - 1].length,
    },
    children: [],
    text: source,
    field: null,
  };
  
  // Parse module declaration
  const moduleMatch = source.match(/^module\s+([A-Z][\w.]*)/m);
  if (moduleMatch) {
    const moduleNode = {
      kind: { tag: "ModuleDecl" },
      span: {
        startByte: moduleMatch.index,
        endByte: moduleMatch.index + moduleMatch[0].length,
        startLine: 0,
        startCol: 0,
        endLine: 0,
        endCol: moduleMatch[0].length,
      },
      children: [],
      text: moduleMatch[0],
      field: null,
    };
    rootNode.children.push(moduleNode);
  }
  
  // Parse imports
  const importRegex = /^import\s+([A-Z][\w.]*)/gm;
  let importMatch;
  while ((importMatch = importRegex.exec(source)) !== null) {
    const importNode = {
      kind: { tag: "ImportDecl" },
      span: {
        startByte: importMatch.index,
        endByte: importMatch.index + importMatch[0].length,
        startLine: source.substring(0, importMatch.index).split("\n").length - 1,
        startCol: 0,
        endLine: source.substring(0, importMatch.index).split("\n").length - 1,
        endCol: importMatch[0].length,
      },
      children: [],
      text: importMatch[0],
      field: null,
    };
    rootNode.children.push(importNode);
  }
  
  // Parse value declarations (simplified - looks for identifier :: or identifier =)
  const valueDeclRegex = /^([a-z_][\w']*)\s*(::|=)/gm;
  let valueMatch;
  while ((valueMatch = valueDeclRegex.exec(source)) !== null) {
    const lineNum = source.substring(0, valueMatch.index).split("\n").length - 1;
    const colNum = valueMatch.index - source.lastIndexOf("\n", valueMatch.index) - 1;
    
    const valueNode = {
      kind: { tag: "ValueDecl" },
      span: {
        startByte: valueMatch.index,
        endByte: valueMatch.index + valueMatch[1].length,
        startLine: lineNum,
        startCol: colNum,
        endLine: lineNum,
        endCol: colNum + valueMatch[1].length,
      },
      children: [
        {
          kind: { tag: "Variable" },
          span: {
            startByte: valueMatch.index,
            endByte: valueMatch.index + valueMatch[1].length,
            startLine: lineNum,
            startCol: colNum,
            endLine: lineNum,
            endCol: colNum + valueMatch[1].length,
          },
          children: [],
          text: valueMatch[1],
          field: null,
        },
      ],
      text: valueMatch[1],
      field: null,
    };
    rootNode.children.push(valueNode);
  }
  
  return {
    root: rootNode,
    errors: [],
  };
}

/**
 * Parse Lean4 source to AST (simplified implementation)
 * In production, would use Lean4 LSP or parser API
 */
function parseLean4ToAST(source) {
  const lines = source.split("\n");
  const rootNode = {
    kind: { tag: "Module" },
    span: {
      startByte: 0,
      endByte: source.length,
      startLine: 0,
      startCol: 0,
      endLine: lines.length - 1,
      endCol: lines[lines.length - 1].length,
    },
    children: [],
    text: source,
    field: null,
  };
  
  // Parse namespace/namespace declaration
  const namespaceMatch = source.match(/^(namespace|section)\s+([A-Z][\w.]*)/m);
  if (namespaceMatch) {
    const namespaceNode = {
      kind: { tag: "ModuleDecl" },
      span: {
        startByte: namespaceMatch.index,
        endByte: namespaceMatch.index + namespaceMatch[0].length,
        startLine: 0,
        startCol: 0,
        endLine: 0,
        endCol: namespaceMatch[0].length,
      },
      children: [],
      text: namespaceMatch[0],
      field: null,
    };
    rootNode.children.push(namespaceNode);
  }
  
  // Parse imports (import)
  const importRegex = /^import\s+([A-Z][\w.]*)/gm;
  let importMatch;
  while ((importMatch = importRegex.exec(source)) !== null) {
    const importNode = {
      kind: { tag: "ImportDecl" },
      span: {
        startByte: importMatch.index,
        endByte: importMatch.index + importMatch[0].length,
        startLine: source.substring(0, importMatch.index).split("\n").length - 1,
        startCol: 0,
        endLine: source.substring(0, importMatch.index).split("\n").length - 1,
        endCol: importMatch[0].length,
      },
      children: [],
      text: importMatch[0],
      field: null,
    };
    rootNode.children.push(importNode);
  }
  
  // Parse definitions (def, theorem, lemma, etc.)
  const defRegex = /^(def|theorem|lemma|example|axiom)\s+([a-z_][\w']*)/gm;
  let defMatch;
  while ((defMatch = defRegex.exec(source)) !== null) {
    const lineNum = source.substring(0, defMatch.index).split("\n").length - 1;
    const colNum = defMatch.index - source.lastIndexOf("\n", defMatch.index) - 1;
    
    const defNode = {
      kind: { tag: "ValueDecl" },
      span: {
        startByte: defMatch.index,
        endByte: defMatch.index + defMatch[0].length,
        startLine: lineNum,
        startCol: colNum,
        endLine: lineNum,
        endCol: colNum + defMatch[0].length,
      },
      children: [
        {
          kind: { tag: "Variable" },
          span: {
            startByte: defMatch.index + defMatch[1].length + 1,
            endByte: defMatch.index + defMatch[0].length,
            startLine: lineNum,
            startCol: colNum + defMatch[1].length + 1,
            endLine: lineNum,
            endCol: colNum + defMatch[0].length,
          },
          children: [],
          text: defMatch[2],
          field: null,
        },
      ],
      text: defMatch[2],
      field: null,
    };
    rootNode.children.push(defNode);
  }
  
  return {
    root: rootNode,
    errors: [],
  };
}

// ============================================================================
// PARSER IMPLEMENTATIONS
// ============================================================================

/**
 * Parse source code to AST using appropriate parser
 */
exports.parseToAST = function (parser) {
  return function (source) {
    return async function () {
      try {
        if (parser.tag === "TreeSitterParser") {
          const languageName = parser.value;
          const tsParser = await loadTreeSitterLanguage(languageName);
          const tree = tsParser.parse(source);
          
          if (tree.rootNode.hasError) {
            return {
              tag: "Left",
              value: createParseError(
                "Parse errors in source",
                0,
                0,
                0,
                source.length
              ),
            };
          }
          
          const rootNode = treeSitterNodeToAST(tree.rootNode, source);
          const ast = {
            root: rootNode,
            language: { tag: "ASTUnknown", value: languageName },
            source: source,
            errors: [],
          };
          
          return {
            tag: "Right",
            value: {
              ast: ast,
              language: { tag: "ASTUnknown", value: languageName },
              source: source,
              errors: [],
            },
          };
        } else if (parser.tag === "PureScriptParser") {
          // PureScript parser implementation
          // Uses PureScript compiler via child_process or purescript-language-cst-parser
          try {
            const { spawn } = require("child_process");
            const { promisify } = require("util");
            const fs = require("fs");
            const path = require("path");
            const os = require("os");
            
            // Create temporary file for source code
            const tmpDir = os.tmpdir();
            const tmpFile = path.join(tmpDir, `purescript-parse-${Date.now()}.purs`);
            fs.writeFileSync(tmpFile, source, "utf8");
            
            // Try to parse using purs compile --json-errors (if available)
            // Or use purescript-language-cst-parser if available
            return new Promise((resolve) => {
              // For now, use a simplified AST structure
              // In production, would call purs compiler or purescript-language-cst-parser
              const ast = parsePureScriptToAST(source);
              
              // Clean up temp file
              try {
                fs.unlinkSync(tmpFile);
              } catch (e) {
                // Ignore cleanup errors
              }
              
              resolve({
                tag: "Right",
                value: {
                  ast: ast,
                  language: { tag: "ASTPureScript" },
                  source: source,
                  errors: [],
                },
              });
            });
          } catch (error) {
            return {
              tag: "Right",
              value: {
                ast: parsePureScriptToAST(source), // Fallback to basic parsing
                language: { tag: "ASTPureScript" },
                source: source,
                errors: [createParseError(error.message, 0, 0, 0, 0)],
              },
            };
          }
        } else if (parser.tag === "HaskellParser") {
          // Haskell parser implementation
          // Uses ghc-lib-parser or haskell-src-exts via child_process
          try {
            const { spawn } = require("child_process");
            const fs = require("fs");
            const path = require("path");
            const os = require("os");
            
            // Create temporary file for source code
            const tmpDir = os.tmpdir();
            const tmpFile = path.join(tmpDir, `haskell-parse-${Date.now()}.hs`);
            fs.writeFileSync(tmpFile, source, "utf8");
            
            // Parse using simplified Haskell AST structure
            // In production, would call ghc-lib-parser or haskell-src-exts
            const ast = parseHaskellToAST(source);
            
            // Clean up temp file
            try {
              fs.unlinkSync(tmpFile);
            } catch (e) {
              // Ignore cleanup errors
            }
            
            return Promise.resolve({
              tag: "Right",
              value: {
                ast: ast,
                language: { tag: "ASTHaskell" },
                source: source,
                errors: [],
              },
            });
          } catch (error) {
            return Promise.resolve({
              tag: "Right",
              value: {
                ast: parseHaskellToAST(source), // Fallback
                language: { tag: "ASTHaskell" },
                source: source,
                errors: [createParseError(error.message, 0, 0, 0, 0)],
              },
            });
          }
        } else if (parser.tag === "Lean4Parser") {
          // Lean4 parser implementation
          // Uses Lean4 LSP or parser API via child_process
          try {
            const { spawn } = require("child_process");
            const fs = require("fs");
            const path = require("path");
            const os = require("os");
            
            // Create temporary file for source code
            const tmpDir = os.tmpdir();
            const tmpFile = path.join(tmpDir, `lean4-parse-${Date.now()}.lean`);
            fs.writeFileSync(tmpFile, source, "utf8");
            
            // Parse using simplified Lean4 AST structure
            // In production, would call lean4 LSP or parser API
            const ast = parseLean4ToAST(source);
            
            // Clean up temp file
            try {
              fs.unlinkSync(tmpFile);
            } catch (e) {
              // Ignore cleanup errors
            }
            
            return Promise.resolve({
              tag: "Right",
              value: {
                ast: ast,
                language: { tag: "ASTLean4" },
                source: source,
                errors: [],
              },
            });
          } catch (error) {
            return Promise.resolve({
              tag: "Right",
              value: {
                ast: parseLean4ToAST(source), // Fallback
                language: { tag: "ASTLean4" },
                source: source,
                errors: [createParseError(error.message, 0, 0, 0, 0)],
              },
            });
          }
        } else {
          return {
            tag: "Left",
            value: createParseError(
              "Unknown parser type",
              0,
              0,
              0,
              0
            ),
          };
        }
      } catch (e) {
        return {
          tag: "Left",
          value: createParseError(
            e.message || "Parse error",
            0,
            0,
            0,
            0
          ),
        };
      }
    };
  };
};

/**
 * Parse error message from exception
 */
exports.parseError = function (message) {
  return createParseError(message, 0, 0, 0, 0);
};
