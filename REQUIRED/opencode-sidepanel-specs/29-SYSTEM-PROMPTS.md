# 29-SYSTEM-PROMPTS: Managing AI System Prompts

## Overview

System prompts define the AI's behavior, personality, and capabilities. This document specifies how to manage, customize, and optimize system prompts.

---

## Default System Prompt

```markdown
You are an expert software engineer with deep knowledge of:
- TypeScript, JavaScript, Python, and modern programming languages
- React, Node.js, and web development frameworks
- System design and architecture
- Testing and debugging strategies

You have access to tools for:
- Reading and writing files
- Running shell commands
- Searching codebases

Guidelines:
- Be concise and direct
- Show code examples when helpful
- Explain your reasoning
- Ask clarifying questions when needed
- Admit when you're uncertain

Current context: Working in ${projectName} with ${fileCount} files in context.
```

---

## Prompt Templates

### Coding Assistant

```typescript
const CODING_ASSISTANT = `
You are an expert software engineer helping with coding tasks.

Your capabilities:
- Read and write code files
- Run tests and commands
- Debug issues
- Refactor code
- Explain concepts

Guidelines:
- Write clean, maintainable code
- Follow project conventions
- Include error handling
- Add comments for complex logic
- Suggest tests when appropriate

Project: {{projectName}}
Language: {{primaryLanguage}}
Framework: {{framework}}
`;
```

### Code Reviewer

```typescript
const CODE_REVIEWER = `
You are a senior engineer conducting code reviews.

Focus on:
- Code correctness and logic errors
- Security vulnerabilities
- Performance issues
- Maintainability and readability
- Test coverage

Be constructive and specific. Explain why changes are needed.
Prioritize issues by severity: critical > major > minor > nitpick.
`;
```

### Documentation Writer

```typescript
const DOCUMENTATION_WRITER = `
You are a technical writer creating documentation.

Goals:
- Clear, concise explanations
- Practical examples
- Accurate technical details
- Consistent formatting

Output format: Markdown with code blocks.
Audience: {{audience}}
`;
```

### Lean4 Proof Assistant

```typescript
const LEAN4_ASSISTANT = `
You are an expert in Lean4 theorem proving.

Capabilities:
- Analyze proof goals
- Suggest tactics
- Explain proof strategies
- Help with type theory

When suggesting tactics:
1. Explain what the tactic does
2. Show how it transforms the goal
3. Suggest follow-up tactics

Current goal: {{proofGoal}}
Available hypotheses: {{hypotheses}}
`;
```

---

## Data Model

```typescript
interface SystemPrompt {
  id: string;
  name: string;
  description: string;
  
  // Content
  template: string;
  variables: PromptVariable[];
  
  // Metadata
  category: PromptCategory;
  isDefault: boolean;
  isCustom: boolean;
  
  // Usage
  tokenEstimate: number;
  lastUsed?: Date;
  useCount: number;
}

interface PromptVariable {
  name: string;
  description: string;
  defaultValue?: string;
  required: boolean;
}

type PromptCategory =
  | 'coding'
  | 'review'
  | 'documentation'
  | 'lean4'
  | 'general'
  | 'custom';

interface PromptContext {
  projectName: string;
  primaryLanguage: string;
  framework?: string;
  fileCount: number;
  currentFile?: string;
  proofGoal?: string;
  hypotheses?: string[];
}
```

---

## Prompt Manager

```typescript
// bridge/src/prompts/manager.ts

export class PromptManager {
  private prompts: Map<string, SystemPrompt> = new Map();
  private activePromptId: string = 'default-coding';
  
  constructor() {
    this.loadBuiltinPrompts();
    this.loadCustomPrompts();
  }
  
  private loadBuiltinPrompts(): void {
    const builtins: SystemPrompt[] = [
      {
        id: 'default-coding',
        name: 'Coding Assistant',
        description: 'General-purpose coding help',
        template: CODING_ASSISTANT,
        variables: [
          { name: 'projectName', description: 'Project name', required: false },
          { name: 'primaryLanguage', description: 'Main language', required: false },
          { name: 'framework', description: 'Framework in use', required: false }
        ],
        category: 'coding',
        isDefault: true,
        isCustom: false,
        tokenEstimate: 200,
        useCount: 0
      },
      {
        id: 'code-reviewer',
        name: 'Code Reviewer',
        description: 'Detailed code review feedback',
        template: CODE_REVIEWER,
        variables: [],
        category: 'review',
        isDefault: false,
        isCustom: false,
        tokenEstimate: 150,
        useCount: 0
      },
      {
        id: 'lean4-assistant',
        name: 'Lean4 Proof Assistant',
        description: 'Help with Lean4 proofs',
        template: LEAN4_ASSISTANT,
        variables: [
          { name: 'proofGoal', description: 'Current proof goal', required: true },
          { name: 'hypotheses', description: 'Available hypotheses', required: false }
        ],
        category: 'lean4',
        isDefault: false,
        isCustom: false,
        tokenEstimate: 180,
        useCount: 0
      }
    ];
    
    for (const prompt of builtins) {
      this.prompts.set(prompt.id, prompt);
    }
  }
  
  render(promptId: string, context: PromptContext): string {
    const prompt = this.prompts.get(promptId);
    if (!prompt) {
      throw new Error(`Prompt not found: ${promptId}`);
    }
    
    let rendered = prompt.template;
    
    // Replace variables
    for (const variable of prompt.variables) {
      const value = context[variable.name as keyof PromptContext] 
        ?? variable.defaultValue 
        ?? '';
      
      rendered = rendered.replace(
        new RegExp(`{{${variable.name}}}`, 'g'),
        String(value)
      );
    }
    
    // Track usage
    prompt.lastUsed = new Date();
    prompt.useCount++;
    
    return rendered.trim();
  }
  
  getActive(): SystemPrompt {
    return this.prompts.get(this.activePromptId)!;
  }
  
  setActive(promptId: string): void {
    if (!this.prompts.has(promptId)) {
      throw new Error(`Prompt not found: ${promptId}`);
    }
    this.activePromptId = promptId;
    this.broadcast('prompt.changed', { promptId });
  }
  
  create(prompt: Omit<SystemPrompt, 'id' | 'isDefault' | 'useCount'>): SystemPrompt {
    const newPrompt: SystemPrompt = {
      ...prompt,
      id: `custom-${generateId()}`,
      isDefault: false,
      isCustom: true,
      useCount: 0
    };
    
    this.prompts.set(newPrompt.id, newPrompt);
    this.saveCustomPrompts();
    
    return newPrompt;
  }
  
  update(promptId: string, updates: Partial<SystemPrompt>): void {
    const prompt = this.prompts.get(promptId);
    if (!prompt) {
      throw new Error(`Prompt not found: ${promptId}`);
    }
    
    if (!prompt.isCustom) {
      throw new Error('Cannot modify builtin prompts');
    }
    
    Object.assign(prompt, updates);
    this.saveCustomPrompts();
  }
  
  delete(promptId: string): void {
    const prompt = this.prompts.get(promptId);
    if (!prompt) return;
    
    if (!prompt.isCustom) {
      throw new Error('Cannot delete builtin prompts');
    }
    
    this.prompts.delete(promptId);
    
    if (this.activePromptId === promptId) {
      this.activePromptId = 'default-coding';
    }
    
    this.saveCustomPrompts();
  }
  
  getAll(): SystemPrompt[] {
    return Array.from(this.prompts.values());
  }
  
  getByCategory(category: PromptCategory): SystemPrompt[] {
    return this.getAll().filter(p => p.category === category);
  }
}
```

---

## Prompt Editor UI

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SYSTEM PROMPTS                                                       [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ ACTIVE ──────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ● Coding Assistant                                    ~200 tokens    │ │
│  │    General-purpose coding help                                        │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ BUILT-IN ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ○ Coding Assistant           coding       200 tk     [Activate]      │ │
│  │  ○ Code Reviewer              review       150 tk     [Activate]      │ │
│  │  ○ Documentation Writer       docs         120 tk     [Activate]      │ │
│  │  ○ Lean4 Proof Assistant      lean4        180 tk     [Activate]      │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ CUSTOM ──────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ○ My Debug Helper            custom       250 tk     [Edit] [Delete] │ │
│  │                                                                        │ │
│  │  [+ Create Custom Prompt]                                             │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Prompt Editor

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  EDIT PROMPT: My Debug Helper                                        [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Name: [My Debug Helper                                                  ]  │
│                                                                             │
│  Description: [Custom prompt for debugging complex issues                ]  │
│                                                                             │
│  Category: [Custom ▼]                                                      │
│                                                                             │
│  ┌─ TEMPLATE ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  You are a debugging expert focused on finding root causes.           │ │
│  │                                                                        │ │
│  │  When debugging:                                                       │ │
│  │  1. Start by understanding the expected behavior                      │ │
│  │  2. Identify where the actual behavior differs                        │ │
│  │  3. Form hypotheses and test them systematically                      │ │
│  │  4. Use logging and breakpoints strategically                         │ │
│  │                                                                        │ │
│  │  Project: {{projectName}}                                             │ │
│  │  Error: {{errorMessage}}                                              │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ VARIABLES ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  {{projectName}}    Project name              [Optional]              │ │
│  │  {{errorMessage}}   Error being debugged      [Required]              │ │
│  │                                                                        │ │
│  │  [+ Add Variable]                                                     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Token estimate: ~250 tokens                                               │
│                                                                             │
│  [Cancel]  [Preview]                                       [Save Prompt]   │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## PureScript Types

```purescript
module Sidepanel.Prompts where

type SystemPrompt =
  { id :: String
  , name :: String
  , description :: String
  , template :: String
  , variables :: Array PromptVariable
  , category :: PromptCategory
  , isDefault :: Boolean
  , isCustom :: Boolean
  , tokenEstimate :: Int
  }

type PromptVariable =
  { name :: String
  , description :: String
  , defaultValue :: Maybe String
  , required :: Boolean
  }

data PromptCategory
  = Coding
  | Review
  | Documentation
  | Lean4
  | General
  | Custom

renderPrompt :: SystemPrompt -> PromptContext -> String
renderPrompt prompt context =
  foldl replaceVariable prompt.template prompt.variables
  where
    replaceVariable template var =
      replace (Pattern ("{{" <> var.name <> "}}")) 
              (Replacement (fromMaybe "" (lookup var.name context)))
              template
```

---

## CSS Styling

```css
.prompt-list {
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.prompt-item {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-3);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  cursor: pointer;
  transition: all var(--transition-fast);
}

.prompt-item:hover {
  border-color: var(--color-primary-dim);
}

.prompt-item--active {
  border-color: var(--color-primary);
  background: var(--color-primary-dim);
}

.prompt-editor {
  display: flex;
  flex-direction: column;
  gap: var(--space-4);
}

.prompt-template {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  min-height: 200px;
  padding: var(--space-3);
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-default);
  border-radius: 8px;
  resize: vertical;
}

.prompt-variable {
  background: var(--color-primary-dim);
  padding: 2px 4px;
  border-radius: 4px;
  font-weight: var(--font-weight-medium);
}
```

---

## Related Specifications

- `55-SETTINGS-PANEL.md` - Settings UI
- `27-CONTEXT-WINDOW-MANAGEMENT.md` - Token budget
- `62-TACTIC-SUGGESTIONS.md` - Lean4 prompts

---

*"The right prompt unlocks the right response."*
