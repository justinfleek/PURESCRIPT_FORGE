import * as fc from 'fast-check';

/**
 * Realistic data generators based on actual usage patterns
 * Not random - samples from probable distributions
 */

/**
 * Real file paths (common patterns)
 */
export const realisticFilePath = (): fc.Arbitrary<string> =>
  fc.oneof(
    // Common file types
    fc.constantFrom(
      'src/index.ts',
      'src/components/Button.tsx',
      'src/utils/helpers.ts',
      'package.json',
      'tsconfig.json',
      'README.md',
      'src/context/store.tsx',
      'src/hooks/useState.ts',
      'test/utils.ts',
      '.gitignore',
    ),
    fc.tuple(
      fc.constantFrom('src', 'lib', 'packages', 'test'),
      fc.constantFrom('components', 'utils', 'hooks', 'context'),
      fc.constantFrom('index.ts', 'utils.ts', 'types.ts', 'test.ts'),
    ).map(([dir, subdir, file]) => `${dir}/${subdir}/${file}`),
    // Long paths
    fc.array(fc.constantFrom('src', 'components', 'ui'), { minLength: 3, maxLength: 8 })
      .map(parts => parts.join('/') + '/file.ts'),
  );

/**
 * Real prompt text (common patterns)
 */
export const realisticPromptText = (): fc.Arbitrary<string> =>
  fc.oneof(
    // Short commands
    fc.constantFrom(
      'Fix the bug',
      'Add tests',
      'Refactor this',
      'Update docs',
    ),
    fc.tuple(
      fc.constantFrom('Create', 'Fix', 'Update', 'Refactor', 'Add'),
      fc.constantFrom('component', 'function', 'hook', 'test', 'utility'),
      fc.string({ minLength: 10, maxLength: 50 }),
    ).map(([action, thing, desc]) => `${action} a ${thing} that ${desc}`),
    // Long prompts
    fc.string({ minLength: 50, maxLength: 500 })
      .filter(s => s.trim().length > 0),
  );

/**
 * Real voice names (actual TTS voices)
 */
export const realisticVoiceName = (): fc.Arbitrary<string> =>
  fc.constantFrom(
    'Ryan', 'Alice', 'Bob', 'Charlie', 'Diana', 'Eve',
    'Frank', 'Grace', 'Henry', 'Ivy', 'Jack', 'Kate',
  );

export const realisticTranscriptMessage = (): fc.Arbitrary<{
  id: string;
  role: 'user' | 'assistant';
  text: string;
  timestamp: Date;
  audioUrl: string | null;
}> =>
  fc.record({
    id: fc.uuid(),
    role: fc.constantFrom<'user' | 'assistant'>('user', 'assistant'),
    text: realisticPromptText(),
    timestamp: fc.date({ min: new Date(2024, 0, 1), max: new Date() }),
    audioUrl: fc.oneof(
      fc.constant(null),
      fc.constant('https://example.com/audio.mp3'),
    ),
  });

/**
 * Real file selections (common line ranges)
 */
export const realisticFileSelection = (): fc.Arbitrary<{
  startLine: number;
  startChar: number;
  endLine: number;
  endChar: number;
}> =>
  fc.record({
    startLine: fc.integer({ min: 1, max: 1000 }),
    startChar: fc.integer({ min: 0, max: 100 }),
    endLine: fc.integer({ min: 1, max: 1000 }),
    endChar: fc.integer({ min: 0, max: 100 }),
  }).filter(sel => sel.startLine <= sel.endLine);

export const realisticPromptPart = (): fc.Arbitrary<
  | { type: 'text'; content: string; start: number; end: number }
  | { type: 'file'; path: string; content: string; start: number; end: number; selection?: any }
  | { type: 'agent'; name: string; content: string; start: number; end: number }
> =>
  fc.oneof(
    // Text parts (most common)
    fc.record({
      type: fc.constant<'text'>('text'),
      content: realisticPromptText(),
      start: fc.integer({ min: 0, max: 1000 }),
      end: fc.integer({ min: 0, max: 1000 }),
    }).filter(p => p.end >= p.start),
    fc.record({
      type: fc.constant<'file'>('file'),
      path: realisticFilePath(),
      content: fc.string({ minLength: 1, maxLength: 50 }),
      start: fc.integer({ min: 0, max: 1000 }),
      end: fc.integer({ min: 0, max: 1000 }),
      selection: fc.option(realisticFileSelection()),
    }).filter(p => p.end >= p.start),
    // Agent parts (less common)
    fc.record({
      type: fc.constant<'agent'>('agent'),
      name: fc.constantFrom('agent1', 'agent2', 'helper'),
      content: fc.string({ minLength: 1, maxLength: 30 }),
      start: fc.integer({ min: 0, max: 1000 }),
      end: fc.integer({ min: 0, max: 1000 }),
    }).filter(p => p.end >= p.start),
  );

export const realisticPrompt = (): fc.Arbitrary<Array<any>> =>
  fc.array(realisticPromptPart(), { minLength: 1, maxLength: 10 })
    .map(parts => {
      let position = 0;
      return parts.map(part => {
        const length = 'content' in part ? part.content.length : 10;
        const fixed = { ...part, start: position, end: position + length };
        position += length;
        return fixed;
      });
    });
