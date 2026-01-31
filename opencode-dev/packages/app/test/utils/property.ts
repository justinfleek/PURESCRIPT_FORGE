import * as fc from 'fast-check';
import type { Arbitrary } from 'fast-check';

/**
 * Property test utilities for UI components
 */

/**
 * Generate valid CSS class names
 */
export const cssClassName = (): Arbitrary<string> =>
  fc.string({ minLength: 1, maxLength: 50 }).filter(s => /^[a-zA-Z][a-zA-Z0-9_-]*$/.test(s));

/**
 * Generate valid file paths
 */
export const filePath = (): Arbitrary<string> =>
  fc.string({ minLength: 1, maxLength: 200 })
    .filter(s => s.length > 0 && !s.includes('\0'))
    .map(s => s.replace(/\/+/g, '/'));

/**
 * Generate valid file names
 */
export const fileName = (): Arbitrary<string> =>
  fc.string({ minLength: 1, maxLength: 100 })
    .filter(s => !s.includes('/') && !s.includes('\0') && s.trim().length > 0);

/**
 * Generate valid voice names
 */
export const voiceName = (): Arbitrary<string> =>
  fc.constantFrom('Ryan', 'Alice', 'Bob', 'Charlie', 'Diana', 'Eve', 'Frank', 'Grace');

/**
 * Generate audio levels (0-1)
 */
export const audioLevel = (): Arbitrary<number> =>
  fc.float({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });

/**
 * Generate transcript messages
 */
export const transcriptMessage = (): Arbitrary<{
  id: string;
  role: 'user' | 'assistant';
  text: string;
  timestamp: Date;
  audioUrl: string | null;
}> =>
  fc.record({
    id: fc.uuid(),
    role: fc.constantFrom<'user' | 'assistant'>('user', 'assistant'),
    text: fc.string({ minLength: 0, maxLength: 1000 }),
    timestamp: fc.date({ min: new Date(2020, 0, 1), max: new Date() }),
    audioUrl: fc.oneof(fc.constant(null), fc.webUrl()),
  });

/**
 * Generate arrays of transcript messages
 */
export const transcriptMessages = (): Arbitrary<Array<{
  id: string;
  role: 'user' | 'assistant';
  text: string;
  timestamp: Date;
  audioUrl: string | null;
}>> =>
  fc.array(transcriptMessage(), { minLength: 0, maxLength: 50 });

/**
 * Generate file tree nodes
 */
export const fileNode = (): Arbitrary<{
  path: string;
  type: 'file' | 'directory';
  name: string;
}> =>
  fc.record({
    path: filePath(),
    type: fc.constantFrom<'file' | 'directory'>('file', 'directory'),
    name: fileName(),
  });

/**
 * Property test runner with better error messages
 */
export async function propertyTest<T>(
  name: string,
  arbitrary: Arbitrary<T>,
  predicate: (value: T) => boolean | Promise<boolean>,
  options: { numRuns?: number; seed?: number } = {}
): Promise<void> {
  const { numRuns = 100, seed } = options;

  await fc.assert(
    fc.asyncProperty(arbitrary, async (value) => {
      const result = await predicate(value);
      if (!result) {
        throw new Error(`Property failed for value: ${JSON.stringify(value, null, 2)}`);
      }
      return result;
    }),
    {
      numRuns,
      seed,
      verbose: true,
    }
  );
}
