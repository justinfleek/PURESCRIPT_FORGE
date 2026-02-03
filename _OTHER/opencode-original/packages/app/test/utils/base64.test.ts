import { describe, it, expect } from 'vitest';
import { decode64 } from '@/utils/base64';

describe('base64 utilities', () => {
  it('decodes valid base64', () => {
    const encoded = btoa('hello world');
    expect(decode64(encoded)).toBe('hello world');
  });

  it('returns undefined for invalid base64', () => {
    expect(decode64('!!!invalid!!!')).toBeUndefined();
  });

  it('handles undefined input', () => {
    expect(decode64(undefined)).toBeUndefined();
  });

  it('decodes realistic directory paths', () => {
    const paths = ['/home/user/project', '/Users/john/code', 'C:\\Users\\john\\code'];
    for (const path of paths) {
      const encoded = btoa(path);
      expect(decode64(encoded)).toBe(path);
    }
  });
});
