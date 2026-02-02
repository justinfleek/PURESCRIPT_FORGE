#!/usr/bin/env python3
"""
Run All Tests - Comprehensive Test Runner

Runs all test suites:
- Unit tests
- Property-based tests
- Integration tests
- E2E tests
- Performance tests
- Memory tests
"""

import subprocess
import sys
from pathlib import Path

# Add parent to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def run_tests():
    """Run all test suites."""
    test_suites = [
        ("Unit Tests", ["tests/unit"]),
        ("Property Tests", ["tests/property"]),
        ("Integration Tests", ["tests/integration"]),
        ("E2E Tests", ["tests/e2e"]),
        ("Performance Tests", ["tests/performance", "-m", "performance"]),
        ("Memory Tests", ["tests/memory", "-m", "memory"]),
    ]
    
    results = {}
    
    for suite_name, test_paths in test_suites:
        print(f"\n{'=' * 70}")
        print(f"Running: {suite_name}")
        print('=' * 70)
        
        cmd = ["pytest", "-v"] + test_paths
        
        try:
            result = subprocess.run(
                cmd,
                cwd=Path(__file__).parent.parent,
                capture_output=True,
                text=True,
            )
            
            results[suite_name] = {
                "passed": result.returncode == 0,
                "output": result.stdout + result.stderr,
            }
            
            if result.returncode == 0:
                print(f"✅ {suite_name} PASSED")
            else:
                print(f"❌ {suite_name} FAILED")
                print(result.stdout)
                print(result.stderr)
        
        except Exception as e:
            print(f"❌ {suite_name} ERROR: {e}")
            results[suite_name] = {
                "passed": False,
                "output": str(e),
            }
    
    # Summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    
    all_passed = True
    for suite_name, result in results.items():
        status = "✅ PASSED" if result["passed"] else "❌ FAILED"
        print(f"{suite_name}: {status}")
        if not result["passed"]:
            all_passed = False
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(run_tests())
