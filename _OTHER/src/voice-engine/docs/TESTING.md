# Testing Guide

Comprehensive testing guide for the voice engine.

## Table of Contents

1. [Test Structure](#test-structure)
2. [Running Tests](#running-tests)
3. [Test Types](#test-types)
4. [Reproducible Distributions](#reproducible-distributions)
5. [Writing Tests](#writing-tests)
6. [Performance Testing](#performance-testing)
7. [Memory Testing](#memory-testing)

## Test Structure

```
tests/
├── conftest.py              # Pytest configuration and fixtures
├── pytest.ini              # Pytest settings
├── run_all_tests.py        # Test runner script
├── unit/                    # Unit tests
│   ├── test_routing.py
│   └── test_voice_engine.py
├── property/                # Property-based tests
│   └── test_distributions.py
├── integration/             # Integration tests
│   └── test_voice_chat.py
├── e2e/                     # End-to-end tests
│   └── test_full_flow.py
├── performance/             # Performance benchmarks
│   └── test_benchmarks.py
├── memory/                  # Memory profiling
│   └── test_profiling.py
└── fixtures/                # Test data generators
    └── test_data.py
```

## Running Tests

### Run All Tests

```bash
# From voice-engine directory
pytest tests/ -v

# Or use the test runner
python tests/run_all_tests.py
```

### Run Specific Test Suite

```bash
# Unit tests only
pytest tests/unit/ -v

# Property tests only
pytest tests/property/ -v

# Integration tests only
pytest tests/integration/ -v

# E2E tests only
pytest tests/e2e/ -v

# Performance tests only
pytest tests/performance/ -m performance -v

# Memory tests only
pytest tests/memory/ -m memory -v
```

### Run Specific Test

```bash
pytest tests/unit/test_routing.py::TestRouting::test_route_email_query -v
```

### Run with Coverage

```bash
pytest tests/ --cov=toolbox --cov-report=html --cov-report=term-missing
```

## Test Types

### Unit Tests

**Purpose**: Test individual components in isolation.

**Location**: `tests/unit/`

**Examples**:
- Routing logic
- Voice engine operations
- Cache operations
- Validation functions

**Characteristics**:
- Fast (< 1ms per test)
- No external dependencies
- Deterministic
- Isolated

### Property-Based Tests

**Purpose**: Test properties that should hold for all inputs.

**Location**: `tests/property/`

**Examples**:
- Routing is idempotent
- Routing is deterministic
- TTS respects bounds
- Functions are total

**Characteristics**:
- Use reproducible distributions
- Test invariants
- Cover edge cases
- Verify mathematical properties

### Integration Tests

**Purpose**: Test component interactions.

**Location**: `tests/integration/`

**Examples**:
- Voice chat engine flow
- Database operations
- Cache integration
- Provider integration

**Characteristics**:
- Test real interactions
- Use test database
- Mock external APIs
- Verify end-to-end flow

### E2E Tests

**Purpose**: Test complete system flow.

**Location**: `tests/e2e/`

**Examples**:
- Full voice chat flow
- Session management
- Error handling
- Conversation context

**Characteristics**:
- Test complete user journey
- Use real components (where possible)
- Verify all steps complete
- Check error paths

### Performance Tests

**Purpose**: Benchmark performance characteristics.

**Location**: `tests/performance/`

**Examples**:
- Latency measurements
- Throughput tests
- Cache performance
- Memory usage

**Characteristics**:
- Measure metrics (p50, p95, p99)
- Compare against thresholds
- Report performance stats
- Identify bottlenecks

### Memory Tests

**Purpose**: Profile memory usage and detect leaks.

**Location**: `tests/memory/`

**Examples**:
- Memory usage per operation
- Cache memory footprint
- Leak detection
- Peak memory tracking

**Characteristics**:
- Use tracemalloc
- Track memory over iterations
- Detect unbounded growth
- Report memory stats

## Reproducible Distributions

All property-based tests use reproducible random distributions to ensure deterministic behavior.

### ReproducibleDistribution

```python
from tests.fixtures.test_data import ReproducibleDistribution

dist = ReproducibleDistribution(seed=42)

# Generate reproducible random values
text = dist.generate_text(min_words=5, max_words=20)
audio = dist.generate_audio_bytes(size_bytes=1024)
```

### Using in Tests

```python
@pytest.fixture
def dist(reproducible_seed: int) -> ReproducibleDistribution:
    return ReproducibleDistribution(seed=reproducible_seed)

def test_routing_deterministic(dist: ReproducibleDistribution):
    query = dist.generate_text()
    result1 = route_query(query)
    result2 = route_query(query)
    assert result1.analyst.role == result2.analyst.role
```

## Writing Tests

### Unit Test Example

```python
import pytest
from toolbox.llm.routing import route_query

def test_route_email_query():
    """Test routing email-related query."""
    result = route_query("How do I improve email open rates?")
    
    assert isinstance(result, RoutingResult)
    assert result.analyst.role == AnalystRole.EMAIL_SPECIALIST
    assert result.confidence > 0.0
    assert result.confidence <= 1.0
```

### Property Test Example

```python
@pytest.mark.parametrize("query", [
    "email marketing strategy",
    "SEO optimization",
    "content planning",
])
def test_routing_idempotent(query: str):
    """Test that routing is idempotent."""
    result1 = route_query(query)
    result2 = route_query(query)
    
    assert result1.analyst.role == result2.analyst.role
    assert result1.confidence == result2.confidence
```

### Integration Test Example

```python
@pytest.mark.asyncio
async def test_voice_chat_flow(voice_engine, test_db):
    """Test voice chat flow."""
    result = await voice_chat.process_message(
        conversation_id="test",
        user_id="test_user",
        audio_data=sample_audio_bytes,
        audio_format="wav",
    )
    
    assert result is not None
    assert "user_transcript" in result
    assert "assistant_text" in result
```

### Performance Test Example

```python
@pytest.mark.asyncio
async def test_tts_latency(voice_engine):
    """Benchmark TTS synthesis latency."""
    benchmark = PerformanceBenchmark()
    
    async def synthesize():
        return await voice_engine.text_to_speech(
            text="Hello, performance test",
            voice="test_voice",
        )
    
    stats = benchmark.measure_latency(synthesize)
    
    assert stats["p95"] < 1000.0  # p95 < 1 second
    print(f"Mean latency: {stats['mean']:.2f}ms")
```

## Performance Testing

### Latency Benchmarks

Expected latencies:
- **Routing**: < 10ms (mean)
- **TTS (cached)**: < 5ms (mean)
- **TTS (uncached)**: < 500ms (mean)
- **STT (mock)**: < 10ms (mean)
- **Chat (cached)**: < 5ms (mean)

### Running Performance Tests

```bash
# Run performance tests
pytest tests/performance/ -m performance -v -s

# Output includes:
# - Mean latency
# - P50, P95, P99 percentiles
# - Standard deviation
# - Min/max values
```

## Memory Testing

### Memory Profiling

```python
import tracemalloc

tracemalloc.start()
# ... run code ...
current, peak = tracemalloc.get_traced_memory()
tracemalloc.stop()

print(f"Peak memory: {peak / 1024 / 1024:.2f} MB")
```

### Leak Detection

```python
def test_memory_leak(voice_engine):
    """Test for memory leaks."""
    profiler = MemoryProfiler()
    
    memory = profiler.check_leak(
        lambda: voice_engine.text_to_speech("test"),
        iterations=1000,
    )
    
    bytes_per_iteration = memory["peak_bytes"] / memory["iterations"]
    assert bytes_per_iteration < 1024 * 1024  # < 1MB per iteration
```

## Test Fixtures

### Common Fixtures

- `test_db`: Temporary SQLite database
- `voice_engine`: Voice engine with test providers
- `mock_tts_provider`: Mock TTS provider
- `mock_stt_provider`: Mock STT provider
- `sample_audio_bytes`: Sample audio data
- `reproducible_seed`: Fixed random seed (42)

### Using Fixtures

```python
@pytest.mark.asyncio
async def test_with_fixtures(voice_engine, test_db, sample_audio_bytes):
    """Test using fixtures."""
    result = await voice_engine.speech_to_text(
        audio_data=sample_audio_bytes,
        audio_format="wav",
    )
    assert result is not None
```

## Continuous Integration

### GitHub Actions Example

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions/setup-python@v2
        with:
          python-version: '3.10'
      - run: pip install -r requirements.txt
      - run: pip install pytest pytest-asyncio pytest-cov
      - run: pytest tests/ -v --cov=toolbox --cov-report=xml
      - run: pytest tests/performance/ -m performance
```

## Best Practices

1. **Deterministic**: All tests should be deterministic (use fixed seeds)
2. **Fast**: Unit tests should run in < 1ms
3. **Isolated**: Tests should not depend on each other
4. **Clear**: Test names should describe what they test
5. **Complete**: Test both success and error paths
6. **Maintainable**: Keep tests simple and focused

## Troubleshooting

### Tests Failing Intermittently

- Check for race conditions
- Verify test isolation
- Check for shared state
- Use fixed seeds for randomness

### Slow Tests

- Profile tests to find bottlenecks
- Mock external dependencies
- Use test database instead of real
- Cache expensive operations

### Memory Issues

- Check for memory leaks
- Verify cache cleanup
- Monitor memory usage
- Use tracemalloc for profiling
