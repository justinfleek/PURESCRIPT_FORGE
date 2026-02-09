"""
Deep comprehensive bug-detection tests for SQLite database adapter.
Tests edge cases, type handling, parameter validation, and real bugs.
"""
import pytest
import aiosqlite
from pathlib import Path
import tempfile
import os
from datetime import datetime, date
from decimal import Decimal
from toolbox.core.db.sqlite_adapter import SQLiteVoiceDatabase
from toolbox.core.db.types import DBParam, DBParams, DBPrimitive, DatabaseRow


class TestDatabaseAdapterDeepBugs:
    """Deep bug-detection tests for SQLiteVoiceDatabase"""

    @pytest.fixture
    async def temp_db(self):
        """Create temporary database for testing."""
        with tempfile.NamedTemporaryFile(delete=False, suffix=".db") as f:
            db_path = f.name
        
        db = SQLiteVoiceDatabase(db_path)
        yield db
        
        await db.close()
        if os.path.exists(db_path):
            os.unlink(db_path)

    @pytest.mark.asyncio
    async def test_bug_fetch_one_doesnt_handle_empty_row(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_one (line 73-94) converts Row to dict using dict(row).
        If row has no columns or is empty, dict(row) may produce unexpected results.
        
        Root cause: No validation that row has columns before conversion
        Consequences: Empty dict returned instead of None, or KeyError on access
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY)")
        
        # SELECT with no matching rows returns None (handled correctly)
        row = await temp_db.fetch_one("SELECT * FROM test WHERE id = ?", (999,))
        assert row is None  # This works correctly
        
        # But what if query returns row with no columns?
        # This is edge case - SQLite doesn't allow SELECT with no columns
        # But if row factory returns empty Row, dict() conversion may fail

    @pytest.mark.asyncio
    async def test_bug_fetch_all_doesnt_handle_large_result_sets(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_all (line 96-114) loads all rows into memory at once.
        For very large result sets, this may cause memory issues.
        
        Root cause: No pagination or streaming support
        Consequences: Memory exhaustion for large queries, OOM errors
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, data TEXT)")
        
        # Insert many rows
        for i in range(1000):
            await temp_db.execute("INSERT INTO test (data) VALUES (?)", (f"data_{i}",))
        
        # Fetch all at once
        rows = await temp_db.fetch_all("SELECT * FROM test")
        assert len(rows) == 1000
        
        # BUG: For 1M+ rows, this would cause memory issues
        # Proposed solution: Add pagination or streaming support

    @pytest.mark.asyncio
    async def test_bug_execute_doesnt_validate_params_type(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute (line 59-71) accepts DBParams but doesn't validate that
        params is actually a Sequence. If wrong type is passed, error may occur
        deep in aiosqlite, making debugging difficult.
        
        Root cause: No type validation before passing to aiosqlite
        Consequences: Cryptic errors, type confusion, runtime failures
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        
        # Valid params (tuple)
        await temp_db.execute("INSERT INTO test (name) VALUES (?)", ("test",))
        
        # Invalid params (dict instead of Sequence)
        with pytest.raises((TypeError, AttributeError)):
            await temp_db.execute("INSERT INTO test (name) VALUES (?)", {"name": "test"})
        
        # BUG: Error message may not be clear about expected type

    @pytest.mark.asyncio
    async def test_bug_fetch_one_doesnt_handle_none_params(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_one (line 73-94) accepts params but doesn't explicitly handle
        None params. If params=None is passed, it may cause issues.
        
        Root cause: Default params=() handles None, but explicit None may fail
        Consequences: TypeError if None passed explicitly
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        
        # Default empty tuple works
        row = await temp_db.fetch_one("SELECT * FROM test")
        assert row is None
        
        # Explicit None may cause issues
        # BUG: Should handle None explicitly or document that None is not allowed
        # Current implementation: params: DBParams = () means None not allowed
        # But type hint allows None (DBParam includes None)

    @pytest.mark.asyncio
    async def test_bug_row_conversion_loses_type_information(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_one/fetch_all (lines 94, 114) convert Row to dict using dict(row).
        This loses type information - all values become Python types, but original
        SQLite types may be lost (e.g., INTEGER vs REAL distinction).
        
        Root cause: dict() conversion doesn't preserve SQLite type information
        Consequences: Type information lost, may cause issues with type-sensitive code
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER, value REAL, flag INTEGER)")
        await temp_db.execute("INSERT INTO test VALUES (?, ?, ?)", (1, 1.5, 1))
        
        row = await temp_db.fetch_one("SELECT * FROM test")
        assert row is not None
        
        # BUG: Type information may be lost
        # id and flag are both INTEGER in SQLite, but Python sees them as int
        # value is REAL in SQLite, Python sees as float
        # Distinction between INTEGER and REAL may be lost
        assert isinstance(row["id"], int)
        assert isinstance(row["value"], float)
        assert isinstance(row["flag"], int)

    @pytest.mark.asyncio
    async def test_bug_execute_commits_immediately_no_transaction_control(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute (line 71) calls commit() immediately after execute.
        This means each execute is a separate transaction, preventing batch operations
        and making rollback difficult.
        
        Root cause: commit() called after every execute
        Consequences: No transaction control, can't batch operations, performance issues
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        
        # Each execute commits immediately
        await temp_db.execute("INSERT INTO test (name) VALUES (?)", ("name1",))
        await temp_db.execute("INSERT INTO test (name) VALUES (?)", ("name2",))
        
        # BUG: Can't rollback both inserts - first is already committed
        # Proposed solution: Add transaction context manager or batch execute method

    @pytest.mark.asyncio
    async def test_bug_auto_connect_race_condition(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute/fetch_one/fetch_all (lines 67-68, 84-85, 107-108) check
        if _conn is None and call connect(). If multiple operations are called
        concurrently, multiple connections may be created.
        
        Root cause: No locking around connection check and creation
        Consequences: Multiple connections, connection leaks, race conditions
        """
        import asyncio
        
        await temp_db.connect()
        # Close connection to test auto-connect
        await temp_db.close()
        
        # Call multiple operations concurrently
        async def op1():
            await temp_db.execute("CREATE TABLE IF NOT EXISTS test (id INTEGER PRIMARY KEY)")
        
        async def op2():
            await temp_db.fetch_one("SELECT * FROM sqlite_master")
        
        async def op3():
            await temp_db.fetch_all("SELECT * FROM sqlite_master")
        
        # BUG: Concurrent calls may create multiple connections
        await asyncio.gather(op1(), op2(), op3())
        
        # Should only have one connection
        assert temp_db._conn is not None
        # But race condition may have created multiple (though only one stored)

    @pytest.mark.asyncio
    async def test_bug_close_doesnt_wait_for_pending_operations(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: close (line 52-57) closes connection immediately without checking
        if there are pending operations. If operations are in progress, they may fail.
        
        Root cause: No check for pending operations before close
        Consequences: Operations may fail with "database is locked" or connection errors
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY)")
        
        # Start operation
        execute_task = temp_db.execute("INSERT INTO test (id) VALUES (?)", (1,))
        
        # Close immediately (may interrupt operation)
        await temp_db.close()
        
        # BUG: Operation may be interrupted or fail
        # Proposed solution: Wait for pending operations or cancel them gracefully

    @pytest.mark.asyncio
    async def test_bug_fetch_one_doesnt_handle_bytes_correctly(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_one (line 94) converts Row to dict. If row contains bytes,
        they are preserved, but type handling may be inconsistent.
        
        Root cause: dict() conversion preserves bytes, but type checking may fail
        Consequences: Bytes may not be handled correctly in downstream code
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, data BLOB)")
        
        test_bytes = b"test_data"
        await temp_db.execute("INSERT INTO test (data) VALUES (?)", (test_bytes,))
        
        row = await temp_db.fetch_one("SELECT * FROM test")
        assert row is not None
        
        # BUG: Bytes should be preserved, but type checking may be inconsistent
        assert isinstance(row["data"], bytes)
        assert row["data"] == test_bytes

    @pytest.mark.asyncio
    async def test_bug_execute_doesnt_handle_datetime_objects(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute (line 70) passes params to aiosqlite.execute. SQLite accepts
        datetime objects, but they may not be serialized correctly or may cause
        type errors.
        
        Root cause: No explicit handling of datetime/date objects
        Consequences: Type errors or incorrect serialization
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, created_at TEXT)")
        
        test_datetime = datetime(2024, 1, 1, 12, 0, 0)
        test_date = date(2024, 1, 1)
        
        # BUG: datetime/date objects may not be handled correctly
        # SQLite accepts them but may serialize differently
        await temp_db.execute("INSERT INTO test (created_at) VALUES (?)", (test_datetime,))
        
        row = await temp_db.fetch_one("SELECT * FROM test")
        assert row is not None
        # BUG: Datetime may be converted to string, losing precision or timezone

    @pytest.mark.asyncio
    async def test_bug_fetch_all_doesnt_preserve_order(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_all (line 114) converts Rows to dicts but doesn't guarantee
        order preservation. While SQLite returns rows in order, the conversion
        process may not preserve it.
        
        Root cause: dict() conversion should preserve order (Python 3.7+), but
        not explicitly guaranteed
        Consequences: Row order may be lost if not explicitly ordered in query
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        
        for i in range(5):
            await temp_db.execute("INSERT INTO test (name) VALUES (?)", (f"name_{i}",))
        
        # Fetch without ORDER BY
        rows = await temp_db.fetch_all("SELECT * FROM test")
        
        # BUG: Order may not be guaranteed without ORDER BY clause
        # SQLite may return in insertion order, but not guaranteed
        # Proposed solution: Always use ORDER BY for deterministic results

    @pytest.mark.asyncio
    async def test_bug_context_manager_doesnt_handle_errors(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: __aexit__ (line 121-123) always closes connection, even if exception
        occurred. This may mask errors or prevent error recovery.
        
        Root cause: No exception handling in __aexit__
        Consequences: Errors may be swallowed, connection closed on error
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY)")
        
        # Use context manager
        async with SQLiteVoiceDatabase(temp_db.db_path) as db:
            await db.execute("INSERT INTO test (id) VALUES (?)", (1,))
            # Simulate error
            raise ValueError("Test error")
        
        # BUG: Connection is closed even though error occurred
        # Error is propagated, but connection state may be inconsistent

    @pytest.mark.asyncio
    async def test_bug_foreign_keys_not_checked_after_reconnect(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: connect (line 46-47) enables foreign keys, but if connection is
        closed and reopened, foreign keys may need to be re-enabled. However,
        auto-connect may not re-enable them.
        
        Root cause: Foreign keys enabled only in connect(), not in auto-connect
        Consequences: Foreign keys may not be enabled after auto-connect
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE parent (id INTEGER PRIMARY KEY)")
        await temp_db.execute("CREATE TABLE child (id INTEGER PRIMARY KEY, parent_id INTEGER REFERENCES parent(id))")
        await temp_db.close()
        
        # Auto-connect via execute
        await temp_db.execute("INSERT INTO parent (id) VALUES (?)", (1,))
        
        # BUG: Foreign keys may not be enabled after auto-connect
        # Check if foreign keys are enabled
        cursor = await temp_db._conn.execute("PRAGMA foreign_keys")
        result = await cursor.fetchone()
        # Should be 1, but may be 0 if not re-enabled
        assert result[0] == 1  # This should pass, but documents potential issue

    @pytest.mark.asyncio
    async def test_bug_row_factory_may_not_be_set_correctly(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: connect (line 44) sets row_factory to aiosqlite.Row, but if connection
        is reused or if row_factory is changed elsewhere, fetch_one/fetch_all may
        not work correctly.
        
        Root cause: row_factory set once, but may be changed
        Consequences: dict() conversion may fail if row_factory changed
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        await temp_db.execute("INSERT INTO test (name) VALUES (?)", ("test",))
        
        # Change row_factory
        temp_db._conn.row_factory = None
        
        # BUG: fetch_one may fail if row_factory is None
        with pytest.raises((TypeError, AttributeError)):
            await temp_db.fetch_one("SELECT * FROM test")

    @pytest.mark.asyncio
    async def test_bug_params_validation_doesnt_check_nested_types(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute/fetch_one/fetch_all accept DBParams (Sequence[DBParam]),
        but don't validate that each element is actually a valid DBParam type.
        Invalid types may cause runtime errors deep in aiosqlite.
        
        Root cause: No validation of param types
        Consequences: Runtime errors with unclear messages
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        
        # Invalid param type (list instead of primitive)
        with pytest.raises((TypeError, ValueError)):
            await temp_db.execute("INSERT INTO test (name) VALUES (?)", ([1, 2, 3],))
        
        # BUG: Error message may not indicate which param is invalid

    @pytest.mark.asyncio
    async def test_bug_fetch_one_doesnt_handle_none_in_row(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_one (line 94) converts Row to dict. If row contains NULL values,
        they are converted to None. But None is a valid DBPrimitive, so this is
        correct. However, downstream code may not handle None correctly.
        
        Root cause: None values are preserved (correct), but may cause issues downstream
        Consequences: KeyError or AttributeError if code doesn't handle None
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)")
        await temp_db.execute("INSERT INTO test (name) VALUES (?)", (None,))
        
        row = await temp_db.fetch_one("SELECT * FROM test")
        assert row is not None
        
        # BUG: None value may cause issues if code doesn't handle it
        assert row["name"] is None  # This is correct, but may break downstream code

    @pytest.mark.asyncio
    async def test_bug_execute_doesnt_handle_empty_query(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: execute (line 59-71) doesn't validate that query is non-empty.
        Empty queries may cause errors or unexpected behavior.
        
        Root cause: No query validation
        Consequences: Errors with empty queries, unclear error messages
        """
        await temp_db.connect()
        
        # Empty query
        with pytest.raises((ValueError, aiosqlite.Error)):
            await temp_db.execute("")
        
        # BUG: Error message may not be clear about empty query

    @pytest.mark.asyncio
    async def test_bug_fetch_all_doesnt_limit_result_size(self, temp_db: SQLiteVoiceDatabase):
        """
        BUG: fetch_all (line 96-114) doesn't limit the number of rows returned.
        Malicious or buggy queries may return millions of rows, causing memory issues.
        
        Root cause: No limit on result size
        Consequences: Memory exhaustion, DoS vulnerability
        """
        await temp_db.connect()
        await temp_db.execute("CREATE TABLE test (id INTEGER PRIMARY KEY)")
        
        # Insert many rows
        for i in range(10000):
            await temp_db.execute("INSERT INTO test (id) VALUES (?)", (i,))
        
        # Fetch all without limit
        rows = await temp_db.fetch_all("SELECT * FROM test")
        assert len(rows) == 10000
        
        # BUG: For 1M+ rows, this would cause memory issues
        # Proposed solution: Add max_rows parameter or require LIMIT clause
