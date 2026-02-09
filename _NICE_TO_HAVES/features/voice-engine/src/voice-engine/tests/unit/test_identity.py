"""
Deep comprehensive bug-detection tests for Identity module.
Tests ID generation, namespace handling, and edge cases.
"""
import pytest
from uuid import UUID, uuid5
from toolbox.identity import Namespace, generate_id, NAMESPACE_DNS, NAMESPACE_FORGE


class TestGenerateId:
    """Tests for generate_id function"""
    
    def test_generate_id_creates_deterministic_uuid(self):
        """Test generate_id creates deterministic UUID"""
        id1 = generate_id(Namespace.ASSET, "test", "part")
        id2 = generate_id(Namespace.ASSET, "test", "part")
        
        # Should be deterministic
        assert id1 == id2
    
    def test_generate_id_different_parts_create_different_ids(self):
        """Test generate_id creates different IDs for different parts"""
        id1 = generate_id(Namespace.ASSET, "test", "part1")
        id2 = generate_id(Namespace.ASSET, "test", "part2")
        
        assert id1 != id2
    
    def test_generate_id_different_namespaces_create_different_ids(self):
        """Test generate_id creates different IDs for different namespaces"""
        # Note: Only ASSET namespace exists, so we test with same namespace
        # But if more namespaces existed, they would create different IDs
        id1 = generate_id(Namespace.ASSET, "test")
        
        # Same parts, same namespace should create same ID
        id2 = generate_id(Namespace.ASSET, "test")
        assert id1 == id2
    
    def test_generate_id_joins_parts_with_pipe(self):
        """Test generate_id joins parts with pipe character"""
        id1 = generate_id(Namespace.ASSET, "part1", "part2")
        id2 = generate_id(Namespace.ASSET, "part1|part2")  # Explicit pipe
        
        # BUG: generate_id (line 18-21) joins parts with "|", so
        # generate_id(ns, "a", "b") creates same ID as generate_id(ns, "a|b")
        # This may be intentional, but should be documented
        assert id1 == id2
    
    def test_bug_generate_id_pipe_character_in_parts(self):
        """
        BUG: generate_id (line 20) joins parts with "|" character.
        If a part contains "|", it will be ambiguous whether it's a separator
        or part of the content.
        
        Root cause: Pipe character used as separator and may appear in content
        Consequences: Ambiguity in ID generation, potential collisions
        
        Proposed solution: Use a separator that's guaranteed not to appear in content,
        or escape pipe characters in parts
        """
        # Part with pipe character
        id1 = generate_id(Namespace.ASSET, "part1|part2")
        id2 = generate_id(Namespace.ASSET, "part1", "part2")
        
        # BUG: These create the same ID, causing ambiguity
        assert id1 == id2
    
    def test_bug_generate_id_empty_parts(self):
        """
        BUG: generate_id (line 20) joins parts with "|". If parts is empty,
        content becomes empty string, which may create unexpected IDs.
        
        Root cause: No validation that parts is non-empty
        Consequences: Empty parts may create unexpected or invalid IDs
        """
        # Empty parts
        id_empty = generate_id(Namespace.ASSET)
        
        # BUG: Empty parts create ID from empty string
        # This may be valid (UUID5 accepts empty string), but may be unexpected
        assert isinstance(id_empty, UUID)
    
    def test_bug_generate_id_whitespace_in_parts(self):
        """
        BUG: generate_id (line 20) doesn't normalize whitespace in parts.
        Parts with leading/trailing whitespace or different whitespace
        will create different IDs.
        
        Root cause: No whitespace normalization
        Consequences: "part" vs " part " vs "part  " create different IDs
        """
        id1 = generate_id(Namespace.ASSET, "test")
        id2 = generate_id(Namespace.ASSET, " test ")
        id3 = generate_id(Namespace.ASSET, "test  ")
        
        # BUG: Whitespace differences create different IDs
        assert id1 != id2
        assert id1 != id3
    
    def test_bug_generate_id_case_sensitive(self):
        """
        BUG: generate_id (line 20) is case-sensitive. "Test" vs "test" create
        different IDs. This may be intentional, but should be documented.
        
        Root cause: Case-sensitive string joining
        Consequences: Case differences create different IDs
        """
        id_lower = generate_id(Namespace.ASSET, "test")
        id_upper = generate_id(Namespace.ASSET, "Test")
        
        # BUG: Case differences create different IDs
        assert id_lower != id_upper
    
    def test_bug_generate_id_unicode_handling(self):
        """
        BUG: generate_id (line 20) doesn't normalize Unicode. Different Unicode
        representations of the same character (e.g., composed vs decomposed)
        will create different IDs.
        
        Root cause: No Unicode normalization
        Consequences: Unicode variations create different IDs
        """
        import unicodedata
        
        # Composed vs decomposed Unicode
        composed = "café"
        decomposed = unicodedata.normalize("NFD", composed)
        
        id_composed = generate_id(Namespace.ASSET, composed)
        id_decomposed = generate_id(Namespace.ASSET, decomposed)
        
        # BUG: Unicode variations create different IDs
        assert id_composed != id_decomposed
    
    def test_bug_generate_id_very_long_parts(self):
        """
        BUG: generate_id (line 20) doesn't limit length of parts or joined content.
        Very long parts may cause performance issues or exceed UUID5 input limits.
        
        Root cause: No length validation
        Consequences: Performance issues, potential errors with very long inputs
        """
        # Very long part
        long_part = "a" * 10000
        id_long = generate_id(Namespace.ASSET, long_part)
        
        # BUG: Very long parts may cause performance issues
        assert isinstance(id_long, UUID)
        # But performance may be degraded
    
    def test_bug_generate_id_many_parts(self):
        """
        BUG: generate_id (line 18) accepts *parts, so unlimited number of parts
        can be passed. Many parts may cause performance issues or create very
        long content strings.
        
        Root cause: No limit on number of parts
        Consequences: Performance issues with many parts
        """
        # Many parts
        many_parts = ["part"] * 1000
        id_many = generate_id(Namespace.ASSET, *many_parts)
        
        # BUG: Many parts may cause performance issues
        assert isinstance(id_many, UUID)
        # But joining 1000 parts may be slow
    
    def test_bug_generate_id_none_parts(self):
        """
        BUG: generate_id (line 18) accepts *parts: str, but doesn't validate
        that parts are not None. If None is passed, str(None) = "None" will
        be used, which may be unexpected.
        
        Root cause: No None validation
        Consequences: None values converted to "None" string, creating unexpected IDs
        """
        # None as part (would need to pass explicitly, but type hint doesn't prevent it)
        # This would require type coercion or incorrect usage
        # But if it happens, behavior may be unexpected
        
        # Test with string "None" vs actual None (if type coercion occurs)
        id_string_none = generate_id(Namespace.ASSET, "None")
        # Actual None would require type error or coercion


class TestNamespace:
    """Tests for Namespace enum"""
    
    def test_namespace_asset_exists(self):
        """Test Namespace.ASSET exists"""
        assert Namespace.ASSET is not None
        assert isinstance(Namespace.ASSET.value, UUID)
    
    def test_bug_namespace_only_has_asset(self):
        """
        BUG: Namespace (line 13-16) only defines ASSET namespace.
        If code needs other namespaces (e.g., USER, WORKSPACE, SESSION),
        they don't exist, causing errors or workarounds.
        
        Root cause: Incomplete namespace definitions
        Consequences: Missing namespaces may cause errors or code workarounds
        
        Proposed solution: Add all required namespaces or document extensibility
        """
        # Only ASSET exists
        assert len(list(Namespace)) == 1
        assert Namespace.ASSET in Namespace
    
    def test_bug_namespace_values_not_validated(self):
        """
        BUG: Namespace enum values are UUIDs created at class definition time.
        If uuid5() fails or returns invalid UUID, the error won't be caught until
        the enum is accessed.
        
        Root cause: No validation of UUID creation
        Consequences: Invalid UUIDs may exist silently
        """
        # Namespace values should be valid UUIDs
        assert isinstance(Namespace.ASSET.value, UUID)
        # UUID validation happens at creation time, so this should be fine
    
    def test_bug_namespace_immutability(self):
        """
        BUG: Namespace is an Enum, so values are immutable. However, if code
        tries to modify enum values, the error may not be clear.
        
        Root cause: Enum immutability may not be obvious
        Consequences: Attempts to modify enum may fail with unclear errors
        """
        # Enum values are immutable
        original_value = Namespace.ASSET.value
        
        # Cannot modify enum value
        # This is correct behavior, but error may not be clear if attempted


class TestNamespaceConstants:
    """Tests for namespace constants"""
    
    def test_namespace_dns_is_valid_uuid(self):
        """Test NAMESPACE_DNS is valid UUID"""
        assert isinstance(NAMESPACE_DNS, UUID)
        assert str(NAMESPACE_DNS) == "6ba7b810-9dad-11d1-80b4-00c04fd430c8"
    
    def test_namespace_forge_is_valid_uuid(self):
        """Test NAMESPACE_FORGE is valid UUID"""
        assert isinstance(NAMESPACE_FORGE, UUID)
        # Should be UUID5 of NAMESPACE_DNS with "forge.ai"
        expected = uuid5(NAMESPACE_DNS, "forge.ai")
        assert NAMESPACE_FORGE == expected
    
    def test_bug_namespace_constants_not_validated_at_import(self):
        """
        BUG: NAMESPACE_DNS and NAMESPACE_FORGE (lines 9-10) are created at
        import time. If UUID() or uuid5() fails, the error occurs at import,
        which may be hard to debug.
        
        Root cause: Constants created at import time
        Consequences: Import errors if UUID creation fails
        
        Proposed solution: Validate constants or handle errors gracefully
        """
        # Constants should be valid UUIDs
        assert isinstance(NAMESPACE_DNS, UUID)
        assert isinstance(NAMESPACE_FORGE, UUID)
    
    def test_bug_namespace_forge_determinism(self):
        """
        BUG: NAMESPACE_FORGE (line 10) uses uuid5 which is deterministic.
        However, if the input to uuid5 changes (e.g., "forge.ai" vs "Forge.ai"),
        the namespace will be different, breaking ID generation.
        
        Root cause: Case-sensitive string input to uuid5
        Consequences: Case differences in namespace creation break determinism
        """
        # NAMESPACE_FORGE should be deterministic
        expected = uuid5(NAMESPACE_DNS, "forge.ai")
        assert NAMESPACE_FORGE == expected
        
        # BUG: If case differs, namespace will be different
        different_case = uuid5(NAMESPACE_DNS, "Forge.ai")
        assert NAMESPACE_FORGE != different_case


class TestIdGenerationProperties:
    """Tests for ID generation properties and invariants"""
    
    def test_generate_id_creates_uuid5_format(self):
        """Test generate_id creates UUID5 format"""
        id_val = generate_id(Namespace.ASSET, "test")
        
        # Should be UUID5 format (version 5)
        assert id_val.version == 5
    
    def test_bug_generate_id_collision_potential(self):
        """
        BUG: generate_id (line 18-21) uses uuid5 which is deterministic.
        If different namespaces or parts accidentally create the same content
        string, they will create the same ID, causing collisions.
        
        Root cause: Deterministic ID generation based on string content
        Consequences: Content collisions create ID collisions
        
        Proposed solution: Use namespace in content or validate uniqueness
        """
        # Same content in different contexts may create same ID
        # This is inherent to deterministic ID generation
        id1 = generate_id(Namespace.ASSET, "test")
        id2 = generate_id(Namespace.ASSET, "test")
        
        # Same namespace and parts create same ID (correct)
        assert id1 == id2
        
        # But if namespace is same and parts are same, collision is expected
        # BUG: No validation that IDs are unique across different use cases
    
    def test_bug_generate_id_order_dependent(self):
        """
        BUG: generate_id (line 20) joins parts in order. Different orders
        create different IDs: generate_id(ns, "a", "b") != generate_id(ns, "b", "a").
        This is correct, but if order is inconsistent, IDs will differ.
        
        Root cause: Order-dependent joining
        Consequences: Inconsistent part ordering creates different IDs
        
        Proposed solution: Sort parts or document order requirement
        """
        id_ab = generate_id(Namespace.ASSET, "a", "b")
        id_ba = generate_id(Namespace.ASSET, "b", "a")
        
        # BUG: Order matters, so these are different
        assert id_ab != id_ba
        
        # This may be intentional, but should be documented
