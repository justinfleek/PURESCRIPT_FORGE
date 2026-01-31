"""
Nexus Database Layer - Content Store
CRUD operations for web content and extracted information
"""

import sqlite3
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from datetime import datetime, timedelta
import json


@dataclass
class WebContent:
    """Web content record"""
    id: str
    url: str
    content_type: str  # html, pdf, text, etc.
    content: str  # Full content or path to file
    title: Optional[str] = None
    metadata: Optional[Dict[str, Any]] = None
    fetched_at: str = ""
    expires_at: Optional[str] = None


@dataclass
class ExtractedEntity:
    """Extracted entity record"""
    id: str
    content_id: str
    entity_type: str  # person, place, concept, etc.
    entity_text: str
    confidence: float  # 0.0 to 1.0
    properties: Optional[Dict[str, Any]] = None
    created_at: str = ""


@dataclass
class ExtractedRelation:
    """Extracted relation record"""
    id: str
    content_id: str
    source_entity_id: str
    target_entity_id: str
    relation_type: str
    confidence: float  # 0.0 to 1.0
    properties: Optional[Dict[str, Any]] = None
    created_at: str = ""


class ContentStore:
    """
    Content store for CRUD operations on web content and extracted information.
    
    Stores web content cache and extracted entities/relations.
    """
    
    def __init__(self, conn: sqlite3.Connection):
        """
        Initialize content store.
        
        Args:
            conn: SQLite connection
        """
        self.conn = conn
    
    def save_content(self, content: WebContent) -> None:
        """
        Save web content to database.
        
        Args:
            content: Web content to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO web_content (
                id, url, content_type, content, title, metadata,
                fetched_at, expires_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            content.id,
            content.url,
            content.content_type,
            content.content,
            content.title,
            json.dumps(content.metadata) if content.metadata else None,
            content.fetched_at,
            content.expires_at
        ))
        self.conn.commit()
    
    def load_content(self, content_id: str) -> Optional[WebContent]:
        """
        Load web content from database.
        
        Args:
            content_id: Content ID
            
        Returns:
            Web content or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM web_content WHERE id = ?
        """, (content_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return WebContent(
            id=row["id"],
            url=row["url"],
            content_type=row["content_type"],
            content=row["content"],
            title=row["title"],
            metadata=json.loads(row["metadata"]) if row["metadata"] else None,
            fetched_at=row["fetched_at"],
            expires_at=row["expires_at"]
        )
    
    def load_content_by_url(self, url: str) -> Optional[WebContent]:
        """
        Load web content by URL.
        
        Args:
            url: URL
            
        Returns:
            Web content or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM web_content WHERE url = ?
        """, (url,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return WebContent(
            id=row["id"],
            url=row["url"],
            content_type=row["content_type"],
            content=row["content"],
            title=row["title"],
            metadata=json.loads(row["metadata"]) if row["metadata"] else None,
            fetched_at=row["fetched_at"],
            expires_at=row["expires_at"]
        )
    
    def save_entity(self, entity: ExtractedEntity) -> None:
        """
        Save extracted entity to database.
        
        Args:
            entity: Extracted entity to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO extracted_entities (
                id, content_id, entity_type, entity_text,
                confidence, properties, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (
            entity.id,
            entity.content_id,
            entity.entity_type,
            entity.entity_text,
            entity.confidence,
            json.dumps(entity.properties) if entity.properties else None,
            entity.created_at
        ))
        self.conn.commit()
    
    def load_entities(self, content_id: str) -> List[ExtractedEntity]:
        """
        Load extracted entities for content.
        
        Args:
            content_id: Content ID
            
        Returns:
            List of extracted entities
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM extracted_entities
            WHERE content_id = ?
            ORDER BY confidence DESC
        """, (content_id,))
        rows = cursor.fetchall()
        
        return [
            ExtractedEntity(
                id=row["id"],
                content_id=row["content_id"],
                entity_type=row["entity_type"],
                entity_text=row["entity_text"],
                confidence=row["confidence"],
                properties=json.loads(row["properties"]) if row["properties"] else None,
                created_at=row["created_at"]
            )
            for row in rows
        ]
    
    def save_relation(self, relation: ExtractedRelation) -> None:
        """
        Save extracted relation to database.
        
        Args:
            relation: Extracted relation to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO extracted_relations (
                id, content_id, source_entity_id, target_entity_id,
                relation_type, confidence, properties, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            relation.id,
            relation.content_id,
            relation.source_entity_id,
            relation.target_entity_id,
            relation.relation_type,
            relation.confidence,
            json.dumps(relation.properties) if relation.properties else None,
            relation.created_at
        ))
        self.conn.commit()
    
    def load_relations(self, content_id: str) -> List[ExtractedRelation]:
        """
        Load extracted relations for content.
        
        Args:
            content_id: Content ID
            
        Returns:
            List of extracted relations
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM extracted_relations
            WHERE content_id = ?
            ORDER BY confidence DESC
        """, (content_id,))
        rows = cursor.fetchall()
        
        return [
            ExtractedRelation(
                id=row["id"],
                content_id=row["content_id"],
                source_entity_id=row["source_entity_id"],
                target_entity_id=row["target_entity_id"],
                relation_type=row["relation_type"],
                confidence=row["confidence"],
                properties=json.loads(row["properties"]) if row["properties"] else None,
                created_at=row["created_at"]
            )
            for row in rows
        ]
    
    def delete_content(self, content_id: str) -> None:
        """
        Delete web content and its extracted entities/relations.
        
        Args:
            content_id: Content ID
        """
        cursor = self.conn.cursor()
        # Delete relations first
        cursor.execute("DELETE FROM extracted_relations WHERE content_id = ?", (content_id,))
        # Delete entities
        cursor.execute("DELETE FROM extracted_entities WHERE content_id = ?", (content_id,))
        # Delete content
        cursor.execute("DELETE FROM web_content WHERE id = ?", (content_id,))
        self.conn.commit()
    
    def cleanup_expired_content(self, max_age_days: int = 30) -> int:
        """
        Delete expired web content older than max_age_days.
        
        Args:
            max_age_days: Maximum age in days
            
        Returns:
            Number of deleted records
        """
        cursor = self.conn.cursor()
        cutoff_date = (datetime.utcnow() - timedelta(days=max_age_days)).isoformat()
        
        # Find expired content
        cursor.execute("""
            SELECT id FROM web_content
            WHERE expires_at IS NOT NULL AND expires_at < ?
            OR fetched_at < ?
        """, (cutoff_date, cutoff_date))
        expired_ids = [row[0] for row in cursor.fetchall()]
        
        # Delete expired content
        for content_id in expired_ids:
            self.delete_content(content_id)
        
        return len(expired_ids)
