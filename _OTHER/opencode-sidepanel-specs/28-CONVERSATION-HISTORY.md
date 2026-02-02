# 28-CONVERSATION-HISTORY: Message History Management

## Overview

Conversation history management handles storing, retrieving, searching, and pruning message history for AI sessions.

---

## History Structure

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        CONVERSATION HISTORY                                  │
│                                                                              │
│  Session: Debug Auth (sess_abc123)                                          │
│  Created: Jan 15, 2025 12:30 PM                                             │
│  Messages: 24                                                               │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ #1  USER       12:30:00    "Help me debug this auth flow..."        │   │
│  │ #2  ASSISTANT  12:30:15    "I'll analyze the code. Let me..."       │   │
│  │ #3  TOOL       12:30:16    read_file: src/auth/session.ts           │   │
│  │ #4  ASSISTANT  12:30:45    "I found the issue. The token..."        │   │
│  │ #5  USER       12:31:00    "Can you fix it and write tests?"        │   │
│  │ #6  ASSISTANT  12:31:30    "Sure, here's the fix..."                │   │
│  │ #7  TOOL       12:31:31    write_file: src/auth/session.ts          │   │
│  │ ...                                                                  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface ConversationHistory {
  sessionId: string;
  messages: HistoryMessage[];
  
  // Metadata
  createdAt: Date;
  updatedAt: Date;
  
  // Statistics
  messageCount: number;
  totalTokens: number;
  
  // State
  isArchived: boolean;
  isPinned: boolean;
}

interface HistoryMessage {
  id: string;
  sequence: number;
  
  // Content
  role: 'user' | 'assistant' | 'system' | 'tool';
  content: string;
  
  // Tool-related
  toolCalls?: ToolCall[];
  toolCallId?: string;  // For tool response messages
  
  // Metrics
  timestamp: Date;
  tokens?: {
    prompt: number;
    completion: number;
  };
  
  // UI state
  isCollapsed?: boolean;
  isBookmarked?: boolean;
  
  // Edit history
  editedAt?: Date;
  originalContent?: string;
}

interface HistoryQuery {
  sessionId?: string;
  role?: MessageRole;
  search?: string;
  dateRange?: { start: Date; end: Date };
  hasToolCalls?: boolean;
  isBookmarked?: boolean;
  limit?: number;
  offset?: number;
}

interface HistoryStats {
  totalMessages: number;
  userMessages: number;
  assistantMessages: number;
  toolMessages: number;
  totalTokens: number;
  avgTokensPerMessage: number;
  timespan: { start: Date; end: Date };
}
```

---

## History Manager

```typescript
// bridge/src/history/manager.ts

export class HistoryManager {
  private db: Database;
  
  async addMessage(
    sessionId: string,
    message: Omit<HistoryMessage, 'id' | 'sequence'>
  ): Promise<HistoryMessage> {
    const sequence = await this.getNextSequence(sessionId);
    
    const fullMessage: HistoryMessage = {
      id: generateId(),
      sequence,
      ...message,
      timestamp: message.timestamp ?? new Date()
    };
    
    await this.db.run(`
      INSERT INTO messages (id, session_id, sequence, role, content, timestamp, tokens_prompt, tokens_completion, tool_calls, tool_call_id)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `, [
      fullMessage.id,
      sessionId,
      fullMessage.sequence,
      fullMessage.role,
      fullMessage.content,
      fullMessage.timestamp.toISOString(),
      fullMessage.tokens?.prompt ?? null,
      fullMessage.tokens?.completion ?? null,
      fullMessage.toolCalls ? JSON.stringify(fullMessage.toolCalls) : null,
      fullMessage.toolCallId ?? null
    ]);
    
    // Update session
    await this.db.run(`
      UPDATE sessions SET updated_at = ? WHERE id = ?
    `, [new Date().toISOString(), sessionId]);
    
    // Broadcast
    this.broadcast('history.message.added', { sessionId, message: fullMessage });
    
    return fullMessage;
  }
  
  async getHistory(sessionId: string): Promise<ConversationHistory> {
    const messages = await this.db.all<HistoryMessage>(`
      SELECT * FROM messages 
      WHERE session_id = ? 
      ORDER BY sequence ASC
    `, [sessionId]);
    
    const session = await this.db.get(`
      SELECT * FROM sessions WHERE id = ?
    `, [sessionId]);
    
    return {
      sessionId,
      messages: messages.map(this.parseMessage),
      createdAt: new Date(session.created_at),
      updatedAt: new Date(session.updated_at),
      messageCount: messages.length,
      totalTokens: this.calculateTotalTokens(messages),
      isArchived: session.is_archived === 1,
      isPinned: session.is_pinned === 1
    };
  }
  
  async search(query: HistoryQuery): Promise<HistoryMessage[]> {
    let sql = 'SELECT * FROM messages WHERE 1=1';
    const params: any[] = [];
    
    if (query.sessionId) {
      sql += ' AND session_id = ?';
      params.push(query.sessionId);
    }
    
    if (query.role) {
      sql += ' AND role = ?';
      params.push(query.role);
    }
    
    if (query.search) {
      sql += ' AND content LIKE ?';
      params.push(`%${query.search}%`);
    }
    
    if (query.dateRange) {
      sql += ' AND timestamp BETWEEN ? AND ?';
      params.push(query.dateRange.start.toISOString());
      params.push(query.dateRange.end.toISOString());
    }
    
    if (query.hasToolCalls !== undefined) {
      sql += query.hasToolCalls 
        ? ' AND tool_calls IS NOT NULL'
        : ' AND tool_calls IS NULL';
    }
    
    if (query.isBookmarked) {
      sql += ' AND is_bookmarked = 1';
    }
    
    sql += ' ORDER BY timestamp DESC';
    
    if (query.limit) {
      sql += ' LIMIT ?';
      params.push(query.limit);
    }
    
    if (query.offset) {
      sql += ' OFFSET ?';
      params.push(query.offset);
    }
    
    const results = await this.db.all<HistoryMessage>(sql, params);
    return results.map(this.parseMessage);
  }
  
  async getStats(sessionId?: string): Promise<HistoryStats> {
    const whereClause = sessionId ? 'WHERE session_id = ?' : '';
    const params = sessionId ? [sessionId] : [];
    
    const stats = await this.db.get(`
      SELECT 
        COUNT(*) as total,
        SUM(CASE WHEN role = 'user' THEN 1 ELSE 0 END) as user_count,
        SUM(CASE WHEN role = 'assistant' THEN 1 ELSE 0 END) as assistant_count,
        SUM(CASE WHEN role = 'tool' THEN 1 ELSE 0 END) as tool_count,
        SUM(COALESCE(tokens_prompt, 0) + COALESCE(tokens_completion, 0)) as total_tokens,
        MIN(timestamp) as first_message,
        MAX(timestamp) as last_message
      FROM messages ${whereClause}
    `, params);
    
    return {
      totalMessages: stats.total,
      userMessages: stats.user_count,
      assistantMessages: stats.assistant_count,
      toolMessages: stats.tool_count,
      totalTokens: stats.total_tokens ?? 0,
      avgTokensPerMessage: stats.total > 0 ? stats.total_tokens / stats.total : 0,
      timespan: {
        start: new Date(stats.first_message),
        end: new Date(stats.last_message)
      }
    };
  }
  
  async bookmarkMessage(messageId: string, bookmarked: boolean): Promise<void> {
    await this.db.run(`
      UPDATE messages SET is_bookmarked = ? WHERE id = ?
    `, [bookmarked ? 1 : 0, messageId]);
    
    this.broadcast('history.message.bookmarked', { messageId, bookmarked });
  }
  
  async deleteMessage(messageId: string): Promise<void> {
    // Get message for broadcast
    const message = await this.db.get(`SELECT * FROM messages WHERE id = ?`, [messageId]);
    
    await this.db.run(`DELETE FROM messages WHERE id = ?`, [messageId]);
    
    // Resequence remaining messages
    await this.resequence(message.session_id);
    
    this.broadcast('history.message.deleted', { messageId, sessionId: message.session_id });
  }
  
  async pruneHistory(
    sessionId: string,
    options: PruneOptions
  ): Promise<number> {
    let deleted = 0;
    
    if (options.keepLast) {
      // Keep only the last N messages
      const toDelete = await this.db.all(`
        SELECT id FROM messages 
        WHERE session_id = ?
        ORDER BY sequence DESC
        LIMIT -1 OFFSET ?
      `, [sessionId, options.keepLast]);
      
      for (const msg of toDelete) {
        await this.deleteMessage(msg.id);
        deleted++;
      }
    }
    
    if (options.olderThan) {
      // Delete messages older than date
      const result = await this.db.run(`
        DELETE FROM messages 
        WHERE session_id = ? AND timestamp < ?
      `, [sessionId, options.olderThan.toISOString()]);
      
      deleted += result.changes;
    }
    
    return deleted;
  }
  
  private parseMessage(row: any): HistoryMessage {
    return {
      id: row.id,
      sequence: row.sequence,
      role: row.role,
      content: row.content,
      timestamp: new Date(row.timestamp),
      tokens: row.tokens_prompt ? {
        prompt: row.tokens_prompt,
        completion: row.tokens_completion
      } : undefined,
      toolCalls: row.tool_calls ? JSON.parse(row.tool_calls) : undefined,
      toolCallId: row.tool_call_id,
      isCollapsed: row.is_collapsed === 1,
      isBookmarked: row.is_bookmarked === 1
    };
  }
}

interface PruneOptions {
  keepLast?: number;
  olderThan?: Date;
  keepBookmarked?: boolean;
}
```

---

## History Visualization

### Message List Component

```purescript
module Sidepanel.Components.HistoryList where

renderHistoryList :: forall m. Array HistoryMessage -> H.ComponentHTML Action () m
renderHistoryList messages =
  HH.div
    [ HP.class_ (H.ClassName "history-list") ]
    (mapWithIndex renderMessageItem messages)

renderMessageItem :: forall m. Int -> HistoryMessage -> H.ComponentHTML Action () m
renderMessageItem index msg =
  HH.div
    [ HP.classes $ messageClasses msg
    , HP.id ("msg-" <> show index)
    ]
    [ HH.div [ HP.class_ (H.ClassName "message-header") ]
        [ HH.span [ HP.class_ (H.ClassName "message-number") ]
            [ HH.text $ "#" <> show (index + 1) ]
        , HH.span [ HP.classes $ roleClasses msg.role ]
            [ HH.text $ show msg.role ]
        , HH.span [ HP.class_ (H.ClassName "message-time") ]
            [ HH.text $ formatTime msg.timestamp ]
        , when (isJust msg.tokens) $
            HH.span [ HP.class_ (H.ClassName "message-tokens") ]
              [ HH.text $ formatTokens msg.tokens ]
        , renderMessageActions msg
        ]
    , HH.div [ HP.class_ (H.ClassName "message-content") ]
        [ if msg.isCollapsed
            then HH.text $ truncate 100 msg.content <> "..."
            else renderContent msg
        ]
    ]

renderContent :: forall m. HistoryMessage -> H.ComponentHTML Action () m
renderContent msg = case msg.role of
  Tool -> renderToolMessage msg
  _ -> HH.div_ [ HH.text msg.content ]

renderToolMessage :: forall m. HistoryMessage -> H.ComponentHTML Action () m
renderToolMessage msg =
  HH.div
    [ HP.class_ (H.ClassName "tool-message") ]
    [ HH.span [ HP.class_ (H.ClassName "tool-icon") ] [ HH.text "🔧" ]
    , HH.span [ HP.class_ (H.ClassName "tool-name") ]
        [ HH.text $ maybe "tool" _.function.name (head =<< msg.toolCalls) ]
    , HH.div [ HP.class_ (H.ClassName "tool-result") ]
        [ HH.text msg.content ]
    ]
```

---

## CSS Styling

```css
.history-list {
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.message-item {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  overflow: hidden;
}

.message-item--user {
  border-left: 3px solid var(--color-primary);
}

.message-item--assistant {
  border-left: 3px solid var(--color-success);
}

.message-item--tool {
  border-left: 3px solid var(--color-warning);
  background: var(--color-bg-base);
}

.message-item--bookmarked {
  border-color: var(--color-warning);
}

.message-header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-elevated);
  border-bottom: 1px solid var(--color-border-subtle);
}

.message-number {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.message-role {
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  text-transform: uppercase;
  padding: 2px 6px;
  border-radius: 4px;
}

.message-role--user {
  background: var(--color-primary-dim);
  color: var(--color-primary);
}

.message-role--assistant {
  background: var(--color-success-dim);
  color: var(--color-success);
}

.message-time {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  margin-left: auto;
}

.message-content {
  padding: var(--space-3);
}
```

---

## Related Specifications

- `23-SESSION-MANAGEMENT.md` - Session handling
- `24-MESSAGE-FLOW.md` - Message lifecycle
- `66-SEARCH-VIEW.md` - Searching history

---

*"Every conversation is history. Preserve it well."*
