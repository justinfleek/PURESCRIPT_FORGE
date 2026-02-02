/**
 * Persistence Layer
 * Wires database to state store for automatic persistence
 */
import { StateStore } from '../state/store.js';
import { DatabaseManager, type SessionRecord } from './schema.js';
import { randomUUID } from 'crypto';
import pino from 'pino';

const logger = pino({ name: 'persistence' });

/**
 * Wire database persistence to state store
 */
export function wirePersistence(store: StateStore, db: DatabaseManager): () => void {
  // Auto-save balance history
  const balanceUnsubscribe = store.onStateChange((path, value) => {
    if (path === 'balance') {
      const balance = store.getState().balance;
      db.recordBalanceHistory(
        balance.venice.diem,
        balance.venice.usd,
        balance.venice.effective,
        balance.consumptionRate,
        balance.timeToDepletion
      );
    }
  });
  
  // Auto-save sessions
  const sessionUnsubscribe = store.onStateChange((path, value) => {
    if (path === 'session') {
      const session = store.getState().session;
      if (session !== null) {
        const sessionRecord: SessionRecord = {
          id: randomUUID(),
          sessionId: session.id,
          promptTokens: session.promptTokens,
          completionTokens: session.completionTokens,
          cost: session.cost,
          model: session.model,
          provider: session.provider,
          startedAt: session.startedAt,
          endedAt: null,
        };
        
        try {
          db.saveSession(sessionRecord);
          logger.debug('Session auto-saved', { sessionId: session.id });
        } catch (error) {
          logger.error('Failed to auto-save session', {
            error: error instanceof Error ? error.message : String(error),
            sessionId: session.id,
          });
        }
      } else {
        // Session cleared - mark as ended
        // Note: We'd need to track the last session ID to mark it as ended
        // For now, just log
        logger.debug('Session cleared');
      }
    }
  });
  
  // Auto-save voice state
  const voiceUnsubscribe = store.onStateChange((path, value) => {
    if (path.startsWith('voice.')) {
      const voice = store.getState().voice;
      
      // Save voice session
      if (voice.session) {
        try {
          db.saveVoiceSession({
            id: voice.session.id,
            conversationId: voice.session.conversationId,
            orgId: voice.session.orgId,
            userId: voice.session.userId,
            state: voice.session.state,
            totalAudioSeconds: voice.session.totalAudioSeconds,
            totalSttTokens: voice.session.totalSttTokens,
            totalTtsCharacters: voice.session.totalTtsCharacters,
            startedAt: voice.session.startedAt,
            endedAt: voice.session.endedAt,
          });
          logger.debug('Voice session auto-saved', { sessionId: voice.session.id });
        } catch (error) {
          logger.error('Failed to auto-save voice session', {
            error: error instanceof Error ? error.message : String(error),
            sessionId: voice.session.id,
          });
        }
      }
      
      // Save voice messages
      if (voice.messages.length > 0 && voice.session) {
        try {
          const currentSession = voice.session;
          const messagesToSave = voice.messages.map(msg => ({
            id: msg.id,
            sessionId: currentSession.id,
            conversationId: currentSession.conversationId,
            role: msg.role,
            text: msg.text,
            audioUrl: msg.audioUrl,
            durationSeconds: msg.durationSeconds,
            sttConfidence: msg.sttConfidence,
            createdAt: msg.timestamp,
          }));
          
          db.saveVoiceMessages(messagesToSave);
          logger.debug('Voice messages auto-saved', { count: messagesToSave.length });
        } catch (error) {
          logger.error('Failed to auto-save voice messages', {
            error: error instanceof Error ? error.message : String(error),
          });
        }
      }
    }
  });
  
  // Return cleanup function
  return () => {
    balanceUnsubscribe();
    sessionUnsubscribe();
    voiceUnsubscribe();
  };
}
