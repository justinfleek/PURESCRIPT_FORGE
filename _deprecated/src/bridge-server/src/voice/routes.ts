/**
 * Voice API Routes
 * 
 * Express routes that proxy to Python voice engine service.
 */

import express, { Request, Response } from 'express';
import { VoiceService } from './integration.js';

// Simple multipart parser (no multer dependency)
function parseMultipartFormData(req: Request): Promise<{ fields: Record<string, string>, files: Record<string, Buffer> }> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk) => chunks.push(chunk));
    req.on('end', () => {
      // For now, expect audio as raw body or use FormData
      // In production, use proper multipart parser
      resolve({ fields: req.body || {}, files: {} });
    });
    req.on('error', reject);
  });
}

export function createVoiceRoutes(voiceService: VoiceService): express.Router {
  const router = express.Router();

  /**
   * POST /api/voice/chat
   * Process voice message (audio → transcript → AI → audio)
   */
  router.post('/chat', express.raw({ type: '*/*', limit: '25mb' }), async (req: Request, res: Response) => {
    try {
      // Get audio from request body
      const audioBuffer = req.body as Buffer;
      if (!audioBuffer || audioBuffer.length === 0) {
        return res.status(400).json({ error: 'Audio file required' });
      }

      // Get parameters from query or headers
      const conversationId = (req.query.conversation_id as string) || 'default';
      const voice = (req.query.voice as string) || 'Ryan';
      const language = (req.query.language as string) || 'en';

      // Create FormData for Python service
      const formData = new FormData();
      const blob = new Blob([audioBuffer], { type: req.headers['content-type'] || 'audio/webm' });
      formData.append('audio', blob, 'audio.webm');
      formData.append('conversation_id', conversationId);
      formData.append('voice', voice);
      formData.append('language', language);

      const response = await voiceService.proxyRequest('/api/voice/chat', {
        method: 'POST',
        body: formData,
      });

      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Voice chat failed', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * POST /api/voice/chat/text
   * Text input with audio output
   */
  router.post('/chat/text', express.json(), async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest('/api/voice/chat/text', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          text: req.body.text,
          conversation_id: req.body.conversation_id || 'default',
          voice: req.body.voice || 'Ryan',
        }),
      });

      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Voice chat failed', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * GET /api/voice/models
   * List available TTS models
   */
  router.get('/models', async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest('/api/voice/models');
      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Failed to list models', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * POST /api/voice/models/download
   * Download TTS model
   */
  router.post('/models/download', express.json(), async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest('/api/voice/models/download', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ model_id: req.body.model_id }),
      });

      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Failed to download model', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * GET /api/voice/voices
   * List available voices
   */
  router.get('/voices', async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest('/api/voice/voices');
      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Failed to list voices', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * GET /api/voice/sessions/:id
   * Get voice session
   */
  router.get('/sessions/:id', async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest(`/api/voice/sessions/${req.params.id}`);
      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Failed to get session', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  /**
   * POST /api/voice/sessions/:id/end
   * End voice session
   */
  router.post('/sessions/:id/end', async (req: Request, res: Response) => {
    try {
      const response = await voiceService.proxyRequest(`/api/voice/sessions/${req.params.id}/end`, {
        method: 'POST',
      });

      const data = await response.json();
      res.json(data);
    } catch (error) {
      res.status(500).json({ 
        error: 'Failed to end session', 
        message: error instanceof Error ? error.message : String(error) 
      });
    }
  });

  return router;
}
