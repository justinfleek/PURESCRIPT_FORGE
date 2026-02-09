"""
Voice Engine API Server - FastAPI application.

Full integration with Bridge Server database and Venice API.
"""

import os
import logging
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from .routes.voice import router as voice_router
from .deps import init_voice_services
from .services import create_voice_services, shutdown_voice_services, VoiceServices

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global services
_voice_services: VoiceServices | None = None


async def setup_voice_services():
    """Setup voice services with full integration."""
    global _voice_services
    
    logger.info("Initializing voice services...")
    
    # Get database path (use Bridge Server database)
    db_path = os.getenv(
        "VOICE_DB_PATH",
        os.path.join(os.path.expanduser("~"), ".forge-sidepanel", "bridge.db"),
    )
    
    # Get Venice API key
    venice_key = os.getenv("VENICE_API_KEY")
    if not venice_key:
        raise ValueError("VENICE_API_KEY environment variable is required")
    
    # Create all services
    _voice_services = await create_voice_services(
        db_path=db_path,
        venice_api_key=venice_key,
    )
    
    # Initialize dependency injection
    init_voice_services(_voice_services)
    
    logger.info("Voice services initialized successfully")


# Create FastAPI app
app = FastAPI(
    title="Voice Engine API",
    description="Voice chat API with Qwen3-TTS integration",
    version="1.0.0",
)

# CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, restrict to specific origins
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include routers
app.include_router(voice_router, prefix="/api")

# Startup event
@app.on_event("startup")
async def startup_event():
    """Initialize services on startup."""
    await setup_voice_services()


# Shutdown event
@app.on_event("shutdown")
async def shutdown_event():
    """Shutdown services on shutdown."""
    global _voice_services
    if _voice_services:
        await shutdown_voice_services(_voice_services)
        _voice_services = None


# Health check
@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {"status": "ok", "service": "voice-engine"}


if __name__ == "__main__":
    import uvicorn
    port = int(os.getenv("PORT", "8001"))
    uvicorn.run(app, host="0.0.0.0", port=port)
