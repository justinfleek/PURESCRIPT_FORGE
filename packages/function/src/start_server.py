#!/usr/bin/env python3
"""
Start Voice Engine Server

Simple script to start the FastAPI voice engine server.
"""

import os
import sys
from pathlib import Path

# Add src directory to path
src_dir = Path(__file__).parent / "apps" / "api" / "src"
sys.path.insert(0, str(src_dir.parent.parent.parent))

# Set environment variables if not set
if not os.getenv("VENICE_API_KEY"):
    print("⚠️  WARNING: VENICE_API_KEY not set")
    print("   Set it with: export VENICE_API_KEY=your_key")

if not os.getenv("VOICE_DB_PATH"):
    db_path = Path.home() / ".opencode-sidepanel" / "bridge.db"
    os.environ["VOICE_DB_PATH"] = str(db_path)
    print(f"Using database: {db_path}")

# Import and run
if __name__ == "__main__":
    import uvicorn
    from apps.api.src.main import app
    
    port = int(os.getenv("PORT", "8001"))
    print(f"Starting Voice Engine server on port {port}...")
    print(f"Health check: http://localhost:{port}/health")
    print(f"API docs: http://localhost:{port}/docs")
    
    uvicorn.run(
        app,
        host="0.0.0.0",
        port=port,
        log_level="info",
    )
