"""
Nexus Agent Orchestrator - Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-agent-orchestrator",
    version="0.1.0",
    description="Nexus Agent Orchestrator - Launch and manage agents in bubblewrap sandboxes",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.8",
    install_requires=[],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
        ],
    },
)
