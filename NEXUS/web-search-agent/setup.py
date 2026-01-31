"""
Nexus Web Search Agent - Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-web-search-agent",
    version="0.1.0",
    description="Nexus Web Search Agent - Autonomous web search",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.8",
    install_requires=[
        "requests>=2.28.0",
        "beautifulsoup4>=4.11.0",  # For HTML parsing (would be used in production)
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
        ],
    },
)
