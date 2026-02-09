"""
Nexus Content Extraction Agent - Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-content-extraction-agent",
    version="0.1.0",
    description="Nexus Content Extraction Agent - Extract semantic information",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.8",
    install_requires=[
        # Would include spaCy, NLTK, etc. in production
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
        ],
    },
)
