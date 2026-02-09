"""
Nexus Semantic Cells - Python Package Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-semantic-cells",
    version="0.1.0",
    description="Semantic Cell Architecture - Predictive Processing Framework",
    author="FORGE",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.10",
    install_requires=[
        "numpy>=1.24.0",
        "dataclasses-json>=0.6.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
            "black>=23.0.0",
            "mypy>=1.0.0",
        ],
    },
)
