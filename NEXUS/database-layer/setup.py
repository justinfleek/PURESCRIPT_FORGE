"""
Nexus Database Layer - Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-database-layer",
    version="0.1.0",
    description="Nexus Database Layer - SQLite + DuckDB persistence",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.8",
    install_requires=[
        "duckdb>=0.9.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
        ],
    },
)
