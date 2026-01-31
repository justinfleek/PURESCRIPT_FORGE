"""
Nexus Network Formation Agent - Setup
"""

from setuptools import setup, find_packages

setup(
    name="nexus-network-formation-agent",
    version="0.1.0",
    description="Nexus Network Formation Agent - Form social networks",
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
