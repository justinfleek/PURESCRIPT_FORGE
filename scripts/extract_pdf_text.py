#!/usr/bin/env python3
"""Extract text from PDF file"""
import sys
import os

try:
    import PyPDF2
    
    pdf_path = sys.argv[1] if len(sys.argv) > 1 else r"c:\Users\justi\Desktop\CODER\render_specs.pdf"
    
    with open(pdf_path, 'rb') as pdf_file:
        reader = PyPDF2.PdfReader(pdf_file)
        text = []
        for page in reader.pages:
            text.append(page.extract_text())
        
        print("\n".join(text))
        
except ImportError:
    print("PyPDF2 not available. Trying alternative method...", file=sys.stderr)
    try:
        import pdfplumber
        
        pdf_path = sys.argv[1] if len(sys.argv) > 1 else r"c:\Users\justi\Desktop\CODER\render_specs.pdf"
        
        with pdfplumber.open(pdf_path) as pdf:
            text = []
            for page in pdf.pages:
                text.append(page.extract_text() or "")
            
            print("\n".join(text))
            
    except ImportError:
        print("No PDF extraction library available. Please install PyPDF2 or pdfplumber.", file=sys.stderr)
        sys.exit(1)
