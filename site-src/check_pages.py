#!/usr/bin/env python3
"""Check the page numbers of the links from the tours to the papers.

Each directive {{in-paper: Lemma 2.2 | 5}} in site-src/pages/ names a statement, a section or a
figure and a page. This script reads that page of the PDF with pdftotext (poppler) and looks for
the head of the statement, the section or the figure. Run it after a paper changes:

    python3 site-src/check_pages.py

The exit code is 0 if every reference is on its page, and 1 if not.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SITE = HERE.parent / "site"
STATEMENT = re.compile(r"^(Theorem|Lemma|Proposition|Corollary) (\d+\.\d+)$")
SECTION = re.compile(r"^Section (\d+(?:\.\d+)?)$")
FIGURE = re.compile(r"^Figure (\d+)$")


def page_lines(pdf: Path, page: int) -> list[str]:
    out = subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), "-layout", str(pdf), "-"],
        check=True, capture_output=True, text=True,
    ).stdout
    return [line.strip() for line in out.splitlines()]


def found(label: str, lines: list[str]) -> bool:
    if match := STATEMENT.match(label):
        head = re.compile(rf"^{match[1]} {re.escape(match[2])}\s*(\(|\.)")
        return any(head.match(line) for line in lines)
    if match := SECTION.match(label):
        head = re.compile(rf"^{re.escape(match[1])}\s+[A-Z]")
        return any(head.match(line) and len(line) < 80 for line in lines)
    if match := FIGURE.match(label):
        return any(line.startswith(f"Figure {match[1]}.") for line in lines)
    if label.startswith("Fine print"):
        return any(line.startswith("Fine print.") for line in lines)
    raise ValueError(f"unknown kind of reference: {label}")


def main() -> int:
    errors = 0
    count = 0
    for source in sorted((HERE / "pages").glob("*.html")):
        text = source.read_text()
        header = re.match(r"<!--page\s*(.*?)-->", text, re.S)
        if header is None:
            raise ValueError(f"{source.name} has no page header")
        meta = json.loads(header[1])
        for key, items in re.findall(r"\{\{in-paper(?:@([\w-]+))?:([^}]+)\}\}", text):
            paper = meta["otherPapers"][key] if key else meta["paper"]
            pdf = SITE / paper["file"]
            for item in items.split(";"):
                label, page = (part.strip() for part in item.split("|"))
                count += 1
                if not found(label, page_lines(pdf, int(page))):
                    errors += 1
                    print(f"{source.name}: {label} is not on page {page} of {paper['file']}")
    print(f"{count} references, {errors} errors")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
