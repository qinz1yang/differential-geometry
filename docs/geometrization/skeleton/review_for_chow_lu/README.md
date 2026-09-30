# Mathematical review for Bennett Chow and Peng Lu

The review freezes the Lean skeleton at
`ea0fae60ee01ef8c8d9b57a51794c6538f679c5d` (Blueprint 207).
No Lean mathematical source or blueprint text was changed in preparing it.
Mathematical approval by the readers is pending.

- [Printable report](../../../../output/pdf/geometrization_skeleton_mathematical_review.pdf)
- [Standalone LaTeX](geometrization_skeleton_mathematical_review.tex)
- [Combined Markdown](geometrization_skeleton_mathematical_review.md)
- [All 121 declaration mappings](declaration_coverage.json)
- [Exact frozen skeleton source text](exact_sources.txt)
- [Source hashes](source_snapshot.json)
- [Report consistency checks](report_verification.json)
- [PDF checks](pdf_verification.json)
- [Visual inspection record](visual_review.json)

Start with E1–E2 (the exact endpoint), F3–F8 (the actual assembly and its
quantifiers), and the joint-review worksheet. The remaining sections give the
full family translations, proof-status distinctions, and corner cases. The
declaration register links to immutable source lines in Ziyang's private
repository; GitHub access is required to open those links.

The single `.tex` file contains its complete preamble and body; compile with
XeLaTeX in Overleaf, or with Tectonic. It requires no external figure files
or bibliography. Its textual cover is equivalent to the ReportLab cover of
the distributed PDF. The detailed mathematical body is produced from that
same standalone source.

The family Markdown files and coverage records are the editable working
sources. `build_review.py` assembles them and verifies coverage and source
hashes. It does not check mathematical truth. The recorded successful Lean
build is the preexisting pinned receipt in `../evidence/verification.json`;
no new Lean build was necessary for this documentation-only task.

Document tools used: Pandoc 3.6.4, Tectonic 0.15.0, ReportLab, pypdf,
pdfplumber, and Poppler raster rendering. The mathematical body was compiled
without overfull boxes, missing glyphs, or unresolved-reference warnings.
Ordinary underfull paragraph warnings are typography diagnostics, not
mathematical verification failures. `finish_pdf.py` replaces only the cover
while preserving mathematical pages, named destinations and bookmarks.
