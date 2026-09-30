"""Create the ReportLab review cover and retain the LaTeX mathematical body.

Requires reportlab, pypdf, pdfplumber and Pillow. Does not edit Lean sources.
The separately supplied standalone TeX has an equivalent textual cover.
"""
from pathlib import Path
import hashlib
import json
from reportlab.pdfgen import canvas
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from pypdf import PdfReader, PdfWriter
from pypdf.generic import NameObject, ArrayObject
import pdfplumber

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
TMP = REPO / 'tmp/pdfs/chow_lu_review'
OUT = REPO / 'output/pdf'
OUT.mkdir(parents=True, exist_ok=True)
STEM = 'geometrization_skeleton_mathematical_review'
fonts = Path('/System/Library/Fonts/Supplemental')
pdfmetrics.registerFont(TTFont('ReviewSans', str(fonts / 'Arial.ttf')))
pdfmetrics.registerFont(TTFont('ReviewSansBold', str(fonts / 'Arial Bold.ttf')))
cover = TMP / 'cover.pdf'
c = canvas.Canvas(str(cover), pagesize=(612, 792))
navy, gray = HexColor('#17364D'), HexColor('#52616B')
def line(text, y, size=11, bold=False, color=navy):
    c.setFillColor(color)
    c.setFont('ReviewSansBold' if bold else 'ReviewSans', size)
    c.drawString(57, y, text)

line('BLUEPRINT 207 / FROZEN LEAN SKELETON', 725, 10, color=gray)
c.setStrokeColor(navy)
c.setLineWidth(1.2)
c.line(57, 703, 555, 703)
line('Geometrization in Lean', 638, 31, True)
line('Mathematical reading of the skeleton', 600, 21)
line('Review copy for Bennett Chow and Peng Lu', 549, 15)
line('121 authored declarations  /  17 admitted theorems', 465, 13, True)
line('Six admissions occur in the main endpoint proof.', 440, 12)
for i, text in enumerate([
    'An exact reading of the definitions, statements and written assembly proofs,',
    'with assumptions, quantifier order, corner cases and omitted conclusions.',
    '',
    'Includes a source-linked declaration register and a joint-review worksheet.',
    'No Lean mathematical source was changed for this review.',
]):
    line(text, 376 - 22 * i, 11, color=gray)
c.setStrokeColor(HexColor('#C9D3DA'))
c.setLineWidth(0.5)
c.line(57, 192, 555, 192)
line('Frozen source commit', 169, 10, color=gray)
line('ea0fae60ee01ef8c8d9b57a51794c6538f679c5d', 151, 10)
line('Private branch: codex/geometrization-blueprint-skeleton-207', 121, 10)
line('Statements awaiting mathematical review; not a proof-complete formalization.', 72, 10, color=gray)
c.save()

body = PdfReader(str(TMP / (STEM + '.pdf')))
writer = PdfWriter()
writer.clone_document_from_reader(body)
# Replace only cover content, preserving body page indices, destinations and outlines.
writer.pages[0][NameObject('/Contents')] = ArrayObject()
writer.pages[0].merge_page(PdfReader(str(cover)).pages[0])
writer.add_metadata({'/Title': 'Geometrization in Lean: mathematical reading of the skeleton',
                     '/Author': 'Prepared for Bennett Chow and Peng Lu',
                     '/Subject': 'Frozen Blueprint 207 skeleton; statements and admissions for mathematical review'})
target = OUT / (STEM + '.pdf')
with target.open('wb') as f:
    writer.write(f)

# Geometric bounds flag clipped text on any page; visual QA remains required.
outside = []
replacement_chars = []
with pdfplumber.open(target) as pdf:
    for i, p in enumerate(pdf.pages, 1):
        for ch in p.chars:
            if ch['x0'] < 24 or ch['x1'] > p.width - 24 or ch['top'] < 16 or ch['bottom'] > p.height - 16:
                outside.append({'page': i, 'text': ch['text'], 'bbox': [ch['x0'], ch['top'], ch['x1'], ch['bottom']]})
            if '\ufffd' in ch['text'] or '\u25a0' in ch['text']:
                replacement_chars.append({'page': i, 'text': ch['text']})
    pages = len(pdf.pages)
record = dict(pdf=str(target.relative_to(REPO)), pages=pages,
    pdf_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
    standalone_tex_sha256=hashlib.sha256((HERE / (STEM + '.tex')).read_bytes()).hexdigest(),
    outer_page_bounds_violations=outside, replacement_glyphs=replacement_chars,
    visual_inspection='Recorded separately after raster inspection; bounds alone do not certify layout.')
(HERE / 'pdf_verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'Created {pages}-page PDF; {len(outside)} outer-bound violations; {len(replacement_chars)} replacement glyphs.')
assert not outside and not replacement_chars
