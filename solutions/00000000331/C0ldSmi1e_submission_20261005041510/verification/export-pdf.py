from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import time

root = Path('/private/tmp/tlmc331-report')
out = Path('/private/tmp/tlmc331-verification')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
before = sha(root / 'main.tex')
command = ['/private/tmp/tlmc310-pdf/tectonic', '--outdir', str(root), str(root / 'main.tex')]
started = time.monotonic()
run = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=180)
raw = run.stdout + run.stderr
(root / 'export-raw.txt').write_text(raw)
normalized = '\n'.join(line.rstrip() for line in raw.splitlines()) + '\n'
(out / 'report-export.txt').write_text(normalized)
if run.returncode != 0:
    raise RuntimeError(raw)
if before != sha(root / 'main.tex'):
    raise RuntimeError('Source changed during export')
diagnostics = [line for line in raw.splitlines() if re.search(r'warning|overfull|underfull|error:', line, re.I)]
if diagnostics:
    raise RuntimeError(diagnostics)
binroot = Path('/Users/daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override')
info = subprocess.run([str(binroot / 'pdfinfo'), str(root / 'main.pdf')], capture_output=True, text=True, check=True)
(out / 'pdfinfo.txt').write_text(info.stdout)
pages = int(re.search(r'^Pages:\s+(\d+)', info.stdout, re.M).group(1))
render = [str(binroot / 'pdftoppm'), '-scale-to', '1600', '-png', str(root / 'main.pdf'), str(root / 'page')]
for previous in root.glob('page-*.png'):
    if re.fullmatch(r'page-\d+\.png', previous.name):
        previous.unlink()
rendered = subprocess.run(render, capture_output=True, text=True, check=True)
images = sorted(root.glob('page-*.png'))
if len(images) != pages:
    raise RuntimeError('Rendered page coverage differs')
record = {
    'status': 'AWAITING_VISUAL_REVIEW',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_sha256': before, 'pdf_sha256': sha(root / 'main.pdf'),
    'page_count': pages, 'pdf_bytes': (root / 'main.pdf').stat().st_size,
    'native_compiler': {'kind': 'success', 'tool': 'compile_latex_document', 'source_sha256': before},
    'export': {'command': command, 'exit_code': run.returncode,
        'elapsed_seconds': round(time.monotonic() - started, 3),
        'warnings_or_box_diagnostics': diagnostics,
        'raw_log_local_path': str(root / 'export-raw.txt'),
        'raw_log_sha256': sha(root / 'export-raw.txt'),
        'packaged_log': 'report-export.txt', 'packaged_log_sha256': sha(out / 'report-export.txt'),
        'log_normalization': 'Strip trailing whitespace on each line, preserve all line contents and order, terminate with one newline.'},
    'render': {'command': render, 'exit_code': rendered.returncode,
        'images': [{'path': str(p), 'sha256': sha(p)} for p in images]},
    'visual_review': {'status': 'PENDING'}
}
(out / 'pdf.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: record[k] for k in ['status', 'page_count', 'pdf_bytes', 'source_sha256', 'pdf_sha256']}, indent=2))
