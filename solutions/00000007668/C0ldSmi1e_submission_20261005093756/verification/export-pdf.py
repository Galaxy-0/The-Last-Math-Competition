from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import time

parser = argparse.ArgumentParser(description="Export matching LaTeX and render every page; native compilation is separately recorded.")
parser.add_argument("--report", type=Path, default=Path("/private/tmp/tlmc7668-report"))
parser.add_argument("--evidence", type=Path, default=Path("/private/tmp/tlmc7668-verification"))
parser.add_argument("--native-confirmation", type=Path)
parser.add_argument("--tectonic", default="/private/tmp/tlmc310-pdf/tectonic")
parser.add_argument("--poppler-dir", type=Path, default=Path("/Users/daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override"))
args = parser.parse_args()
root = args.report.resolve()
out = args.evidence.resolve()
out.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
before = sha(root / 'main.tex')
native = {'kind': 'not_invoked', 'note': 'This script does not invoke the Codex native compiler.'}
if args.native_confirmation is not None:
    native = json.loads(args.native_confirmation.read_text())
    assert native['kind'] == 'success' and native['source_sha256'] == before
command = [args.tectonic, '--outdir', str(root), str(root / 'main.tex')]
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
binroot = args.poppler_dir
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
    'native_compiler': native,
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
