"""Record final document identity and verify the exported PDF matches its source run."""
import hashlib, json, pathlib
from pypdf import PdfReader
root=pathlib.Path('/private/tmp/tlmc545-document')
identity=json.loads(pathlib.Path('/private/tmp/tlmc545-package-location.json').read_text())
package=pathlib.Path(identity['folder'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tex=package/'report.tex'
pdf=package/'report.pdf'
export_run=root/'runs/20261005T235413.083538Z'
assert json.loads((export_run/'result.json').read_text())['exit_code']==0
assert (export_run/'stderr.txt').read_text()==''
assert (export_run/'before/package/report.tex').read_bytes()==tex.read_bytes()
assert (root/'report.tex').read_bytes()==tex.read_bytes()
assert (root/'export/report.pdf').read_bytes()==pdf.read_bytes()
native=json.loads((root/'native-compile-final.json').read_text())
assert json.loads(native['content'][0]['text'])['kind']=='success'
reader=PdfReader(pdf)
assert len(reader.pages)==5
text='\n\n'.join(f'PAGE {i+1}\n'+page.extract_text() for i,page in enumerate(reader.pages))
(root/'report-text.txt').write_text(text)
frozen=json.loads(pathlib.Path('/private/tmp/tlmc545-proof/author-freeze.json').read_text())
for name,expected in frozen['source_sha256'].items():
    assert sha(pathlib.Path('/private/tmp/tlmc545-proof')/name)==expected,name
rendered=[root/'render'/f'report-{n}.png' for n in range(1,6)]
assert all(p.exists() for p in rendered)
result={
 'status':'PASS', 'package_identity':identity,
 'source':{'path':str(tex),'sha256':sha(tex)},
 'pdf':{'path':str(pdf),'sha256':sha(pdf),'pages':5,'page_sizes_points':[list(p.mediabox) for p in reader.pages]},
 'native_compile':'success; final source; native-compile-final.json',
 'export_compile_run':str(export_run),'export_stderr':'empty; no warnings',
 'render_run':str(root/'runs/20261005T235427.366598Z'),
 'visual_inspection':'All five final page PNGs inspected: legible, aligned, unclipped; no overlaps, missing glyphs, or layout defects observed.',
 'rendered_pages':[{'path':str(p),'sha256':sha(p)} for p in rendered],
 'frozen_lean_and_configuration':'all source hashes unchanged',
 'skill_marker':'successfully run exactly once immediately before first authoring command; expected one PDF',
 'native_repairs':'one source syntax correction after first native compile failed; subsequent native compiles succeeded',
 'failed_export_attempts':'preserved: unavailable enumitem and then optional small typewriter font; removed those dependencies without installation',
 'source_and_pdf_frozen':True
}
(root/'document-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
