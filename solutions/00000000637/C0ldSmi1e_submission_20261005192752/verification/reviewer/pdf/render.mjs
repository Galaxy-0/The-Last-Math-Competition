import fs from 'node:fs';
import crypto from 'node:crypto';
import {createRequire} from 'node:module';
const require=createRequire(import.meta.url);
const base='/Users/daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/';
const {createCanvas,DOMMatrix,ImageData,Path2D}=require(base+'@napi-rs/canvas');
Object.assign(globalThis,{DOMMatrix,ImageData,Path2D});
const pdfjs=await import(base+'pdfjs-dist/legacy/build/pdf.mjs');
const input='/private/tmp/tlmc637-pdf/report.pdf'; const data=fs.readFileSync(input);
const pdf=await pdfjs.getDocument({data:new Uint8Array(data),cMapUrl:base+'pdfjs-dist/cmaps/',cMapPacked:true,standardFontDataUrl:base+'pdfjs-dist/standard_fonts/',useSystemFonts:false}).promise;
const record={pdf_sha256:crypto.createHash('sha256').update(data).digest('hex'),renderer:'pdfjs-dist with bundled Adobe CMaps and @napi-rs/canvas',pages:pdf.numPages,outputs:[]};let texts=[];
for(let i=1;i<=pdf.numPages;i++) {const page=await pdf.getPage(i);const v=page.getViewport({scale:1.8});const canvas=createCanvas(Math.ceil(v.width),Math.ceil(v.height));await page.render({canvasContext:canvas.getContext('2d'),viewport:v}).promise;const p='/private/tmp/tlmc637-review/pdf/page-'+i+'.png';fs.writeFileSync(p,canvas.toBuffer('image/png'));record.outputs.push(p);texts.push((await page.getTextContent()).items.map(x=>x.str).join(' '));}
fs.writeFileSync('/private/tmp/tlmc637-review/pdf/render-record.json',JSON.stringify(record,null,2)+'\n');fs.writeFileSync('/private/tmp/tlmc637-review/pdf/report-text.txt',texts.join('\n\f\n'));console.log(JSON.stringify(record));
