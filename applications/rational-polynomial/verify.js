"use strict";
// Checks archive identity and executable construction steps, not prose proofs.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const zlib = require("node:zlib");
const assert = require("node:assert/strict");
const { execFileSync } = require("node:child_process");
const dir = path.join(__dirname, "artifacts");
const hash = b => crypto.createHash("sha256").update(b).digest("hex");
const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, "package-manifest.json")));
assert.equal(manifest.format, "k215-rational-polynomial-distribution-v1");
assert(process.argv.slice(2).every(a => a === "--prepare-only"), "Only --prepare-only is supported");
const names = new Set();
for (const f of manifest.files) {
  assert(/^[a-zA-Z0-9_.-]+$/.test(f.name) && f.name !== "." && f.name !== "..");
  assert(!names.has(f.name), "Duplicate artifact name"); names.add(f.name);
  assert(f.storedName === f.name || f.storedName === f.name + ".gz");
  assert(Number.isSafeInteger(f.bytes) && f.bytes > 0);
  const stored = fs.readFileSync(path.join(dir, f.storedName));
  assert.equal(stored.length, f.storedBytes, f.storedName);
  assert.equal(hash(stored), f.storedSHA256, f.storedName);
  const b = f.storedName === f.name ? stored : zlib.gunzipSync(stored, {maxOutputLength:f.bytes});
  assert.equal(b.length, f.bytes, f.name);
  assert.equal(hash(b), f.sha256, f.name);
  if (f.storedName !== f.name) {
    const dest = path.join(dir, f.name);
    if (fs.existsSync(dest)) assert.equal(hash(fs.readFileSync(dest)), f.sha256, "Existing artifact differs: " + f.name);
    else fs.writeFileSync(dest, b, {flag:"wx"});
  }
}
// The publication manifest also contains every file bound by both original
// manifests. Check this relationship independently of the executable checks.
for (const name of ["universal-rational-proof-manifest.json", "zfc-inconsistency-manifest.json"]) {
  const inner = JSON.parse(fs.readFileSync(path.join(dir, name)));
  for (const f of inner.files) {
    const outer = manifest.files.find(g => g.name === f.name);
    assert(outer, "Missing dependency: " + f.name);
    assert.equal(outer.bytes, f.bytes); assert.equal(outer.sha256, f.sha256);
  }
}
assert.equal(manifest.polynomialSHA256, hash(fs.readFileSync(path.join(dir, "zfc-inconsistency-polynomial.json"))));
console.log(`Prepared and hash-checked ${manifest.files.length} artifacts.`);
if (!process.argv.includes("--prepare-only")) {
  for (const script of ["verify-k215-specialization.js", "verify-universal-proof-package.js"]) {
    execFileSync(process.execPath, [path.join(dir, script)], {cwd:dir, stdio:"inherit"});
  }
  for (const f of manifest.files) assert.equal(hash(fs.readFileSync(path.join(dir, f.name))), f.sha256, "Check changed a bound artifact: " + f.name);
  console.log("Construction and package checks passed. Written arithmetic proofs are not checked by this command.");
}
