"use strict";
// Integrity and polynomial-assembly checks. This is not a proof checker.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const assert = require("node:assert/strict");
const { auditBundle, readInputs } = require("./audit-rational-expression.js");
const expectedSHA = "be7347c439459759121cda9656eda501afd75ca48897aa0f0acf5f85f6a43b1f";
const digest = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const read = name => fs.readFileSync(path.join(__dirname, name));
const json = name => JSON.parse(read(name));

function verify() {
  const manifest = json("universal-rational-proof-manifest.json");
  assert.equal(manifest.format, "universal-rational-proof-package-v1");
  assert.equal(manifest.polynomial.sha256, expectedSHA);
  assert.equal(manifest.polynomial.witnessCount, 878664928321);
  const files = new Map();
  for (const entry of manifest.files) {
    assert.equal(path.basename(entry.name), entry.name, "Unexpected manifest path");
    assert(!files.has(entry.name), "Duplicate manifest file");
    const bytes = read(entry.name);
    assert.equal(bytes.length, entry.bytes, `Size changed: ${entry.name}`);
    assert.equal(digest(bytes), entry.sha256, `Hash changed: ${entry.name}`);
    files.set(entry.name, entry);
  }
  for (const group of manifest.evidenceGroups) {
    for (const name of group.files) assert(files.has(name), `Unbound evidence: ${name}`);
  }
  let bindings = 0;
  for (const name of manifest.bindingReports) {
    const report = json(name);
    assert.equal(report.passed, true, `Failed binding report: ${name}`);
    for (const item of report.bindings) {
      const entry = files.get(item.name);
      assert(entry, `Binding absent from manifest: ${item.name}`);
      assert.equal(entry.sha256, item.sha256, `Stale report: ${name}: ${item.name}`);
      assert.equal(entry.bytes, item.bytes, `Stale size: ${name}: ${item.name}`);
      bindings++;
    }
  }
  const bytes = read("universal-rational-equation.json");
  assert.equal(digest(bytes), expectedSHA);
  const bundle = JSON.parse(bytes);
  assert.deepEqual(bundle.parameterNames, ["e", "n"]);
  assert.equal(bundle.parameterDomain, "ordinary nonnegative integers");
  assert.equal(bundle.witnessDomain, "rational numbers");
  const { sources, baseModel } = readInputs();
  const assembly = auditBundle(bundle, sources, { templates: baseModel });
  const savedAssembly = json("universal-rational-expression-audit.json");
  assert.equal(savedAssembly.expressionSHA256, expectedSHA);
  delete savedAssembly.expressionSHA256;
  assert.deepEqual(assembly, savedAssembly, "Assembly report is stale");
  assert.equal(assembly.witnessCount, 878664928321);
  assert.equal(assembly.variableCount, assembly.witnessCount + 2);
  const height = json("height-constant-binding-checks.json");
  assert.equal(height.passed, true);
  assert.equal(height.candidateSha256, expectedSHA);
  assert.equal(height.heightProofSha256, files.get("six-contact-height-proof.txt").sha256);
  const mutation = json("rational-expression-audit-checks.json");
  assert.equal(mutation.passed, true);
  assert.equal(mutation.fullAuditPassed, true);
  assert.equal(mutation.mutationsRejected.length, 9);
  const schur = json("determinant-schur-checks.json");
  assert.equal(schur.passed, true);
  assert.equal(schur.cases, 72);
  const result = {
    date: "2026-11-03",
    integrityPassed: true,
    fullAssemblyRechecked: true,
    boundFiles: files.size,
    checkedReportBindings: bindings,
    candidateSHA256: expectedSHA,
    witnessCount: assembly.witnessCount,
    totalVariableCount: assembly.variableCount,
    mathematicalProofCheckedByThisScript: false,
    scope: "File integrity, source bindings and full polynomial assembly. The written mathematical review is the separate completion audit; this script does not prove arithmetic lemmas."
  };
  fs.writeFileSync(path.join(__dirname, "proof-package-integrity-checks.json"), JSON.stringify(result, null, 2) + "\n");
  return result;
}
module.exports = { verify };
if (require.main === module) console.log(JSON.stringify(verify(), null, 2));
