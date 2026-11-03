"use strict";
const fs = require("node:fs"), path = require("node:path"), assert = require("node:assert/strict");
const { parseTable, TapeCompiler, hash, REVISION, TM_SHA, U_SHA } = require("./build-k215-specialization.js");
const { decodeHeader, encodeProgram } = require("./universal-interpreter.js");
const read = n => fs.readFileSync(path.join(__dirname, n));
const json = n => JSON.parse(read(n));
const src = json("k215-source-specification.json");
assert.equal(src.revision, REVISION);
const files = new Map(src.files.map(f => [f.path, f]));
assert.equal(files.size, src.files.length);
for (const f of files.values()) assert.equal(hash(Buffer.from(f.text)), f.sha256);
const source = n => { assert(files.has(n), n); return files.get(n).text; };
const entries = source("manifests/final-spec-closure.sha256").split(/\r?\n/)
  .filter(l => l && !l.startsWith("#")).map(l => l.trim().split(/\s+/));
assert.equal(entries.length, 23);
for (const [sha, name] of entries) assert.equal(hash(Buffer.from(source(name))), sha);
const closure = new Set();
function imports(name) {
  if (closure.has(name)) return;
  closure.add(name);
  const text = source(name).replace(/--[^\n]*/g, "");
  for (const m of text.matchAll(/import\s+"([^"]+)"\s*;/g)) imports(path.posix.normalize(path.posix.join(path.posix.dirname(name), m[1])));
}
imports("pa-mm0/targets/final.mm0");
assert.deepEqual([...closure].sort(), entries.map(e => e[1]).sort());
const receipt = JSON.parse(source("receipt/thm1/report.json"));
assert.equal(receipt.status, "PASSED");
assert.equal(receipt.module, "k215_final_thm1");
assert.equal(receipt.new_project_axioms, false);
assert.equal(receipt.dependency_graph_closed, true);
assert.equal(receipt.wrong_conclusion_rejected, true);
assert(receipt.checked_theorems.includes("K215_halts_iff_ZFC_inconsistent_final"));
for (const [sha, name] of entries) {
  if (name.startsWith("pa-mm0/") && name !== "pa-mm0/targets/final.mm0") {
    assert.equal(receipt.sources[name.slice(7)], sha);
    assert(!/\baxiom\b/.test(source(name).replace(/--[^\n]*/g, "")));
  }
}
for (const name of ["k215_final_thm1.mm0", "k215_final_thm1.mm1"]) {
  assert.equal(receipt.sources[name], hash(Buffer.from(source("pa-mm0/" + name))));
}
function statement(text, name) {
  const m = text.replace(/--[^\n]*/g, "").match(new RegExp("\\btheorem\\s+" + name + "\\b([^$]*)\\$([^$]*)\\$\\s*;"));
  assert(m, name); return m.slice(1).map(s => s.replace(/\s+/g, " ").trim());
}
const theorem = statement(source("pa-mm0/k215_final_thm1.mm0"), "K215_halts_iff_ZFC_inconsistent_final");
assert.deepEqual(theorem, [":", "k215LiteralHalts <-> zfcInconsistent"]);
assert.deepEqual(theorem, statement(source("pa-mm0/targets/final.mm0"), "K215_halts_iff_ZFC_inconsistent"));

const literal = source("pa-mm0/k215_literal_tm.mm0");
assert.equal(hash(Buffer.from(literal)), TM_SHA);
const table = parseTable(literal);
// Independent extraction of every (q,bit) entry checks the AST evaluation.
const direct = Array.from({ length: 215 }, () => null);
const numeral = "(?:k215Num)?(\\d+)";
const re = new RegExp("\\(if \\(q = " + numeral + "\\) \\(if \\(b = 0\\) \\((\\d), (\\d), " + numeral + "\\) \\((\\d), (\\d), " + numeral + "\\)\\)", "g");
let parsed = 0;
for (const m of literal.matchAll(re)) {
  const [q, w0, d0, t0, w1, d1, t1] = m.slice(1).map(Number);
  assert.equal(direct[q], null); direct[q] = [[w0, d0, t0], [w1, d1, t1]]; parsed++;
}
assert.equal(parsed, 215); assert.deepEqual(direct, table);
assert.deepEqual(json("k215-transition-table.json").table, table);
const machine = json("k215-register-program.json");
assert.deepEqual(machine, new TapeCompiler().compile(table));
assert.equal(machine.boundaryStates[0], 0);
assert.equal(machine.program.filter(i => i.op === "halt").length, 1);
for (const ins of machine.program) if (ins.op === "add") assert.notEqual(ins.register, 3);

const code = BigInt(read("k215-program-code.txt").toString().trim());
assert.equal(code, BigInt("0x" + read("k215-program-code.hex").toString().trim()));
assert.equal(code, encodeProgram(machine.program));
const header = decodeHeader(code), mask = header.base - 1n;
let data = header.data;
for (const ins of machine.program) {
  const fields = []; for (let j = 0; j < 4; j++) { fields.push(Number(data & mask)); data >>= BigInt(header.width); }
  const expected = ins.op === "halt" ? [0, 0, 0, 0] : ins.op === "add" ? [1, ins.register, ins.next, 0] : [2, ins.register, ins.nonzero, ins.zero];
  assert.deepEqual(fields, expected);
}
assert.equal(data, 0n);

const boundary = new Map(machine.boundaryStates.map((pc, q) => [pc, q]));
function oneStep(q, l, r, limit = 2000000) {
  let pc = machine.boundaryStates[q]; const reg = [l, r, 0n, 0n];
  for (let steps = 0; steps < limit; steps++) {
    if (steps && boundary.has(pc)) {
      assert.equal(reg[2], 0n); assert.equal(reg[3], 0n);
      return [boundary.get(pc), reg[0], reg[1]];
    }
    const ins = machine.program[pc]; assert.notEqual(ins.op, "halt");
    if (ins.op === "add") { reg[ins.register]++; pc = ins.next; }
    else if (reg[ins.register] > 0n) { reg[ins.register]--; pc = ins.nonzero; }
    else pc = ins.zero;
  }
  throw Error("Step verification exceeded explicit test budget");
}
function reference(q, l, r) {
  const [w, d, t] = direct[q][Number(r % 2n)];
  return d === 0 ? [t, l / 2n, l % 2n + 2n * BigInt(w) + 4n * (r / 2n)]
    : [t, 2n * l + BigInt(w), r / 2n];
}
let cases = 0;
const values = [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 16n, 31n];
for (let q = 0; q < 215; q++) for (const l of values) for (const r of values) {
  assert.deepEqual(oneStep(q, l, r), reference(q, l, r)); cases++;
}
// Consecutive blank-tape execution, independently checked using a cell map.
const tape = new Map(); let head = 0, q = 0, state = [0, 0n, 0n];
for (let step = 0; step < 32; step++) {
  state = oneStep(...state);
  const [w, d, t] = direct[q][tape.get(head) || 0]; tape.set(head, w); head += d ? 1 : -1; q = t;
  let l = 0n, r = 0n;
  for (const [cell, value] of tape) if (value) {
    if (cell < head) l += 1n << BigInt(head - cell - 1);
    else r += 1n << BigInt(cell - head);
  }
  assert.deepEqual(state, [q, l, r]);
}

const poly = json("zfc-inconsistency-polynomial.json");
assert.equal(poly.format, "integer-parameter-specialization-of-rational-polynomial-v1");
assert.equal(poly.definingOperation, "literal-polynomial-substitution");
assert.deepEqual(poly.parameterNames, []);
assert.deepEqual(poly.substitutions, [{ parameter: "e", integer: code.toString() }, { parameter: "n", integer: "0" }]);
assert.equal(hash(read("universal-rational-equation.json")), U_SHA);
assert.deepEqual(poly.sourcePolynomial, json("universal-rational-equation.json"));
assert.equal(poly.sourcePolynomialSHA256, U_SHA);
assert.equal(poly.variableCount, poly.sourcePolynomial.witnessCount);
const report = { passed: true, sourceRevision: REVISION, frozenSpecificationFilesChecked: 23,
  recordedMM0TheoremHasNoHypotheses: true, specificationHashesAgreeWithRecordedReceipt: true,
  fullMM0ProofRecheckedLocally: false, literalTransitionsChecked: 430,
  transitionExecutionCases: cases, independentBlankTapePrefixSteps: 32,
  everyEncodedRegisterInstructionChecked: true, registerInstructions: machine.program.length,
  parameterSubstitutionAndFullSourceEqualityChecked: true,
  programCodeBits: code.toString(2).length, programCodeDecimalDigits: code.toString().length,
  polynomialSHA256: hash(read("zfc-inconsistency-polynomial.json")), variableCount: poly.variableCount,
  limits: "Finite execution cases supplement the general loop-invariant simulation proof. The rational theorem relies on the prior written universality proof and the upstream MM0 theorem; the 4.6 GB MM0 proof was not rechecked here." };
fs.writeFileSync(path.join(__dirname, "k215-specialization-checks.json"), JSON.stringify(report, null, 2) + "\n");
console.log(JSON.stringify(report, null, 2));
