"use strict";
const fs = require("node:fs"), path = require("node:path"), crypto = require("node:crypto");
const assert = require("node:assert/strict");
const { encodeProgram, decodeHeader } = require("./universal-interpreter.js");
const REVISION = "c16fb4c751b27f03233929ec56135f32f342dfed";
const TM_SHA = "175a704301df3887f75e4d7ecbd3b7a15b0423dae39758797d578e751732d4c5";
const U_SHA = "be7347c439459759121cda9656eda501afd75ca48897aa0f0acf5f85f6a43b1f";
const hash = x => crypto.createHash("sha256").update(x).digest("hex");
const write = (name, obj) => fs.writeFileSync(path.join(__dirname, name), JSON.stringify(obj, null, 2) + "\n");

// Parse the entire restricted expression grammar used by all 22 blocks.
// This deliberately refuses an unfamiliar expression rather than ignoring it.
function parseTable(text) {
  assert.equal(hash(Buffer.from(text)), TM_SHA, "Unexpected literal-machine specification");
  for (let n = 10; n <= 215; n++) {
    const prev = n === 10 ? "9" : `k215Num${n - 1}`;
    assert(text.includes(`def k215Num${n}: nat = $ suc ${prev} $;`));
  }
  const blocks = new Map();
  for (const m of text.matchAll(/def k215TMActionBlock(\d+) \(q b: nat\): nat = \$([\s\S]*?)\$;/g)) {
    const toks = m[2].match(/k215TMActionBlock\d+|k215Num\d+|if|q|b|\d+|[(),=]/g);
    assert.equal(toks.join(""), m[2].replace(/\s+/g, ""));
    let i = 0;
    const eat = t => { assert.equal(toks[i++], t); };
    const num = () => {
      const t = toks[i++]; assert(/^(?:k215Num)?\d+$/.test(t));
      return Number(t.replace("k215Num", ""));
    };
    function expression() {
      eat("("); let node;
      if (toks[i] === "if") {
        eat("if"); eat("("); const v = toks[i++]; assert(["q", "b"].includes(v));
        eat("="); const n = num(); eat(")");
        node = { type: "if", v, n, yes: expression(), no: expression() };
      } else if (/^k215TMActionBlock/.test(toks[i])) {
        const k = Number(toks[i++].replace("k215TMActionBlock", ""));
        eat("q"); eat("b"); node = { type: "block", k };
      } else {
        const w = num(); eat(","); const d = num(); eat(","); const target = num();
        assert([0, 1].includes(w) && [0, 1].includes(d) && target <= 215);
        node = { type: "action", value: [w, d, target] };
      }
      eat(")"); return node;
    }
    const node = expression(); assert.equal(i, toks.length);
    const k = Number(m[1]); assert(!blocks.has(k)); blocks.set(k, node);
  }
  assert.equal(blocks.size, 22);
  assert(text.includes("def k215TMAction (q b: nat): nat = $ k215TMActionBlock0 q b $;"));
  function evaluate(node, q, b, active = new Set()) {
    if (node.type === "action") return node.value;
    if (node.type === "if") return evaluate((node.v === "q" ? q : b) === node.n ? node.yes : node.no, q, b, active);
    assert(blocks.has(node.k) && !active.has(node.k), "Invalid block reference");
    return evaluate(blocks.get(node.k), q, b, new Set([...active, node.k]));
  }
  return Array.from({ length: 215 }, (_, q) => [0, 1].map(b => evaluate(blocks.get(0), q, b)));
}

class TapeCompiler {
  constructor() { this.program = []; this.labels = new Map(); this.serial = 0; }
  fresh() { return `m${this.serial++}`; }
  at(label) { assert(!this.labels.has(label)); this.labels.set(label, this.program.length); }
  sub(register, nonzero, zero) { this.program.push({ op: "sub", register, nonzero, zero }); }
  inc(register) { this.program.push({ op: "add", register, next: this.program.length + 1 }); }
  jump(target) { this.sub(3, target, target); }
  // Precondition T=0. Replace x by k*x+c, restoring T=0.
  scale(x, k, c) {
    const loop = this.fresh(), body = this.fresh(), restore = this.fresh(), put = this.fresh(), end = this.fresh();
    this.at(loop); this.sub(x, body, restore);
    this.at(body); for (let j = 0; j < k; j++) this.inc(2); this.jump(loop);
    this.at(restore); this.sub(2, put, end);
    this.at(put); this.inc(x); this.jump(restore);
    this.at(end); for (let j = 0; j < c; j++) this.inc(x);
  }
  // Precondition T=0. Replace x by floor(x/2), restoring T=0,
  // and branch on the original remainder. No other tape register changes.
  pop(x, evenTarget, oddTarget) {
    const loop = this.fresh(), first = this.fresh(), pair = this.fresh();
    const even = this.fresh(), odd = this.fresh();
    this.at(loop); this.sub(x, first, even);
    this.at(first); this.sub(x, pair, odd);
    this.at(pair); this.inc(2); this.jump(loop);
    for (const [start, target] of [[even, evenTarget], [odd, oddTarget]]) {
      const put = this.fresh(), done = this.fresh();
      this.at(start); this.sub(2, put, done);
      this.at(put); this.inc(x); this.jump(start);
      this.at(done); this.jump(target);
    }
  }
  compile(table) {
    for (let q = 0; q < table.length; q++) {
      // Keep state entries distinct from the pop macro's internal loop.
      // Every visit to q_i then denotes a complete simulated transition.
      this.at(`q${q}`);
      const entry = this.fresh(); this.jump(entry); this.at(entry);
      this.pop(1, `a${q}_0`, `a${q}_1`);
      for (let b = 0; b < 2; b++) {
        this.at(`a${q}_${b}`);
        const [w, d, target] = table[q][b];
        if (d === 1) { this.scale(0, 2, w); this.jump(`q${target}`); }
        else {
          this.scale(1, 4, 2 * w);
          const even = this.fresh(), odd = this.fresh();
          this.pop(0, even, odd);
          this.at(even); this.jump(`q${target}`);
          this.at(odd); this.inc(1); this.jump(`q${target}`);
        }
      }
    }
    this.at(`q${table.length}`); this.program.push({ op: "halt" });
    const resolve = t => typeof t === "number" ? t : this.labels.get(t);
    const program = this.program.map(ins => {
      if (ins.op === "halt") return ins;
      const out = { ...ins };
      for (const field of ins.op === "add" ? ["next"] : ["nonzero", "zero"]) {
        out[field] = resolve(out[field]);
        assert(Number.isInteger(out[field]) && out[field] >= 0 && out[field] < this.program.length);
      }
      return out;
    });
    return { format: "k215-register-simulation-v1", registers: 4,
      registerNames: ["L", "R", "temporary", "zero"], input: "register 0 = 0; all others = 0",
      boundaryStates: Array.from({ length: table.length + 1 }, (_, q) => this.labels.get(`q${q}`)), program };
  }
}

function build() {
  const bundle = JSON.parse(fs.readFileSync(path.join(__dirname, "k215-source-specification.json")));
  assert.equal(bundle.revision, REVISION);
  const literal = bundle.files.find(f => f.path === "pa-mm0/k215_literal_tm.mm0");
  assert.equal(literal.sha256, TM_SHA);
  const table = parseTable(literal.text);
  write("k215-transition-table.json", { revision: REVISION, sourceSHA256: TM_SHA,
    states: 215, alphabet: [0, 1], initialState: 0, blank: 0, haltState: 215,
    entryMeaning: "[written bit, direction (0=left,1=right), next state]", table });
  const machine = new TapeCompiler().compile(table);
  write("k215-register-program.json", machine);
  const code = encodeProgram(machine.program), decimal = code.toString(), hexadecimal = code.toString(16);
  fs.writeFileSync(path.join(__dirname, "k215-program-code.txt"), decimal + "\n");
  fs.writeFileSync(path.join(__dirname, "k215-program-code.hex"), hexadecimal + "\n");
  const bytes = fs.readFileSync(path.join(__dirname, "universal-rational-equation.json"));
  assert.equal(hash(bytes), U_SHA);
  const universal = JSON.parse(bytes), N = universal.witnessCount;
  const polynomial = {
    format: "integer-parameter-specialization-of-rational-polynomial-v1",
    name: "ZFC inconsistency polynomial from K215",
    variableCount: N, variableDomain: "Q", coefficientRing: "Z", parameterNames: [],
    definingOperation: "literal-polynomial-substitution",
    definition: "P(w_1,...,w_N)=U(e_K215,0,w_1,...,w_N)",
    semantics: "Interpret sourcePolynomial by its included polynomial expression rules. In its root recipe replace local variable 0 by substitutions[0].integer and local variable 1 by substitutions[1].integer. Replace its local variable j+2 by the free variable w_(j+1). Expand by finite polynomial substitution. No additional equations or existential variables are introduced.",
    substitutions: [{ parameter: "e", integer: decimal }, { parameter: "n", integer: "0" }],
    sourcePolynomialSHA256: U_SHA, sourcePolynomial: universal,
    provenance: { machineRepository: "https://github.com/elliotglazer/k215-pa", revision: REVISION,
      literalMachineSHA256: TM_SHA, theorem: "K215_halts_iff_ZFC_inconsistent_final",
      interpretation: "A rational zero exists iff the pinned K215 machine halts on blank tape, hence iff the pinned arithmetized ZFC proof predicate proves falsity.",
      proofStatus: "Uses the existing written universality proof and the upstream MM0 theorem. The complete MM0 proof binary was not rechecked locally." }
  };
  // Compact, retaining all source definitions. This file is independently usable.
  const polyBytes = Buffer.from(JSON.stringify(polynomial) + "\n");
  fs.writeFileSync(path.join(__dirname, "zfc-inconsistency-polynomial.json"), polyBytes);
  const report = { revision: REVISION, literalMachineSHA256: TM_SHA, transitions: 430,
    registers: machine.registers, registerInstructions: machine.program.length,
    programCodeBits: code.toString(2).length, programCodeDecimalDigits: decimal.length,
    programFieldWidth: decodeHeader(code).width, variableCount: N,
    polynomialBytes: polyBytes.length, polynomialSHA256: hash(polyBytes), sourcePolynomialSHA256: U_SHA };
  write("k215-specialization-build.json", report); return report;
}
module.exports = { parseTable, TapeCompiler, build, hash, REVISION, TM_SHA, U_SHA };
if (require.main === module) console.log(JSON.stringify(build(), null, 2));
