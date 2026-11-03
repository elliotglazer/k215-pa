"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {buildUniversalInterpreter}=require("./universal-interpreter.js");
const {compileHierarchical,auditStructure}=require("./hierarchical-integer-compiler.js");
const read=name=>fs.readFileSync(path.join(__dirname,name));
const machine=buildUniversalInterpreter();
const savedMachine=JSON.parse(read("universal-interpreter-program.json"));
const saved=JSON.parse(read("universal-integer-polynomial.json"));
const fresh=compileHierarchical(machine.program,machine.registers,machine.inputNames);
const equal=JSON.stringify(saved)===JSON.stringify(fresh);
if(!equal)throw Error("Saved natural polynomial differs from current source compilation");
const programEqual=JSON.stringify(savedMachine.program)===JSON.stringify(machine.program)
  &&savedMachine.registers===machine.registers;
if(!programEqual)throw Error("Saved primitive program differs from current source");
const files=["integer-diophantine-compiler.js","hierarchical-integer-compiler.js",
  "universal-interpreter.js","universal-interpreter-program.json","universal-integer-polynomial.json"];
const bindings=files.map(name=>{const bytes=read(name);return {name,bytes:bytes.length,
  sha256:crypto.createHash("sha256").update(bytes).digest("hex")};});
const report={date:"2026-11-03",passed:true,savedPolynomialExactlyMatchesFreshCompilation:equal,
  savedPrimitiveProgramExactlyMatchesSource:programEqual,structure:auditStructure(saved),bindings,
  scope:"Exact source-to-artifact binding; semantic correctness is the separate written proof."};
fs.writeFileSync(path.join(__dirname,"integer-stage-binding-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
