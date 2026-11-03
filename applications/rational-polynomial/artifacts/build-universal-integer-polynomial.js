"use strict";
const fs=require("node:fs"),path=require("node:path");
const {compileRegisterMachine}=require("./integer-diophantine-compiler.js");
const {compileHierarchical,evaluateHierarchical,expansionHash,auditStructure}=require("./hierarchical-integer-compiler.js");
const {buildUniversalInterpreter}=require("./universal-interpreter.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
const tests=[
 {p:[{op:"sub",register:0,nonzero:0,zero:1},{op:"halt"}],r:1,inputs:["a"]},
 {p:[{op:"sub",register:0,nonzero:0,zero:1},{op:"sub",register:1,nonzero:1,zero:2},{op:"halt"}],r:2,inputs:["a","b"]}
];
const checks=[];
for(const t of tests){
 const flat=compileRegisterMachine(t.p,t.r,t.inputs),compact=compileHierarchical(t.p,t.r,t.inputs);
 assert(flat.variables.length===compact.variableCount,"variable numbering");
 const hf=expansionHash(flat),hc=expansionHash(compact);assert(hf===hc,"substitution changed polynomial");
 for(let seed=0;seed<3;seed++){
  const assignment=Array.from({length:compact.variableCount},(_,j)=>(j+seed)%2);
  assert(evaluateHierarchical(flat,assignment)===evaluateHierarchical(compact,assignment),"evaluation");
 }
 checks.push({...auditStructure(compact),expansionHash:hf});
}
const machine=buildUniversalInterpreter();
const universal=compileHierarchical(machine.program,machine.registers,machine.inputNames);
const summary=auditStructure(universal);
assert(summary.variables===1305804,"unexpected universal variable count");
const output=path.join(__dirname,"universal-integer-polynomial.json");
fs.writeFileSync(output,JSON.stringify(universal)+"\n");
const reread=JSON.parse(fs.readFileSync(output,"utf8"));assert(auditStructure(reread).valid,"saved circuit invalid");
const report={passed:true,smallPolynomialEqualityChecks:checks,universal:summary,
 bytes:fs.statSync(output).size,domain:"All quantified variables are natural numbers.",
 limitation:"This is not yet the requested rational polynomial."};
fs.writeFileSync(path.join(__dirname,"hierarchical-compiler-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

