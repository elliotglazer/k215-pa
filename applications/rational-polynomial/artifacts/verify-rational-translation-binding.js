"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {buildUniversalExpression}=require("./rational-circuit-translator.js");
const read=name=>fs.readFileSync(path.join(__dirname,name));
const hash=data=>crypto.createHash("sha256").update(data).digest("hex");
const check=(ok,message)=>{if(!ok)throw Error(message);};

function checkPrivateBlocks(source,name){
  const blocks=new Map(),explicit=new Set(source.variables.map(v=>v.index));
  for(const block of source.witnessBlocks){
    check(!blocks.has(block.start),name+": repeated private block");
    check(block.length===79&&block.template===0,name+": changed power block");
    blocks.set(block.start,{...block,uses:0});
    for(let i=block.start;i<block.start+block.length;i++)
      check(!explicit.has(i),name+": private witness is also an explicit variable");
  }
  for(const node of source.nodes){
    if(node.op==="var")check(explicit.has(node.args[0]),name+": escaped private witness");
    if(node.op==="call"){
      const block=blocks.get(node.args[4]);
      check(node.args[0]===0&&block,name+": call has no power block");
      block.uses++;
    }
  }
  for(const block of blocks.values())check(block.uses===1,name+": private block is shared or unused");
  return {name,blocks:blocks.size,eachUsedExactlyOnce:true,noParentVariableReferences:true};
}

function main(){
  const saved=read("universal-rational-equation.json");
  check(hash(saved)==="be7347c439459759121cda9656eda501afd75ca48897aa0f0acf5f85f6a43b1f","Candidate hash changed");
  const fresh=Buffer.from(JSON.stringify(buildUniversalExpression())+"\n");
  check(fresh.equals(saved),"Fresh source generation differs from the saved candidate");
  const privateScopes=["universal-integer-polynomial.json","accuracy-integer-polynomial.json"]
    .map(name=>checkPrivateBlocks(JSON.parse(read(name)),name));
  const names=["rational-circuit-translator.js","finite-polynomial-expressions.js",
    "rational-model-assembly.js","rational-elliptic-core.js","rational-polynomial-library.js",
    "elliptic-division-polynomials.js","multiplication-certificate.js","fixed-certificate-constants.js",
    "integer-diophantine-compiler.js","universal-rational-equation.json",
    "integer-halting-correctness-proof.txt","accuracy-correctness-proof.txt",
    "rational-universality-conditional-proof.txt","multiplication-certificate-correctness-proof.txt"];
  const bindings=names.map(name=>{const bytes=read(name);return {name,bytes:bytes.length,sha256:hash(bytes)};});
  const report={date:"2026-11-03",passed:true,freshGenerationMatchesEveryByte:true,privateScopes,bindings,
    scope:"Source/artifact binding and private witness scope. Arithmetic exactness of the multiplication template remains a separate mathematical obligation."};
  fs.writeFileSync(path.join(__dirname,"rational-translation-binding-checks.json"),JSON.stringify(report,null,2)+"\n");
  console.log(JSON.stringify(report,null,2));
}
if(require.main===module)main();
module.exports={main,checkPrivateBlocks};
