"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {auditStructure}=require("./hierarchical-integer-compiler.js");
const {decodeHeader}=require("./universal-interpreter.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
const read=name=>fs.readFileSync(path.join(__dirname,name),"utf8");
const hash=s=>crypto.createHash("sha256").update(s).digest("hex");
const source=read("universal-integer-polynomial.json"),a=JSON.parse(source);
const hex=read("accuracy-program-code.hex").trim(),programCode=BigInt("0x"+hex);
const machine=JSON.parse(read("accuracy-register-program.json")),header=decodeHeader(programCode);
assert(header.width%4===0,"hex-aligned width expected for this generated program");
const fieldDigits=header.width/4,recordDigits=fieldDigits*4;
const data=header.data.toString(16).padStart(recordDigits*machine.program.length,"0");
for(let i=0;i<machine.program.length;i++){
 const start=data.length-(i+1)*recordDigits,chunk=data.slice(start,start+recordDigits);
 let rec=BigInt("0x"+chunk),fields=[];
 for(let j=0;j<4;j++){fields.push(Number(rec%header.base));rec/=header.base;}
 const x=machine.program[i],expected=x.op==="halt"?[0,0,0,0]:x.op==="add"?[1,x.register,x.next,0]:[2,x.register,x.nonzero,x.zero];
 assert(fields.every((v,j)=>v===expected[j]),"Program-code roundtrip at state "+i);
}
const oldVariables=a.variables;
for(const n of a.nodes){
 if(n.op==="var"){
  const old=n.args[0];
  if(old===0){n.op="const";n.args=[programCode.toString()];}
  else n.args=[old===1?4:old+3];
 }else if(n.op==="call")n.args[4]+=3;
}
a.witnessBlocks.forEach(b=>b.start+=3);a.variableCount+=3;
a.variables=oldVariables.filter(v=>v.index!==0).map(v=>({
 ...v,index:v.index===1?4:v.index+3,name:v.index===1?"paired_input":v.name,kind:"witness"
}));
const node=(op,args)=>{const id=a.nodes.length;a.nodes.push({op,args});return id;};
const variable=(index,name,kind)=>{const id=node("var",[index]);a.variables.push({index,name,kind,node:id});return id;};
const k=variable(0,"k","input"),h=variable(1,"h","input"),j=variable(2,"j","input"),q=variable(3,"pair_h_j","witness");
const u=a.variables.find(v=>v.index===4).node;
const plus=(x,y)=>node("add",[x,y]),times=(x,y)=>node("mul",[x,y]);
const two=node("const",["2"]),one=node("const",["1"]),minus=node("const",["-1"]);
const sub=(x,y)=>plus(x,times(minus,y)),sq=x=>times(x,x);
function pairResidual(result,x,y){
 const s=plus(x,y);return sub(times(two,result),plus(times(s,plus(s,one)),times(two,y)));
}
const originalRoot=a.root;
a.root=plus(plus(sq(originalRoot),sq(pairResidual(q,h,j))),sq(pairResidual(u,k,q)));
delete a.formulas;delete a.formula;
a.metadata={inputNames:["k","h","j"],meaning:"exact accuracy relation on natural indices",
 sourceCircuitSHA256:hash(source),programHexSHA256:hash(hex+"\n"),
 programBitLength:programCode.toString(2).length,
 composition:"H(eAccuracy,pair(k,pair(h,j)),w)=0; pairing is expressed by two quadratic equations.",
 warning:"Natural-witness circuit. It is not yet a rational Diophantine formula."};
const audit=auditStructure(a);
assert(audit.variables===1305807&&audit.witnesses===1305804,"accuracy count");
const text=JSON.stringify(a)+"\n",out=path.join(__dirname,"accuracy-integer-polynomial.json");
fs.writeFileSync(out,text);
const report={passed:true,codeRoundtripStates:machine.program.length,...audit,
 bytes:Buffer.byteLength(text),sha256:hash(text),programHexSHA256:a.metadata.programHexSHA256};
fs.writeFileSync(path.join(__dirname,"accuracy-polynomial-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

