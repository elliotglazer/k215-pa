"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {buildAccuracyIR,lowerIR}=require("./accuracy-program.js");
const {encodeProgram}=require("./universal-interpreter.js");
const {auditStructure}=require("./hierarchical-integer-compiler.js");
const read=name=>fs.readFileSync(path.join(__dirname,name));
const json=name=>JSON.parse(read(name));
const hash=data=>crypto.createHash("sha256").update(data).digest("hex");
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const check=(ok,message)=>{if(!ok)throw Error(message);};

// Sparse polynomials for the small outer pairing expression only.
// H is an independent symbol standing for the entire old circuit root.
function add(a,b){const r=new Map(a);for(const [m,c] of b){const v=(r.get(m)||0n)+c;if(v)r.set(m,v);else r.delete(m);}return r;}
function mul(a,b){const r=new Map();for(const [m,c] of a)for(const [n,d] of b){
  const key=[...m.split(","),...n.split(",")].filter(Boolean).sort().join(",");
  const v=(r.get(key)||0n)+c*d;if(v)r.set(key,v);else r.delete(key);
}return r;}
const C=n=>new Map(BigInt(n)===0n?[]:[["",BigInt(n)]]),V=x=>new Map([[x,1n]]);
const neg=a=>mul(C(-1),a),sub=(a,b)=>add(a,neg(b)),sq=a=>mul(a,a);
const canon=p=>JSON.stringify([...p].sort(([a],[b])=>a.localeCompare(b)).map(([m,c])=>[m,String(c)]));

function main(){
  const ir=buildAccuracyIR(),machine=lowerIR(ir);
  check(same(ir,json("accuracy-program-ir.json")),"Saved IR differs from its source");
  check(same(machine,json("accuracy-register-program.json")),"Saved primitive program differs from lowering");
  const code=encodeProgram(machine.program),hex=read("accuracy-program-code.hex").toString().trim();
  check(code===BigInt("0x"+hex),"Program code differs from the fresh primitive program");
  const hBytes=read("universal-integer-polynomial.json"),h=JSON.parse(hBytes),a=json("accuracy-integer-polynomial.json");
  check(hash(hBytes)==="27a840c06c68bfae88da84a934d6e7f0ca2778dd3e56ec2bf3b4d4eb8171fe04","Natural halting theorem binding changed");
  const codeDecimal=String(code),shift=i=>i===1?4:i+3;
  h.nodes.forEach((node,i)=>{
    const expected={op:node.op,args:node.args.slice()};
    if(node.op==="var"){
      if(node.args[0]===0){expected.op="const";expected.args=[codeDecimal];}
      else expected.args=[shift(node.args[0])];
    }else if(node.op==="call")expected.args[4]+=3;
    check(same(a.nodes[i],expected),"Old circuit changed at node "+i);
  });
  check(same(a.templates,h.templates),"Power polynomial changed");
  check(same(a.witnessBlocks,h.witnessBlocks.map(b=>({...b,start:b.start+3}))),"Private witness blocks changed");
  check(a.variableCount===h.variableCount+3,"Wrong total variable count");
  const vm=new Map(a.variables.map(v=>[v.index,v]));
  check(vm.size===a.variables.length,"Repeated explicit variable");
  for(const v of h.variables)if(v.index!==0){
    const w=vm.get(shift(v.index));check(w&&w.node===v.node&&w.kind==="witness","Old natural variable changed");
  }
  for(let i=0;i<4;i++){
    const v=vm.get(i);check(v&&v.kind===(i<3?"input":"witness"),"Pairing variable kind changed");
    check(same(a.nodes[v.node],{op:"var",args:[i]}),"Pairing variable node changed");
  }
  check(a.variables.length===h.variables.length+3,"Unexpected explicit variable");
  const memo=new Map();
  function outer(id){
    if(id===h.root)return V("H");
    if(memo.has(id))return memo.get(id);
    const node=a.nodes[id];let r;
    if(node.op==="var"&&node.args[0]<=4)r=V("v"+node.args[0]);
    else if(node.op==="const")r=C(node.args[0]);
    else if(id>=h.nodes.length&&(node.op==="add"||node.op==="mul"))
      r=(node.op==="add"?add:mul)(outer(node.args[0]),outer(node.args[1]));
    else throw Error("Unexpected dependency in pairing expression");
    memo.set(id,r);return r;
  }
  const [k,hv,j,q,u]=[0,1,2,3,4].map(i=>V("v"+i));
  const pairResidual=(z,x,y)=>sub(mul(C(2),z),add(mul(add(x,y),add(add(x,y),C(1))),mul(C(2),y)));
  const expected=add(add(sq(V("H")),sq(pairResidual(q,hv,j))),sq(pairResidual(u,k,q)));
  check(canon(outer(a.root))===canon(expected),"Pairing polynomial is not the required sum of squares");
  check(a.metadata.sourceCircuitSHA256===hash(hBytes),"Source metadata hash changed");
  check(a.metadata.programHexSHA256===hash(hex+"\n"),"Program metadata hash changed");
  const structure=auditStructure(a);
  check(structure.witnesses===1305804,"Accuracy witness count changed");

  const reductions=[];
  for(const [p,s] of [[17,6],[23,5]]){
    const mod=x=>(x%p+p)%p,d=mod(75-53*s);let count=1;
    for(let x=0;x<p;x++)for(let y=0;y<p;y++)if(mod(y*y)===mod(x*x*x-d*d*x))count++;
    reductions.push({prime:p,sqrt2:s,d,pointCount:count});
  }
  check(reductions[0].pointCount===20&&reductions[1].pointCount===24,"Torsion bound count changed");
  const fa=(x,y)=>[x[0]+y[0],x[1]+y[1]],fm=(x,y)=>[x[0]*y[0]+2n*x[1]*y[1],x[0]*y[1]+x[1]*y[0]];
  const X=[13128n,-9280n],Y=[-1979520n,1399728n],Z=[8n,0n],A=[-11243n,7950n];
  const z2=fm(Z,Z),left=fm(Y,Y),right=fa(fm(fm(X,X),X),fm(fm(A,X),fm(z2,z2)));
  check(left[0]===right[0]&&left[1]===right[1],"Initial projective point is not on E");
  const files=["accuracy-program.js","accuracy-program-ir.json","accuracy-register-program.json",
    "accuracy-program-code.hex","accuracy-integer-polynomial.json","universal-interpreter.js"];
  const bindings=files.map(name=>{const b=read(name);return {name,bytes:b.length,sha256:hash(b)};});
  const report={date:"2026-11-03",passed:true,freshIRAndLoweringMatch:true,fullProgramCodeMatches:true,
    oldCircuitNodesChecked:h.nodes.length,pairingPolynomialVerifiedSymbolically:true,structure,
    elementaryEllipticChecks:{projectivePointOnCurve:true,reductions},bindings,
    scope:"Artifact binding and finite arithmetic; the general algorithm and lowering proof is in accuracy-correctness-proof.txt."};
  fs.writeFileSync(path.join(__dirname,"accuracy-binding-checks.json"),JSON.stringify(report,null,2)+"\n");
  console.log(JSON.stringify(report,null,2));
}
if(require.main===module)main();
module.exports={main};
