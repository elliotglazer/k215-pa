"use strict";
const fs=require("node:fs"),path=require("node:path");
const {RationalBuilder,EllipticCore}=require("./rational-elliptic-core.js");
const {fixedScalarRelation}=require("./elliptic-division-polynomials.js");
const {q,qadd,qmul,qinv,P,pointMul,coordinates}=require("./rational-field-arithmetic.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
function evaluate(t,assignment){
 const values=[];for(const n of t.nodes){
  if(n.op==="const")values.push(q(n.args[0]));
  else if(n.op==="var")values.push(assignment[n.args[0]]);
  else if(n.op==="add")values.push(qadd(values[n.args[0]],values[n.args[1]]));
  else if(n.op==="mul")values.push(qmul(values[n.args[0]],values[n.args[1]]));
  else throw Error("Unexpected operation");
 }
 return {value:values[t.root],values};
}


let exactCases=0,changedXCases=0,changedYCases=0;const artifacts=[];
const pointCache=new Map();
const cp=k=>{if(!pointCache.has(k))pointCache.set(k,coordinates(pointMul(P,k)));return pointCache.get(k);};
for(const n of [0,1,2,3,4,5,6,7,8,-1,-4]){
 const b=new RationalBuilder(Array.from({length:10},(_,i)=>"p"+i)),e=new EllipticCore(b),
  t=b.artifact(fixedScalarRelation(e,b.inputs.slice(0,5),b.inputs.slice(5),n),{n});
 assert(t.variables.length===10+(n===0?0:1),"fixed witness count");
 const witness=t.variables.find(v=>v.name==="fixed_scalar.inverse_norm");
 let normNode;
 if(witness){
  for(const f of t.formulas)if(f.op==="eq"){
   const lhs=t.nodes[f.args[0]],rhs=t.nodes[f.args[1]];
   if(lhs.op==="mul"&&lhs.args.includes(witness.node)&&rhs.op==="const"&&rhs.args[0]==="1")
    normNode=lhs.args.find(i=>i!==witness.node);
  }
  assert(normNode!==undefined,"inverse guard missing");
 }
 for(const k of [-1,0,1,2]){
  const assignment=cp(k).concat(cp(n*k));
  if(witness)assignment.push(q(0));
  if(witness&&k!==0){
   const value=evaluate(t,assignment).values[normNode];assert(value[0]!==0n,"division polynomial zero on nontorsion point");
   assignment[witness.index]=qinv(value);
  }
  assert(evaluate(t,assignment).value[0]===0n,"scalar graph rejects "+n+","+k);exactCases++;
  const changedX=assignment.slice();changedX[6]=qadd(changedX[6],q(1));
  assert(evaluate(t,changedX).value[0]!==0n,"scalar graph accepts changed x");changedXCases++;
  if(n!==0&&k!==0){
   const changedY=assignment.slice();changedY[8]=[-changedY[8][0],changedY[8][1]];changedY[9]=[-changedY[9][0],changedY[9][1]];
   assert(evaluate(t,changedY).value[0]!==0n,"scalar graph accepts wrong y sign");changedYCases++;
  }
 }
 artifacts.push({n,nodes:t.nodes.length,witnesses:t.variables.length-10});
}
const report={passed:true,exactCases,changedXCases,changedYCases,artifacts,
 method:"Compare division-polynomial graph with independent affine double-and-add over Q(sqrt(2)).",
 limitation:"Finite checks supplement the classical division-polynomial identity; they do not establish the arithmetic certificate dependencies."};
fs.writeFileSync(path.join(__dirname,"division-polynomial-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

