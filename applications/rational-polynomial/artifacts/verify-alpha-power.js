"use strict";
// Construct full natural witness assignments for the actual polynomial macros.
// This checks execution/transcription; the general equivalence is an AFP input.
const fs=require("node:fs");
const path=require("node:path");
const crypto=require("node:crypto");
const {Builder,evaluateCircuit}=require("./integer-diophantine-compiler.js");
const check=(ok,message)=>{if(!ok)throw Error(message);};
function alpha(b,n){
  let x=0n,y=1n;
  for(let i=0n;i<n;i++)[x,y]=[y,b*y-x];
  return x;
}
function egcd(a,b){
  let x=1n,y=0n;
  while(b){const q=a/b;[a,b]=[b,a-q*b];[x,y]=[y,x-q*y];}
  return [a,x];
}
const mod=(a,m)=>(a%m+m)%m;
function alphaWitnesses(b,n){
  check(b>3n&&n>=0n,"alpha domain");
  const X=alpha(b,n);
  let k=1n,u=alpha(b,k);
  while(u<=2n*X||u<=2n*n||u%2n===0n){k++;u=alpha(b,k);}
  const t=alpha(b,k+1n),m=k*u;
  const s=alpha(b,m),r=alpha(b,m-1n),v=b*s-2n*r;
  check(s%(u*u)===0n,"Lucas divisibility in witness construction");
  const [g,inv]=egcd(v,u);
  check(g===1n,"CRT coprimality");
  // w=b+v*j solves both congruences; the extra period makes w>2.
  const w=b+v*mod((2n-b)*inv,u)+u*v;
  const x=alpha(w,n),y=alpha(w,n+1n);
  return {X,values:[r,s,t,u,v,w,x,y],k,m};
}
class WitnessBuilder extends Builder{
  constructor(names){super(names);this.helpers=[];this.alphaCalls=[];this.powerCalls=[];}
  lt(a,b){const start=this.variables.length;const f=super.lt(a,b);this.helpers.push({type:"lt",a,b,start});return f;}
  divides(a,b){const start=this.variables.length;const f=super.divides(a,b);this.helpers.push({type:"divides",a,b,start});return f;}
  congruent(a,m,b){const start=this.variables.length;const f=super.congruent(a,m,b);this.helpers.push({type:"congruent",a,b,m,start});return f;}
  alpha(X,B,N){const start=this.variables.length;const f=super.alpha(X,B,N);this.alphaCalls.push({X,B,N,start});return f;}
  power(P,Q,R){const start=this.variables.length;const f=super.power(P,Q,R);this.powerCalls.push({P,Q,R,start});return f;}
}
function nodeValue(b,assignment,id){
  const n=b.nodes[id];
  if(n.op==="const")return BigInt(n.args[0]);
  if(n.op==="var")return assignment[n.args[0]];
  const a=nodeValue(b,assignment,n.args[0]),c=nodeValue(b,assignment,n.args[1]);
  return n.op==="add"?a+c:a*c;
}
function helperWitnesses(b,assignment){
  for(const h of b.helpers){
    const a=nodeValue(b,assignment,h.a),v=nodeValue(b,assignment,h.b);
    if(h.type==="lt")assignment[h.start]=v>a?v-a-1n:0n;
    else if(h.type==="divides")assignment[h.start]=a!==0n&&v%a===0n?v/a:0n;
    else{
      const m=nodeValue(b,assignment,h.m),delta=v-a;
      if(m!==0n&&delta%m===0n){
        if(delta>=0n)assignment[h.start]=delta/m;
        else assignment[h.start+1]=-delta/m;
      }
    }
  }
}
function runCase(kind,base,index){
  const result=kind==="alpha"?alpha(base,index):base**index;
  const b=new WitnessBuilder(["result","base","index"]);
  const f=kind==="alpha"?b.alpha(...b.inputs):b.power(...b.inputs);
  const artifact=b.artifact(f),assignment=Array(artifact.variables.length).fill(0n);
  assignment[0]=result;assignment[1]=base;assignment[2]=index;
  if(kind==="power"&&base>0n){
    const a0=alpha(base+4n,index+1n),parameter=a0+base*base+2n;
    const m=parameter*base-base*base-1n;
    const vals=[parameter,m,a0,alpha(parameter,index),alpha(parameter,index+1n)];
    vals.forEach((x,i)=>assignment[b.powerCalls[0].start+i]=x);
  }
  let maxLucasIndex=0n;
  if(kind==="alpha"||base>0n)for(const call of b.alphaCalls){
    const aw=alphaWitnesses(nodeValue(b,assignment,call.B),nodeValue(b,assignment,call.N));
    check(nodeValue(b,assignment,call.X)===aw.X,"alpha call result binding");
    aw.values.forEach((x,i)=>assignment[call.start+i]=x);
    if(aw.m>maxLucasIndex)maxLucasIndex=aw.m;
  }
  helperWitnesses(b,assignment);
  check(assignment.every(x=>x>=0n),"negative witness");
  check(evaluateCircuit(artifact,assignment)===0n,"constructed assignment is not a polynomial zero");
  const wrong=assignment.slice();wrong[0]++;
  check(evaluateCircuit(artifact,wrong)!==0n,"changed result still vanishes");
  return {kind,base:String(base),index:String(index),result:String(result),
    variables:artifact.variables.length,nodes:artifact.nodes.length,
    largestWitnessDigits:Math.max(...assignment.map(x=>x.toString().length)),
    maxLucasIndex:String(maxLucasIndex),assignment:assignment.map(String)};
}
function main(){
  const cases=[];
  for(const [b,n] of [[4n,0n],[4n,1n],[4n,2n],[4n,3n],[5n,2n],[7n,1n]])cases.push(runCase("alpha",b,n));
  for(const [b,n] of [[0n,0n],[0n,1n],[0n,3n],[1n,0n],[2n,0n],[1n,1n],[2n,1n]])cases.push(runCase("power",b,n));
  const root=path.resolve(__dirname,".."),tree=JSON.parse(fs.readFileSync(path.join(root,"work/afp-diophantine-tree.json")));
  const sources=["Alpha_Sequence.thy","Exponential_Relation.thy","Exponentiation.thy"].map(name=>{
    const bytes=fs.readFileSync(path.join(root,"work",name)),record=tree.find(x=>x.name===name);
    const blob=crypto.createHash("sha1").update(Buffer.from(`blob ${bytes.length}\0`)).update(bytes).digest("hex");
    check(blob===record.sha,"downloaded source differs from API blob: "+name);
    return {name,gitBlob:blob,sha256:crypto.createHash("sha256").update(bytes).digest("hex"),url:record.html_url};
  });
  const report={passed:true,alphaCases:6,powerCases:7,changedResultCases:13,sources,
    cases:cases.map(({assignment,...rest})=>rest),
    limitations:["Finite witness checks do not prove soundness for all assignments.",
      "General equivalence uses the cited AFP theorems and the written compiler proof.",
      "All variables here range over natural numbers, not arbitrary rationals."]};
  fs.writeFileSync(path.join(__dirname,"alpha-power-witnesses.json"),JSON.stringify({cases},null,2)+"\n");
  fs.writeFileSync(path.join(__dirname,"alpha-power-checks.json"),JSON.stringify(report,null,2)+"\n");
  console.log(JSON.stringify(report,null,2));
}
if(require.main===module)main();
module.exports={alpha,alphaWitnesses,runCase};
