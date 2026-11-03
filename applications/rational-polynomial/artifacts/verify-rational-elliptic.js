"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {makeTemplates}=require("./rational-elliptic-core.js");
const {buildAccuracyIR,runIR,triple}=require("./accuracy-program.js");
const assert=(ok,msg)=>{if(!ok)throw Error(msg);};
const abs=a=>a<0n?-a:a;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a;}
function Q(a,b=1n){a=BigInt(a);b=BigInt(b);if(!b)throw Error("Zero denominator");if(b<0n){a=-a;b=-b;}const g=gcd(a,b);return [a/g,b/g];}
const qa=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const qm=(a,b)=>Q(a[0]*b[0],a[1]*b[1]);
const qi=a=>Q(a[1],a[0]);
function F(a,b=0n,c=1n){a=BigInt(a);b=BigInt(b);c=BigInt(c);if(!c)throw Error("Zero denominator");if(c<0n){a=-a;b=-b;c=-c;}const g=gcd(gcd(a,b),c);return [a/g,b/g,c/g];}
const fa=(a,b)=>F(a[0]*b[2]+b[0]*a[2],a[1]*b[2]+b[1]*a[2],a[2]*b[2]);
const fn=a=>F(-a[0],-a[1],a[2]);
const fsu=(a,b)=>fa(a,fn(b));
const fm=(a,b)=>F(a[0]*b[0]+2n*a[1]*b[1],a[0]*b[1]+a[1]*b[0],a[2]*b[2]);
const fi=a=>F(a[0]*a[2],-a[1]*a[2],a[0]*a[0]-2n*a[1]*a[1]);
const fd=(a,b)=>fm(a,fi(b));
const fk=(a,k)=>fm(a,F(k));
const fe=(a,b)=>a.every((x,i)=>x===b[i]);
const norm=a=>Q(a[0]*a[0]-2n*a[1]*a[1],a[2]*a[2]);
const coef=F(-11243,7950),half=[F(-7,5),F(-280,198)];
function plus(p,q){
 if(!p)return q;if(!q)return p;
 if(fe(p[0],q[0])&&fe(p[1],fn(q[1])))return null;
 const m=fe(p[0],q[0])?fd(fa(fk(fm(p[0],p[0]),3),coef),fk(p[1],2)):fd(fsu(q[1],p[1]),fsu(q[0],p[0]));
 const x=fsu(fsu(fm(m,m),p[0]),q[0]);return [x,fsu(fm(m,fsu(p[0],x)),p[1])];
}
const pn=p=>p?[p[0],fn(p[1])]:null;
const halves=new Map([[0,null]]),points=new Map([[0,null]]);
for(let n=1;n<=6;n++){halves.set(n,plus(halves.get(n-1),half));halves.set(-n,pn(halves.get(n)));}
for(let n=-6;n<=6;n++)points.set(n,plus(halves.get(n),halves.get(n)));
const generator=[F(1641,-1160,8),F(-123720,87483,32)];
assert(fe(points.get(1)[0],generator[0])&&fe(points.get(1)[1],generator[1]),"half generator");
const ir=buildAccuracyIR();
function readS(r,s){return r[s[0]]-r[s[1]];}
function readF(r,f){return F(readS(r,f[0]),readS(r,f[1]));}
for(let n=1;n<=6;n++){
 const run=runIR(ir,triple(1,n,n));assert(run.accepted,"IR k=1");
 const [X,Y,Z]=ir.debug.H.map(c=>readF(run.registers,c));
 const affine=[fd(X,fm(Z,Z)),fd(Y,fm(fm(Z,Z),Z))];
 assert(fe(affine[0],points.get(n)[0])&&fe(affine[1],points.get(n)[1]),"independent Jacobian comparison");
}
function putF(m,name,a){m[name+".0"]=Q(a[0],a[2]);m[name+".1"]=Q(a[1],a[2]);}
function putP(m,name,p){
 const a=p?[Q(0),Q(p[0][0],p[0][2]),Q(p[0][1],p[0][2]),Q(p[1][0],p[1][2]),Q(p[1][1],p[1][2])]:[Q(1),Q(0),Q(0),Q(0),Q(0)];
 a.forEach((v,i)=>m[name+"."+i]=v);
}
function putMember(m,name,h){
 if(!h)return;
 putF(m,name+".X",h[0]);putF(m,name+".Y",h[1]);
 putF(m,name+".slope",fd(fa(fk(fm(h[0],h[0]),3),coef),fk(h[1],2)));
 m[name+".inverse_norm_y"]=qi(norm(h[1]));
}
function putAdd(m,name,p,q){
 if(!p||!q)return;
 if(!fe(p[0],q[0])){
  const d=fsu(q[0],p[0]);
  m[name+".general.inverse_norm"]=qi(norm(d));
  putF(m,name+".general.slope",fd(fsu(q[1],p[1]),d));
 }else if(fe(p[1],q[1])){
  m[name+".double.inverse_norm"]=qi(norm(p[1]));
  putF(m,name+".double.slope",fd(fa(fk(fm(p[0],p[0]),3),coef),fk(p[1],2)));
 }
}
function evaluate(a,values){
 const variables=a.variables.map(v=>values[v.name]||Q(0)),nodes=[];
 for(const n of a.nodes){
  if(n.op==="const")nodes.push(Q(n.args[0]));
  else if(n.op==="var")nodes.push(variables[n.args[0]]);
  else if(n.op==="add")nodes.push(qa(nodes[n.args[0]],nodes[n.args[1]]));
  else if(n.op==="mul")nodes.push(qm(nodes[n.args[0]],nodes[n.args[1]]));
  else throw Error("Unknown polynomial node "+n.op);
 }
 return nodes[a.root][0]===0n;
}
const templates=makeTemplates();
let memberCases=0,addCases=0,traceCases=0,changedOutputsRejected=0;
for(let n=-3;n<=3;n++){
 const m={};putP(m,"p",points.get(n));putMember(m,"member",halves.get(n));
 assert(evaluate(templates.member,m),"member "+n);memberCases++;
 const bad={...m,"p.0":Q(2)};assert(!evaluate(templates.member,bad),"invalid flag");changedOutputsRejected++;
}
for(let n=-3;n<=3;n++)for(let k=-3;k<=3;k++){
 const m={};putP(m,"p",points.get(n));putP(m,"q",points.get(k));putP(m,"r",points.get(n+k));
 putMember(m,"add.left",halves.get(n));putMember(m,"add.right",halves.get(k));
 putAdd(m,"add",points.get(n),points.get(k));
 assert(evaluate(templates.add,m),"sum "+n+","+k);addCases++;
 const bad={...m,"r.1":qa(m["r.1"],Q(1))};
 assert(!evaluate(templates.add,bad),"changed sum output");changedOutputsRejected++;
}
for(let h=-3;h<=3;h++)if(h)for(let j=-3;j<=3;j++){
 const hp=points.get(h),jp=points.get(j),zh=fd(fn(hp[0]),hp[1]),zj=jp?fd(fn(jp[0]),jp[1]):F(0),quotient=fd(zj,zh);
 const m={r:Q(quotient[0],quotient[2])};
 putP(m,"h",hp);putP(m,"j",jp);putMember(m,"h.member",halves.get(h));putMember(m,"j.member",halves.get(j));
 putF(m,"trace_ratio.zh",zh);putF(m,"trace_ratio.zj",zj);putF(m,"trace_ratio.quotient",quotient);
 m["trace_ratio.h.inverse_norm"]=qi(norm(hp[1]));
 if(jp)m["trace_ratio.j.inverse_norm"]=qi(norm(jp[1]));
 m["trace_ratio.quotient.inverse_norm"]=qi(norm(zh));
 assert(evaluate(templates.traceRatio,m),"trace ratio "+h+","+j);traceCases++;
 assert(!evaluate(templates.traceRatio,{...m,r:qa(m.r,Q(1))}),"changed trace output");changedOutputsRejected++;
}
let closeCases=0;
for(const sign of [-1n,1n]){
 const m={a:Q(sign*3n,40n),r:Q(0),close_0:Q(5,4)};
 assert(evaluate(templates.close,m),"strict proximity positive");closeCases++;
}
assert(evaluate(templates.close,{a:Q(9),r:Q(9),close_0:Q(1)}),"zero distance");closeCases++;
for(const numerator of [5n,6n])for(let w=0n;w<=4n;w++){
 assert(!evaluate(templates.close,{a:Q(numerator,40),r:Q(0),close_0:Q(w)}),"boundary/outside assignment");closeCases++;
}
const data=JSON.stringify(templates)+"\n",hash=crypto.createHash("sha256").update(data).digest("hex");
fs.writeFileSync(path.join(__dirname,"rational-elliptic-templates.json"),data);
const report={passed:true,independentJacobianComparisons:6,memberCases,addCases,traceCases,closeCases,changedOutputsRejected,
 templatesSha256:hash,
 limitations:["Finite exact examples do not prove the general arithmetic dependencies.",
 "Rejected mutations test explicit witness assignments; general soundness follows from the chart equations, not bounded witness search.",
 "This module defines membership, addition and coordinate functions, not multiplication of model indices."]};
fs.writeFileSync(path.join(__dirname,"rational-elliptic-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

