"use strict";
const fs=require("node:fs"),path=require("node:path");
const {buildAccuracyIR,runIR,lowerIR,triple}=require("./accuracy-program.js");
const {encodeProgram}=require("./universal-interpreter.js");
const {validateProgram}=require("./integer-diophantine-compiler.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b];}return a;}
function F(a,b=0n,c=1n){a=BigInt(a);b=BigInt(b);c=BigInt(c);if(!c)throw Error("Zero denominator");if(c<0n){a=-a;b=-b;c=-c;}const g=gcd(gcd(a,b),c);return [a/g,b/g,c/g];}
const add=(x,y)=>F(x[0]*y[2]+y[0]*x[2],x[1]*y[2]+y[1]*x[2],x[2]*y[2]);
const neg=x=>F(-x[0],-x[1],x[2]);
const sub=(x,y)=>add(x,neg(y));
const mul=(x,y)=>F(x[0]*y[0]+2n*x[1]*y[1],x[0]*y[1]+x[1]*y[0],x[2]*y[2]);
const inv=x=>F(x[2]*x[0],-x[2]*x[1],x[0]**2n-2n*x[1]**2n);
const div=(x,y)=>mul(x,inv(y));
const scale=(x,k)=>mul(x,F(k));
const eq=(x,y)=>x.every((a,i)=>a===y[i]);
const coef=F(-11243n,7950n),P=[F(1641n,-1160n,8n),F(-123720n,87483n,32n)];
function plus(p,q){
 if(!p)return q;if(!q)return p;
 if(eq(p[0],q[0])&&eq(p[1],neg(q[1])))return null;
 const slope=eq(p[0],q[0])?div(add(scale(mul(p[0],p[0]),3),coef),scale(p[1],2)):div(sub(q[1],p[1]),sub(q[0],p[0]));
 const x=sub(sub(mul(slope,slope),p[0]),q[0]);
 return [x,sub(mul(slope,sub(p[0],x)),p[1])];
}
const extended=process.argv.includes("--extended");
const points=[null];
function ensurePoints(n){while(points.length<=n)points.push(plus(points.at(-1),P));}
ensurePoints(16);
function rho(h,j){
 if(!j)return F(0);
 return div(div(neg(points[j][0]),points[j][1]),div(neg(points[h][0]),points[h][1]));
}
const ir=buildAccuracyIR();
function readS(reg,s){return reg[s[0]]-reg[s[1]];}
function readF(reg,f){return F(readS(reg,f[0]),readS(reg,f[1]));}
function checkPoint(reg,coords,expected){
 const [X,Y,Z]=coords.map(c=>readF(reg,c));
 const xx=div(X,mul(Z,Z)),yy=div(Y,mul(mul(Z,Z),Z));
 assert(eq(xx,expected[0])&&eq(yy,expected[1]),"Jacobian differs from independent affine arithmetic");
 assert(eq(mul(yy,yy),add(mul(mul(xx,xx),xx),mul(coef,xx))),"curve equation");
}
const cases=[];
for(let k=0;k<=4;k++)for(let h=1;h<=4;h++){
 const j=k*h,rr=rho(h,j),expected=64n*(rr[0]-BigInt(k)*rr[2])**2n<rr[2]**2n;
 const result=runIR(ir,triple(k,h,j));
 assert(result.accepted===expected,"accuracy predicate");
 if(j){
  checkPoint(result.registers,ir.debug.H,points[h]);checkPoint(result.registers,ir.debug.J,points[j]);
  const N=readS(result.registers,ir.debug.numerator),D=readS(result.registers,ir.debug.denominator);
  assert(N*rr[2]===D*rr[0],"trace ratio");
 }
 cases.push({k,h,j,accepted:result.accepted,ticks:result.ticks});
}
for(const [k,h,j] of [[1,0,0],[0,0,0],[1,1,2],[2,1,1],[0,2,1]])
 assert(!runIR(ir,triple(k,h,j)).accepted,"invalid indices accepted");
let nontrivialAccepted=null;
if(extended)for(let h=1;h<=40;h++){
 ensurePoints(2*h);
 const rr=rho(h,2*h);
 if(64n*(rr[0]-2n*rr[2])**2n<rr[2]**2n){
  const result=runIR(ir,triple(2,h,2*h));
  assert(result.accepted,"nontrivial accuracy acceptance");
  checkPoint(result.registers,ir.debug.H,points[h]);checkPoint(result.registers,ir.debug.J,points[2*h]);
  nontrivialAccepted={k:2,h,j:2*h,ticks:result.ticks};break;
 }
}
const machine=lowerIR(ir);validateProgram(machine.program,machine.registers);
fs.writeFileSync(path.join(__dirname,"accuracy-program-ir.json"),JSON.stringify(ir)+"\n");
fs.writeFileSync(path.join(__dirname,"accuracy-register-program.json"),JSON.stringify(machine)+"\n");
const programCode=encodeProgram(machine.program),hex=programCode.toString(16);
fs.writeFileSync(path.join(__dirname,"accuracy-program-code.hex"),hex+"\n");
const report={passed:true,irRegisters:ir.registers,states:machine.program.length,primitiveRegisters:machine.registers,
 codeBits:programCode.toString(2).length,codeHexDigits:hex.length,cases,extended,nontrivialAccepted,invalidIndexCases:5,
 limitations:["Nontrivial elliptic examples were executed in the exact BigInt IR, not by the much slower unary primitive machine.",
 "The primitive lowering relies on the separately checked macro semantics and structural induction."]};
fs.writeFileSync(path.join(__dirname,"accuracy-program-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

