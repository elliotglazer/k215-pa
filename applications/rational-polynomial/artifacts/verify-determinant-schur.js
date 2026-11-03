"use strict";
// Finite Laurent-polynomial checks of the corrected approximate-inverse formula.
// These checks supplement, and do not replace, the arbitrary-size algebra proof.
const fs=require("node:fs"),path=require("node:path");
const check=(p,s)=>{if(!p)throw Error(s);};
function trial(n,M,seed){
 const mod=2n**BigInt(M),reduce=x=>(x%mod+mod)%mod;
 const term=(k,c)=>{c=reduce(BigInt(c));return c?new Map([[k,c]]):new Map();};
 const add=(a,b)=>{const r=new Map(a);for(const [k,c] of b){const v=reduce((r.get(k)||0n)+c);if(v)r.set(k,v);else r.delete(k);}return r;};
 const mul=(a,b)=>{let r=new Map();for(const [i,c] of a)for(const [j,d] of b)r=add(r,term(i+j,c*d));return r;};
 const mat=f=>Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>f(i,j)));
 const I=mat((i,j)=>term(0,i===j?1:0));
 const plus=(A,B)=>mat((i,j)=>add(A[i][j],B[i][j]));
 const times=(A,B)=>mat((i,j)=>{let p=new Map();for(let k=0;k<n;k++)p=add(p,mul(A[i][k],B[k][j]));return p;});
 const scale=(a,A)=>mat((i,j)=>mul(term(0,a),A[i][j]));
 const same=(A,B)=>A.every((r,i)=>r.every((p,j)=>p.size===B[i][j].size&&[...p].every(([k,c])=>B[i][j].get(k)===c)));
 const degrees=Array.from({length:n},(_,i)=>1+(i+seed)%4);
 const weights=Array.from({length:n},(_,i)=>1+(2*i+seed)%5);
 const A=mat((i,j)=>i===j?add(term(degrees[i],1),term(0,2*weights[i])):term(0,0));
 const C=mat((i,j)=>term(i===j?-degrees[i]:0,i===j?1:0));
 const E=mat((i,j)=>add(term((i+2*j+seed)%3,1+(i+j+seed)%5),term(0,i-j)));
 const B=plus(A,scale(2,E));
 const F=plus(mat((i,j)=>term(i===j?-degrees[i]:0,i===j?weights[i]:0)),times(E,C));
 check(same(times(B,C),plus(I,scale(2,F))),"BC=I+2F failed");
 let sum=I,power=I;
 for(let j=1;j<M;j++){power=times(power,scale(-2,F));sum=plus(sum,power);}
 const inverse=times(C,sum);
 check(same(times(B,inverse),I)&&same(times(inverse,B),I),"Geometric inverse failed");
 let pole=0;for(const row of inverse)for(const p of row)for(const k of p.keys())pole=Math.max(pole,-k);
 check(pole<=4*M,"Precision-dependent pole bound failed");
 return {size:n,precision:M,seed,pole,bound:4*M};
}
function main(){
 const cases=[];
 for(const n of [1,2,3,6])for(let M=1;M<=6;M++)for(let seed=0;seed<3;seed++)cases.push(trial(n,M,seed));
 // (t+2)^-1 modulo 8 has pole order 3, disproving a precision-independent
 // order-one bound on the exact inverse of a block with residual determinant t.
 const counterexample={modulus:8,block:"t+2",inverse:"t^-1-2*t^-2+4*t^-3",residualDeterminantOrder:1,inversePoleOrder:3};
 const report={date:"2026-11-03",passed:true,cases:cases.length,counterexample,results:cases,
  scope:"Exact finite Laurent-polynomial matrix arithmetic. The general proof uses approximate adjugate inverses and is in paired-functional-and-uniformity-proof.txt, section 6."};
 fs.writeFileSync(path.join(__dirname,"determinant-schur-checks.json"),JSON.stringify(report,null,2)+"\n");
 console.log(JSON.stringify({passed:true,cases:cases.length,counterexample},null,2));
}
if(require.main===module)main();
module.exports={trial,main};
