// Run with Node.js, or evaluate this expression in any ES2020 JavaScript engine.
// Checks finite algebra only. It does not prove the Shimura, height, or
// pointwise-converse theorems used by the construction.
(() => {
"use strict";
const assert=(b,s)=>{if(!b)throw Error(s);};
const add=(a,b)=>Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||0n)+(b[i]||0n));
const scale=(a,c)=>a.map(x=>x*c);
const mul=(a,b)=>{const c=Array(a.length+b.length-1).fill(0n);a.forEach((x,i)=>b.forEach((y,j)=>c[i+j]+=x*y));return c;};
const pow=(a,n)=>{let b=[1n];while(n--)b=mul(b,a);return b;};
const value=(a,x)=>a.reduceRight((r,c)=>r*x+c,0n);
const abs=x=>x<0n?-x:x;
const norm=a=>a.reduce((s,x)=>s+abs(x),0n);
const det=A=>A.length===0?1n:A[0].reduce((s,x,j)=>s+(j%2?-1n:1n)*x*det(A.slice(1).map(r=>r.filter((_,k)=>k!==j))),0n);
const resultant2=(a,b)=>det([
 [a[2],a[1],a[0],0n],[0n,a[2],a[1],a[0]],
 [b[2],b[1],b[0],0n],[0n,b[2],b[1],b[0]]]);
const only235=x=>{x=abs(x);if(!x)return false;for(const p of [2n,3n,5n])while(x%p===0n)x/=p;return x===1n;};
const roots=[0n,-15n,-20n,-24n,-30n,-60n];
const F=roots.reduce((a,r)=>mul(a,[-r,1n]),[1n]);
const G=[3600n,300n,7n];
const factors=[[-1800n,-60n,1n],[3600n,480n,13n],[7200n,600n,11n]];
const H=factors.reduce(mul,[1n]);
const P=scale(pow(F,2),-57600n), Q=pow(G,6);
assert(add(add(Q,scale(pow(F,2),-97200n)),scale(pow(H,2),-1n)).every(x=>x===0n),"map identity");
assert(norm(P)<4000n**6n && norm(Q)<4000n**6n,"coefficient height");
const quadratics=[G,...factors], resultants=[];
for(let i=0;i<4;i++){
 const a=quadratics[i], disc=a[1]**2n-4n*a[0]*a[2];
 assert(only235(disc),"discriminant support");
 for(let j=i+1;j<4;j++){
  const r=resultant2(a,quadratics[j]);
  assert(only235(r),"resultant support");
  resultants.push({i,j,resultant:String(r)});
 }
}
assert(roots.every(r=>only235(value(G,r))),"contact disjointness");
for(let i=0;i<6;i++)for(let j=i+1;j<6;j++)assert(only235(roots[i]-roots[j]),"contact separation");
// Quaternion multiplication, i^2=2, j^2=-3, k=ij.
const table=[
 [[0,1],[1,1],[2,1],[3,1]],
 [[1,1],[0,2],[3,1],[2,2]],
 [[2,1],[3,-1],[0,-3],[1,3]],
 [[3,1],[2,-2],[1,-3],[0,6]]];
const qm=(a,b)=>{let c=[0n,0n,0n,0n];for(let i=0;i<4;i++)for(let j=0;j<4;j++){const [k,v]=table[i][j];c[k]+=a[i]*b[j]*BigInt(v);}return c;};
const bar=a=>a.map((x,i)=>i?-x:x);
const mu=[0n,0n,2n,1n], basis2=[[2n,0n,0n,0n],[0n,2n,0n,0n],[1n,0n,1n,0n],[0n,1n,0n,1n]];
assert(qm(mu,mu).every((x,i)=>x===(i?0n:-6n)),"mu square");
const gram=basis2.map(a=>basis2.map(b=>{let q=-qm(qm(mu,a),bar(b))[0];assert(q%12n===0n,"pairing integral");return q/12n;}));
assert(det(gram)===1n,"self-dual pairing");
// Exact multiplication in the displayed maximal-order basis, reduced mod 3.
// This independently checks the finite level index used in the cover bound.
const toOrderFromQuarter=q=>{
 const numerators=[q[0]-q[2],q[1]-q[3],2n*q[2],2n*q[3]];
 assert(numerators.every(x=>x%4n===0n),"order multiplication integral");
 return numerators.map(x=>x/4n);
};
const orderTable=basis2.map(a=>basis2.map(b=>toOrderFromQuarter(qm(a,b))));
const mod3=x=>((x%3n)+3n)%3n;
const orderMul3=(a,b)=>{
 const r=[0n,0n,0n,0n];
 for(let i=0;i<4;i++)for(let j=0;j<4;j++)for(let k=0;k<4;k++)r[k]+=a[i]*b[j]*orderTable[i][j][k];
 return r.map(mod3);
};
const orderElements=Array.from({length:81},(_,v)=>[0,1,2,3].map(k=>BigInt(Math.floor(v/3**k)%3)));
const isOne=a=>a[0]===1n&&a.slice(1).every(x=>x===0n);
const orderNorm3=a=>{
 const q=[0n,0n,0n,0n];
 for(let i=0;i<4;i++)for(let k=0;k<4;k++)q[k]+=a[i]*basis2[i][k];
 const n=qm(q,bar(q))[0];
 assert(n%4n===0n,"order norm integral");
 return mod3(n/4n);
};
const units3=orderElements.filter(a=>orderElements.some(b=>isOne(orderMul3(a,b))&&isOne(orderMul3(b,a))));
assert(units3.length===72,"level-three unit count");
assert(orderElements.every(a=>units3.includes(a)===(orderNorm3(a)!==0n)),"unit norm criterion");
const normOne3=units3.filter(a=>orderNorm3(a)===1n).length;
assert(normOne3===36,"norm-one level-three count");
const levelThree={ringSize:81,unitCount:units3.length,normOneCount:normOne3,
 effectiveLevelIndexBound:units3.length/2,effectiveNormalizerIndexBound:4*units3.length/2};
for(const Bp of [1n,4n])for(const v12 of [0n,1n,2n]){
 const Cp=14n*Bp,Dp=51n*Cp,Ep=52n*Cp+v12+4n;
 assert(2n*Ep-Cp-2n*Dp>v12,"trace precision");
 assert(2n*Ep-Cp-2n*v12>=4n,"pole threshold");
}
assert(22n<2n**5n,"small-prime union bound");
assert(40n*10000n*2n**24n+96n<10n**13n,"base-height arithmetic");
const result={passed:true,contacts:roots.map(String),F:F.map(String),G:G.map(String),H:H.map(String),
 numeratorNorm:String(norm(P)),denominatorNorm:String(norm(Q)),gram:gram.map(r=>r.map(String)),
 resultants,levelThree,notes:"Only finite identities and inequalities were checked."};
if(typeof console!=="undefined")console.log(JSON.stringify(result,null,2));
return result;
})()

