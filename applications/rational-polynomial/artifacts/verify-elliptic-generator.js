// Exact finite verification for the generator proof in elliptic-generator-proof.txt.
// Run with Node.js 18 or later. No packages or network access are used.
"use strict";
function verifyGeneratorSearch() {
  const abs = x => x < 0n ? -x : x;
  const gcd = (a,b) => { a=abs(a); b=abs(b); while(b) [a,b]=[b,a%b]; return a; };
  const sqrt = n => {
    if(n < 0n) return null;
    if(n < 2n) return n;
    let x=1n << BigInt(Math.ceil(n.toString(2).length/2));
    for(;;) {
      const y=(x+n/x)/2n;
      if(y>=x) return x*x===n ? x : null;
      x=y;
    }
  };
  const rat = (n,d=1n) => {
    if(d<0n) { n=-n; d=-d; }
    const g=gcd(n,d); return [n/g,d/g];
  };
  const ratSqrt = (n,d) => {
    if(n<0n) return null;
    const [a,b]=rat(n,d), x=sqrt(a), y=sqrt(b);
    return x===null || y===null ? null : [x,y];
  };
  // Test whether x^3-(11-6 sqrt(2))*x is a square in Q(sqrt(2)).
  // Input x=(A+B sqrt(2))/C. Output a square root in rational components.
  const testX = (A,B,C) => {
    A=BigInt(A); B=BigInt(B); C=BigInt(C);
    const common=gcd(gcd(A,B),C); A/=common; B/=common; C/=common;
    const u=A*A*A+6n*A*B*B-(11n*A-12n*B)*C*C;
    const v=3n*A*A*B+2n*B*B*B-(11n*B-6n*A)*C*C;
    const den=C*C*C, normRoot=sqrt(u*u-2n*v*v);
    if(normRoot===null) return null;
    for(const t of [normRoot,-normRoot]) {
      const y0=ratSqrt(u+t,2n*den);
      if(!y0) continue;
      let y1;
      if(y0[0]===0n) {
        if(v!==0n) continue;
        y1=ratSqrt(u,2n*den);
        if(!y1) continue;
      } else {
        y1=rat(v*y0[1],2n*den*y0[0]);
      }
      // Independently substitute the reported square root.
      const yd=y0[1]*y1[1], ya=y0[0]*y1[1], yb=y1[0]*y0[1];
      if((ya*ya+2n*yb*yb)*den!==u*yd*yd ||
          2n*ya*yb*den!==v*yd*yd) throw new Error("Square-root substitution failed");
      return {x:[A,B,C].map(String),y0:y0.map(String),y1:y1.map(String)};
    }
    return null;
  };
  const igcd=(a,b) => { a=Math.abs(a); b=Math.abs(b); while(b) [a,b]=[b,a%b]; return a; };
  const points=new Map();
  const discriminants=new Map();
  for(let k=1;k<=162;k++) discriminants.set(2*k*k,k);
  let candidates=0;
  for(let a=1;a<=81;a++) for(let b=-162;b<=162;b++) for(let c=-81;c<=81;c++) {
    const D=b*b-4*a*c;
    if(D<=0 || D%2) continue;
    const k=discriminants.get(D);
    // Every number operation in the enumeration is an exact integer < 2^53.
    if(k===undefined || igcd(igcd(a,b),c)!==1) continue;
    for(const sign of [1,-1]) {
      candidates++;
      const P=testX(-b,sign*k,2*a);
      if(P) points.set(P.x.join(","),P);
    }
  }
  for(let c=1;c<=9;c++) for(let a=-9;a<=9;a++) if(igcd(a,c)===1) {
    const P=testX(a,0,c);
    if(P) points.set(P.x.join(","),P);
  }
  const expected=[
    "0,0,1","3,-1,1","-3,1,1",
    "1,1,1","23,-17,1","2,4,1","5,-4,2"
  ].sort();
  const actual=[...points.keys()].sort();
  if(JSON.stringify(actual)!==JSON.stringify(expected)) throw new Error("Unexpected point set");
  // Exact comparison proving (log(41^3*676))/108 + log(392)/3 < log(9).
  if(!(41n**3n*676n*392n**36n < 9n**108n)) throw new Error("Height inequality failed");
  return {passed:true,quadraticCandidates:candidates,points:[...points.values()]};
}
if(typeof console!=="undefined") console.log(JSON.stringify(verifyGeneratorSearch(),null,2));

