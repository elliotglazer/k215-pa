"use strict";
const {EllipticCore}=require("./rational-elliptic-core.js");
/*
 * On y^2=x^3+A*x, normalized division polynomials f_n satisfy
 * psi_n=f_n for odd n and psi_n=2*y*f_n for even n.
 * All recurrences below use only integer-coefficient polynomial operations.
 */
function divisionPolynomials(e,x,y){
 const zero=e.fc(0),one=e.fc(1),A=e.A,x2=e.fsquare(x),x3=e.fmul(x2,x),x4=e.fsquare(x2),
  A2=e.fsquare(A),A3=e.fmul(A2,A),curve=e.fadd(x3,e.fmul(A,x)),
  D=e.fscale(16,e.fsquare(curve)),memo=new Map();
 memo.set(0n,zero);memo.set(1n,one);memo.set(2n,one);
 memo.set(3n,e.fsub(e.fadd(e.fscale(3,x4),e.fscale(6,e.fmul(A,x2))),A2));
 memo.set(4n,e.fscale(2,e.fsub(e.fsub(e.fadd(e.fmul(x4,x2),e.fscale(5,e.fmul(A,x4))),
   e.fscale(5,e.fmul(A2,x2))),A3)));
 function normal(n){
  n=BigInt(n);if(n<0n)throw Error("Normalized division index must be nonnegative");
  if(memo.has(n))return memo.get(n);
  const m=n/2n;let result;
  if(n%2n===0n){
    result=e.fmul(normal(m),e.fsub(e.fmul(normal(m+2n),e.fsquare(normal(m-1n))),
      e.fmul(normal(m-2n),e.fsquare(normal(m+1n)))));
  }else{
    const left=e.fmul(normal(m+2n),e.fpow(normal(m),3)),
      right=e.fmul(normal(m-1n),e.fpow(normal(m+1n),3));
    result=m%2n===0n?e.fsub(e.fmul(D,left),right):e.fsub(left,e.fmul(D,right));
  }
  memo.set(n,result);return result;
 }
 function psi(n){n=BigInt(n);if(n<0n)return e.fneg(psi(-n));
  return n%2n===0n?e.fmul(e.fscale(2,y),normal(n)):normal(n);}
 return {normal,psi,memo};
}
/*
 * Preconditions: p belongs to the torsion-free carrier D.
 * One rational inverse-norm witness, regardless of the size of n!=0.
 */
function fixedScalarRelation(e,p,r,n,name="fixed_scalar"){
 n=BigInt(n);if(n===0n)return e.isO(r);
 if(n<0n)return fixedScalarRelation(e,e.neg(p),r,-n,name);
 const b=e.b,{psi}=divisionPolynomials(e,e.x(p),e.y(p)),g=psi(n),g2=e.fsquare(g),
  xnumerator=e.fsub(e.fmul(e.x(p),g2),e.fmul(psi(n+1n),psi(n-1n))),
  ynumerator=psi(2n*n);
 return b.or(b.and(e.isO(p),e.isO(r)),
   b.and(e.finite(p),e.finite(r),e.fnonzero(g,name+".inverse_norm"),
    e.feq(e.fmul(g2,e.x(r)),xnumerator),
    e.feq(e.fmul(e.fscale(2,e.fsquare(g2)),e.y(r)),ynumerator)));
}
function addFixedScalar(library,n,name="fixed_scalar"){
 n=BigInt(n);
 library.define(name,["p","r"].flatMap(s=>Array.from({length:5},(_,i)=>s+"."+i)),(b,args)=>{
  const e=new EllipticCore(b);return fixedScalarRelation(e,args.slice(0,5),args.slice(5),n);
 },{meaning:"r=[n]p",n:String(n),preconditions:"p belongs to D",
   source:"Classical division-polynomial recurrences and psi_(2n)=2*y([n]p)*psi_n^4"});
 return name;
}
module.exports={divisionPolynomials,fixedScalarRelation,addFixedScalar};

