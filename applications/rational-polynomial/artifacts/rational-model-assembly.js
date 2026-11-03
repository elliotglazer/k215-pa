"use strict";
const {EllipticCore}=require("./rational-elliptic-core.js");
const {indexCode}=require("./rational-field-arithmetic.js");
const {addFixedScalar}=require("./elliptic-division-polynomials.js");
const pointNames=(prefix,n)=>Array.from({length:n},(_,i)=>Array.from({length:5},(_,j)=>prefix+i+"."+j)).flat();
function integerGuardPolynomial(b,inputs,T){
 T=BigInt(T);if(T<0n)throw Error("Negative guard cutoff");
 const constants=new Map();
 for(let n=-T;n<=T;n++)constants.set(n,indexCode(n));
 let product=b.constant(1),falseTriples=0n;
 for(let a=-T;a<=T;a++)for(let c=-T;c<=T;c++)for(let d=-T;d<=T;d++){
   if(a*c===d)continue;
   const expected=[...constants.get(a),...constants.get(c),...constants.get(d)];
   const denominator=expected.reduce((d,pair)=>d*pair[1],1n);
   const distance=b.add(...inputs.map((x,i)=>b.square(b.sub(b.scale(denominator,x),
     b.constant((denominator/expected[i][1])*expected[i][0])))));
   product=b.mul(product,distance);falseTriples++;
 }
 return {product,falseTriples};
}
function addFiniteGuard(library,T,name="finite_guard"){
 T=BigInt(T);if(T<0n)throw Error("Negative finite guard bound");
 const metadata={meaning:"Exclude every false index triple in [-T,T]^3",bound:String(T),integerCoefficientFactors:true};
 library.define(name,pointNames("P",3),(b,inputs)=>{
   const {product,falseTriples}=integerGuardPolynomial(b,inputs,T);
   metadata.guardNode=product;metadata.falseTriples=String(falseTriples);
   return b.nonzero(product,"guard_inverse");
 },metadata);
 return name;
}
function fixedMultiple(b,e,p,k,name){
 k=BigInt(k);if(k<0n)return fixedMultiple(b,e,e.neg(p),-k,name);
 let out=e.O(),base=p,i=0;const formulas=[];
 while(k){
   if(k&1n){const q=e.point(name+".sum."+i);formulas.push(b.call("raw_add",out.concat(base,q)));out=q;}
   k>>=1n;
   if(k){const q=e.point(name+".double."+i);formulas.push(b.call("raw_add",base.concat(base,q)));base=q;}
   i++;
 }
 return {value:out,formula:b.and(...formulas)};
}
/*
 * The parameter values must be the prescribed fixed constants, or verified
 * stronger choices satisfying the same arithmetic bounds. This routine does
 * not certify arbitrary caller-supplied constants.
 */
function bindMultiplication(library,{cstar,ell,T},name="multiply"){
 cstar=BigInt(cstar);ell=BigInt(ell);T=BigInt(T);
 if(cstar<=0n||ell<=0n||T<0n)throw Error("Invalid fixed constants");
 const scalarName=addFixedScalar(library,cstar,name+".scalar");
 const guardName=addFiniteGuard(library,T,name+".guard");
 library.define(name,pointNames("P",3),(b,inputs)=>{
   const e=new EllipticCore(b),roots=[inputs.slice(0,5),inputs.slice(5,10),inputs.slice(10)],
     shifts=[e.P(),...roots].map((p,i)=>{
       const value=e.point("shift."+i);return {value,formula:b.call(scalarName,p.concat(value))};
     });
   return b.and(...shifts.map(s=>s.formula),
     b.call("height_certificate",inputs.concat([b.constant(ell)],shifts.flatMap(s=>s.value))),
     b.call(guardName,inputs));
 },{meaning:"Exact multiplication of model indices when the fixed constants satisfy their prescribed bounds",
   cstar:String(cstar),ell:String(ell),T:String(T),
   arithmeticDependencies:["six-contact height estimate","pole completeness","linear prime-pattern theorem","rank-one generator and local formal-group arguments"]});
 return name;
}
function addNaturalModel(library,multiplication="multiply",name="natural"){
 library.define(name,pointNames("A",1),(b,A)=>{
   const e=new EllipticCore(b),us=Array.from({length:4},(_,i)=>e.point("square_root."+i)),
     squares=Array.from({length:4},(_,i)=>e.point("square."+i)),f=[];
   for(let i=0;i<4;i++)f.push(b.call(multiplication,us[i].concat(us[i],squares[i])));
   let sum=squares[0];
   for(let i=1;i<4;i++){
     const next=i===3?A:e.point("partial_sum."+i);
     f.push(b.call("raw_add",sum.concat(squares[i],next)));sum=next;
   }
   return b.and(...f);
 },{meaning:"A codes a nonnegative integer, by the four-square theorem",
   preconditions:"The referenced multiplication template is exact on D"});
 return name;
}
module.exports={integerGuardPolynomial,addFiniteGuard,fixedMultiple,bindMultiplication,addNaturalModel};

