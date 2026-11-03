"use strict";
const {RationalBuilder,EllipticCore}=require("./rational-elliptic-core.js");
const {auditLibrary}=require("./rational-polynomial-library.js");
const {divisionPolynomials}=require("./elliptic-division-polynomials.js");
const {integerGuardPolynomial,addNaturalModel}=require("./rational-model-assembly.js");
const {buildCertificateLibrary}=require("./multiplication-certificate.js");
const {P0,W}=require("./fixed-certificate-constants.js");
const ref=name=>["ref",name],lit=n=>["literal",String(n)];
const plus=(a,b)=>["add",a,b],times=(a,b)=>["mul",a,b],power=(a,b)=>["pow",a,b];
function fixedDefinitions(extra={}){
 const d={
  P0:lit(P0),W:lit(W),
  Hproduct:["catalogue_product",ref("W"),lit(22),lit(324)],
  Hmax:["catalogue_max",ref("W"),lit(22),lit(324)],
  Ns:times(ref("P0"),ref("Hproduct")),
  M:["least_formal_multiple",ref("Ns")],
  cstar:times(lit(4),ref("M")),
  ell:times(lit(12),times(power(ref("P0"),lit(2916)),power(ref("Hproduct"),lit(732)))),
  F:["factorial",lit(324)],
  D:times(ref("F"),power(lit(3),times(lit(256),power(ref("F"),lit(4))))),
  G0:lit(116064000000n),
  E0:times(lit(10),power(times(ref("D"),ref("G0")),lit(2))),
  R:["max",ref("D"),ref("Hmax"),ref("cstar"),power(lit(10),lit(12))],
  Q:power(ref("R"),times(ref("R"),ref("E0"))),
  Bcm:plus(times(power(ref("D"),lit(2)),power(lit(3),times(lit(21000),power(ref("D"),lit(2))))),lit(1)),
  Ccm:plus(times(lit(2),ref("Bcm")),times(lit(4096),plus(plus(lit(1028),times(lit(5),ref("D"))),times(lit(84000),power(ref("D"),lit(2)))))),
  Aheight:times(times(lit(2),power(lit(10),lit(13))),["max",lit(1),ref("Ccm"),power(ref("Q"),lit(17))]),
  T:power(times(lit(48),ref("Aheight")),lit(13))
 };
 for(const [name,value] of Object.entries(extra)){
  if(Object.prototype.hasOwnProperty.call(d,name))throw Error("Cannot replace prescribed constant "+name);
  d[name]=lit(value);
 }
 return d;
}
function validateFixedExpression(expr,known){
 if(!Array.isArray(expr)||typeof expr[0]!=="string")throw Error("Bad fixed expression");
 const [op,...args]=expr;
 if(op==="literal"){
  if(args.length!==1||typeof args[0]!=="string"||!/^(-?[1-9][0-9]*|0)$/.test(args[0]))throw Error("Bad integer literal");
 }else if(op==="ref"){
  if(args.length!==1||typeof args[0]!=="string"||!known.has(args[0]))throw Error("Unknown or forward fixed reference");
 }else{
  const arities={add:2,mul:2,pow:2,factorial:1,catalogue_product:3,catalogue_max:3,least_formal_multiple:1};
  if(op==="max"){if(args.length<1)throw Error("Empty maximum");}
  else if(arities[op]!==args.length)throw Error("Bad fixed operator "+op);
  args.forEach(a=>validateFixedExpression(a,known));
 }
}
function auditFixedDefinitions(definitions){
 const known=new Set();
 for(const [name,value] of Object.entries(definitions)){validateFixedExpression(value,known);known.add(name);}
 const expected=fixedDefinitions();
 for(const [name,value] of Object.entries(expected)){
  if(JSON.stringify(definitions[name])!==JSON.stringify(value))throw Error("Prescribed constant changed: "+name);
 }
 for(const name of known)if(!(name in expected)&&definitions[name][0]!=="literal")throw Error("Extra fixed constant must be literal");
 return known;
}
function macroPsi(b,index,x,y){
 return [0,1].map(component=>b.node("psi_component",[index,...x,...y,component]));
}
function finiteScalarFormula(b,p,r,index){
 const e=new EllipticCore(b),g=macroPsi(b,index,e.x(p),e.y(p)),g2=e.fsquare(g),
  gp=macroPsi(b,plus(index,lit(1)),e.x(p),e.y(p)),
  gm=macroPsi(b,plus(index,lit(-1)),e.x(p),e.y(p)),
  gdouble=macroPsi(b,times(lit(2),index),e.x(p),e.y(p)),
  xn=e.fsub(e.fmul(e.x(p),g2),e.fmul(gp,gm));
 return b.or(b.and(e.isO(p),e.isO(r)),
  b.and(e.finite(p),e.finite(r),e.fnonzero(g,"fixed_scalar.inverse_norm"),
   e.feq(e.fmul(g2,e.x(r)),xn),
   e.feq(e.fmul(e.fscale(2,e.fsquare(g2)),e.y(r)),gdouble)));
}
function addFiniteScalar(library,index,name){
 library.define(name,["p","r"].flatMap(s=>Array.from({length:5},(_,i)=>s+"."+i)),
  (b,a)=>finiteScalarFormula(b,a.slice(0,5),a.slice(5),index),
  {meaning:"r=[fixed positive index]p",fixedIndex:index,preconditions:"p belongs to D; fixed index is positive"});
 return name;
}
function buildFiniteModel(){
 const library=buildCertificateLibrary(),scalar=addFiniteScalar(library,ref("cstar"),"multiply.scalar"),
  names=Array.from({length:15},(_,i)=>"P"+Math.floor(i/5)+"."+(i%5));
 library.define("multiply.guard",names,(b,p)=>{
  const product=b.node("finite_guard_product",[ref("T"),...p]);
  return b.nonzero(product,"guard_inverse");
 },{meaning:"The explicitly bounded integer-coefficient false-triple product",cutoff:ref("T")});
 library.define("multiply",names,(b,p)=>{
  const e=new EllipticCore(b),points=[e.P(),p.slice(0,5),p.slice(5,10),p.slice(10)],conditions=[],
   shifts=points.map((point,i)=>{const out=e.point("shift."+i);conditions.push(b.call(scalar,point.concat(out)));return out;}),
   ell=b.node("fixed_integer",[ref("ell")]);
  conditions.push(b.call("height_certificate",p.concat([ell],shifts.flat())),b.call("multiply.guard",p));
  return b.and(...conditions);
 },{meaning:"Exact index multiplication with the prescribed constants",fixedConstantBinding:"fixedDefinitions-v1"});
 addNaturalModel(library);
 return library;
}
function finiteArtifact(library,extraConstants={},metadata={}){
 const a=library.artifact(metadata);a.format="finite-expression-rational-polynomial-library-v1";
 a.fixedConstants=fixedDefinitions(extraConstants);
 a.finitePolynomialConstructors={
  version:1,
  fixed_integer:"Substitute the fixed integer expression; no quantified variables occur in it.",
  psi_component:"Component 0 or 1 of the classical psi_n(x,y) for the fixed integer n, with psi_2=2y. Expand by the normalized recurrences in elliptic-division-polynomials.js.",
  finite_guard_product:"Product over a,b,c in [-T,T] with a*b!=c of the integer denominator-cleared squared-distance factors specified in rational-model-assembly.js."
 };
 return a;
}
function auditFiniteLibrary(library){
 if(library.format!=="finite-expression-rational-polynomial-library-v1"||library.finitePolynomialConstructors?.version!==1)throw Error("Unknown finite constructor format");
 const known=auditFixedDefinitions(library.fixedConstants),macros=[];
 const fake={templates:library.templates.map(t=>({...t,nodes:t.nodes.map((n,i)=>{
  if(["const","var","add","mul","call"].includes(n.op))return n;
  let references;
  if(n.op==="fixed_integer"){
   if(n.args.length!==1)throw Error("Bad fixed coefficient");validateFixedExpression(n.args[0],known);references=[];
  }else if(n.op==="psi_component"){
   if(n.args.length!==6||![0,1].includes(n.args[5]))throw Error("Bad division-polynomial component");
   validateFixedExpression(n.args[0],known);references=n.args.slice(1,5);
  }else if(n.op==="finite_guard_product"){
   if(n.args.length!==16||JSON.stringify(n.args[0])!==JSON.stringify(ref("T")))throw Error("Bad finite guard binding");
   references=n.args.slice(1);
  }else throw Error("Unknown polynomial constructor "+n.op);
  if(references.some(k=>!Number.isSafeInteger(k)||k<0||k>=i))throw Error("Bad finite-constructor edge");
  macros.push({template:t.name,node:i,op:n.op});
  return {op:"const",args:["0"]};
 })}))};
 const ordinary=auditLibrary(fake);
 return {...ordinary,finitePolynomialConstructors:macros,fixedConstants:Object.keys(library.fixedConstants)};
}
/* Fixture expansion is used only to verify the finite constructor rules.
 * A fixture does NOT replace the prescribed constants in a delivered artifact.
 */
function evaluateFixed(expr,definitions,fixture={},stack=new Set()){
 const [op,...args]=expr;
 if(op==="literal")return BigInt(args[0]);
 if(op==="ref"){
  const name=args[0];
  if(Object.prototype.hasOwnProperty.call(fixture,name))return BigInt(fixture[name]);
  if(stack.has(name))throw Error("Cyclic coefficient");
  const s=new Set(stack);s.add(name);return evaluateFixed(definitions[name],definitions,fixture,s);
 }
 const v=args.map(a=>evaluateFixed(a,definitions,fixture,stack));
 if(op==="add")return v[0]+v[1];if(op==="mul")return v[0]*v[1];
 if(op==="pow")return v[0]**v[1];if(op==="max")return v.reduce((a,b)=>a>b?a:b);
 if(op==="factorial"){let r=1n;for(let i=2n;i<=v[0];i++)r*=i;return r;}
 throw Error("Do not evaluate the astronomical search coefficients in a fixture expansion: "+op);
}
function expandFiniteTemplate(library,id,fixture={}){
 const t=library.templates[id],b=new RationalBuilder(),e=new EllipticCore(b),values=[];
 // Preserve variable indices exactly; expansion creates no new variables.
 for(const n of t.nodes){
  if(n.op==="const")values.push(b.constant(n.args[0]));
  else if(n.op==="var")values.push(b.node("var",n.args));
  else if(n.op==="add"||n.op==="mul")values.push(b.node(n.op,n.args.map(k=>values[k])));
  else if(n.op==="call")values.push(b.node("call",[n.args[0],...n.args.slice(1,-1).map(k=>values[k]),n.args.at(-1)]));
  else if(n.op==="fixed_integer")values.push(b.constant(evaluateFixed(n.args[0],library.fixedConstants,fixture)));
  else if(n.op==="psi_component"){
   const index=evaluateFixed(n.args[0],library.fixedConstants,fixture),
    x=n.args.slice(1,3).map(k=>values[k]),y=n.args.slice(3,5).map(k=>values[k]);
   values.push(divisionPolynomials(e,x,y).psi(index)[n.args[5]]);
  }else if(n.op==="finite_guard_product"){
   const T=evaluateFixed(n.args[0],library.fixedConstants,fixture);
   values.push(integerGuardPolynomial(b,n.args.slice(1).map(k=>values[k]),T).product);
  }else throw Error("Unknown constructor");
 }
 return {...t,nodes:b.nodes,root:values[t.root]};
}
module.exports={ref,lit,plus,times,fixedDefinitions,validateFixedExpression,auditFixedDefinitions,
 addFiniteScalar,buildFiniteModel,finiteArtifact,auditFiniteLibrary,evaluateFixed,expandFiniteTemplate};
if(require.main===module){
 const fs=require("node:fs"),path=require("node:path"),library=buildFiniteModel(),a=finiteArtifact(library,{},{
  meaning:"The fixed multiplication model as an explicit finite polynomial expression.",
  limitation:"Arithmetic dependencies and the full universal composition still require final audit."}),audit=auditFiniteLibrary(a);
 fs.writeFileSync(path.join(__dirname,"fixed-rational-model.json"),JSON.stringify(a)+"\n");
 fs.writeFileSync(path.join(__dirname,"fixed-rational-model-structure.json"),JSON.stringify(audit,null,2)+"\n");
 console.log(JSON.stringify(audit,null,2));
}

