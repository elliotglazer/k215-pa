"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {EllipticCore}=require("./rational-elliptic-core.js");
const {buildFiniteModel,finiteArtifact,auditFiniteLibrary,addFiniteScalar,ref}=require("./finite-polynomial-expressions.js");
const SOURCE_HASHES={
 "universal-integer-polynomial.json":"27a840c06c68bfae88da84a934d6e7f0ca2778dd3e56ec2bf3b4d4eb8171fe04",
 "accuracy-integer-polynomial.json":"6d1a4f92baa7f4931fa053875639d1f5c80a18498e5342fc1ac43b06bd6f52c6"
};
const hash=x=>crypto.createHash("sha256").update(x).digest("hex");
class Allocation {
 constructor(parameters){this.next=parameters;}
 take(n){if(!Number.isSafeInteger(n)||n<0)throw Error("Bad allocation");const p=this.next;this.next+=n;
  if(!Number.isSafeInteger(this.next))throw Error("Variable index exceeds exact integer range");return p;}
}
class Translator {
 constructor(library){this.library=library;this.constants=new Map();this.extraConstants={};}
 witnesses(name){return this.library.templates[this.library.id(name)].witnessCount;}
 fixedScalar(value){
  if(this.constants.has(value))return this.constants.get(value);
  if(!/^[1-9][0-9]*$/.test(value))throw Error("This compiler expects positive nontrivial fixed scalar constants");
  const name="integer_constant_"+this.constants.size,templateName="scalar."+name;
  this.extraConstants[name]=value;addFiniteScalar(this.library,ref(name),templateName);
  const entry={valueRef:name,template:this.library.id(templateName)};
  this.constants.set(value,entry);return entry;
 }
 translate(source,{name,sourceInputCount,naturalInputs,outputMode,sourceFile,sourceHash,powerRecipe}){
  const parameterCount=5*(sourceInputCount+(outputMode==="value"?1:0)),allocation=new Allocation(parameterCount),
   generator=[allocation.take(1),allocation.take(1),allocation.take(1)],sourceVariables=[],varRefs=new Map(),
   sourceNodePoints=[],operations=[],constantDefinitions=[],constantRefs=new Map(),
   natural=this.library.id("natural"),addition=this.library.id("raw_add"),multiplication=this.library.id("multiply");
  const explicit=source.variables||Array.from({length:source.variableCount},(_,index)=>({index,kind:index<sourceInputCount?"input":"witness"}));
  const inputs=explicit.filter(v=>v.kind==="input");
  if(inputs.length!==sourceInputCount||inputs.some((v,i)=>v.index!==i))throw Error("Source inputs must be the first variables");
  for(const v of explicit){
   const isInput=v.kind==="input",point=isInput?5*v.index:allocation.take(5);
   const naturalStart=!isInput||naturalInputs?allocation.take(this.witnesses("natural")):null;
   varRefs.set(v.index,point);sourceVariables.push([v.index,point,naturalStart]);
  }
  for(let i=0;i<source.nodes.length;i++){
   const n=source.nodes[i];let out;
   if(n.op==="var"){
    if(!varRefs.has(n.args[0]))throw Error("A source variable escapes its local template");
    out=varRefs.get(n.args[0]);
   }else if(n.op==="const"){
    const value=n.args[0];
    if(value==="0")out=-1;else if(value==="1")out=-2;else if(value==="-1")out=-3;
    else if(constantRefs.has(value))out=constantRefs.get(value);
    else{
     const entry=this.fixedScalar(value);out=allocation.take(5);
     const witnessStart=allocation.take(this.library.templates[entry.template].witnessCount);
     constantRefs.set(value,out);constantDefinitions.push({...entry,point:out,witnessStart,firstSourceNode:i});
    }
   }else if(n.op==="add"||n.op==="mul"){
    if(n.args.length!==2||n.args.some(j=>j<0||j>=i))throw Error("Invalid source edge");
    out=allocation.take(5);
    const w=allocation.take(this.witnesses(n.op==="add"?"raw_add":"multiply"));
    operations.push([n.op==="add"?0:1,i,sourceNodePoints[n.args[0]],sourceNodePoints[n.args[1]],out,w]);
   }else if(n.op==="call"){
    if(!powerRecipe||n.args.length!==5||n.args[0]!==0||n.args.slice(1,4).some(j=>j<0||j>=i))throw Error("Unexpected source call");
    const block=source.witnessBlocks.find(b=>b.start===n.args[4]);
    if(!block||block.length!==79)throw Error("Unexpected source witness block");
    out=allocation.take(5);const w=allocation.take(powerRecipe.witnessCount);
    operations.push([2,i,...n.args.slice(1,4).map(j=>sourceNodePoints[j]),out,w]);
   }else throw Error("Unexpected source operation "+n.op);
   sourceNodePoints.push(out);
  }
  return {format:"model-evaluation-polynomial-recipe-v1",name,parameterCount,variableCount:allocation.next,
   witnessCount:allocation.next-parameterCount,sourceInputCount,naturalInputs,outputMode,
   sourceFile,sourceHash,sourceRoot:source.root,sourceVariableCount:source.variableCount,
   generator,sourceVariables,sourceNodePoints,constantDefinitions,operations,
   operationTemplates:{natural,addition,multiplication,power:powerRecipe?powerRecipe.name:null},
   rootEquality:[sourceNodePoints[source.root],outputMode==="value"?5*sourceInputCount:-1]};
 }
}
function variable(i){return ["var",i];}
function variables(start,length){return Array.from({length},(_,i)=>variable(start+i));}
function composition(name,parameterCount,build){
 const a=new Allocation(parameterCount),explicitWitnessRanges=[],calls=[];
 const fresh=n=>{const start=a.take(n);explicitWitnessRanges.push([start,n]);return start;};
 const call=(kind,target,parameters,witnessCount)=>{
  const witnessStart=a.take(witnessCount);calls.push({kind,target,parameters,witnessStart,witnessCount});
 };
 build(fresh,call);
 return {format:"sum-of-squares-composition-v1",name,parameterCount,variableCount:a.next,witnessCount:a.next-parameterCount,
  explicitWitnessRanges,calls};
}
function constructorDefinitions(){
 return {
  expressionSemantics:"All local variables are rational. Template calls substitute their parameter expressions and a disjoint consecutive witness block. A recipe is the sum of squares of all its prescribed constraint polynomials. Repeated finite substitution produces one polynomial in Z[e,n,w].",
scalarNodeEncoding:{const:"args=[decimal integer]",var:"args=[local variable index]",add:"args=[left node,right node]",mul:"args=[left node,right node]",
   call:"args=[library template index,parameter node indices...,witnessStart]. The callee root polynomial is substituted literally. Nodes are topologically ordered.",
   fixed_integer:"args=[fixed integer expression]",psi_component:"args=[fixed integer index expression,x0 node,x1 node,y0 node,y1 node,component 0 or 1]",
   finite_guard_product:"args=[fixed cutoff expression,fifteen coordinate nodes in point-major order]"},
  templateMeaning:"Only nodes and root define the template polynomial; formulas and metadata are diagnostic. The first parameterCount local variables are parameters. The remaining local variables are existential witnesses.",
  modelRecordEncoding:{
   sourceVariables:"Each row is [source variable index,point reference,naturalWitnessStart or null]. A non-null start contributes a call to the operationTemplates.natural polynomial on that point.",
   constantDefinitions:"Each record contributes its scalar template polynomial on the local generator P and record.point, using record.witnessStart. Its fixed coefficient is bound in library.fixedConstants.",
   operation0:"[0,source node,left point,right point,output point,witnessStart] contributes the addition template polynomial.",
   operation1:"[1,source node,left point,right point,output point,witnessStart] contributes the multiplication template polynomial.",
   operation2:"[2,source node,parameter point 0,parameter point 1,parameter point 2,output point,witnessStart] contributes the power-value recipe polynomial.",
   rootEquality:"The five coordinate differences of its two point references are constraints.",
   diagnosticFields:"Source node numbers, sourceNodePoints, source hashes and provenance identify the translation; they add no constraints beyond the listed calls and rootEquality."
  },
  compositionMeaning:"For sum-of-squares-composition-v1, each call contributes its callee polynomial evaluated at call.parameters, using call.witnessStart. kind=template selects a library template; kind=recipe selects a named recipe. Scalar parameters of the form [var,i] mean local variable i. Sum the squares of all contributed polynomials.",
  rootVariableOrdering:"The universal recipe's local variables 0 and 1 are e and n. Its remaining variables, in increasing index order, are the fixed rational witness tuple. Variable ranges declare variables, not additional equations.",
  pointReferences:"A nonnegative point reference s means variables s,...,s+4. -1 means (1,0,0,0,0). -2 means (0,g0,-145,g1,g2). -3 means (0,g0,-145,-g1,-g2), using the recipe's three generator variables.",
  generatorConstraints:["8*g0-1641","4*g1+15465","32*g2-87483"],
  modelRecipeConstraints:"Include the three generator constraints; each listed natural call; each scalar-constant call on P and its output; every listed add/multiply/power-evaluation call; and the five differences in rootEquality. Square each polynomial and add. No source operation is a separate zero condition unless expressed by this recipe.",
  libraryCallBinding:"For a callee with p parameter variables, replace its variables 0,...,p-1 by the supplied scalar expressions; replace its variable p+j by the caller variable witnessStart+j.",
  quadraticField:{basis:"1,sqrt(2)",addition:"componentwise",product:"(a,b)*(c,d)=(ac+2bd,ad+bc)",A:["-11243","7950"]},
  psiNormalization:{
   definition:"psi_n=f_n(x) when n is odd; psi_n=2*y*f_n(x) when n is even; psi_-n=-psi_n.",
   bases:["f_0=0","f_1=f_2=1","f_3=3*x^4+6*A*x^2-A^2","f_4=2*(x^6+5*A*x^4-5*A^2*x^2-A^3)"],
   recurrenceEven:"f_(2m)=f_m*(f_(m+2)*f_(m-1)^2-f_(m-2)*f_(m+1)^2), m>=3",
   recurrenceOdd:"For m>=2 set L=f_(m+2)*f_m^3, R=f_(m-1)*f_(m+1)^3 and D=16*(x^3+A*x)^2. f_(2m+1)=D*L-R for even m, and L-D*R for odd m.",
   componentMeaning:"psi_component returns the indicated coefficient in basis 1,sqrt(2), after these finite polynomial recurrences and field multiplication are expanded."
  },
  fixedPointCodes:{
   P:["0","1641/8","-145","-15465/4","87483/32"],
   zero:"iota(0)=(1,0,0,0,0)",
   positive:"For n>0 evaluate g=psi_n at P, x_n=x(P)-psi_(n+1)(P)*psi_(n-1)(P)/g^2, y_n=psi_(2n)(P)/(2*g^4). Its code is (0,coeff0(x_n),coeff1(x_n),coeff0(y_n),coeff1(y_n)).",
   negative:"iota(-n) is obtained from iota(n) by negating the two y coefficients.",
   nonzeroDenominators:"P is nontorsion, so these fixed coefficient calculations have nonzero denominators."
  },
  finiteGuard:{
   bound:"T is the fixed integer from fixedConstants, never a quantified variable.",
   factor:"For a,b,c in [-T,T] with a*b!=c, write the fifteen coordinates of iota(a),iota(b),iota(c) as A_j/B_j with B_j>0, gcd(A_j,B_j)=1. Put D=product_j B_j. The factor is sum_j (D*X_j-(D/B_j)*A_j)^2.",
   polynomial:"The product of these factors. An empty product is 1."
  },
  coefficientAlgorithms:{
   catalogue:"For every 1<=r<W with gcd(r,W)=1, list the first k primes p>B with p congruent to r modulo W. catalogue_product is their product and catalogue_max their maximum.",
   localMultiplier:"For N>0, least_formal_multiple(N) is the least m>=1 such that 1/x([m]P)=(a+b*sqrt(2))/c, c>0, gcd(a,b,c)=1, satisfies N^4|a, N^4|b, gcd(c,N)=1.",
   termination:"The prime lists exist by Dirichlet's theorem. The least formal multiple exists because the prescribed local formal subgroups have finite index. Other operators are ordinary finite integer arithmetic."
  }
 };
}
function buildUniversalExpression(directory=__dirname){
 const read=name=>{
  const bytes=fs.readFileSync(path.join(directory,name)),actual=hash(bytes);
  if(actual!==SOURCE_HASHES[name])throw Error("Pinned source changed: "+name);
  return {source:JSON.parse(bytes),hash:actual};
 };
 const h=read("universal-integer-polynomial.json"),acc=read("accuracy-integer-polynomial.json");
 if(JSON.stringify(h.source.templates)!==JSON.stringify(acc.source.templates))throw Error("Power template mismatch");
 const library=buildFiniteModel(),translator=new Translator(library),powerSource=h.source.templates[0],
  power=translator.translate(powerSource,{name:"power_value",sourceInputCount:3,naturalInputs:false,outputMode:"value",
   sourceFile:"universal-integer-polynomial.json#templates/0",sourceHash:hash(JSON.stringify(powerSource))}),
  halting=translator.translate(h.source,{name:"halting",sourceInputCount:2,naturalInputs:true,outputMode:"zero",
   sourceFile:"universal-integer-polynomial.json",sourceHash:h.hash,powerRecipe:power}),
  accuracy=translator.translate(acc.source,{name:"accuracy",sourceInputCount:3,naturalInputs:true,outputMode:"zero",
   sourceFile:"accuracy-integer-polynomial.json",sourceHash:acc.hash,powerRecipe:power});
 library.define("raw_trace_ratio",Array.from({length:11},(_,i)=>"a"+i),(b,p)=>{
  const e=new EllipticCore(b);return e.traceRatio(p.slice(0,5),p.slice(5,10),p[10]);
 },{meaning:"r=Tr(z(J)/z(H))/2 with H nonzero",preconditions:"H,J belong to D"});
 library.define("strict_close",["a","r"],(b,p)=>new EllipticCore(b).closeTo(...p),{meaning:"abs(a-r)<1/8"});
 const trace=library.id("raw_trace_ratio"),close=library.id("strict_close");
 const bridge=composition("bridge",6,(fresh,call)=>{
  const H=fresh(5),J=fresh(5),r=fresh(1);
  call("recipe","accuracy",variables(1,5).concat(variables(H,5),variables(J,5)),accuracy.witnessCount);
  call("template",trace,variables(H,5).concat(variables(J,5),[variable(r)]),library.templates[trace].witnessCount);
  call("template",close,[variable(0),variable(r)],library.templates[close].witnessCount);
 });
 const universal=composition("universal",2,(fresh,call)=>{
  const A=fresh(5),B=fresh(5);
  call("recipe","halting",variables(A,5).concat(variables(B,5)),halting.witnessCount);
  call("recipe","bridge",[variable(0),...variables(A,5)],bridge.witnessCount);
  call("recipe","bridge",[variable(1),...variables(B,5)],bridge.witnessCount);
 });
 const expected={power_value:17786698,halting:292887770443,accuracy:292888578910,bridge:292888578934,universal:878664928321};
 for(const recipe of [power,halting,accuracy,bridge,universal])if(recipe.witnessCount!==expected[recipe.name])throw Error("Count differs from specification: "+recipe.name);
 const finiteLibrary=finiteArtifact(library,translator.extraConstants,{
  meaning:"The fixed polynomial library used by the universal expression. All fixed integer coefficients are bound."});
 auditFiniteLibrary(finiteLibrary);
 return {format:"universal-rational-polynomial-expression-v1",status:"Candidate finite polynomial expression; full implementation and arithmetic completion audits pending.",
  parameterNames:["e","n"],parameterDomain:"ordinary nonnegative integers",witnessDomain:"rational numbers",
  witnessCount:universal.witnessCount,rootRecipe:"universal",definitions:constructorDefinitions(),
  library:finiteLibrary,recipes:{power_value:power,halting,accuracy,bridge,universal},
  sourceHashes:SOURCE_HASHES,
  intendedTheorem:"For every e,n in N, the polynomial has a rational witness tuple iff the encoded program e halts on input n.",
  limitations:["This artifact is a finite expression for a polynomial, not an expanded monomial list.",
   "The universality claim still requires the complete translation audit and the recorded arithmetic dependencies."]};
}
module.exports={Allocation,Translator,composition,constructorDefinitions,buildUniversalExpression,SOURCE_HASHES,hash};
if(require.main===module){
 const a=buildUniversalExpression(),data=JSON.stringify(a)+"\n",output=path.join(__dirname,"universal-rational-equation.json");
 fs.writeFileSync(output,data);
 const report={written:true,bytes:Buffer.byteLength(data),sha256:hash(data),witnessCount:a.witnessCount,
  recipes:Object.fromEntries(Object.entries(a.recipes).map(([k,v])=>[k,{parameters:v.parameterCount,witnesses:v.witnessCount,
   operations:v.operations?.length||0,sourceVariables:v.sourceVariables?.length||0}])),
  limitation:a.status};
 fs.writeFileSync(path.join(__dirname,"universal-rational-expression-build.json"),JSON.stringify(report,null,2)+"\n");
 console.log(JSON.stringify(report,null,2));
}

