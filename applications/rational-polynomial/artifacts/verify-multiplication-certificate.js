"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {buildCertificateLibrary}=require("./multiplication-certificate.js");
const {auditLibrary,expandTemplate}=require("./rational-polynomial-library.js");
const {addFiniteGuard,bindMultiplication,addNaturalModel}=require("./rational-model-assembly.js");
const ar=require("./rational-field-arithmetic.js");
const constants=require("./fixed-certificate-constants.js");
const {q,qadd,qsub,qmul,qinv,f,add,sub,neg,mul,inv,div,scale,equal,norm,P,HALF,A,pointAdd,pointNeg,pointMul,coordinates}=ar;
const assert=(b,s)=>{if(!b)throw Error(s);};
const fields=x=>[q(x[0],x[2]),q(x[1],x[2])];
const fieldFrom=(a,b)=>f(a[0]*b[1],b[0]*a[1],a[1]*b[1]);
const pointFrom=p=>p[0][0]===p[0][1]?null:[fieldFrom(p[1],p[2]),fieldFrom(p[3],p[4])];
const pointKey=p=>JSON.stringify(p.map(x=>x.map(String)));
const halves=new Map();
for(const n of [0,1,2,3,4])halves.set(pointKey(coordinates(pointMul(P,n))),pointMul(HALF,n));
function putF(m,name,x){fields(x).forEach((v,i)=>m[name+"."+i]=v);}
function putP(m,name,x){coordinates(x).forEach((v,i)=>m[name+"."+i]=v);}
const logTerms=JSON.parse(fs.readFileSync(path.join(__dirname,"formal-logarithm-25.json"))).terms;
function power(x,n){let y=f(1);while(n){if(n%2)y=mul(y,x);n=Math.floor(n/2);if(n)x=mul(x,x);}return y;}
function logarithm(z){return logTerms.reduce((sum,t)=>add(sum,mul(f(...t.coefficient_pair),power(z,t.exponent))),f(0));}
const zOf=p=>p?div(neg(p[0]),p[1]):f(0);
const reciprocal=p=>p?inv(p[0]):f(0);
const conjugate=x=>f(x[0],-x[1],x[2]);
function groupData(C,first){
 const second=first.map((p,i)=>pointAdd(p,pointNeg(C[i]))),points=first.concat(second),
  zs=points.map(zOf),logs=zs.map(logarithm),rs=points.map(reciprocal),
  ratios=[0,1].flatMap(s=>[1,2,3].map(i=>div(logs[4*s+i],logs[4*s]))),w={};
 first.forEach((p,i)=>putP(w,"first."+i,p));second.forEach((p,i)=>putP(w,"second."+i,p));
 zs.forEach((x,i)=>putF(w,"z."+i,x));logs.forEach((x,i)=>putF(w,"L."+i,x));rs.forEach((x,i)=>putF(w,"reciprocal."+i,x));
 for(let s=0;s<2;s++)for(let i=1;i<=3;i++)putF(w,"ratio."+s+"."+i,ratios[3*s+i-1]);
 w.log_first_inverse=qinv(norm(logs[0]));w.log_second_inverse=qinv(norm(logs[4]));
 const tests=rs.slice(0,4).concat(rs.slice(4).map(conjugate),[0,1,2].map(i=>sub(ratios[i],conjugate(ratios[3+i]))),
  [sub(mul(ratios[0],ratios[1]),ratios[2])]);
 return {w,tests};
}
function witnesses(name,parameters,context={}){
 const w={};
 if(name==="member"){
  const p=pointFrom(parameters);if(!p)return w;
  const key=pointKey(parameters);if(!halves.has(key))throw Error("No independently supplied half");
  const h=halves.get(key);putF(w,"member.X",h[0]);putF(w,"member.Y",h[1]);
  putF(w,"member.slope",div(add(scale(mul(h[0],h[0]),3),A),scale(h[1],2)));
  w["member.inverse_norm_y"]=qinv(norm(h[1]));
 }else if(name==="raw_add"){
  const p=pointFrom(parameters.slice(0,5)),r=pointFrom(parameters.slice(5,10));if(!p||!r)return w;
  if(!equal(p[0],r[0])){
   const d=sub(r[0],p[0]);w["add.general.inverse_norm"]=qinv(norm(d));
   putF(w,"add.general.slope",div(sub(r[1],p[1]),d));
  }else if(equal(p[1],r[1])){
   w["add.double.inverse_norm"]=qinv(norm(p[1]));
   putF(w,"add.double.slope",div(add(scale(mul(p[0],p[0]),3),A),scale(p[1],2)));
  }
 }else if(name==="raw_z"){
  const p=pointFrom(parameters.slice(0,5));if(p)w["z.inverse_norm"]=qinv(norm(p[1]));
 }else if(name==="test_group")return context.group.w;
 return w;
}
function constructAndEvaluate(library,id,parameters,context={}){
 const t=library.templates[id],given=Array.from({length:t.variableCount},()=>q(0)),
  w=witnesses(t.name,parameters,context),byIndex=new Map(t.variables.map(v=>[v.index,v])),values=[];
 parameters.forEach((v,i)=>given[i]=v);
 for(const v of t.variables){
  if(v.kind==="input")continue;
  if(Object.prototype.hasOwnProperty.call(w,v.name))given[v.index]=w[v.name];
  if(v.name.startsWith("fixed_")){const [a,d]=v.name.slice(6).split("/");given[v.index]=q(a,d);}
 }
 for(const n of t.nodes){
  if(n.op==="const")values.push(q(n.args[0]));
  else if(n.op==="var"){
   const variable=byIndex.get(n.args[0]);
   if(variable?.name==="guard_inverse"){
    const g=values[t.metadata.guardNode];given[n.args[0]]=g[0]?qinv(g):q(0);
   }
   values.push(given[n.args[0]]);
  }else if(n.op==="add")values.push(qadd(values[n.args[0]],values[n.args[1]]));
  else if(n.op==="mul")values.push(qmul(values[n.args[0]],values[n.args[1]]));
  else if(n.op==="call"){
   const target=n.args[0],callee=library.templates[target],start=n.args.at(-1),
     result=constructAndEvaluate(library,target,n.args.slice(1,-1).map(j=>values[j]),context);
   result.assignment.slice(callee.parameterCount).forEach((v,k)=>given[start+k]=v);values.push(result.value);
  }else throw Error("Bad operation");
 }
 return {value:values[t.root],assignment:given};
}
function evaluateFlat(t,assignment){
 const values=[];
 for(const n of t.nodes){
  if(n.op==="const")values.push(q(n.args[0]));
  else if(n.op==="var")values.push(assignment[n.args[0]]);
  else if(n.op==="add")values.push(qadd(values[n.args[0]],values[n.args[1]]));
  else if(n.op==="mul")values.push(qmul(values[n.args[0]],values[n.args[1]]));
  else throw Error("Flat polynomial not expanded");
 }
 return values[t.root];
}
const builder=buildCertificateLibrary(),library=builder.artifact(),structure=auditLibrary(library),
 groupId=builder.id("test_group"),expanded=expandTemplate(library,groupId),
 C=[4,4,8,8].map(n=>pointMul(P,n)),first=[2,1,3,4].map(n=>pointMul(P,n)),
 group=groupData(C,first),parameters=C.flatMap(coordinates).concat(group.tests.flatMap(fields)),
 result=constructAndEvaluate(library,groupId,parameters,{group});
assert(result.value[0]===0n,"test group rejected exact witnesses");
assert(evaluateFlat(expanded,result.assignment)[0]===0n,"expanded group rejected exact witnesses");
const changed=parameters.slice();changed[changed.length-1]=qadd(changed.at(-1),q(1));
const changedResult=constructAndEvaluate(library,groupId,changed,{group});
assert(changedResult.value[0]!==0n,"test group ignored changed output");
const changedFlat=evaluateFlat(expanded,changedResult.assignment);
assert(changedFlat[0]===changedResult.value[0]&&changedFlat[1]===changedResult.value[1],"hierarchical substitution changed polynomial value");
assert(JSON.stringify(library.templates[groupId].metadata.precisions)===JSON.stringify([1,1,1,1,1,1,1,1,25,25,25,25]),"precision metadata");
addFiniteGuard(builder,1n,"guard_test");const guardId=builder.id("guard_test");let guardCases=0;
for(let a=-1;a<=1;a++)for(let b=-1;b<=1;b++)for(let c=-1;c<=1;c++){
 const params=[a,b,c].flatMap(n=>coordinates(pointMul(P,n))),r=constructAndEvaluate(builder.artifact(),guardId,params);
 assert((r.value[0]===0n)===(a*b===c),"finite guard mismatch "+[a,b,c]);guardCases++;
}
const outside=constructAndEvaluate(builder.artifact(),guardId,[2,2,1].flatMap(n=>coordinates(pointMul(P,n))));
assert(outside.value[0]===0n,"finite guard incorrectly excludes outside box");guardCases++;
const sieve=Array(501).fill(true);sieve[0]=sieve[1]=false;
for(let i=2;i*i<=500;i++)if(sieve[i])for(let j=i*i;j<=500;j+=i)sieve[j]=false;
for(let i=0;i<=500;i++)assert(constants.isPrime(i)===sieve[i],"prime test mismatch");
const cat=constants.catalogueProduct(4n,2,4n);
assert(cat.product===5005n&&cat.maximum===13n&&cat.number===4n,"small catalogue");
assert(constants.W===4n*constants.P0,"small modulus");
assert(constants.localMultiplier(1n)===1n,"empty local condition");
let depthCases=0;
for(const Ns of [2n,3n,6n])for(const a of [1n,2n])for(const d of [1n,5n]){
 const reciprocalValue=f(Ns**4n*a,Ns**4n,d);
 assert(ar.localDepthCondition([inv(reciprocalValue),f(1)],Ns),"divisible reciprocal coefficients");depthCases++;
}
bindMultiplication(builder,{cstar:4n,ell:12n,T:1n},"toy_multiply");
addNaturalModel(builder,"toy_multiply","toy_natural");
const toyStructure=auditLibrary(builder.artifact());
const data=fs.readFileSync(path.join(__dirname,"multiplication-certificate-library.json")),
 report={passed:true,certificateStructure:structure,groupExactWitnessCases:1,groupChangedOutputCases:1,
  groupFlatExpansionNodes:expanded.nodes.length,guardCases,primalityChecks:501,smallCatalogueChecked:true,localDepthCases:depthCases,
  toyAssembly:toyStructure.templates.filter(x=>x.name.startsWith("toy_")),
  certificateLibrarySHA256:crypto.createHash("sha256").update(data).digest("hex"),
  limitations:["The large prescribed constants have not been evaluated.",
   "The toy assembly checks syntax and substitution with deliberately small constants; it does not claim correct index multiplication.",
   "Finite checks do not prove the arithmetic height, prime-pattern or pointwise-converse inputs."]};
fs.writeFileSync(path.join(__dirname,"multiplication-certificate-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

