"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {buildFiniteModel,finiteArtifact,auditFiniteLibrary,expandFiniteTemplate}=require("./finite-polynomial-expressions.js");
const {buildCertificateLibrary}=require("./multiplication-certificate.js");
const {bindMultiplication,addNaturalModel}=require("./rational-model-assembly.js");
const assert=(x,s)=>{if(!x)throw Error(s);};
function localHash(t){
 const H=s=>crypto.createHash("sha256").update(s).digest("hex"),hs=[];
 for(const n of t.nodes){
  if(n.op==="const"||n.op==="var")hs.push(H(n.op+":"+n.args[0]));
  else if(n.op==="add"||n.op==="mul")hs.push(H(n.op+":"+n.args.map(i=>hs[i]).join(":")));
  else if(n.op==="call")hs.push(H("call:"+n.args[0]+":"+n.args.at(-1)+":"+n.args.slice(1,-1).map(i=>hs[i]).join(":")));
  else throw Error("An unexpanded constructor remains");
 }
 return hs[t.root];
}
const symbolic=finiteArtifact(buildFiniteModel()),baseAudit=auditFiniteLibrary(symbolic),checks=[];
for(const fixture of [{cstar:4n,ell:12n,T:1n},{cstar:8n,ell:144n,T:0n}]){
 const direct=buildCertificateLibrary();bindMultiplication(direct,fixture);addNaturalModel(direct);
 for(let id=9;id<direct.templates.length;id++){
  const expanded=expandFiniteTemplate(symbolic,id,fixture),a=localHash(expanded),b=localHash(direct.templates[id]);
  assert(a===b,"Finite expansion differs in "+direct.templates[id].name);
  assert(expanded.variableCount===direct.templates[id].variableCount,"Variable count changed");
  checks.push({fixture:Object.fromEntries(Object.entries(fixture).map(([k,v])=>[k,String(v)])),template:direct.templates[id].name,hash:a});
 }
}
let mutations=0;
function reject(mutator){
 const a=JSON.parse(JSON.stringify(symbolic));mutator(a);let rejected=false;
 try{auditFiniteLibrary(a);}catch(_){rejected=true;}
 assert(rejected,"Invalid constructor binding accepted");mutations++;
}
reject(a=>a.fixedConstants.P0=["literal","1"]);
reject(a=>a.templates[9].nodes.find(n=>n.op==="psi_component").args[1]=999999);
reject(a=>a.templates[10].nodes.find(n=>n.op==="finite_guard_product").args[0]=["literal","1"]);
reject(a=>a.templates[11].nodes.find(n=>n.op==="fixed_integer").args[0]=["variable",0]);
const report={passed:true,checks,invalidBindingsRejected:mutations,
 variableCounts:baseAudit.templates.filter(t=>["multiply","natural"].includes(t.name)),
 limitation:"Fixture values only verify expansion rules. They never replace the prescribed fixed constants in the candidate universal expression."};
fs.writeFileSync(path.join(__dirname,"finite-polynomial-expression-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

