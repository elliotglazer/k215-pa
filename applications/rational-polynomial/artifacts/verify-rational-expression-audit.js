"use strict";
const fs=require("node:fs"),path=require("node:path");
const {auditBundle,readInputs}=require("./audit-rational-expression.js");
const bundle=JSON.parse(fs.readFileSync(path.join(__dirname,"universal-rational-equation.json"))),
 {sources,baseModel}=readInputs(),model={templates:baseModel},accepted=auditBundle(bundle,sources,model),rejected=[];
function trial(name,mutate){
 const candidate={...bundle,recipes:{...bundle.recipes},library:{...bundle.library,templates:bundle.library.templates.slice(),fixedConstants:{...bundle.library.fixedConstants}}};
 mutate(candidate);let message;
 try{auditBundle(candidate,sources,model);}catch(e){message=e.message;}
 if(!message)throw Error("Audit accepted mutation "+name);rejected.push({name,message});
}
trial("missing natural constraint",a=>{
 const r=a.recipes.halting={...a.recipes.halting,sourceVariables:a.recipes.halting.sourceVariables.slice()};
 r.sourceVariables[0]=r.sourceVariables[0].slice();r.sourceVariables[0][2]=null;
});
trial("changed arithmetic operation",a=>{
 const r=a.recipes.halting={...a.recipes.halting,operations:a.recipes.halting.operations.slice()};
 r.operations[0]=r.operations[0].slice();r.operations[0][0]=1-r.operations[0][0];
});
trial("power value forced to zero",a=>a.recipes.power_value={...a.recipes.power_value,rootEquality:[a.recipes.power_value.rootEquality[0],-1]});
trial("aliased witness block",a=>{
 const r=a.recipes.halting={...a.recipes.halting,operations:a.recipes.halting.operations.slice()};
 r.operations[1]=r.operations[1].slice();r.operations[1][r.operations[1].length-1]=r.operations[0].at(-1);
});
trial("bridge input changed",a=>{
 const r=a.recipes.bridge={...a.recipes.bridge,calls:a.recipes.bridge.calls.slice()};
 r.calls[2]={...r.calls[2],parameters:[["var",1],r.calls[2].parameters[1]]};
});
trial("outer input n replaced by e",a=>{
 const r=a.recipes.universal={...a.recipes.universal,calls:a.recipes.universal.calls.slice()};
 r.calls[2]={...r.calls[2],parameters:[["var",0],...r.calls[2].parameters.slice(1)]};
});
trial("changed fixed normalization",a=>a.library.fixedConstants.ell=["literal","12"]);
trial("removed trace guard through coefficient mutation",a=>{
 const id=a.library.templates.findIndex(t=>t.name==="raw_trace_ratio");
 const t=a.library.templates[id]={...a.library.templates[id],nodes:a.library.templates[id].nodes.slice()};
 const at=t.nodes.findIndex(n=>n.op==="const"&&n.args[0]==="1");
 t.nodes[at]={op:"const",args:["0"]};
});
trial("wrong scalar constant binding",a=>{
 const r=a.recipes.halting={...a.recipes.halting,constantDefinitions:a.recipes.halting.constantDefinitions.slice()};
 r.constantDefinitions[0]={...r.constantDefinitions[0],valueRef:r.constantDefinitions[1].valueRef};
});
const report={passed:true,fullAuditPassed:accepted.valid,mutationsRejected:rejected,
 limitation:"These tests check the assembly auditor; the arithmetic model and source compiler proofs remain separate obligations."};
fs.writeFileSync(path.join(__dirname,"rational-expression-audit-checks.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));

