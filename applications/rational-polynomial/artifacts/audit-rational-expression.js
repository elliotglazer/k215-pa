"use strict";
const fs=require("node:fs"),path=require("node:path");
const {SOURCE_HASHES,hash,constructorDefinitions}=require("./rational-circuit-translator.js");
const {auditFiniteLibrary,addFiniteScalar}=require("./finite-polynomial-expressions.js");
const {PolynomialLibrary}=require("./rational-polynomial-library.js");
const {EllipticCore}=require("./rational-elliptic-core.js");
const assert=(x,s)=>{if(!x)throw Error(s);};
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const integer=x=>Number.isSafeInteger(x)&&x>=0;
function checkCoverage(parameterCount,variableCount,spans,label){
 assert(integer(parameterCount)&&integer(variableCount)&&variableCount>=parameterCount,"Invalid size "+label);
 const sorted=spans.filter(s=>s[1]!==0).sort((a,b)=>a[0]-b[0]);let end=parameterCount;
 for(const [start,length] of sorted){
  assert(integer(start)&&integer(length)&&start===end,"Gap or overlap "+label+" at "+end);
  end+=length;assert(Number.isSafeInteger(end),"Unsafe range");
 }
 assert(end===variableCount,"Incomplete coverage "+label);
}
function sourceInputs(source,count){
 const variables=source.variables||Array.from({length:source.variableCount},(_,i)=>({index:i,kind:i<count?"input":"witness"}));
 assert(variables.filter(v=>v.kind==="input").length===count,"Source input count");
 return variables;
}
function auditEvaluation(bundle,r,source,{inputs,naturalInputs,mode,sourceHash}){
 const library=bundle.library,ts=library.templates;
 assert(r.format==="model-evaluation-polynomial-recipe-v1","Unknown recipe format");
 assert(r.sourceInputCount===inputs&&r.naturalInputs===naturalInputs&&r.outputMode===mode,"Recipe interface mismatch");
 assert(r.parameterCount===5*(inputs+(mode==="value"?1:0)),"Parameter width mismatch");
 assert(r.witnessCount===r.variableCount-r.parameterCount,"Witness count mismatch");
 assert(r.sourceHash===sourceHash&&r.sourceRoot===source.root&&r.sourceVariableCount===source.variableCount,"Pinned source metadata mismatch");
 const table=r.operationTemplates;
 assert(ts[table.natural]?.name==="natural"&&ts[table.addition]?.name==="raw_add"&&ts[table.multiplication]?.name==="multiply","Wrong arithmetic templates");
 const power=table.power===null?null:bundle.recipes[table.power];
 assert((!!power)===(!!source.witnessBlocks?.length),"Unexpected power interface");
 if(power)assert(power.name==="power_value","Wrong power recipe");
 assert(r.generator.length===3&&r.generator.every(integer),"Invalid generator variables");
 const spans=r.generator.map(i=>[i,1]),vars=sourceInputs(source,inputs),varMap=new Map();
 assert(vars.length===r.sourceVariables.length,"Source variable lost");
 for(let i=0;i<vars.length;i++){
  const v=vars[i],row=r.sourceVariables[i];
  assert(row.length===3&&row[0]===v.index,"Source variable reordered");
  const point=row[1],start=row[2],input=v.kind==="input";
  assert(integer(point),"Invalid point reference");
  if(input)assert(point===5*v.index&&v.index<inputs,"Input point changed");
  else spans.push([point,5]);
  if(!input||naturalInputs){
   assert(integer(start),"Missing natural-number constraint");
   spans.push([start,ts[table.natural].witnessCount]);
  }else assert(start===null,"Unwanted restriction on signed template parameter");
  assert(!varMap.has(v.index),"Duplicate source variable");varMap.set(v.index,point);
 }
 const constants=new Map(),constantPoints=new Set();
 for(const c of r.constantDefinitions){
  const value=library.fixedConstants[c.valueRef];
  assert(value?.[0]==="literal"&&/^[1-9][0-9]*$/.test(value[1]),"Nonliteral or nonpositive source coefficient");
  assert(!["1"].includes(value[1])&&!constants.has(value[1]),"Unnecessary or duplicate constant");
  const target=ts[c.template];
  assert(target?.parameterCount===10&&target.witnessCount===1&&same(target.metadata.fixedIndex,["ref",c.valueRef]),"Wrong fixed scalar binding");
  assert(integer(c.point)&&integer(c.witnessStart),"Bad scalar variable range");
  assert(source.nodes[c.firstSourceNode]?.op==="const"&&source.nodes[c.firstSourceNode].args[0]===value[1],"Scalar source provenance");
  spans.push([c.point,5],[c.witnessStart,1]);constants.set(value[1],c.point);constantPoints.add(c.point);
 }
 const opMap=new Map();
 for(const op of r.operations){
  assert(Array.isArray(op)&&[0,1,2].includes(op[0])&&integer(op[1]),"Bad operation record");
  assert(!opMap.has(op[1]),"Duplicate operation");opMap.set(op[1],op);
 }
 assert(r.sourceNodePoints.length===source.nodes.length,"Missing source node mapping");
 const usedConstants=new Set();let operationCount=0;
 for(let i=0;i<source.nodes.length;i++){
  const n=source.nodes[i],point=r.sourceNodePoints[i],op=opMap.get(i);
  if(n.op==="var"){
   assert(point===varMap.get(n.args[0])&&!op,"Variable map changed or escaped private scope");
  }else if(n.op==="const"){
   const value=n.args[0],expected=value==="0"?-1:value==="1"?-2:value==="-1"?-3:constants.get(value);
   assert(point===expected&&expected!==undefined&&!op,"Constant map changed");
   if(!["0","1","-1"].includes(value))usedConstants.add(value);
  }else if(n.op==="add"||n.op==="mul"){
   operationCount++;
   assert(op&&op.length===6&&op[0]===(n.op==="add"?0:1),"Operation kind changed");
   assert(n.args.length===2&&n.args.every(j=>integer(j)&&j<i),"Bad source order");
   assert(op[2]===r.sourceNodePoints[n.args[0]]&&op[3]===r.sourceNodePoints[n.args[1]]&&op[4]===point,"Operation operands changed");
   assert(integer(op[4])&&integer(op[5]),"Bad operation allocation");
   spans.push([op[4],5],[op[5],ts[n.op==="add"?table.addition:table.multiplication].witnessCount]);
  }else if(n.op==="call"){
   operationCount++;
   assert(power&&op&&op.length===7&&op[0]===2&&n.args.length===5&&n.args[0]===0,"Power call changed");
   assert(n.args.slice(1,4).every(j=>integer(j)&&j<i),"Bad power argument order");
   assert(same(op.slice(2,5),n.args.slice(1,4).map(j=>r.sourceNodePoints[j]))&&op[5]===point,"Power inputs/output changed");
   assert(integer(op[5])&&integer(op[6]),"Bad power allocation");
   const block=source.witnessBlocks.find(b=>b.start===n.args[4]);
   assert(block?.length===79,"Private power witnesses changed");
   spans.push([op[5],5],[op[6],power.witnessCount]);
  }else throw Error("Unsupported source operation");
 }
 assert(operationCount===r.operations.length&&usedConstants.size===constants.size,"Extraneous constraints");
 assert(same(r.rootEquality,[r.sourceNodePoints[source.root],mode==="value"?5*inputs:-1]),"Output equation changed");
 checkCoverage(r.parameterCount,r.variableCount,spans,r.name);
 return {name:r.name,sourceNodesChecked:source.nodes.length,sourceVariablesChecked:vars.length,
  operationsChecked:operationCount,witnesses:r.witnessCount,privateWitnessScopeChecked:true,completeVariableCoverage:true};
}
function varExpr(i){return ["var",i];}
function varExprs(start,count){return Array.from({length:count},(_,i)=>varExpr(start+i));}
function auditComposition(bundle,r,expectedParameters,buildExpected){
 assert(r.format==="sum-of-squares-composition-v1"&&r.parameterCount===expectedParameters,"Composition interface changed");
 assert(r.witnessCount===r.variableCount-r.parameterCount,"Composition witness count");
 const spans=r.explicitWitnessRanges.map(x=>x.slice());
 const expected=buildExpected(r.explicitWitnessRanges);
 assert(r.calls.length===expected.length,"Composition call count changed");
 for(let i=0;i<r.calls.length;i++){
  const c=r.calls[i],e=expected[i];
  assert(c.kind===e.kind&&c.target===e.target&&same(c.parameters,e.parameters),"Composition wiring changed");
  const t=c.kind==="recipe"?bundle.recipes[c.target]:bundle.library.templates[c.target];
  assert(t&&c.witnessCount===t.witnessCount&&c.parameters.length===t.parameterCount,"Composition callee interface");
  for(const p of c.parameters)assert(p[0]==="var"&&p.length===2&&integer(p[1])&&p[1]<r.variableCount,"Invalid composition expression");
  spans.push([c.witnessStart,c.witnessCount]);
 }
 checkCoverage(r.parameterCount,r.variableCount,spans,r.name);
 return {name:r.name,callsChecked:r.calls.length,witnesses:r.witnessCount,completeVariableCoverage:true};
}

function auditAdditionalTemplates(bundle,baseLength){
 const used=new Set(Object.values(bundle.recipes).flatMap(r=>(r.constantDefinitions||[]).map(c=>c.template)));
 for(let id=baseLength;id<bundle.library.templates.length;id++){
  const actual=bundle.library.templates[id],expected=new PolynomialLibrary();
  if(actual.name.startsWith("scalar.")){
   const name=actual.name.slice(7),value=bundle.library.fixedConstants[name];
   assert(used.has(id)&&value?.[0]==="literal"&&/^[1-9][0-9]*$/.test(value[1]),"Unexpected scalar template");
   addFiniteScalar(expected,["ref",name],actual.name);
  }else if(actual.name==="raw_trace_ratio"){
   expected.define(actual.name,Array.from({length:11},(_,i)=>"a"+i),(b,p)=>{
    const e=new EllipticCore(b);return e.traceRatio(p.slice(0,5),p.slice(5,10),p[10]);
   },{meaning:"r=Tr(z(J)/z(H))/2 with H nonzero",preconditions:"H,J belong to D"});
  }else if(actual.name==="strict_close"){
   expected.define(actual.name,["a","r"],(b,p)=>new EllipticCore(b).closeTo(...p),{meaning:"abs(a-r)<1/8"});
  }else throw Error("Unexpected additional template");
  assert(same(actual,expected.templates[0]),"Additional template polynomial changed: "+actual.name);
 }
}

function auditBundle(bundle,sources,baseModel){
 assert(bundle.format==="universal-rational-polynomial-expression-v1","Unknown expression format");
 assert(same(bundle.parameterNames,["e","n"])&&bundle.parameterDomain==="ordinary nonnegative integers"&&bundle.witnessDomain==="rational numbers","External interface changed");
 assert(bundle.rootRecipe==="universal"&&same(bundle.definitions,constructorDefinitions()),"Polynomial semantics changed");
 assert(same(bundle.sourceHashes,SOURCE_HASHES),"Source manifest changed");
 const finite=auditFiniteLibrary(bundle.library);
 assert(same(bundle.library.templates.slice(0,baseModel.templates.length),baseModel.templates),"Base multiplication model changed");
 auditAdditionalTemplates(bundle,baseModel.templates.length);
 const ts=bundle.library.templates;
 assert(ts.find(t=>t.name==="multiply")?.witnessCount===35134&&ts.find(t=>t.name==="natural")?.witnessCount===140604,"Base model counts");
 const powerSource=sources.halting.templates[0];
 assert(same(sources.halting.templates,sources.accuracy.templates),"Source power templates differ");
 const evaluations=[
  auditEvaluation(bundle,bundle.recipes.power_value,powerSource,{inputs:3,naturalInputs:false,mode:"value",sourceHash:hash(JSON.stringify(powerSource))}),
  auditEvaluation(bundle,bundle.recipes.halting,sources.halting,{inputs:2,naturalInputs:true,mode:"zero",sourceHash:SOURCE_HASHES["universal-integer-polynomial.json"]}),
  auditEvaluation(bundle,bundle.recipes.accuracy,sources.accuracy,{inputs:3,naturalInputs:true,mode:"zero",sourceHash:SOURCE_HASHES["accuracy-integer-polynomial.json"]})
 ];
 const trace=ts.findIndex(t=>t.name==="raw_trace_ratio"),close=ts.findIndex(t=>t.name==="strict_close");
 assert(trace>=0&&close>=0&&ts[trace].witnessCount===9&&ts[close].witnessCount===4,"Bridge arithmetic interface changed");
 const bridge=auditComposition(bundle,bundle.recipes.bridge,6,ranges=>{
  assert(ranges.length===3&&same(ranges.map(x=>x[1]),[5,5,1]),"Bridge local variables changed");
  const [H,J,r]=ranges.map(x=>x[0]);
  return [
   {kind:"recipe",target:"accuracy",parameters:varExprs(1,5).concat(varExprs(H,5),varExprs(J,5))},
   {kind:"template",target:trace,parameters:varExprs(H,5).concat(varExprs(J,5),[varExpr(r)])},
   {kind:"template",target:close,parameters:[varExpr(0),varExpr(r)]}
  ];
 });
 const universal=auditComposition(bundle,bundle.recipes.universal,2,ranges=>{
  assert(ranges.length===2&&same(ranges.map(x=>x[1]),[5,5]),"Outer model variables changed");
  const [A,B]=ranges.map(x=>x[0]);
  return [
   {kind:"recipe",target:"halting",parameters:varExprs(A,5).concat(varExprs(B,5))},
   {kind:"recipe",target:"bridge",parameters:[varExpr(0),...varExprs(A,5)]},
   {kind:"recipe",target:"bridge",parameters:[varExpr(1),...varExprs(B,5)]}
  ];
 });
 assert(bundle.witnessCount===universal.witnesses&&bundle.witnessCount===878664928321,"Final witness count changed");
 return {valid:true,evaluations,compositions:[bridge,universal],fixedPolynomialConstructors:finite.finitePolynomialConstructors.length,
  variableCount:bundle.recipes.universal.variableCount,witnessCount:bundle.witnessCount,
  limitation:"This verifies polynomial assembly against pinned source circuits and the checked model template. It does not prove their arithmetic theorems."};
}
function readInputs(directory=__dirname){
 const readPinned=file=>{
  const bytes=fs.readFileSync(path.join(directory,file));
  assert(hash(bytes)===SOURCE_HASHES[file],"Pinned source hash failed");return JSON.parse(bytes);
 };
 return {sources:{halting:readPinned("universal-integer-polynomial.json"),accuracy:readPinned("accuracy-integer-polynomial.json")},
  baseModel:JSON.parse(fs.readFileSync(path.join(directory,"fixed-rational-model.json"))).templates};
}
module.exports={auditEvaluation,auditComposition,auditBundle,readInputs,checkCoverage};
if(require.main===module){
 const bytes=fs.readFileSync(path.join(__dirname,"universal-rational-equation.json")),bundle=JSON.parse(bytes),
  {sources,baseModel}=readInputs(),report=auditBundle(bundle,sources,{templates:baseModel});
 report.expressionSHA256=hash(bytes);
 fs.writeFileSync(path.join(__dirname,"universal-rational-expression-audit.json"),JSON.stringify(report,null,2)+"\n");
 console.log(JSON.stringify(report,null,2));
}

