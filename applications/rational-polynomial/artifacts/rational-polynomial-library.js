"use strict";
const {RationalBuilder}=require("./rational-elliptic-core.js");
/*
 * Each call is literal polynomial substitution. Its last argument is the
 * start of a private block of witnesses. Library references go backwards.
 * All parameters and witnesses are rational numbers.
 */
class PolynomialLibrary {
  constructor(){this.templates=[];this.names=new Map();}
  define(name,parameterNames,build,metadata={}){
    if(this.names.has(name))throw Error("Duplicate template "+name);
    const b=new LibraryBuilder(this,parameterNames),formula=build(b,b.inputs);
    const a=b.artifact(formula,metadata);
    a.name=name;a.parameterCount=parameterNames.length;
    a.witnessCount=a.variableCount-a.parameterCount;
    const id=this.templates.length;
    this.templates.push(a);this.names.set(name,id);return id;
  }
  id(name){if(!this.names.has(name))throw Error("Unknown template "+name);return this.names.get(name);}
  artifact(metadata={}){return {format:"rational-polynomial-library-v1",variableDomain:"rational numbers",templates:this.templates,metadata};}
}
class LibraryBuilder extends RationalBuilder {
  constructor(library,names=[]){super(names);this.library=library;this.blocks=[];}
  variable(name="w",kind="witness"){
    const index=this.variableCount===undefined?this.variables.length:this.variableCount;
    this.variableCount=index+1;
    const node=this.node("var",[index]);this.variables.push({index,name,kind,node});return node;
  }
  call(name,parameters){
    const id=this.library.id(name),t=this.library.templates[id];
    if(parameters.length!==t.parameterCount)throw Error("Wrong parameter count for "+name);
    const start=this.variableCount;this.variableCount+=t.witnessCount;
    if(!Number.isSafeInteger(this.variableCount))throw Error("Too many variables for this materialized library");
    this.blocks.push({start,length:t.witnessCount,template:id});
    const node=this.node("call",[id,...parameters,start]);
    return this.fnode("polynomial",[node]);
  }
  artifact(formula,metadata={}){
    const a=super.artifact(formula,metadata);
    a.format="hierarchical-rational-polynomial-circuit-v1";
    a.variableCount=this.variableCount;a.witnessBlocks=this.blocks;return a;
  }
}
function auditLibrary(library){
  const ts=library.templates,report=[];
  for(let id=0;id<ts.length;id++){
    const t=ts[id];
    if(!Number.isSafeInteger(t.variableCount)||t.variableCount<0||
       t.parameterCount+t.witnessCount!==t.variableCount)throw Error("Bad variable count");
    const spans=t.variables.map(v=>({start:v.index,length:1,kind:"explicit"}))
      .concat(t.witnessBlocks.map(b=>({...b,kind:"block"}))).filter(s=>s.length);
    spans.sort((a,b)=>a.start-b.start);let next=0;
    for(const s of spans){if(s.start!==next)throw Error("Gap or overlap in "+t.name);next+=s.length;}
    if(next!==t.variableCount)throw Error("Incomplete variable coverage");
    for(let k=0;k<t.parameterCount;k++){
      const v=t.variables.find(v=>v.index===k);
      if(!v||v.kind!=="input")throw Error("Parameters not first");
    }
    const blocks=new Map(t.witnessBlocks.map(b=>[b.start+":"+b.template,b]));
    let calls=0;
    t.nodes.forEach((n,j)=>{
      if(n.op==="const"){BigInt(n.args[0]);if(n.args.length!==1)throw Error("Bad constant");}
      else if(n.op==="var"){
        if(n.args.length!==1||!Number.isSafeInteger(n.args[0])||n.args[0]<0||n.args[0]>=t.variableCount)throw Error("Bad variable");
      }else if(n.op==="add"||n.op==="mul"){
        if(n.args.length!==2||n.args.some(k=>!Number.isSafeInteger(k)||k<0||k>=j))throw Error("Bad edge");
      }else if(n.op==="call"){
        calls++;const target=n.args[0],callee=ts[target],start=n.args.at(-1),args=n.args.slice(1,-1);
        if(!Number.isSafeInteger(target)||target<0||target>=id||!callee||args.length!==callee.parameterCount||
          args.some(k=>!Number.isSafeInteger(k)||k<0||k>=j))throw Error("Bad call edge");
        const block=blocks.get(start+":"+target);
        if(!block||block.length!==callee.witnessCount)throw Error("Bad witness substitution");
      }else throw Error("Non-polynomial operation "+n.op);
    });
    if(!Number.isSafeInteger(t.root)||t.root<0||t.root>=t.nodes.length)throw Error("Bad root");
    if(calls!==t.witnessBlocks.length)throw Error("Unused witness block");
    report.push({name:t.name,parameters:t.parameterCount,witnesses:t.witnessCount,nodes:t.nodes.length,calls});
  }
  return {valid:true,templates:report};
}
/* Expand to a single ordinary polynomial DAG, with the same global variables.
 * This is intended for small verification cases. It may be very large.
 */
function expandTemplate(library,id){
  const template=library.templates[id],nodes=[],cache=new Map();
  const node=(op,args)=>{const key=JSON.stringify([op,...args]);if(cache.has(key))return cache.get(key);
    const index=nodes.length;nodes.push({op,args});cache.set(key,index);return index;};
  function expand(t,parameters,witnessMap){
    const local=[],variable=k=>k<t.parameterCount?parameters[k]:node("var",[witnessMap(k-t.parameterCount)]);
    for(const n of t.nodes){
      if(n.op==="const")local.push(node("const",n.args));
      else if(n.op==="var")local.push(variable(n.args[0]));
      else if(n.op==="add"||n.op==="mul")local.push(node(n.op,n.args.map(k=>local[k])));
      else if(n.op==="call"){
        const callee=library.templates[n.args[0]],start=n.args.at(-1);
        local.push(expand(callee,n.args.slice(1,-1).map(k=>local[k]),
          k=>{const localIndex=start+k;if(localIndex<t.parameterCount)throw Error("Witness aliases parameter");
            return witnessMap(localIndex-t.parameterCount);}));
      }else throw Error("Unexpanded operation");
    }
    return local[t.root];
  }
  const parameters=Array.from({length:template.parameterCount},(_,k)=>node("var",[k]));
  const root=expand(template,parameters,k=>template.parameterCount+k);
  return {format:"rational-polynomial-circuit-v1",variableCount:template.variableCount,nodes,root};
}
module.exports={PolynomialLibrary,LibraryBuilder,auditLibrary,expandTemplate};

