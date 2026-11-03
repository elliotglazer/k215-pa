"use strict";
const {Builder,compileRegisterMachine}=require("./integer-diophantine-compiler.js");
const pb=new Builder(["result","base","exponent"]);
const POWER=pb.artifact(pb.power(...pb.inputs),{meaning:"result=base^exponent on N"});
const POWER_WITNESSES=POWER.variables.length-3;

class HierarchicalBuilder extends Builder {
  constructor(names) {super(names);this.blocks=[];}
  variable(name="w",kind="witness") {
    const index=this.variableCount===undefined?this.variables.length:this.variableCount;
    this.variableCount=index+1;
    const node=this.node("var",[index]);this.variables.push({index,name,kind,node});return node;
  }
  power(P,Q,R) {
    this.macroCounts.power++;this.macroCounts.alpha+=3;
    const start=this.variableCount;this.variableCount+=POWER_WITNESSES;
    this.blocks.push({start,length:POWER_WITNESSES,template:0});
    const id=this.node("call",[0,P,Q,R,start]);
    return this.fnode("polynomial",[id]);
  }
  artifact(formula,metadata={}) {
    const a=super.artifact(formula,metadata);
    a.format="hierarchical-natural-diophantine-circuit-v1";
    a.variableCount=this.variableCount;a.witnessBlocks=this.blocks;
    a.templates=[{parameterCount:3,witnessCount:POWER_WITNESSES,
      variableCount:POWER.variables.length,nodes:POWER.nodes,root:POWER.root,
      meaning:POWER.metadata.meaning}];
    return a;
  }
}
function compileHierarchical(program,registers,inputNames=["input"]) {
  return compileRegisterMachine(program,registers,inputNames,{BuilderClass:HierarchicalBuilder});
}
function evaluateHierarchical(a,assignment) {
  const count=a.variableCount||a.variables.length;
  if(assignment.length!==count)throw Error("Wrong assignment size");
  const given=assignment.map(BigInt);
  function evalNodes(nodes,root,vars,templates) {
    const values=[];
    nodes.forEach((n,i)=>{
      if(n.op==="const")values[i]=BigInt(n.args[0]);
      else if(n.op==="var")values[i]=vars[n.args[0]];
      else if(n.op==="add")values[i]=values[n.args[0]]+values[n.args[1]];
      else if(n.op==="mul")values[i]=values[n.args[0]]*values[n.args[1]];
      else if(n.op==="call"){
        const [id,...rest]=n.args,t=templates[id],start=rest.pop();
        const args=rest.map(j=>values[j]).concat(vars.slice(start,start+t.witnessCount));
        values[i]=evalNodes(t.nodes,t.root,args,[]);
      } else throw Error("Unknown node");
    });
    return values[root];
  }
  return evalNodes(a.nodes,a.root,given,a.templates||[]);
}
/* A hash of the fully substituted expression tree, retaining operand order.
 * Equal hashes establish identical construction for tested artifacts, not
 * the semantic correctness of the imported arithmetic theorem.
 */
function expansionHash(a) {
  const {createHash}=require("node:crypto");
  const hash=s=>createHash("sha256").update(s).digest("hex");
  const vh=i=>hash("var:"+i);
  function nodesHash(nodes,root,vars,templates){
    const hs=[];
    nodes.forEach((n,i)=>{
      if(n.op==="const")hs[i]=hash("const:"+n.args[0]);
      else if(n.op==="var")hs[i]=vars?vars[n.args[0]]:vh(n.args[0]);
      else if(n.op==="add"||n.op==="mul")hs[i]=hash(n.op+":"+hs[n.args[0]]+":"+hs[n.args[1]]);
      else if(n.op==="call"){
        const [id,...rest]=n.args,t=templates[id],start=rest.pop();
        const args=rest.map(j=>hs[j]);
        for(let j=0;j<t.witnessCount;j++)args.push(vars?vars[start+j]:vh(start+j));
        hs[i]=nodesHash(t.nodes,t.root,args,[]);
      }else throw Error("Unknown node");
    });return hs[root];
  }
  return nodesHash(a.nodes,a.root,null,a.templates||[]);
}
function auditStructure(a){
  const covered=new Uint8Array(a.variableCount);
  for(const v of a.variables){if(v.index<0||v.index>=covered.length||covered[v.index])throw Error("Duplicate variable");covered[v.index]=1;}
  for(const b of a.witnessBlocks)for(let j=0;j<b.length;j++){
    const i=b.start+j;if(i>=covered.length||covered[i])throw Error("Overlapping witness block");covered[i]=1;
  }
  if(covered.some(x=>!x))throw Error("Unspecified variable");
  let calls=0;
  a.nodes.forEach((n,i)=>{
    if(n.op==="add"||n.op==="mul"){if(n.args.some(j=>j>=i||j<0))throw Error("Forward edge");}
    else if(n.op==="var"){if(!Number.isSafeInteger(n.args[0])||n.args[0]>=a.variableCount)throw Error("Bad variable");}
    else if(n.op==="const"){BigInt(n.args[0]);}
    else if(n.op==="call"){
      calls++;const [id,P,Q,R,start]=n.args,t=a.templates[id];
      if(!t||[P,Q,R].some(j=>j>=i||j<0)||!a.witnessBlocks.some(b=>b.start===start&&b.length===t.witnessCount))throw Error("Bad call");
    }else throw Error("Unexpected primitive");
  });
  for(const t of a.templates)t.nodes.forEach((n,i)=>{
    if(n.op==="add"||n.op==="mul"){if(n.args.some(j=>j>=i||j<0))throw Error("Template forward edge");}
    else if(n.op==="var"){if(n.args[0]>=t.variableCount)throw Error("Template variable");}
    else if(n.op==="const"){BigInt(n.args[0]);}else throw Error("Unexpanded template");
  });
  return {valid:true,variables:a.variableCount,witnesses:a.variableCount-a.metadata.inputNames.length,
    nodes:a.nodes.length,calls,templates:a.templates.length,templateNodes:a.templates[0].nodes.length};
}
module.exports={HierarchicalBuilder,compileHierarchical,evaluateHierarchical,expansionHash,auditStructure};

