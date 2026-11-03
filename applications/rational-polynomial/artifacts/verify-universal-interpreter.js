"use strict";
const {Assembler,buildUniversalInterpreter,encodeProgram,runEncoded,runPrimitive}=require("./universal-interpreter.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
function exec(machine,inputs,limit=2000000){
 const tape=Array(machine.registers).fill(0n);inputs.forEach((v,i)=>tape[i]=BigInt(v));let pc=0;
 for(let t=0;t<limit;t++){
  const x=machine.program[pc];if(x.op==="halt")return tape;
  if(x.op==="add"){tape[x.register]++;pc=x.next;}
  else if(tape[x.register]){tape[x.register]--;pc=x.nonzero;}else pc=x.zero;
 }
 throw Error("Macro exceeded test limit");
}
function macro(inputs,fn){const a=new Assembler(inputs);fn(a);a.code.push({op:"halt"});return a.finish();}
let macroCases=0;
const copying=macro(2,a=>a.copy(0,1));
const adding=macro(2,a=>a.addInto(0,1));
const doubling=macro(1,a=>a.addInto(0,0));
const dividing=macro(4,a=>a.divmod(2,3,0,1));
const consing=macro(3,a=>a.cons(2,0,1));
const uncon=macro(3,a=>a.uncons(1,2,0));
for(let x=0;x<=5;x++)for(let y=0;y<=5;y++){
 let t=exec(copying,[x,y]);assert(t[0]===BigInt(y)&&t[1]===BigInt(y),"copy preserves");
 t=exec(adding,[x,y]);assert(t[0]===BigInt(x+y)&&t[1]===BigInt(y),"addition preserves");
 if(y){t=exec(dividing,[x,y]);assert(t[2]===BigInt(Math.floor(x/y))&&t[3]===BigInt(x%y),"division");}
 t=exec(consing,[x,y]);const c=2n**BigInt(x)*(2n*BigInt(y)+1n);assert(t[2]===c,"cons");
 t=exec(uncon,[c]);assert(t[1]===BigInt(x)&&t[2]===BigInt(y),"uncons");
 macroCases+=y?5:4;
}
for(let x=0;x<=10;x++){assert(exec(doubling,[x])[0]===BigInt(2*x),"alias doubling");macroCases++;}
assert(exec(uncon,[0])[1]===0n&&exec(uncon,[0])[2]===0n,"nil uncons");macroCases++;
const getter=macro(3,a=>a.getList(2,0,1));
const setter=macro(4,a=>a.setList(3,0,1,2));
const cons=(h,t)=>2n**BigInt(h)*(2n*t+1n);
const list=xs=>xs.reduceRight((t,h)=>cons(h,t),0n);
for(const xs of [[],[0],[1,0],[2,1,0]])for(let i=0;i<4;i++){
 assert(exec(getter,[list(xs),i])[2]===BigInt(xs[i]||0),"get list");
 for(let v=0;v<3;v++){
  const ys=xs.slice();while(ys.length<=i)ys.push(0);ys[i]=v;
  assert(exec(setter,[list(xs),i,v])[3]===list(ys),"set list");
  macroCases++;
 }
 macroCases++;
}
const vm=buildUniversalInterpreter(),examples=[];
const clear=[{op:"sub",register:0,nonzero:0,zero:1},{op:"halt"}];
const add=[{op:"add",register:0,next:1},{op:"halt"}];
for(const p of [clear,add])for(let n=0;n<=3;n++){
 const e=encodeProgram(p),reference=runEncoded(e,n),actual=runPrimitive(vm,[e,n],2000000);
 assert(reference.halted&&actual.halted&&actual.allZero,"universal interpreter example");
 examples.push({e:String(e),n,primitiveSteps:actual.steps});
}
for(const e of [0n,2n,4n,27n]){
 const actual=runPrimitive(vm,[e,2],2000000);assert(actual.halted&&actual.allZero,"invalid code halts");
 examples.push({e:String(e),n:2,primitiveSteps:actual.steps});
}
const looping=[{op:"add",register:0,next:0},{op:"halt"}],loopCode=encodeProgram(looping);
assert(!runEncoded(loopCode,0,20).halted,"reference loop");
assert(!runPrimitive(vm,[loopCode,0],100000).halted,"bounded interpreter loop");
const result={passed:true,macroCases,interpreterStates:vm.program.length,interpreterRegisters:vm.registers,
 examples,boundedNonhaltingCheck:{e:String(loopCode),steps:100000},
 limitations:["Finite execution checks do not prove universality.","Unbounded correctness uses the macro invariants and simulation argument in universal-interpreter-spec.txt."]};
console.log(JSON.stringify(result,null,2));module.exports=result;

