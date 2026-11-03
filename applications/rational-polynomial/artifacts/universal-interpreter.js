"use strict";
/* Exact finite program numbering and a generated two-input interpreter.
 * Primitive instructions are the add/sub/halt machine of the integer compiler.
 * Input registers 0,1 contain the ordinary numbers e,n.
 */
class Assembler {
  constructor(inputs=2) {this.code=[];this.labels=new Map();this.labelCount=0;this.registers=inputs;this.zero=this.temp();}
  temp(){return this.registers++;}
  label(){return "L"+this.labelCount++;}
  at(l){if(this.labels.has(l))throw Error("Duplicate label");this.labels.set(l,this.code.length);}
  add1(r){this.code.push({op:"add",register:r,next:this.code.length+1});}
  dec(r){const n=this.code.length+1;this.code.push({op:"sub",register:r,nonzero:n,zero:n});}
  branch(r,nz,z){this.code.push({op:"sub",register:r,nonzero:nz,zero:z});}
  jump(l){this.branch(this.zero,l,l);}
  clear(r){const n=this.code.length;this.branch(r,n,n+1);}
  take(r,body){const loop=this.label(),yes=this.label(),end=this.label();this.at(loop);this.branch(r,yes,end);this.at(yes);body();this.jump(loop);this.at(end);}
  ifNZ(r,yes,no=()=>{}){const restore=this.label(),other=this.label(),end=this.label();this.branch(r,restore,other);this.at(restore);this.add1(r);yes();this.jump(end);this.at(other);no();this.at(end);}
  whileNZ(r,body){const loop=this.label(),restore=this.label(),end=this.label();this.at(loop);this.branch(r,restore,end);this.at(restore);this.add1(r);body();this.jump(loop);this.at(end);}
  set(r,n){this.clear(r);for(let i=0;i<n;i++)this.add1(r);}
  copy(out,x){
    if(out===x)return;
    const t=this.temp();this.clear(out);this.clear(t);
    this.take(x,()=>{this.add1(out);this.add1(t);});
    this.take(t,()=>this.add1(x));
  }
  addInto(out,x){
    if(out===x){const saved=this.temp();this.copy(saved,x);this.addInto(out,saved);return;}
    const t=this.temp();this.clear(t);
    this.take(x,()=>{this.add1(out);this.add1(t);});
    this.take(t,()=>this.add1(x));
  }
  ifLt(x,y,yes,no){
    const a=this.temp(),b=this.temp();this.copy(a,x);this.copy(b,y);
    const loop=this.label(),test=this.label(),lt=this.label(),ge=this.label(),end=this.label();
    this.at(loop);this.branch(b,test,ge);this.at(test);this.branch(a,loop,lt);
    this.at(lt);yes();this.jump(end);this.at(ge);no();this.at(end);
  }
  divmod2(q,r,x){
    if(q===r)throw Error("Aliased outputs");
    const rem=this.temp();this.copy(rem,x);this.clear(q);
    const loop=this.label(),first=this.label(),pair=this.label(),even=this.label(),odd=this.label(),end=this.label();
    this.at(loop);this.branch(rem,first,even);this.at(first);this.branch(rem,pair,odd);
    this.at(pair);this.add1(q);this.jump(loop);
    this.at(even);this.clear(r);this.jump(end);this.at(odd);this.set(r,1);this.at(end);
  }
  divmod(q,r,x,y){
    if(q===r)throw Error("Aliased outputs");
    const rem=this.temp(),quot=this.temp(),count=this.temp();
    this.copy(rem,x);this.clear(quot);
    const loop=this.label(),end=this.label();this.at(loop);
    this.ifLt(rem,y,()=>this.jump(end),()=>{
      this.copy(count,y);this.take(count,()=>this.dec(rem));this.add1(quot);this.jump(loop);
    });
    this.at(end);this.copy(q,quot);this.copy(r,rem);
  }
  cons(out,head,tail){
    const acc=this.temp(),count=this.temp();this.copy(acc,tail);this.addInto(acc,acc);this.add1(acc);
    this.copy(count,head);this.take(count,()=>this.addInto(acc,acc));this.copy(out,acc);
  }
  uncons(head,tail,code){
    if(head===tail)throw Error("Aliased outputs");
    const u=this.temp(),q=this.temp(),r=this.temp();this.copy(u,code);this.clear(head);
    this.ifNZ(u,()=>{
      const loop=this.label(),end=this.label();this.at(loop);this.divmod2(q,r,u);
      this.ifNZ(r,()=>{this.copy(tail,q);this.jump(end);},()=>{this.add1(head);this.copy(u,q);this.jump(loop);});
      this.at(end);
    },()=>this.clear(tail));
  }
  getList(out,list,index){
    const cur=this.temp(),count=this.temp(),h=this.temp(),t=this.temp();
    this.copy(cur,list);this.copy(count,index);
    this.take(count,()=>{this.uncons(h,t,cur);this.copy(cur,t);});
    this.uncons(out,t,cur);
  }
  setList(out,list,index,value){
    const cur=this.temp(),count=this.temp(),rev=this.temp(),h=this.temp(),t=this.temp(),acc=this.temp();
    this.copy(cur,list);this.copy(count,index);this.clear(rev);
    this.take(count,()=>{this.uncons(h,t,cur);this.cons(rev,h,rev);this.copy(cur,t);});
    this.uncons(h,t,cur);this.cons(acc,value,t);
    this.whileNZ(rev,()=>{this.uncons(h,t,rev);this.cons(acc,h,acc);this.copy(rev,t);});
    this.copy(out,acc);
  }
  finish(){
    const resolve=x=>typeof x==="string"?this.labels.get(x):x;
    return {registers:this.registers,program:this.code.map(x=>{
      if(x.op==="halt")return x;
      if(x.op==="add"){const next=resolve(x.next);if(next===undefined)throw Error("Unresolved label");return {...x,next};}
      const nonzero=resolve(x.nonzero),zero=resolve(x.zero);
      if(nonzero===undefined||zero===undefined)throw Error("Unresolved label");
      return {...x,nonzero,zero};
    })};
  }
}
function buildUniversalInterpreter(){
  const a=new Assembler(2),E=0,N=1;
  const w=a.temp(),D=a.temp(),base=a.temp(),pc=a.temp(),tape=a.temp(),value=a.temp();
  const raw=a.temp(),count=a.temp(),op=a.temp(),reg=a.temp(),nz=a.temp(),zz=a.temp(),q=a.temp(),r=a.temp();
  const ec=a.temp(),test=a.temp(),accept=a.label();
  a.copy(ec,E);a.add1(ec);a.uncons(w,D,ec);
  a.ifNZ(w,()=>{},()=>a.jump(accept));
  a.set(base,1);a.copy(count,w);a.take(count,()=>a.addInto(base,base));
  a.clear(pc);a.cons(tape,N,a.zero);
  const loop=a.label();a.at(loop);
  a.copy(raw,D);a.copy(count,pc);a.addInto(count,pc);a.addInto(count,pc);a.addInto(count,pc);
  a.take(count,()=>{a.divmod(q,r,raw,base);a.copy(raw,q);});
  for(const out of [op,reg,nz,zz]){a.divmod(q,out,raw,base);a.copy(raw,q);}
  a.copy(test,op);
  a.ifNZ(test,()=>a.dec(test),()=>a.jump(accept));
  a.ifNZ(test,()=>{
    a.dec(test);a.ifNZ(test,()=>a.jump(accept),()=>{});
  },()=>{});
  // At this point op is exactly 1 or 2.
  a.getList(value,tape,reg);
  a.copy(test,op);a.dec(test);
  a.ifNZ(test,()=>{
    a.ifNZ(value,()=>{a.dec(value);a.copy(pc,nz);},()=>a.copy(pc,zz));
  },()=>{a.add1(value);a.copy(pc,nz);});
  a.setList(tape,tape,reg,value);a.jump(loop);
  a.at(accept);
  const total=a.registers;for(let j=0;j<total;j++)a.clear(j);
  a.code.push({op:"halt"});
  return {...a.finish(),inputNames:["e","n"],encoding:"fixed-width-four-fields-v1"};
}
function encodeProgram(program){
  let max=2;
  for(const x of program)if(x.op!=="halt")max=Math.max(max,x.register,x.op==="add"?x.next:x.nonzero,x.op==="sub"?x.zero:0);
  let w=1;while(2**w<=max)w++;
  const B=1n<<BigInt(w),records=[];
  for(const x of program){
    const fields=x.op==="halt"?[0,0,0,0]:x.op==="add"?[1,x.register,x.next,0]:[2,x.register,x.nonzero,x.zero];
    let rec=0n,p=1n;for(const f of fields){rec+=BigInt(f)*p;p*=B;}
    records.push(rec.toString(2).padStart(4*w,"0"));
  }
  const digits=records.reverse().join("");
  const D=digits?BigInt("0b"+digits):0n;
  return ((2n*D+1n)<<BigInt(w))-1n;
}
function decodeHeader(e){
  let v=BigInt(e)+1n,w=0;
  if(v<=0n)throw Error("Program code must be natural");
  while(v%2n===0n){v/=2n;w++;}
  return {width:w,base:1n<<BigInt(w),data:(v-1n)/2n};
}
function runEncoded(e,n,limit=1000){
  const h=decodeHeader(e),tape=new Map([[0n,BigInt(n)]]);let pc=0n;
  if(!h.width)return {halted:true,steps:0,tape};
  for(let step=0;step<limit;step++){
    let v=h.data/(h.base**(4n*pc)),fields=[];
    for(let k=0;k<4;k++){fields.push(v%h.base);v/=h.base;}
    const [op,j,nz,zz]=fields;
    if(op!==1n&&op!==2n)return {halted:true,steps:step,tape};
    const x=tape.get(j)||0n;
    if(op===1n){tape.set(j,x+1n);pc=nz;}
    else if(x>0n){tape.set(j,x-1n);pc=nz;}else pc=zz;
  }
  return {halted:false,steps:limit,tape};
}
function runPrimitive(machine,inputs,limit=10000000){
  const tape=Array(machine.registers).fill(0n);inputs.forEach((x,i)=>tape[i]=BigInt(x));
  let pc=0;
  for(let step=0;step<limit;step++){
    const x=machine.program[pc];
    if(x.op==="halt")return {halted:true,steps:step,allZero:tape.every(x=>x===0n)};
    if(x.op==="add"){tape[x.register]++;pc=x.next;}
    else if(tape[x.register]>0n){tape[x.register]--;pc=x.nonzero;}else pc=x.zero;
  }
  return {halted:false,steps:limit,pc};
}
module.exports={Assembler,buildUniversalInterpreter,encodeProgram,decodeHeader,runEncoded,runPrimitive};

