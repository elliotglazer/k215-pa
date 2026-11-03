"use strict";

/*
 * Integer Diophantine circuit compiler.
 * All input and witness variables in this module range over N.
 * This is NOT a rational Diophantine definition until translated through
 * an exact Diophantine model. No OpenAI arithmetic theorem is verified here.
 *
 * alpha() and power() follow AFP DPRM_Theorem:
 * Alpha_Sequence.alpha_dioph and Exponential_Relation.exp_repr.
 * Other macros are derived in integer-compiler-spec.txt.
 */
class Builder {
  constructor(inputNames = []) {
    this.nodes=[]; this.cache=new Map(); this.variables=[];
    this.formulas=[]; this.formulaCache=new Map();
    this.inputs=inputNames.map(name=>this.variable(name,"input"));
    this.macroCounts={alpha:0,power:0,binomial:0,orthogonal:0,mask:0,bitAnd:0};
  }
  node(op,args) {
    const key=JSON.stringify([op,...args]);
    if(this.cache.has(key))return this.cache.get(key);
    const id=this.nodes.length;this.nodes.push({op,args});this.cache.set(key,id);return id;
  }
  constant(n) {return this.node("const",[BigInt(n).toString()]);}
  variable(name="w",kind="witness") {
    const index=this.variables.length,id=this.node("var",[index]);
    this.variables.push({index,name,kind,node:id});return id;
  }
  fresh(name) {return this.variable(name);}
  add(...xs) {
    if(xs.length===0)return this.constant(0);
    return xs.reduce((a,b)=>this.node("add",[a,b]));
  }
  mul(...xs) {
    if(xs.length===0)return this.constant(1);
    return xs.reduce((a,b)=>this.node("mul",[a,b]));
  }
  square(x) {return this.mul(x,x);}
  scale(n,x) {return this.mul(this.constant(n),x);}
  fnode(op,args) {
    const key=JSON.stringify([op,...args]);
    if(this.formulaCache.has(key))return this.formulaCache.get(key);
    const id=this.formulas.length;this.formulas.push({op,args});
    this.formulaCache.set(key,id);return id;
  }
  eq(a,b) {return this.fnode("eq",[a,b]);}
  and(...fs) {return this.fnode("and",fs);}
  or(...fs) {return this.fnode("or",fs);}
  lt(a,b) {
    const d=this.fresh("strict_difference");
    return this.eq(b,this.add(a,this.constant(1),d));
  }
  le(a,b) {
    const d=this.fresh("difference");
    return this.eq(b,this.add(a,d));
  }
  divides(a,b) {return this.eq(b,this.mul(a,this.fresh("divisibility_quotient")));}
  congruent(a,m,b) {
    const u=this.fresh("congruence_left"),v=this.fresh("congruence_right");
    return this.eq(this.add(a,this.mul(m,u)),this.add(b,this.mul(m,v)));
  }
  alpha(X,B,N) {
    this.macroCounts.alpha++;
    const [r,s,t,u,v,w,x,y]=["r","s","t","u","v","w","x","y"].map(n=>this.fresh("alpha_"+n));
    const one=this.constant(1),two=this.constant(2);
    return this.and(
      this.lt(this.constant(3),B),
      this.eq(this.add(one,this.mul(B,u,t)),this.add(this.square(u),this.square(t))),
      this.eq(this.add(one,this.mul(B,s,r)),this.add(this.square(s),this.square(r))),
      this.lt(r,s),
      this.divides(this.square(u),s),
      this.eq(this.add(v,this.scale(2,r)),this.mul(B,s)),
      this.congruent(B,v,w),this.congruent(two,u,w),this.lt(two,w),
      this.eq(this.add(one,this.mul(w,x,y)),this.add(this.square(x),this.square(y))),
      this.lt(this.scale(2,X),u),this.lt(this.scale(2,X),v),
      this.congruent(x,v,X),this.lt(this.scale(2,N),u),this.congruent(x,u,N)
    );
  }
  power(P,Q,R) {
    this.macroCounts.power++;
    const zero=this.constant(0),one=this.constant(1);
    const [b,m,a0,a1,a2]=["b","m","a0","a1","a2"].map(n=>this.fresh("power_"+n));
    return this.or(
      this.and(this.eq(Q,zero),this.eq(R,zero),this.eq(P,one)),
      this.and(this.eq(Q,zero),this.lt(zero,R),this.eq(P,zero)),
      this.and(this.lt(zero,Q),
        this.alpha(a0,this.add(Q,this.constant(4)),this.add(R,one)),
        this.eq(b,this.add(a0,this.square(Q),this.constant(2))),
        this.eq(this.add(m,this.square(Q),one),this.mul(b,Q)),
        this.lt(P,m),
        this.alpha(a1,b,R),this.alpha(a2,b,this.add(R,one)),
        this.congruent(this.add(P,this.mul(b,a1)),m,this.add(this.mul(Q,a1),a2)))
    );
  }
  binomial(C,N,K) {
    this.macroCounts.binomial++;
    const [base,total,place,u,r]=["base","total","place","quotient","remainder"].map(n=>this.fresh("binomial_"+n));
    return this.and(
      this.power(base,this.constant(2),this.add(N,this.constant(1))),
      this.power(total,this.add(base,this.constant(1)),N),
      this.power(place,base,K),
      this.lt(C,base),this.lt(r,place),
      this.eq(total,this.add(this.mul(place,this.add(this.mul(base,u),C)),r))
    );
  }
  odd(x) {return this.eq(x,this.add(this.scale(2,this.fresh("odd_half")),this.constant(1)));}
  orthogonal(a,b) {
    this.macroCounts.orthogonal++;
    const c=this.fresh("orthogonal_binomial");
    return this.and(this.binomial(c,this.add(a,b),a),this.odd(c));
  }
  mask(a,b) {
    this.macroCounts.mask++;
    const c=this.fresh("mask_binomial");
    return this.and(this.binomial(c,b,a),this.odd(c));
  }
  bitAnd(z,x,y) {
    this.macroCounts.bitAnd++;
    const a=this.fresh("and_left_only"),b=this.fresh("and_right_only");
    return this.and(this.eq(x,this.add(z,a)),this.eq(y,this.add(z,b)),
      this.orthogonal(z,a),this.orthogonal(z,b),this.orthogonal(a,b));
  }
  polynomial(formula) {
    const roots=[];
    for(let i=0;i<=formula;i++){
      const f=this.formulas[i];
      if(f.op==="eq")roots[i]=this.add(f.args[0],this.scale(-1,f.args[1]));
      else if(f.op==="polynomial")roots[i]=f.args[0];
      else if(f.op==="and")roots[i]=this.add(...f.args.map(j=>this.square(roots[j])));
      else if(f.op==="or")roots[i]=this.mul(...f.args.map(j=>roots[j]));
      else throw Error("Unexpanded formula "+f.op);
    }
    return roots[formula];
  }
  artifact(formula,metadata={}) {
    const root=this.polynomial(formula);
    return {format:"natural-diophantine-circuit-v1",variableDomain:"nonnegative integers",
      variables:this.variables,nodes:this.nodes,root,formula,
      formulas:this.formulas,macroCounts:this.macroCounts,metadata};
  }
}

function validateProgram(program,registers) {
  if(!Number.isSafeInteger(registers)||registers<1)throw Error("Invalid register count");
  if(!Array.isArray(program)||program.length<1)throw Error("Empty program");
  const halt=program.length-1;
  program.forEach((x,i)=>{
    if(x.op==="halt") {if(i!==halt)throw Error("Only the final instruction may halt");return;}
    if(i===halt)throw Error("Final instruction must halt");
    if(!["add","sub"].includes(x.op))throw Error("Unknown instruction");
    if(!Number.isSafeInteger(x.register)||x.register<0||x.register>=registers)throw Error("Invalid register");
    const targets=x.op==="add"?[x.next]:[x.nonzero,x.zero];
    for(const j of targets)if(!Number.isSafeInteger(j)||j<0||j>halt)throw Error("Invalid jump");
  });
}

/*
 * Inputs occupy the first inputNames.length registers; the rest start at zero.
 * Acceptance means reaching the unique final halt with ALL registers zero.
 * A general halting program must first be transformed by adding cleanup.
 */
function compileRegisterMachine(program,registers,inputNames=["input"],options={}) {
  validateProgram(program,registers);
  if(inputNames.length<1||inputNames.length>registers)throw Error("Invalid input count");
  const BuilderType=options.BuilderClass||Builder;
  const b=new BuilderType(inputNames),initial=b.inputs,zero=b.constant(0),one=b.constant(1);
  const q=b.fresh("time"),c=b.fresh("digit_bits"),K=b.fresh("digit_capacity");
  const B=b.fresh("history_base"),T=b.fresh("last_place"),F=b.fresh("time_mask"),D=b.fresh("register_mask");
  const r=Array.from({length:registers},(_,j)=>b.fresh("history_r"+j));
  const nz=Array.from({length:registers},(_,j)=>b.fresh("nonzero_r"+j));
  const s=program.map((_,i)=>b.fresh("history_s"+i));
  const fs=[
    b.lt(zero,c),b.power(K,b.constant(2),c),b.eq(B,b.scale(4,K)),
    b.lt(b.constant(program.length),B),b.power(T,B,q),...initial.map(a=>b.lt(a,K)),
    b.eq(b.add(b.mul(B,F),one),b.add(F,b.mul(B,T))),
    b.eq(b.add(D,F),b.mul(K,F)),
    b.eq(b.add(...s),F),b.eq(s[s.length-1],T)
  ];
  s.forEach(x=>fs.push(b.mask(x,F)));
  for(let j=0;j<registers;j++){
    fs.push(b.mask(r[j],D),b.lt(r[j],T));
    fs.push(b.bitAnd(b.mul(K,nz[j]),b.add(r[j],D),b.mul(K,F)));
  }
  const inc=Array.from({length:registers},()=>[]);
  const dec=Array.from({length:registers},()=>[]);
  const incoming=program.map(()=>[]);
  program.forEach((x,i)=>{
    if(x.op==="halt")return;
    if(x.op==="add") {inc[x.register].push(s[i]);incoming[x.next].push(s[i]);}
    else {
      const active=b.fresh("sub_nonzero_"+i),inactive=b.fresh("sub_zero_"+i);
      fs.push(b.bitAnd(active,s[i],nz[x.register]),b.eq(s[i],b.add(active,inactive)));
      dec[x.register].push(active);
      incoming[x.nonzero].push(active);incoming[x.zero].push(inactive);
    }
  });
  for(let j=0;j<registers;j++)
    fs.push(b.eq(b.add(r[j],b.mul(B,b.add(...dec[j]))),
      b.add(j<initial.length?initial[j]:zero,b.mul(B,r[j]),b.mul(B,b.add(...inc[j])))));
  for(let i=0;i<program.length;i++)
    fs.push(b.eq(s[i],b.add(i===0?one:zero,b.mul(B,b.add(...incoming[i])))));
  return b.artifact(b.and(...fs),{program,registers,inputNames,semantics:"halt with zero registers",
    source:"Packed-history construction; see integer-compiler-spec.txt"});
}

function runMachine(program,registers,input,limit=100000) {
  validateProgram(program,registers);
  let state=0,tape=Array(registers).fill(0n);
  const supplied=Array.isArray(input)?input:[input];
  if(supplied.length>registers)throw Error("Too many inputs");
  supplied.forEach((x,i)=>tape[i]=BigInt(x));
  const history=[];
  for(let t=0;t<=limit;t++){
    history.push({state,tape:tape.map(String)});
    const x=program[state];
    if(x.op==="halt")return {halted:true,accepted:tape.every(x=>x===0n),steps:t,history};
    if(t===limit)break;
    if(x.op==="add"){tape[x.register]++;state=x.next;}
    else if(tape[x.register]>0n){tape[x.register]--;state=x.nonzero;}else state=x.zero;
  }
  return {halted:false,accepted:false,steps:limit,history};
}

function evaluateCircuit(artifact,assignment) {
  if(assignment.length!==artifact.variables.length)throw Error("Wrong assignment size");
  const vs=assignment.map(BigInt),values=[];
  artifact.nodes.forEach((n,i)=>{
    if(n.op==="const")values[i]=BigInt(n.args[0]);
    else if(n.op==="var")values[i]=vs[n.args[0]];
    else if(n.op==="add")values[i]=values[n.args[0]]+values[n.args[1]];
    else if(n.op==="mul")values[i]=values[n.args[0]]*values[n.args[1]];
    else throw Error("Unknown circuit node");
  });
  return values[artifact.root];
}
module.exports={Builder,compileRegisterMachine,validateProgram,runMachine,evaluateCircuit};

