"use strict";
const {Builder,compileRegisterMachine,runMachine,evaluateCircuit}=require("./integer-diophantine-compiler.js");
const assert=(b,s)=>{if(!b)throw Error(s);};
function choose(n,k) {if(k>n)return 0n;let c=1n;for(let i=1n;i<=k;i++)c=c*(n-i+1n)/i;return c;}
let digitCases=0,bitCases=0,packedCases=0,backendCases=0;
for(let n=0n;n<=14n;n++)for(let k=0n;k<=18n;k++){
 const base=2n**(n+1n),total=(base+1n)**n,place=base**k;
 assert(total/place%base===choose(n,k),"binomial digit");
 digitCases++;
}
for(let a=0n;a<64n;a++)for(let b=0n;b<64n;b++){
 assert((choose(b,a)%2n===1n)===((a&b)===a),"Lucas subset");
 assert((choose(a+b,a)%2n===1n)===((a&b)===0n),"Lucas disjointness");
 const z=a&b, x=a-z,y=b-z;
 assert((z&x)===0n&&(z&y)===0n&&(x&y)===0n,"AND decomposition");
 bitCases++;
}
const pack=(xs,B)=>xs.reduceRight((s,x)=>s*B+BigInt(x),0n);
const programs=[];
for(let target=0;target<2;target++)programs.push([{op:"add",register:0,next:target},{op:"halt"}]);
for(let nz=0;nz<2;nz++)for(let zz=0;zz<2;zz++)
 programs.push([{op:"sub",register:0,nonzero:nz,zero:zz},{op:"halt"}]);
function packedAccept(p,rs,ss,c) {
 const q=rs.length-1,K=2n**BigInt(c),B=4n*K,T=B**BigInt(q);
 const F=(B*T-1n)/(B-1n),D=(K-1n)*F,R=pack(rs,B);
 const S=p.map((_,j)=>pack(ss.map(s=>+(s===j)),B));
 const N=pack(rs.map(r=>+(r>0)),B);
 if(R>=T||S[1]!==T)return false;
 if((R&D)!==R||S.some(x=>(x&F)!==x))return false;
 if(S.reduce((a,b)=>a+b,0n)!==F)return false;
 if(((R+D)&(K*F))!==K*N)return false;
 let A=0n,C=0n,I=[0n,0n];
 if(p[0].op==="add"){A=S[0];I[p[0].next]+=S[0];}
 else {C=S[0]&N;I[p[0].nonzero]+=C;I[p[0].zero]+=S[0]-C;}
 if(R+B*C!==BigInt(rs[0])+B*R+B*A)return false;
 return S.every((s,j)=>s===BigInt(j===0)+B*I[j]);
}
function actualAccept(p,rs,ss) {
 if(ss[0]!==0||ss.at(-1)!==1||rs.at(-1)!==0)return false;
 for(let t=0;t<ss.length-1;t++){
  if(ss[t]===1)return false;
  const x=p[ss[t]],v=rs[t];
  const nv=x.op==="add"?v+1:Math.max(0,v-1);
  const ns=x.op==="add"?x.next:v>0?x.nonzero:x.zero;
  if(rs[t+1]!==nv||ss[t+1]!==ns)return false;
 }
 return true;
}
for(const p of programs)for(let c=1;c<=2;c++)for(let q=0;q<=3;q++){
 const K=2**c;
 for(let rc=0;rc<K**(q+1);rc++){
  let z=rc;const rs=Array.from({length:q+1},()=>{let v=z%K;z=Math.floor(z/K);return v;});
  for(let sc=0;sc<2**(q+1);sc++){
   const ss=Array.from({length:q+1},(_,i)=>(sc>>i)&1);
   assert(packedAccept(p,rs,ss,c)===actualAccept(p,rs,ss),"packed history equivalence");
   packedCases++;
  }
 }
}
// An independent small existential formula exercises strict inequality,
// congruence, conjunction, disjunction and polynomial compilation.
const b=new Builder(["x","y"]),[x,y]=b.inputs;
const ff=b.or(b.and(b.lt(x,y),b.congruent(x,b.constant(3),y)),b.eq(x,b.constant(5)));
const aa=b.artifact(ff);
assert(aa.variables.length===5,"backend witness count");
for(let xv=0;xv<=6;xv++)for(let yv=0;yv<=6;yv++){
 let found=false;
 for(let d=0;d<=7&&!found;d++)for(let u=0;u<=7&&!found;u++)for(let v=0;v<=7&&!found;v++)
  if(evaluateCircuit(aa,[xv,yv,d,u,v])===0n)found=true;
 assert(found===((xv<yv&&(xv-yv)%3===0)||xv===5),"backend existential semantics");
 backendCases++;
}
const clear=[{op:"sub",register:0,nonzero:0,zero:1},{op:"halt"}];
for(let a=0;a<=10;a++)assert(runMachine(clear,1,a).accepted,"clear machine");
const artifact=compileRegisterMachine(clear,1);
assert(artifact.nodes.every(n=>["var","const","add","mul"].includes(n.op)),"unexpanded term");
assert(artifact.formulas.every(f=>["eq","and","or"].includes(f.op)),"unexpanded predicate");
artifact.nodes.forEach((n,i)=>{if(n.op==="add"||n.op==="mul")assert(n.args.every(j=>j<i),"non-topological circuit");});
const result={passed:true,digitCases,bitCases,packedCases,backendCases,
 smokeCircuit:{variables:artifact.variables.length,nodes:artifact.nodes.length,
 formulas:artifact.formulas.length,macroCounts:artifact.macroCounts},
 limitations:["Finite tests do not prove alpha representation or the full compiler.",
 "No full alpha witness assignment was generated.","All witnesses here are natural, not rational."]};
console.log(JSON.stringify(result,null,2));
module.exports=result;

