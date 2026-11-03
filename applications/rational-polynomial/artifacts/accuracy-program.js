"use strict";
const {Assembler}=require("./universal-interpreter.js");
class IR {
  constructor(){this.count=1;this.init=[];this.body=[];this.current=this.body;this.constants=new Map();}
  fresh(){return this.count++;}
  emit(x){this.current.push(x);}
  constant(v){v=BigInt(v).toString();if(this.constants.has(v))return this.constants.get(v);const r=this.fresh();this.constants.set(v,r);this.init.push({op:"set",out:r,value:v});return r;}
  copy(x){const out=this.fresh();this.assign(out,x);return out;}
  assign(out,x){this.emit({op:"copy",out,x});}
  binary(op,x,y){const out=this.fresh();this.emit({op,out,x,y});return out;}
  add(x,y){return this.binary("add",x,y);}
  mul(x,y){return this.binary("mul",x,y);}
  sub(x,y){return this.binary("sub",x,y);}
  block(fn){const old=this.current,out=[];this.current=out;fn();this.current=old;return out;}
  ifNZ(x,yes,no=()=>{}){this.emit({op:"ifNZ",x,yes:this.block(yes),no:this.block(no)});}
  whileNZ(x,fn){this.emit({op:"whileNZ",x,body:this.block(fn)});}
  whileLT(x,y,fn){this.emit({op:"whileLT",x,y,body:this.block(fn)});}
  ifLT(x,y,yes,no){this.emit({op:"ifLT",x,y,yes:this.block(yes),no:this.block(no)});}
  div2(x){const q=this.fresh(),r=this.fresh();this.emit({op:"div2",x,q,r});return [q,r];}
  accept(){this.emit({op:"accept"});}
  reject(){this.emit({op:"reject"});}
  signed(v){v=BigInt(v);return [this.constant(v>0n?v:0n),this.constant(v<0n?-v:0n)];}
  sadd(x,y){const p=this.add(x[0],y[0]),n=this.add(x[1],y[1]);return [this.sub(p,n),this.sub(n,p)];}
  sneg(x){return [x[1],x[0]];}
  ssub(x,y){return this.sadd(x,this.sneg(y));}
  smul(x,y){return [this.add(this.mul(x[0],y[0]),this.mul(x[1],y[1])),this.add(this.mul(x[0],y[1]),this.mul(x[1],y[0]))];}
  ssquare(x){const a=this.add(x[0],x[1]);return [this.mul(a,a),this.constant(0)];}
  sscale(k,x){const c=this.constant(k);return [this.mul(c,x[0]),this.mul(c,x[1])];}
  field(a,b=0){return [this.signed(a),this.signed(b)];}
  fadd(x,y){return [this.sadd(x[0],y[0]),this.sadd(x[1],y[1])];}
  fsub(x,y){return [this.ssub(x[0],y[0]),this.ssub(x[1],y[1])];}
  fmul(x,y){return [this.sadd(this.smul(x[0],y[0]),this.sscale(2,this.smul(x[1],y[1]))),this.sadd(this.smul(x[0],y[1]),this.smul(x[1],y[0]))];}
  fsquare(x){return [this.sadd(this.ssquare(x[0]),this.sscale(2,this.ssquare(x[1]))),this.sscale(2,this.smul(x[0],x[1]))];}
  fscale(k,x){return [this.sscale(k,x[0]),this.sscale(k,x[1])];}
  blankPoint(){return Array.from({length:3},()=>Array.from({length:2},()=>[this.fresh(),this.fresh()]));}
  pointCopy(out,src){for(let c=0;c<3;c++)for(let j=0;j<2;j++)for(let s=0;s<2;s++)this.assign(out[c][j][s],src[c][j][s]);}
  double(P){
    const [X,Y,Z]=P,A=this.fsquare(X),B=this.fsquare(Y),C=this.fsquare(B);
    const D=this.fscale(4,this.fmul(X,B)),Z4=this.fsquare(this.fsquare(Z));
    const E=this.fadd(this.fscale(3,A),this.fmul(this.field(-11243,7950),Z4));
    const XX=this.fsub(this.fsquare(E),this.fscale(2,D));
    const YY=this.fsub(this.fmul(E,this.fsub(D,XX)),this.fscale(8,C));
    const ZZ=this.fscale(2,this.fmul(Y,Z));return [XX,YY,ZZ];
  }
  pointAdd(P,Q){
    const [X1,Y1,Z1]=P,[X2,Y2,Z2]=Q;
    const z1s=this.fsquare(Z1),z2s=this.fsquare(Z2);
    const U1=this.fmul(X1,z2s),U2=this.fmul(X2,z1s);
    const S1=this.fmul(Y1,this.fmul(z2s,Z2)),S2=this.fmul(Y2,this.fmul(z1s,Z1));
    const H=this.fsub(U2,U1),R=this.fsub(S2,S1),H2=this.fsquare(H),H3=this.fmul(H2,H);
    const X=this.fsub(this.fsub(this.fsquare(R),H3),this.fscale(2,this.fmul(U1,H2)));
    const Y=this.fsub(this.fmul(R,this.fsub(this.fmul(U1,H2),X)),this.fmul(S1,H3));
    const Z=this.fmul(H,this.fmul(Z1,Z2));return [X,Y,Z];
  }
  multiple(n){
    const count=this.copy(n),flag=this.copy(this.constant(0)),acc=this.blankPoint(),base=this.blankPoint();
    this.pointCopy(base,[this.field(13128,-9280),this.field(-1979520,1399728),this.field(8)]);
    this.whileNZ(count,()=>{
      const [q,r]=this.div2(count);
      this.ifNZ(r,()=>this.ifNZ(flag,()=>this.pointCopy(acc,this.pointAdd(acc,base)),()=>{
        this.pointCopy(acc,base);this.assign(flag,this.constant(1));
      }));
      this.assign(count,q);
      this.ifNZ(count,()=>this.pointCopy(base,this.double(base)));
    });
    return acc;
  }
  unpair(a){
    const r=this.copy(a),w=this.copy(this.constant(0));
    this.whileLT(w,r,()=>{
      this.assign(r,this.sub(r,this.add(w,this.constant(1))));
      this.assign(w,this.add(w,this.constant(1)));
    });
    return [this.sub(w,r),r];
  }
}
function buildAccuracyIR(){
  const b=new IR(),[k,rest]=b.unpair(0),[h,j]=b.unpair(rest);
  b.ifNZ(h,()=>{},()=>b.reject());
  const product=b.mul(k,h),difference=b.add(b.sub(j,product),b.sub(product,j));
  b.ifNZ(difference,()=>b.reject());
  b.ifNZ(j,()=>{},()=>b.accept());
  const H=b.multiple(h),J=b.multiple(j);
  const A=b.fmul(b.fmul(J[0],J[2]),H[1]),B=b.fmul(b.fmul(H[0],H[2]),J[1]);
  const numerator=b.ssub(b.smul(A[0],B[0]),b.sscale(2,b.smul(A[1],B[1])));
  const denominator=b.ssub(b.ssquare(B[0]),b.sscale(2,b.ssquare(B[1])));
  const error=b.ssub(numerator,b.smul([k,b.constant(0)],denominator));
  const left=b.mul(b.constant(64),b.ssquare(error)[0]),right=b.ssquare(denominator)[0];
  b.ifLT(left,right,()=>b.accept(),()=>b.reject());
  return {format:"natural-register-ir-v1",registers:b.count,inputNames:["paired_k_h_j"],
    init:b.init,body:b.body,debug:{k,h,j,H,J,numerator,denominator,left,right},
    meaning:"h>=1 and j=k*h and abs(Tr(z(jP)/z(hP))/2-k)<1/8"};
}
function runIR(ir,input,limit=1000000){
  const r=Array(ir.registers).fill(0n);r[0]=BigInt(input);let ticks=0;
  function run(code){
    for(const c of code){
      if(++ticks>limit)throw Error("IR step limit");
      if(c.op==="set")r[c.out]=BigInt(c.value);
      else if(c.op==="copy")r[c.out]=r[c.x];
      else if(c.op==="add")r[c.out]=r[c.x]+r[c.y];
      else if(c.op==="mul")r[c.out]=r[c.x]*r[c.y];
      else if(c.op==="sub")r[c.out]=r[c.x]>r[c.y]?r[c.x]-r[c.y]:0n;
      else if(c.op==="div2"){r[c.q]=r[c.x]/2n;r[c.r]=r[c.x]%2n;}
      else if(c.op==="ifNZ"||c.op==="ifLT"){
        const yes=c.op==="ifNZ"?r[c.x]>0n:r[c.x]<r[c.y],z=run(yes?c.yes:c.no);if(z)return z;
      }else if(c.op==="whileNZ"||c.op==="whileLT"){
        while(c.op==="whileNZ"?r[c.x]>0n:r[c.x]<r[c.y]){const z=run(c.body);if(z)return z;}
      }else if(c.op==="accept"||c.op==="reject")return c.op;
      else throw Error("Unknown IR operation");
    }
  }
  const result=run(ir.init)||run(ir.body);
  if(!result)throw Error("IR did not decide");
  return {accepted:result==="accept",ticks,registers:r};
}
function lowerIR(ir){
  const a=new Assembler(1),mapping=[0];
  for(let i=1;i<ir.registers;i++)mapping.push(a.temp());
  const accept=a.label(),reject=a.label();
  const setBig=(out,v)=>{a.clear(out);for(const bit of BigInt(v).toString(2)){a.addInto(out,out);if(bit==="1")a.add1(out);}};
  function lower(code){
    for(const c of code){
      const out=mapping[c.out],x=mapping[c.x],y=mapping[c.y];
      if(c.op==="set")setBig(out,c.value);
      else if(c.op==="copy")a.copy(out,x);
      else if(c.op==="add"){a.copy(out,x);a.addInto(out,y);}
      else if(c.op==="mul"){
        const acc=a.temp(),count=a.temp();a.clear(acc);a.copy(count,x);
        a.take(count,()=>a.addInto(acc,y));a.copy(out,acc);
      }else if(c.op==="sub"){
        const count=a.temp();a.copy(count,y);a.copy(out,x);a.take(count,()=>a.dec(out));
      }else if(c.op==="div2")a.divmod2(mapping[c.q],mapping[c.r],x);
      else if(c.op==="ifNZ")a.ifNZ(x,()=>lower(c.yes),()=>lower(c.no));
      else if(c.op==="ifLT")a.ifLt(x,y,()=>lower(c.yes),()=>lower(c.no));
      else if(c.op==="whileNZ")a.whileNZ(x,()=>lower(c.body));
      else if(c.op==="whileLT"){
        const loop=a.label(),end=a.label();a.at(loop);
        a.ifLt(x,y,()=>{lower(c.body);a.jump(loop);},()=>a.jump(end));a.at(end);
      }else if(c.op==="accept")a.jump(accept);
      else if(c.op==="reject")a.jump(reject);
      else throw Error("Unknown IR operation");
    }
  }
  lower(ir.init);lower(ir.body);a.jump(reject);a.at(reject);a.jump(reject);a.at(accept);
  const total=a.registers;for(let i=0;i<total;i++)a.clear(i);a.code.push({op:"halt"});
  return {...a.finish(),inputNames:ir.inputNames,meaning:ir.meaning};
}
function pair(x,y){x=BigInt(x);y=BigInt(y);return (x+y)*(x+y+1n)/2n+y;}
function triple(k,h,j){return pair(k,pair(h,j));}
module.exports={buildAccuracyIR,runIR,lowerIR,pair,triple};

