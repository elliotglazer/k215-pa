"use strict";
/*
 * Polynomial formulas over Q for E: y^2=x^3+(-11243+7950 sqrt(2))*x.
 * A field element is [a,b], meaning a+b sqrt(2).
 * A point is [o,x0,x1,y0,y1]; O has the unique code [1,0,0,0,0].
 * No multiplication of integer indices is implemented in this module.
 */
const {Builder}=require("./integer-diophantine-compiler.js");
class RationalBuilder extends Builder {
  constructor(inputNames=[]){super(inputNames);this.fixed=[];this.rationalConstants=new Map();}
  sub(a,b){return this.add(a,this.scale(-1,b));}
  rational(p,q=1n){
    p=BigInt(p);q=BigInt(q);if(q===0n)throw Error("Zero rational denominator");
    if(q<0n){p=-p;q=-q;}if(q===1n)return this.constant(p);
    const key=p+"/"+q;if(this.rationalConstants.has(key))return this.rationalConstants.get(key);
    const x=this.fresh("fixed_"+key);
    this.fixed.push(this.eq(this.scale(q,x),this.constant(p)));
    this.rationalConstants.set(key,x);return x;
  }
  nonzero(x,name="inverse"){
    const u=this.fresh(name);return this.eq(this.mul(x,u),this.constant(1));
  }
  positive(x,name="positive"){
    const q=Array.from({length:4},(_,i)=>this.fresh(name+"_"+i));
    return this.eq(this.mul(x,this.add(...q.map(t=>this.square(t)))),this.constant(1));
  }
  artifact(formula,metadata={}){
    const a=super.artifact(this.and(...this.fixed,formula),metadata);
    a.format="rational-existential-polynomial-circuit-v1";
    a.variableDomain="rational numbers";
    return a;
  }
}
class EllipticCore {
  constructor(b){this.b=b;this.zero=b.constant(0);this.one=b.constant(1);
    this.A=[b.constant(-11243),b.constant(7950)];}
  fc(a,b=0){return [this.b.constant(a),this.b.constant(b)];}
  ff(name){return [this.b.fresh(name+".0"),this.b.fresh(name+".1")];}
  feq(x,y){return this.b.and(...x.map((a,i)=>this.b.eq(a,y[i])));}
  fadd(x,y){return x.map((a,i)=>this.b.add(a,y[i]));}
  fneg(x){return x.map(a=>this.b.scale(-1,a));}
  fsub(x,y){return this.fadd(x,this.fneg(y));}
  fscale(k,x){return x.map(a=>this.b.scale(k,a));}
  fmul(x,y){return [this.b.add(this.b.mul(x[0],y[0]),this.b.scale(2,this.b.mul(x[1],y[1]))),
    this.b.add(this.b.mul(x[0],y[1]),this.b.mul(x[1],y[0]))];}
  fsquare(x){return this.fmul(x,x);}
  fpow(x,n){if(!Number.isSafeInteger(n)||n<0)throw Error("Invalid exponent");
    let r=this.fc(1),q=x;while(n){if(n%2)r=this.fmul(r,q);n=Math.floor(n/2);if(n)q=this.fmul(q,q);}return r;}
  fconj(x){return [x[0],this.b.scale(-1,x[1])];}
  fnorm(x){return this.b.sub(this.b.square(x[0]),this.b.scale(2,this.b.square(x[1])));}
  fnonzero(x,name){return this.b.nonzero(this.fnorm(x),name);}
  fdiv(n,d,name){
    const q=this.ff(name);return {value:q,formula:this.b.and(this.fnonzero(d,name+".inverse_norm"),
      this.feq(this.fmul(d,q),n))};
  }
  point(name){return Array.from({length:5},(_,i)=>this.b.fresh(name+"."+i));}
  x(p){return p.slice(1,3);}
  y(p){return p.slice(3,5);}
  O(){return [this.one,this.zero,this.zero,this.zero,this.zero];}
  P(){const b=this.b;return [this.zero,b.rational(1641,8),b.constant(-145),
    b.rational(-15465,4),b.rational(87483,32)];}
  peq(p,q){return this.b.and(...p.map((a,i)=>this.b.eq(a,q[i])));}
  isO(p){return this.peq(p,this.O());}
  finite(p){return this.b.eq(p[0],this.zero);}
  curve(x,y){return this.feq(this.fsquare(y),this.fadd(this.fmul(this.fsquare(x),x),this.fmul(this.A,x)));}
  /*
   * Exact definition of D=2E(F).
   * The finite branch gives a finite preimage with nonzero y and its tangent.
   */
  member(p,name="member"){
    const b=this.b,X=this.ff(name+".X"),Y=this.ff(name+".Y"),m=this.ff(name+".slope");
    const xp=this.fsub(this.fsquare(m),this.fscale(2,X));
    const yp=this.fsub(this.fmul(m,this.fsub(X,xp)),Y);
    return b.or(this.isO(p),b.and(this.finite(p),this.curve(X,Y),
      this.fnonzero(Y,name+".inverse_norm_y"),
      this.feq(this.fmul(this.fscale(2,Y),m),this.fadd(this.fscale(3,this.fsquare(X)),this.A)),
      this.feq(this.x(p),xp),this.feq(this.y(p),yp)));
  }
  /*
   * Preconditions: p and q are canonical points of E(F).
   * Postcondition: r is their canonical sum. Five branches include all charts.
   */
  addRelation(p,q,r,name="add"){
    const b=this.b,x=this.x(p),y=this.y(p),u=this.x(q),v=this.y(q),
      mf=this.ff(name+".general.slope"),md=this.ff(name+".double.slope");
    const output=m=>{
      const xr=this.fsub(this.fsub(this.fsquare(m),x),u);
      return b.and(this.finite(r),this.feq(this.x(r),xr),
        this.feq(this.y(r),this.fsub(this.fmul(m,this.fsub(x,xr)),y)));
    };
    const both=b.and(this.finite(p),this.finite(q));
    return b.or(
      b.and(this.isO(p),this.peq(q,r)),
      b.and(this.finite(p),this.isO(q),this.peq(p,r)),
      b.and(both,this.feq(x,u),this.feq(y,this.fneg(v)),this.isO(r)),
      b.and(both,this.fnonzero(this.fsub(u,x),name+".general.inverse_norm"),
        this.feq(this.fmul(this.fsub(u,x),mf),this.fsub(v,y)),output(mf)),
      b.and(both,this.feq(x,u),this.feq(y,v),this.fnonzero(y,name+".double.inverse_norm"),
        this.feq(this.fmul(this.fscale(2,y),md),this.fadd(this.fscale(3,this.fsquare(x)),this.A)),output(md))
    );
  }
  add(p,q,r,name="add"){
    return this.b.and(this.member(p,name+".left"),this.member(q,name+".right"),this.addRelation(p,q,r,name));
  }
  neg(p){return [p[0],p[1],p[2],this.b.scale(-1,p[3]),this.b.scale(-1,p[4])];}
  scalar(p,k,name="scalar"){
    k=BigInt(k);if(k<0n)return this.scalar(this.neg(p),-k,name);
    const relations=[];let r=this.O(),q=p,i=0;
    while(k){
      if(k&1n){const t=this.point(name+".sum."+i);relations.push(this.addRelation(r,q,t,name+".sum."+i));r=t;}
      k>>=1n;
      if(k){const t=this.point(name+".double."+i);relations.push(this.addRelation(q,q,t,name+".double."+i));q=t;}
      i++;
    }
    return {value:r,formula:this.b.and(...relations)};
  }
  /*
   * Preconditions: p belongs to D. Nonzero field guards remain explicit.
   * z(O)=0; z(p)=-x(p)/y(p) otherwise.
   */
  z(p,value,name="z"){
    return this.b.or(this.b.and(this.isO(p),this.feq(value,this.fc(0))),
      this.b.and(this.finite(p),this.fnonzero(this.y(p),name+".inverse_norm"),
        this.feq(this.fmul(this.y(p),value),this.fneg(this.x(p)))));
  }
  inverseX(p,value,name="inverse_x"){
    return this.b.or(this.b.and(this.isO(p),this.feq(value,this.fc(0))),
      this.b.and(this.finite(p),this.feq(this.fmul(this.x(p),value),this.fc(1))));
  }
  log25(z){
    const d2=this.fc(11243,-7950),coeff=[16575,-6630,11050,-25500,68250,-198900,612612];
    let out=this.fc(0),dPower=this.fc(1);
    for(let j=0;j<coeff.length;j++){
      out=this.fadd(out,this.fscale(coeff[j],this.fmul(dPower,this.fpow(z,4*j+1))));
      dPower=this.fmul(dPower,d2);
    }
    return out;
  }
  /*
   * Preconditions: h,j in D. Formula additionally requires h != O.
   * r is one half of the field trace of z(j)/z(h).
   */
  traceRatio(h,j,r,name="trace_ratio"){
    const zh=this.ff(name+".zh"),zj=this.ff(name+".zj"),q=this.fdiv(zj,zh,name+".quotient");
    return this.b.and(this.finite(h),this.z(h,zh,name+".h"),this.z(j,zj,name+".j"),
      q.formula,this.b.eq(r,q.value[0]));
  }
  closeTo(a,r,name="close"){
    return this.b.positive(this.b.sub(this.one,this.b.scale(64,this.b.square(this.b.sub(a,r)))),name);
  }
}
function makeTemplates(){
  const result={};
  {
    const b=new RationalBuilder(Array.from({length:5},(_,i)=>"p."+i)),e=new EllipticCore(b);
    result.member=b.artifact(e.member(b.inputs),{relation:"p in 2E(Q(sqrt(2)))"});
  }
  {
    const b=new RationalBuilder(Array.from({length:15},(_,i)=>["p","q","r"][Math.floor(i/5)]+"."+(i%5))),e=new EllipticCore(b);
    result.add=b.artifact(e.add(b.inputs.slice(0,5),b.inputs.slice(5,10),b.inputs.slice(10)),{relation:"p,q in D and r=p+q"});
  }
  {
    const b=new RationalBuilder(Array.from({length:11},(_,i)=>i===10?"r":["h","j"][Math.floor(i/5)]+"."+(i%5))),e=new EllipticCore(b),
      h=b.inputs.slice(0,5),j=b.inputs.slice(5,10);
    result.traceRatio=b.artifact(b.and(e.member(h,"h.member"),e.member(j,"j.member"),e.traceRatio(h,j,b.inputs[10])),
      {relation:"h,j in D; h nonzero; r=Tr(z(j)/z(h))/2"});
  }
  {
    const b=new RationalBuilder(["a","r"]),e=new EllipticCore(b);
    result.close=b.artifact(e.closeTo(...b.inputs),{relation:"abs(a-r)<1/8"});
  }
  return result;
}
module.exports={RationalBuilder,EllipticCore,makeTemplates};
if(require.main===module){
  const fs=require("node:fs"),path=require("node:path"),data=makeTemplates();
  fs.writeFileSync(path.join(__dirname,"rational-elliptic-templates.json"),JSON.stringify(data)+"\n");
  console.log(JSON.stringify(Object.fromEntries(Object.entries(data).map(([k,a])=>[k,{variables:a.variables.length,nodes:a.nodes.length,formulas:a.formulas.length}]))));
}

