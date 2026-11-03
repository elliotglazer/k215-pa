"use strict";
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(BigInt(a));b=abs(BigInt(b));while(b)[a,b]=[b,a%b];return a;}
function q(a,b=1n){a=BigInt(a);b=BigInt(b);if(!b)throw Error("Zero denominator");if(b<0n){a=-a;b=-b;}const g=gcd(a,b);return [a/g,b/g];}
const qadd=(a,b)=>q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const qneg=a=>[-a[0],a[1]];
const qmul=(a,b)=>q(a[0]*b[0],a[1]*b[1]);
const qinv=a=>q(a[1],a[0]);
const qsub=(a,b)=>qadd(a,qneg(b));
const qdiv=(a,b)=>qmul(a,qinv(b));
function f(a,b=0n,c=1n){a=BigInt(a);b=BigInt(b);c=BigInt(c);if(!c)throw Error("Zero denominator");if(c<0n){a=-a;b=-b;c=-c;}const g=gcd(gcd(a,b),c);return [a/g,b/g,c/g];}
const add=(a,b)=>f(a[0]*b[2]+b[0]*a[2],a[1]*b[2]+b[1]*a[2],a[2]*b[2]);
const neg=a=>f(-a[0],-a[1],a[2]);
const sub=(a,b)=>add(a,neg(b));
const mul=(a,b)=>f(a[0]*b[0]+2n*a[1]*b[1],a[0]*b[1]+a[1]*b[0],a[2]*b[2]);
const inv=a=>f(a[0]*a[2],-a[1]*a[2],a[0]*a[0]-2n*a[1]*a[1]);
const div=(a,b)=>mul(a,inv(b));
const scale=(a,k)=>mul(a,f(k));
const equal=(a,b)=>a.every((x,i)=>x===b[i]);
const norm=a=>q(a[0]*a[0]-2n*a[1]*a[1],a[2]*a[2]);
const A=f(-11243,7950);
const P=[f(1641,-1160,8),f(-123720,87483,32)];
const HALF=[f(-7,5),f(-280,198)];
function pointAdd(p,r){
 if(!p)return r;if(!r)return p;
 if(equal(p[0],r[0])&&equal(p[1],neg(r[1])))return null;
 const m=equal(p[0],r[0])?div(add(scale(mul(p[0],p[0]),3),A),scale(p[1],2)):
   div(sub(r[1],p[1]),sub(r[0],p[0]));
 const x=sub(sub(mul(m,m),p[0]),r[0]);
 return [x,sub(mul(m,sub(p[0],x)),p[1])];
}
const pointNeg=p=>p?[p[0],neg(p[1])]:null;
function pointMul(p,n){
 n=BigInt(n);if(n<0n)return pointMul(pointNeg(p),-n);
 let out=null,base=p;while(n){if(n&1n)out=pointAdd(out,base);n>>=1n;if(n)base=pointAdd(base,base);}return out;
}
const coordinates=p=>p?[q(0),q(p[0][0],p[0][2]),q(p[0][1],p[0][2]),q(p[1][0],p[1][2]),q(p[1][1],p[1][2])]:
 [q(1),q(0),q(0),q(0),q(0)];
const indexCode=n=>coordinates(pointMul(P,n));
function localDepthCondition(point,primeProduct){
 primeProduct=BigInt(primeProduct);if(primeProduct<1n)throw Error("Invalid prime product");
 if(!point)return true;
 const reciprocal=inv(point[0]),modulus=primeProduct**4n;
 return reciprocal[0]%modulus===0n&&reciprocal[1]%modulus===0n&&gcd(reciprocal[2],primeProduct)===1n;
}
module.exports={abs,gcd,q,qadd,qneg,qsub,qmul,qinv,qdiv,f,add,neg,sub,mul,inv,div,scale,equal,norm,A,P,HALF,pointAdd,pointNeg,pointMul,coordinates,indexCode,localDepthCondition};

