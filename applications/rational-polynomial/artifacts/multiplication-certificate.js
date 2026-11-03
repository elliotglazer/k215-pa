"use strict";
const {PolynomialLibrary,auditLibrary}=require("./rational-polynomial-library.js");
const {EllipticCore}=require("./rational-elliptic-core.js");
const names=(prefix,n)=>Array.from({length:n},(_,i)=>prefix+"."+i);
const pointNames=(prefix,n)=>Array.from({length:n},(_,i)=>names(prefix+i,5)).flat();
const chunks=(xs,n)=>Array.from({length:xs.length/n},(_,i)=>xs.slice(n*i,n*i+n));
function pow(b,x,n){let result=b.constant(1),base=x;while(n){if(n%2)result=b.mul(result,base);n=Math.floor(n/2);if(n)base=b.square(base);}return result;}
function addCore(library){
  library.define("member",names("p",5),(b,p)=>new EllipticCore(b).member(p),{meaning:"p belongs to D=2E(F)"});
  library.define("raw_add",["p","q","r"].flatMap(s=>names(s,5)),(b,p)=>{
    const e=new EllipticCore(b);return e.addRelation(...chunks(p,5));
  },{meaning:"r=p+q",preconditions:"p and q are canonical points of E(F)"});
  library.define("raw_z",names("p",5).concat(names("z",2)),(b,p)=>{
    const e=new EllipticCore(b);return e.z(p.slice(0,5),p.slice(5));
  },{meaning:"z(O)=0; z(p)=-x/y",preconditions:"p belongs to D"});
  library.define("raw_inverse_x",names("p",5).concat(names("inverse_x",2)),(b,p)=>{
    const e=new EllipticCore(b);return e.inverseX(p.slice(0,5),p.slice(5));
  },{meaning:"inverse_x(O)=0; inverse_x(p)=1/x",preconditions:"p belongs to D"});
  library.define("log25",["z","value"].flatMap(s=>names(s,2)),(b,p)=>{
    const e=new EllipticCore(b);return e.feq(e.log25(p.slice(0,2)),p.slice(2));
  },{meaning:"value=L(z), the explicit scaled degree-25 formal logarithm"});
  library.define("pole",["B"],(b,[B])=>{
    const bits=Array.from({length:6},(_,i)=>b.fresh("bit."+i)),
      [e,z,r1,r2,w]=["e","z","r1","r2","w"].map(s=>b.fresh(s));
    const one=b.constant(1),
      m=b.mul(b.sub(one,b.scale(2,bits[0])),...bits.slice(1).map((v,i)=>b.add(one,b.scale([1,2,4,6,12][i],v)))),
      A=b.mul(m,B),H=b.mul(A,b.sub(A,b.square(B))),Az2=b.mul(A,b.square(z)),
      T1=b.mul(A,b.sub(A,e),b.add(A,b.scale(3,e))),
      T2=b.mul(A,b.sub(Az2,b.mul(e,H)),b.add(Az2,b.scale(3,b.mul(e,H)))),
      terms=bits.map(v=>b.square(b.sub(b.square(v),v))).concat([
        b.square(b.sub(b.mul(e,H,z,w),one)),b.square(b.sub(b.square(r1),T1)),b.square(b.sub(b.square(r2),T2))]);
    return b.eq(b.mul(B,b.add(...terms)),b.constant(0));
  },{meaning:"The eleven-witness polynomial Q_pole(B)=0",arithmeticDependency:"Completeness uses the recorded restricted pointwise converse"});
}
function addTestGroup(library){
  library.define("test_group",pointNames("C",4).concat(names("D",24)),(b,p)=>{
    const e=new EllipticCore(b),C=chunks(p.slice(0,20),5),output=chunks(p.slice(20),2),
      first=Array.from({length:4},(_,i)=>e.point("first."+i)),
      second=Array.from({length:4},(_,i)=>e.point("second."+i)),f=[];
    for(let i=0;i<4;i++){
      f.push(b.call("member",first[i]));
      f.push(b.call("raw_add",first[i].concat(e.neg(C[i]),second[i])));
    }
    f.push(e.finite(first[0]),e.finite(second[0]));
    const points=first.concat(second),zs=[],logs=[],reciprocals=[];
    for(let i=0;i<8;i++){
      const z=e.ff("z."+i),L=e.ff("L."+i),r=e.ff("reciprocal."+i);
      f.push(b.call("raw_z",points[i].concat(z)),b.call("log25",z.concat(L)),
        b.call("raw_inverse_x",points[i].concat(r)));
      zs.push(z);logs.push(L);reciprocals.push(r);
    }
    f.push(e.fnonzero(logs[0],"log_first_inverse"),e.fnonzero(logs[4],"log_second_inverse"));
    const ratios=[];
    for(let side=0;side<2;side++)for(let i=1;i<=3;i++){
      const q=e.ff("ratio."+side+"."+i);
      f.push(e.feq(e.fmul(logs[4*side],q),logs[4*side+i]));ratios.push(q);
    }
    const tests=reciprocals.slice(0,4).concat(reciprocals.slice(4).map(x=>e.fconj(x)),
      [0,1,2].map(i=>e.fsub(ratios[i],e.fconj(ratios[3+i]))),
      [e.fsub(e.fmul(ratios[0],ratios[1]),ratios[2])]);
    if(tests.length!==12)throw Error("Wrong test count");
    tests.forEach((x,i)=>f.push(e.feq(output[i],x)));
    return b.and(...f);
  },{meaning:"Twelve field-valued local tests, with eight reciprocal-x tests and four precision-25 tests",
    preconditions:"C0=cstar*P and Ci=cstar*Pi for i=1,2,3; all are points of D",
    precisions:[1,1,1,1,1,1,1,1,25,25,25,25]});
}
function addSlope(library){
  library.define("slope",["t","ell"].concat(pointNames("C",4)),(b,p)=>{
    const e=new EllipticCore(b),[t,ell]=p,C=p.slice(2),one=b.constant(1),u=b.sub(t,one),
      eta=b.fresh("eta"),q=b.fresh("q"),R0=b.fresh("R0"),
      contactProduct=b.mul(...[0,15,20,24,30,60].map(a=>b.add(t,b.constant(a)))),
      a=b.sub(one,b.mul(R0,b.square(q))),R=b.mul(b.square(ell),b.square(a),R0),f=[
        b.eq(b.square(eta),one),b.nonzero(u,"contact_1_inverse"),
        b.nonzero(contactProduct,"contacts_inverse"),b.nonzero(ell,"ell_inverse"),
        b.eq(b.mul(R0,pow(b,u,8)),b.mul(eta,contactProduct)),b.nonzero(a,"a_inverse")];
    const denominators=[b.mul(R0,pow(b,u,2)),b.mul(pow(b,R0,25),pow(b,u,26))],inverses=[];
    for(let g=0;g<6;g++){
      const ds=Array.from({length:12},(_,j)=>e.ff("D."+g+"."+j));
      f.push(b.call("test_group",C.concat(ds.flat())));
      let W=e.fc(1);
      for(let j=0;j<12;j++){
        const normalized=e.ff("normalized."+g+"."+j),den=denominators[j<8?0:1];
        f.push(e.feq(normalized.map(v=>b.mul(den,v)),ds[j]));
        W=e.fmul(W,e.fadd(e.fc(1),e.fsquare(normalized).map(v=>b.mul(R,v))));
      }
      const inverse=e.fdiv(e.fc(1),W,"inverse_W."+g);
      f.push(inverse.formula);inverses.push(inverse.value);
    }
    const theta=b.scale(2,b.add(...inverses.map(v=>v[0]))),B=b.fresh("B");
    f.push(b.nonzero(theta,"theta_inverse"),b.eq(b.mul(B,b.square(theta)),R),b.call("pole",[B]));
    return b.and(...f);
  },{meaning:"One normalized six-contact slope certificate",
    preconditions:"ell is the prescribed nonzero integer; C0=cstar*P and Ci=cstar*Pi",
    contactRoots:[0,-15,-20,-24,-30,-60],evenPole:1,witnessGroups:6});
}
function addHeightCertificate(library){
  library.define("height_certificate",pointNames("P",3).concat(["ell"],pointNames("C",4)),(b,p)=>{
    const e=new EllipticCore(b),roots=chunks(p.slice(0,15),5),ell=p[15],C=p.slice(16),f=[],quantities=[];
    roots.forEach((point,i)=>{
      f.push(b.call("member",point));
      const a0=b.fresh("homogeneous."+i+".a0"),a1=b.fresh("homogeneous."+i+".a1"),den=b.fresh("homogeneous."+i+".b");
      f.push(b.nonzero(den,"homogeneous."+i+".inverse_b"),b.eq(b.mul(den,point[1]),a0),b.eq(b.mul(den,point[2]),a1));
      quantities.push(a0,a1,den);
    });
    quantities.forEach((quantity,i)=>{
      const slopes=Array.from({length:3},(_,j)=>b.fresh("slope."+i+"."+j));
      f.push(b.eq(b.add(...slopes),quantity));
      slopes.forEach(t=>f.push(b.call("slope",[t,ell,...C])));
    });
    return b.and(...f);
  },{meaning:"Twenty-seven slope certificates for nine homogeneous coordinate quantities",
    preconditions:"ell and C are linked to the fixed constants and root points by the outer multiplication formula",
    limitation:"This is the unguarded certificate; false triples in the fixed finite box must still be excluded"});
}
function buildCertificateLibrary(){
  const library=new PolynomialLibrary();addCore(library);addTestGroup(library);addSlope(library);addHeightCertificate(library);
  return library;
}
module.exports={buildCertificateLibrary,addCore,addTestGroup,addSlope,addHeightCertificate,pow};
if(require.main===module){
  const fs=require("node:fs"),path=require("node:path"),library=buildCertificateLibrary(),artifact=library.artifact({
    limitation:"Certificate components only. The fixed-constant binding, finite guard and universal rational equation remain to be composed.",
    source:"six-contact-certificate.txt and linear-prime-certificate.txt"}),checks=auditLibrary(artifact);
  const data=JSON.stringify(artifact)+"\n";
  fs.writeFileSync(path.join(__dirname,"multiplication-certificate-library.json"),data);
  fs.writeFileSync(path.join(__dirname,"multiplication-certificate-structure-checks.json"),JSON.stringify({...checks,bytes:Buffer.byteLength(data)},null,2)+"\n");
  console.log(JSON.stringify({...checks,bytes:Buffer.byteLength(data)},null,2));
}

