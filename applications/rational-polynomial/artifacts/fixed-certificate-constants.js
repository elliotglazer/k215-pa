"use strict";
const {gcd,P,pointAdd,localDepthCondition}=require("./rational-field-arithmetic.js");
function isPrime(n){
 n=BigInt(n);if(n<2n)return false;if(n%2n===0n)return n===2n;
 for(let d=3n;d*d<=n;d+=2n)if(n%d===0n)return false;return true;
}
function primesThrough(bound){bound=BigInt(bound);const p=[];for(let n=2n;n<=bound;n++)if(isPrime(n))p.push(n);return p;}
function progressionPrimes(modulus,residue,count,floor){
 modulus=BigInt(modulus);residue=BigInt(residue);floor=BigInt(floor);
 if(modulus<=0n||residue<=0n||residue>=modulus||gcd(modulus,residue)!==1n||
    !Number.isSafeInteger(count)||count<0)throw Error("Invalid progression");
 let n=residue;if(n<=floor)n+=((floor-n)/modulus+1n)*modulus;
 const result=[];while(result.length<count){if(isPrime(n))result.push(n);n+=modulus;}return result;
}
function catalogueProduct(modulus,count=22,floor=324n){
 modulus=BigInt(modulus);let product=1n,maximum=0n,number=0n;
 for(let r=1n;r<modulus;r++)if(gcd(r,modulus)===1n){
   for(const p of progressionPrimes(modulus,r,count,floor)){product*=p;if(p>maximum)maximum=p;number++;}
 }
 return {product,maximum,number};
}
function localMultiplier(primeProduct){
 primeProduct=BigInt(primeProduct);let point=P,m=1n;
 while(!localDepthCondition(point,primeProduct)){point=pointAdd(point,P);m++;}
 return m;
}
function factorial(n){n=BigInt(n);let f=1n;for(let i=2n;i<=n;i++)f*=i;return f;}
function max(...xs){return xs.reduce((a,b)=>a>b?a:b);}
const smallPrimes=primesThrough(324),P0=smallPrimes.reduce((a,p)=>a*p,1n),W=4n*P0;
/*
 * This is a finite prescription, not a practical instruction to expand the
 * astronomical constants in this runtime. CLI output below only records it.
 * The minimal-m search is justified by the open formal subgroup argument.
 */
function computeConstants(){
 const H=catalogueProduct(W),Ns=P0*H.product,M=localMultiplier(Ns),cstar=4n*M,
  ell=12n*P0**2916n*H.product**732n,F=factorial(324),
  D=F*3n**(256n*F**4n),G0=116064000000n,E0=10n*(D*G0)**2n,
  R=max(D,H.maximum,cstar,10n**12n),Q=R**(R*E0),
  Bcm=D**2n*3n**(21000n*D**2n)+1n,
  Ccm=2n*Bcm+4096n*(1028n+5n*D+84000n*D**2n),
  Aheight=2n*10n**13n*max(1n,Ccm,Q**17n),T=(48n*Aheight)**13n;
 return {P0,W,Hproduct:H.product,Hmax:H.maximum,Ns,M,cstar,ell,D,G0,E0,R,Q,Bcm,Ccm,Aheight,T};
}
function prescription(){
 return {format:"fixed-certificate-constant-prescription-v1",smallPrimes:smallPrimes.map(String),P0:String(P0),W:String(W),
  H:"For each unit r modulo W, take the first 22 primes >324 congruent to r. Hproduct is their product; Hmax their maximum.",
  Ns:"P0*Hproduct",
  M:"The least m>=1 for which inv(x([m]P))=(a+b*sqrt(2))/c in normalized integer coefficients satisfies Ns^4|a, Ns^4|b and gcd(c,Ns)=1.",
  cstar:"4*M",ell:"12*P0^2916*Hproduct^732",
  D:"324!*3^(256*(324!)^4)",G0:"116064000000",E0:"10*(D*G0)^2",
  R:"max(D,Hmax,cstar,10^12)",Q:"R^(R*E0)",Bcm:"D^2*3^(21000*D^2)+1",
  Ccm:"2*Bcm+4096*(1028+5*D+84000*D^2)",Aheight:"2*10^13*max(1,Ccm,Q^17)",T:"(48*Aheight)^13",
  adjustment:"R uses cstar as an upper bound for its prime divisors. This only enlarges the previous height cutoff.",
  status:"A complete finite prescription. The astronomical catalogue, M, ell and T have not been evaluated."};
}
module.exports={isPrime,primesThrough,progressionPrimes,catalogueProduct,localMultiplier,factorial,P0,W,prescription,computeConstants};
if(require.main===module){
 const fs=require("node:fs"),path=require("node:path"),data=prescription();
 fs.writeFileSync(path.join(__dirname,"fixed-certificate-constants.json"),JSON.stringify(data,null,2)+"\n");
 console.log(JSON.stringify({smallPrimeCount:smallPrimes.length,P0:String(P0),W:String(W),status:data.status},null,2));
}

