function verifyNetworkMatrices(maxB) {
 const zero=(n,m=n)=>Array.from({length:n},()=>Array(m).fill(0));
 const id=n=>Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>+(i===j)));
 const tr=A=>A.length?A[0].map((_,j)=>A.map(r=>r[j])):[];
 const mul=(A,B)=>A.map(r=>B[0].map((_,j)=>r.reduce((s,x,k)=>s^(x&B[k][j]),0)));
 const rank=A=>{A=A.map(r=>r.slice());let p=0;for(let j=0;j<(A[0]?.length||0)&&p<A.length;j++){let q=A.findIndex((r,i)=>i>=p&&r[j]);if(q<0)continue;[A[p],A[q]]=[A[q],A[p]];for(let i=0;i<A.length;i++)if(i!==p&&A[i][j])for(let k=j;k<A[i].length;k++)A[i][k]^=A[p][k];p++;}return p;};
 const inv=A=>{let n=A.length;if(!n)return [];let X=A.map((r,i)=>r.concat(id(n)[i]));for(let j=0;j<n;j++){let q=X.findIndex((r,i)=>i>=j&&r[j]);if(q<0)throw Error("singular");[X[j],X[q]]=[X[q],X[j]];for(let i=0;i<n;i++)if(i!==j&&X[i][j])for(let k=j;k<2*n;k++)X[i][k]^=X[j][k];}return X.map(r=>r.slice(n));};
 const dot=(x,y)=>x.reduce((s,a,i)=>s^(a&y[i]),0);
 const mv=(A,v)=>A.map(r=>dot(r,v));
 const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
 const results=[];
 for(let b=1;b<=maxB;b++) {
  let n=3*b,P=zero(n);
  for(let i=0;i<b;i++){for(let j=0;j<3;j++)P[3*i+j][3*i]=1;P[3*i][3*i+1]=1;P[3*i+1][3*i+2]=1;}
  let Pinv=inv(P),cAd=Array(n).fill(0);cAd[1]=1;let c=mv(tr(Pinv),cAd);
  const build=(kind,eps=0)=>{
   let A=zero(n);
   for(let i=0;i<b;i++)A[3*i][3*i]=1;
   let T=id(b);
   if(kind==="S")for(let i=0;i<b;i++)T[i][(i+1)%b]^=1;
   else for(let i=1;i<b;i++)T[i][i-1]=1;
   for(let i=0;i<b;i++)for(let j=0;j<b;j++)A[3*i+1][3*j+2]=A[3*j+2][3*i+1]=T[i][j];
   A[3*(kind==="S"?0:b-1)+2][3*(kind==="S"?0:b-1)+2]=kind==="S"?1:eps;
   return mul(mul(tr(Pinv),A),Pinv);
  };
  let QS=build("S"),QN0=build("N",0),QN1=build("N",1);
  let h=Array.from({length:b},(_,i)=>{let e=Array(n).fill(0);for(let j=0;j<3;j++)e[3*i+j]=1;return mv(QS,e);});
  let subsets=0;
  for(let mask=0;mask<1<<b;mask++){
   let ix=Array.from({length:n},(_,i)=>i).filter(i=>mask&(1<<Math.floor(i/3)));
   let restrict=A=>ix.map(i=>ix.map(j=>A[i][j]));
   let S=restrict(QS),N0=restrict(QN0),N1=restrict(QN1),cc=ix.map(i=>c[i]);
   if(rank(S)!==ix.length-(mask===(1<<b)-1?1:0))throw Error("S rank");
   if(rank(N0)!==ix.length||rank(N1)!==ix.length)throw Error("N rank");
   let delta=ix.length?(dot(cc,mv(inv(N0),cc))^dot(cc,mv(inv(N1),cc))):0;
   if(delta!==+(mask===(1<<b)-1))throw Error("N target");
   for(let A of [S,N0,N1]){
    let sum=ix.map(()=>0);
    for(let i=0;i<b;i++)if(mask&(1<<i))sum=sum.map((v,j)=>v^h[i][ix[j]]);
    if(!eq(mv(A,ix.map(()=>1)),sum))throw Error("grounding");
   }
   subsets++;
  }
  let radAd=Array(n).fill(0);for(let i=0;i<b;i++)radAd[3*i+1]=1;let rad=mv(P,radAd);
  if(mv(QS,rad).some(Boolean)||dot(c,rad)!==1||h.some(v=>dot(v,rad)))throw Error("S radical");
  results.push({b,subsets,grounding:true,singularRanks:true,nonsingularTargets:true,radical:true});
 }
 return {maxB,results,totalSubsets:results.reduce((s,r)=>s+r.subsets,0)};
}

console.log(JSON.stringify(verifyNetworkMatrices(7), null, 2));
