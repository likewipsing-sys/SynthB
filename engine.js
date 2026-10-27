// ===== HANBIT WT-1 · audio engine (AudioWorkletProcessor) =====
const N=2048,NL=11,TAU=Math.PI*2,MAXV=32,CH=32;
const DIVB=[16,8,4,2,1,.5,.25,.125,4/3,2/3,1/3,1/6,3,1.5,.75,.375];
const VOW=[[800,1150,2900],[400,1600,2700],[350,2300,2900],[450,800,2830],[325,700,2530]];
const STACKS=[[0],[0,12],[0,7],[0,12,7,19],[0,4,7],[0,-12]];
const HANN=new Float32Array(1026);for(let i=0;i<1026;i++)HANN[i]=.5-.5*Math.cos(TAU*Math.min(i,1024)/1024);
const HIL1=[.6923878,.9360654322959,.9882295226860,.9987488452737].map(a=>a*a);
const HIL2=[.4021921162426,.8561710882420,.9722909545651,.9952884791278].map(a=>a*a);
const REVB=[29.7,37.1,41.1,43.7,53.3,59.9,67.7,73.1];
const APL=[[142,107,379,277],[229,173,503,421]];
// warp modes: 0 off,1 sync,2 window sync,3 bend+,4 bend-,5 bend±,6 pwm,7 asym+,8 asym-,9 asym±,10 flip,11 mirror,12 quantize,
// 13-17 FM<-A,B,C,Sub,Noise · 18-21 AM<-A,B,C,Sub · 22-25 RM<-A,B,C,Sub
const WSRC=[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2,3,4,0,1,2,3,0,1,2,3];
const WPH=new Uint8Array(26);[1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17].forEach(i=>WPH[i]=1);
const WOUT=new Uint8Array(26);[2,10,18,19,20,21,22,23,24,25].forEach(i=>WOUT[i]=1);

const SINT=new Float32Array(4097);for(let i=0;i<=4096;i++)SINT[i]=Math.sin(TAU*i/4096);
function fsin(c){c-=Math.floor(c);const x=c*4096,j=x|0;return SINT[j]+(SINT[j+1]-SINT[j])*(x-j);}
function ft(x){if(x<-3)return -1;if(x>3)return 1;const q=x*x;return x*(27+q)/(27+9*q);}
function cv(u,c,den){if(u>=1)return 1;if(u<=0)return 0;if(den===0)return u;return (Math.exp(c*5*u)-1)/den;}
function blep(t,dt){if(t<dt){t/=dt;return t+t-t*t-1;}if(t>1-dt){t=(t-1)/dt;return t*t+t+t+1;}return 0;}
function bp(q,w){const e=1+4*w;return q<.5?.5*Math.pow(2*q,e):1-.5*Math.pow(2*(1-q),e);}
function bm(q,w){const e=1/(1+4*w);return q<.5?.5*Math.pow(2*q,e):1-.5*Math.pow(2*(1-q),e);}
function wph(m,w,q,s){
  switch(m){
    case 1:case 2:{const x=q*(1+w*15);return x-Math.floor(x);}
    case 3:return bp(q,w);
    case 4:return bm(q,w);
    case 5:return w>=.5?bp(q,(w-.5)*2):bm(q,(.5-w)*2);
    case 6:{const x=q/(1-.97*w);return x>=1?-1:x;}
    case 7:return Math.pow(q,1+4*w);
    case 8:return Math.pow(q,1/(1+4*w));
    case 9:return w>=.5?Math.pow(q,1+8*(w-.5)):Math.pow(q,1/(1+8*(.5-w)));
    case 11:return q<.5?q:(1-w)*q+w*(1-q);
    case 12:{const st=Math.pow(2,10-9*w);return Math.floor(q*st)/st;}
    case 13:case 14:case 15:case 16:case 17:{const x=q+w*w*3*s;return x-Math.floor(x);}
  }
  return q;
}
function wout(m,w,val,p,s){
  if(m===2)return val*(.5-.5*Math.cos(TAU*p));
  if(m===10)return p>1-w*.999?-val:val;
  if(m>=18&&m<=21)return val*(1-w+w*(s*.5+.5));
  if(m>=22)return val*(1-w+w*s);
  return val;
}
// envelope params p: [dl,a,h,d,s,r,ac,dc,rc,denA,denD,denR] (times in samples)
function eVal(e,p){switch(e.st){
  case 1:return e.v0+(1-e.v0)*cv(e.t/p[1],p[6],p[9]);
  case 2:return 1;
  case 3:return p[4]+(1-p[4])*(1-cv(e.t/p[3],p[7],p[10]));
  case 4:return p[4];
  case 5:return e.rv*(1-cv(e.t/p[5],p[8],p[11]));
  default:return 0;}}
function eAdv(e,p,n){e.t+=n;for(;;){const st=e.st;let d;
  if(st===0)d=p[0];else if(st===1)d=p[1];else if(st===2)d=p[2];else if(st===3)d=p[3];else if(st===5)d=p[5];else return;
  if(e.t<d)return;e.t-=d;if(st===5){e.st=6;return;}e.st=st+1;if(e.st===4){e.t=0;return;}}}
function eDur(e,p){const st=e.st;return st===0?p[0]:st===1?p[1]:st===2?p[2]:st===3?p[3]:st===5?p[5]:0;}

function svfCh(s,o,X,m,g,dg,k,ty,A2,drv,dn,mix){
  let c1=s[o],c2=s[o+1],d1=s[o+2],d2=s[o+3];const two=ty===1||ty===3||ty===5,k2=ty===5?k:1.414;
  for(let i=0;i<m;i++){g+=dg;const dry=X[i];const x=drv?ft(dry*drv)*dn:dry;
    let a1=1/(1+g*(g+k)),a2=g*a1,a3=g*a2;let v3=x-c2,v1=a1*c1+a2*v3,v2=c2+a2*c1+a3*v3;c1=2*v1-c1;c2=2*v2-c2;
    let y;
    switch(ty){case 0:case 1:y=v2;break;case 2:case 3:y=x-k*v1-v2;break;case 4:case 5:y=k*v1;break;case 6:y=x-k*v1;break;
      case 7:y=x+(A2-1)*k*v1;break;case 8:y=x-2*k*v1;break;case 9:y=x+(A2-1)*v2;break;default:y=x+(A2-1)*(x-k*v1-v2);}
    if(two){a1=1/(1+g*(g+k2));a2=g*a1;a3=g*a2;v3=y-d2;v1=a1*d1+a2*v3;v2=d2+a2*d1+a3*v3;d1=2*v1-d1;d2=2*v2-d2;
      y=ty===1?v2:ty===3?y-k2*v1-v2:k2*v1;}
    X[i]=dry+(y-dry)*mix;}
  s[o]=c1;s[o+1]=c2;s[o+2]=d1;s[o+3]=d2;
  if(!(c1<1e9&&c1>-1e9)){s[o]=s[o+1]=s[o+2]=s[o+3]=0;}
}
function ladCh(s,o,X,m,G,k,drv,sat,mix,P,comp){
  let s1=s[o],s2=s[o+1],s3=s[o+2],s4=s[o+3],y=s[o+4];const sg=1+sat*4,si=1/sg;
  for(let i=0;i<m;i++){const dry=X[i];const u=ft(dry*drv-k*ft(y*sg)*si);
    let vv=(u-s1)*G;const a=vv+s1;s1=a+vv;vv=(a-s2)*G;const b=vv+s2;s2=b+vv;
    if(P===4){vv=(b-s3)*G;const c=vv+s3;s3=c+vv;vv=(c-s4)*G;y=vv+s4;s4=y+vv;}else y=b;
    X[i]=dry+(y*comp-dry)*mix;}
  s[o]=s1;s[o+1]=s2;s[o+2]=s3;s[o+3]=s4;s[o+4]=y;
}
function phCh(s,o,X,m,c,fb,mix){
  let z0=s[o],z1=s[o+1],z2=s[o+2],z3=s[o+3],last=s[o+4];
  for(let i=0;i<m;i++){const dry=X[i];let x=dry+fb*last,y;
    y=c[0]*x+z0;z0=x-c[0]*y;x=y;y=c[1]*x+z1;z1=x-c[1]*y;x=y;y=c[2]*x+z2;z2=x-c[2]*y;x=y;y=c[3]*x+z3;z3=x-c[3]*y;
    last=ft(y);X[i]=dry*(1-mix)+(dry+y)*.5*mix;}
  s[o]=z0;s[o+1]=z1;s[o+2]=z2;s[o+3]=z3;s[o+4]=last;
}
function rbj(type,f,gdB,Q,sr,out,o){
  const A=Math.pow(10,gdB/40),w0=TAU*Math.min(f,sr*.49)/sr,cs=Math.cos(w0),sn=Math.sin(w0),al=sn/(2*Q);let b0,b1,b2,a0,a1,a2;
  if(type===1){b0=1+al*A;b1=-2*cs;b2=1-al*A;a0=1+al/A;a1=-2*cs;a2=1-al/A;}
  else if(type===0){const sq=2*Math.sqrt(A)*al;b0=A*((A+1)-(A-1)*cs+sq);b1=2*A*((A-1)-(A+1)*cs);b2=A*((A+1)-(A-1)*cs-sq);a0=(A+1)+(A-1)*cs+sq;a1=-2*((A-1)+(A+1)*cs);a2=(A+1)+(A-1)*cs-sq;}
  else {const sq=2*Math.sqrt(A)*al;b0=A*((A+1)+(A-1)*cs+sq);b1=-2*A*((A-1)+(A+1)*cs);b2=A*((A+1)+(A-1)*cs-sq);a0=(A+1)-(A-1)*cs+sq;a1=2*((A-1)-(A+1)*cs);a2=(A+1)-(A-1)*cs-sq;}
  out[o]=b0/a0;out[o+1]=b1/a0;out[o+2]=b2/a0;out[o+3]=a1/a0;out[o+4]=a2/a0;
}

function mkVoice(np){
  const os=[];for(let o=0;o<3;o++){const g=[];for(let j=0;j<24;j++)g.push({on:false,p:0,inc:0,age:0,len:1,gl:0,gr:0});os.push({ph:new Float64Array(16),sp:new Float64Array(16),ls:0,g,gn:0});}
  const fl=[];for(let f=0;f<2;f++)fl.push({s:new Float64Array(48),gL:-1,gR:-1,cL:new Float32Array(4096),cR:new Float32Array(4096),cw:0});
  return {active:false,rel:false,kill:0,note:60,vel:.8,rnd:0,age:0,id:0,pitch:60,target:60,
    e:[0,1,2,3].map(()=>({st:6,t:0,v0:0,rv:0,v:0})),ep:[0,1,2,3].map(()=>new Float64Array(12)),
    lph:new Float64Array(10),ls:new Float64Array(10),sg:new Float64Array(27).fill(1),src:new Float64Array(27),mod:new Float64Array(np),
    os,fl,raw:[0,1,2,3,4].map(()=>new Float32Array(CH)),subPh:0,nz:new Float64Array(8),nzh:0,oL:new Float32Array(CH),oR:new Float32Array(CH)};
}

class WT1 extends AudioWorkletProcessor{
  constructor(){super();this.ok=false;this.q=[];
    this.port.onmessage=e=>{try{this.msg(e.data);}catch(err){this.port.postMessage({t:'err',m:String(err&&err.stack||err)});}};}
  msg(d){
    if(d.t==='init')return this.init(d);
    if(!this.ok)return;
    switch(d.t){
      case 'n':this.pn[d.i]=d.v;break;
      case 'nn':for(let j=0;j<d.i.length;j++)this.pn[d.i[j]]=d.v[j];break;
      case 'e':this.pe[d.i]=d.v;break;
      case 'ee':for(let j=0;j<d.i.length;j++)this.pe[d.i[j]]=d.v[j];break;
      case 'table':this.tables[d.o]={F:d.F,m:d.m};break;
      case 'frame':{const t=this.tables[d.o];if(t)for(let l=0;l<NL;l++)t.m[l].set(d.m[l],d.i*N);break;}
      case 'sample':this.samples[d.o]=d.d?{d:d.d,sr:d.sr}:null;break;
      case 'lfo':this.lfoT[d.i]=d.d;break;
      case 'routes':this.setRoutes(d.r);break;
      case 'order':this.order=d.a.slice();break;
      case 'on':case 'off':this.q.push(d);break;
      case 'mw':this.mw=d.v;break;
      case 'pb':this.pb=d.v;break;
      case 'panic':for(const v of this.V)v.active=false;this.mono=[];this.q.length=0;this.fxInit();break;
      case 'release':for(const v of this.V)if(v.active)this.release(v);this.mono=[];break;
    }
  }
  init(d){
    const np=d.pk.length;this.np=np;this.pmin=new Float64Array(np);this.pmax=new Float64Array(np);this.pcur=new Uint8Array(np);this.pn=new Float64Array(np);this.isFx=new Uint8Array(np);
    const K={};d.pk.forEach((a,i)=>{K[a[0]]=i;this.pmin[i]=a[1];this.pmax[i]=a[2];this.pcur[i]=a[3];this.pn[i]=a[4];if(a[0].startsWith('fx.'))this.isFx[i]=1;});
    const E={};this.pe=new Float64Array(d.ek.length);d.ek.forEach((a,i)=>{E[a[0]]=i;this.pe[i]=a[1];});
    this.K=K;this.E=E;
    this.OI=['A','B','C'].map(X=>{const o={};['pos','w1','w2','uni','det','blend','width','oct','semi','fine','phase','rand','pan','level'].forEach(p=>o[p]=K[X+'.'+p]);
      ['on','type','wm1','wm2','route','stack','loop'].forEach(p=>o['e'+p]=E[X+'.'+p]);return o;});
    this.SI={oct:K['sub.oct'],level:K['sub.level'],pan:K['sub.pan'],on:E['sub.on'],shape:E['sub.shape'],route:E['sub.route']};
    this.NI={pitch:K['noise.pitch'],level:K['noise.level'],pan:K['noise.pan'],on:E['noise.on'],type:E['noise.type'],route:E['noise.route']};
    this.FI=['f1','f2'].map(F=>({cut:K[F+'.cut'],res:K[F+'.res'],drive:K[F+'.drive'],vr:K[F+'.var'],key:K[F+'.key'],mix:K[F+'.mix'],on:E[F+'.on'],type:E[F+'.type']}));
    this.serial=E['f.serial'];
    this.EI=[1,2,3,4].map(i=>['dl','a','h','d','s','r','ac','dc','rc'].map(p=>K[`env${i}.${p}`]));
    this.LI=[];for(let i=1;i<=10;i++)this.LI.push({rate:K[`lfo${i}.rate`],div:K[`lfo${i}.div`],rise:K[`lfo${i}.rise`],dly:K[`lfo${i}.dly`],smooth:K[`lfo${i}.smooth`],phase:K[`lfo${i}.phase`],sync:E[`lfo${i}.sync`],mode:E[`lfo${i}.mode`]});
    this.GI={voices:K['g.voices'],glide:K['g.glide'],bendUp:K['g.bendUp'],bendDn:K['g.bendDn'],tune:K['g.tune'],master:K['g.master'],bpm:K['g.bpm'],mono:E['g.mono'],legato:E['g.legato'],gmode:E['g.glideMode']};
    this.AI={level:K['amp.level'],vel:K['amp.vel'],pan:K['amp.pan']};
    this.MI=[1,2,3,4,5,6,7,8].map(i=>K['m'+i]);
    const fxk=(id,ps,es)=>{const o={};ps.forEach(p=>o[p]=K[`fx.${id}.${p}`]);(es||[]).forEach(p=>o[p]=E[`fx.${id}.${p}`]);o.on=E[`fx.${id}.on`];return o;};
    this.XI={hyper:fxk('hyper',['rate','det','uni','dim','mix']),dist:fxk('dist',['drive','bias','tone','mix'],['mode']),flanger:fxk('flanger',['rate','depth','fb','mix']),
      phaser:fxk('phaser',['rate','depth','freq','fb','stages','mix']),chorus:fxk('chorus',['rate','depth','dly','fb','lpf','mix']),
      delay:fxk('delay',['tL','tR','fb','lc','hc','mix'],['mode']),comp:fxk('comp',['thr','ratio','att','rel','gain','depth','up','dn'],['mode']),
      reverb:fxk('reverb',['size','decay','pre','damp','lc','width','mix'],['type']),eq:fxk('eq',['f1','g1','q1','f2','g2','q2'],['t1','t2']),
      filter:fxk('filter',['cut','res','drive','mix'],['type']),shift:fxk('shift',['hz','fb','mix']),crush:fxk('crush',['rate','bits','mix']),util:fxk('util',['gain','width','pan'])};
    this.FXIDS=['hyper','dist','flanger','phaser','chorus','delay','comp','reverb','eq','filter','shift','crush','util'];
    this.order=d.order||[0,1,2,3,4,5,6,7,8,9,10,11,12];
    this.tables=[null,null,null];this.samples=[null,null,null];
    this.lfoT=[];for(let i=0;i<10;i++){const t=new Float32Array(1025);for(let j=0;j<1025;j++)t[j]=.5-.5*Math.cos(TAU*j/1024);this.lfoT.push(t);}
    this.V=[];for(let i=0;i<MAXV;i++)this.V.push(mkVoice(np));
    this.gmod=new Float64Array(np);this.gsrc=new Float64Array(27);this.gp=new Float64Array(10);
    this.bus=[0,1,2,3,4,5].map(()=>new Float32Array(CH));this.tL=new Float32Array(CH);this.tR=new Float32Array(CH);
    this.uInc=new Float64Array(16);this.uGl=new Float64Array(16);this.uGr=new Float64Array(16);this.pc=new Float64Array(4);
    this.mixL=new Float32Array(256);this.mixR=new Float32Array(256);
    this.mw=0;this.pb=0;this.mono=[];this.monoV=null;this.lastNote=null;this.lastV=null;this.idc=0;this.vizC=0;this.frame=0;
    this.setRoutes([]);this.fxInit();this.dcL=0;this.dcR=0;this.dxL=0;this.dxR=0;
    this.ok=true;this.port.postMessage({t:'ready'});
  }
  tv(i,n){const c=this.pcur[i],a=this.pmin[i],b=this.pmax[i];return c===1?a*Math.pow(b/a,n):c===2?a+(b-a)*n*n*n:a+(b-a)*n;}
  ev(v,i){let n=this.pn[i]+v.mod[i];n=n<0?0:n>1?1:n;return this.tv(i,n);}
  gv(i){let n=this.pn[i]+this.gmod[i];n=n<0?0:n>1?1:n;return this.tv(i,n);}
  bv(i){return this.tv(i,this.pn[i]);}
  setRoutes(r){
    const vr=[],gr=[];for(const x of r){if(x[2]==null||x[2]<0)continue;(this.isFx[x[2]]?gr:vr).push(x);}
    const pack=a=>({n:a.length,s:Int32Array.from(a,x=>x[0]),a:Int32Array.from(a,x=>x[1]),d:Int32Array.from(a,x=>x[2]),amt:Float64Array.from(a,x=>x[3]),bi:Uint8Array.from(a,x=>x[4]?1:0),e:Float64Array.from(a,x=>Math.pow(4,-(x[5]||0)))});
    this.vr=pack(vr);this.gr=pack(gr);
    this.touched=Int32Array.from(new Set(vr.map(x=>x[2])));this.gtouched=Int32Array.from(new Set(gr.map(x=>x[2])));
    this.lfoUsed=new Uint8Array(10);this.envUsed=new Uint8Array(4);
    for(const x of r)for(const s of [x[0],x[1]]){if(s>=4&&s<14)this.lfoUsed[s-4]=1;if(s>=0&&s<4)this.envUsed[s]=1;}
    if(this.V)for(const v of this.V)v.mod.fill(0);if(this.gmod)this.gmod.fill(0);
  }
  // ---------- notes ----------
  noteOn(n,vel){
    const G=this.GI,mono=this.pe[G.mono]>.5,leg=this.pe[G.legato]>.5,glide=this.bv(G.glide)>.0005;
    if(mono){
      this.mono.push(n);
      const v=this.monoV&&this.monoV.active&&!this.monoV.rel?this.monoV:null;
      if(v&&leg){v.target=n;v.note=n;if(!glide)v.pitch=n;this.lastNote=n;return;}
      if(v){this.trig(v,n,vel,true);return;}
      const nv=this.alloc();this.trig(nv,n,vel,false);this.monoV=nv;return;
    }
    const max=Math.round(this.bv(G.voices));let cnt=0;
    for(const v of this.V)if(v.active&&!v.rel&&!v.kill)cnt++;
    while(cnt>=max){let old=null;for(const v of this.V)if(v.active&&!v.rel&&!v.kill&&(!old||v.id<old.id))old=v;if(!old)break;old.kill=64;cnt--;}
    const v=this.alloc();this.trig(v,n,vel,false);
  }
  alloc(){for(const v of this.V)if(!v.active)return v;let f=null;
    for(const v of this.V){if(!f||(v.rel&&!f.rel)||(v.rel===f.rel&&v.id<f.id))f=v;}return f;}
  trig(v,n,vel,retrig){
    const G=this.GI,glide=this.bv(G.glide)>.0005,gm=this.pe[G.gmode]|0;
    let held=false;for(const x of this.V)if(x!==v&&x.active&&!x.rel){held=true;break;}
    const keep=retrig&&v.active;
    let from=n;if(glide&&this.lastNote!=null&&(gm===0||held||retrig))from=keep?v.pitch:this.lastNote;
    v.note=n;v.target=n;v.pitch=from;v.vel=vel;v.id=++this.idc;v.kill=0;v.rel=false;
    for(let i=0;i<4;i++){const e=v.e[i];e.v0=keep?e.v:0;e.st=0;e.t=0;}
    if(!keep){
      v.age=0;v.rnd=Math.random();
      for(let o=0;o<3;o++){const I=this.OI[o],st=v.os[o],ph0=this.bv(I.phase),rr=this.bv(I.rand);
        for(let i=0;i<16;i++){let p=ph0+rr*Math.random();st.ph[i]=p-Math.floor(p);}
        const sm=this.samples[o];const start=sm?this.bv(I.pos)*sm.d.length:0;for(let i=0;i<16;i++)st.sp[i]=start;st.ls=start;
        for(const g of st.g)g.on=false;st.gn=0;}
      for(const f of v.fl){f.s.fill(0);f.gL=-1;f.gR=-1;f.cL.fill(0);f.cR.fill(0);f.cw=0;}
      v.nz.fill(0);v.nzh=0;v.subPh=0;v.lph.fill(0);v.ls.fill(0);
      for(let i=0;i<10;i++){const t=this.lfoT[i];v.ls[i]=t[Math.min(1024,Math.floor(this.bv(this.LI[i].phase)*1024))];}
      for(const r of v.raw)r.fill(0);
    }
    v.active=true;this.lastNote=n;this.lastV=v;
  }
  release(v){if(v.rel)return;v.rel=true;for(const e of v.e){if(e.st===6)continue;e.rv=e.v;e.st=5;e.t=0;}}
  noteOff(n){
    const G=this.GI;
    if(this.pe[G.mono]>.5){
      const i=this.mono.lastIndexOf(n);if(i>=0)this.mono.splice(i,1);
      const v=this.monoV;if(!v||!v.active||v.rel)return;
      if(v.note===n){
        if(this.mono.length){const t=this.mono[this.mono.length-1];
          if(this.pe[G.legato]>.5){v.target=t;v.note=t;if(this.bv(G.glide)<=.0005)v.pitch=t;this.lastNote=t;}else this.trig(v,t,v.vel,true);}
        else this.release(v);
      }
      return;
    }
    for(const v of this.V)if(v.active&&!v.rel&&v.note===n)this.release(v);
  }
  // ---------- per-voice ----------
  envP(v,i){const p=v.ep[i],I=this.EI[i],sr=sampleRate;
    p[0]=this.ev(v,I[0])*sr;p[1]=Math.max(16,this.ev(v,I[1])*sr);p[2]=this.ev(v,I[2])*sr;p[3]=Math.max(16,this.ev(v,I[3])*sr);
    p[4]=this.ev(v,I[4]);p[5]=Math.max(32,this.ev(v,I[5])*sr);
    for(let j=0;j<3;j++){const c=this.ev(v,I[6+j]);const cc=Math.abs(c)<.02?0:c;p[6+j]=cc;p[9+j]=cc===0?0:Math.exp(cc*5)-1;}}
  voice(v,off,m){
    const sr=sampleRate,pn=this.pn,pe=this.pe,src=v.src,M=v.mod;
    for(let i=1;i<4;i++){if(!this.envUsed[i])continue;this.envP(v,i);const e=v.e[i];eAdv(e,v.ep[i],m);e.v=eVal(e,v.ep[i]);src[i]=e.v;}
    src[0]=v.e[0].v;
    const bpm=this.bv(this.GI.bpm);
    for(let i=0;i<10;i++){const I=this.LI[i];
      const hz=pe[I.sync]>.5?bpm/60/DIVB[Math.round(this.bv(I.div))]:(this.lfoUsed[i]?this.ev(v,I.rate):this.bv(I.rate));
      v.lph[i]+=hz*m/sr;if(v.lph[i]>1e6)v.lph[i]-=Math.floor(v.lph[i]);
      if(!this.lfoUsed[i])continue;
      const mode=pe[I.mode]|0;let ph;
      if(mode===0){ph=this.gp[i]+this.ev(v,I.phase);ph-=Math.floor(ph);}
      else if(mode===1){ph=v.lph[i]+this.ev(v,I.phase);ph-=Math.floor(ph);}
      else ph=Math.min(1,v.lph[i]+this.ev(v,I.phase));
      const t=this.lfoT[i],x=ph*1024,j=x|0;const val=j>=1024?t[1024]:t[j]+(t[j+1]-t[j])*(x-j);
      const sm=this.ev(v,I.smooth);const c=sm<.002?1:1-Math.exp(-m/(sr*sm*.08));v.ls[i]+=(val-v.ls[i])*c;src[4+i]=v.ls[i];
      const age=v.age/sr,dl=this.ev(v,I.dly),rs=this.ev(v,I.rise);v.sg[4+i]=age<dl?0:rs>.002?Math.min(1,(age-dl)/rs):1;
    }
    src[14]=v.vel;src[15]=v.note/127;src[16]=v.rnd;src[17]=this.mw;src[18]=(this.pb+1)*.5;
    for(let i=0;i<8;i++)src[19+i]=pn[this.MI[i]];
    const T=this.touched;for(let j=0;j<T.length;j++)M[T[j]]=0;
    const R=this.vr;
    for(let r=0;r<R.n;r++){const s=R.s[r];let x=src[s];if(R.e[r]!==1)x=Math.pow(x>0?x:0,R.e[r]);if(R.bi[r])x=2*x-1;x*=v.sg[s];const a=R.a[r];if(a>=0)x*=src[a];M[R.d[r]]+=x*R.amt[r];}
    // pitch
    const G=this.GI,gl=this.bv(G.glide);
    if(gl>.0005)v.pitch+=(v.target-v.pitch)*(1-Math.exp(-m/(sr*gl*.3)));else v.pitch=v.target;
    const pb=this.pb,P=v.pitch+(pb>=0?pb*this.bv(G.bendUp):pb*this.bv(G.bendDn)),tune=this.bv(G.tune);
    const B=this.bus;for(let j=0;j<6;j++)B[j].fill(0,0,m);
    const ser=pe[this.serial]>.5;
    // sub & noise
    const SI=this.SI,NI=this.NI;
    if(pe[SI.on]>.5){this.sub(v,P,tune,m);this.toBus(pe[SI.route]|0,m,ser);}else v.raw[3].fill(0,0,m);
    if(pe[NI.on]>.5){this.noise(v,m);this.toBus(pe[NI.route]|0,m,ser);}else v.raw[4].fill(0,0,m);
    for(let o=0;o<3;o++){const I=this.OI[o];if(pe[I.eon]<.5){v.raw[o].fill(0,0,m);continue;}
      const ty=pe[I.etype]|0,lvl=this.ev(v,I.level),pan=this.ev(v,I.pan);
      const pitch=P+12*this.ev(v,I.oct)+this.ev(v,I.semi)+this.ev(v,I.fine)/100;const f=tune*Math.pow(2,(pitch-69)/12);
      if(ty===0)this.wt(v,o,I,f,m);else if(ty===1)this.smp(v,o,I,f,m);else this.grn(v,o,I,f,m);
      const a=(pan+1)*Math.PI/4,gL=lvl*Math.cos(a)*1.4142,gR=lvl*Math.sin(a)*1.4142,tL=this.tL,tR=this.tR;
      for(let s=0;s<m;s++){tL[s]*=gL;tR[s]*=gR;}
      this.toBus(pe[I.eroute]|0,m,ser);}
    const f1L=B[0],f1R=B[1],f2L=B[2],f2R=B[3],dL=B[4],dR=B[5],oL=v.oL,oR=v.oR;
    if(ser){this.filt(v,0,f1L,f1R,m,P);for(let s=0;s<m;s++){f2L[s]+=f1L[s];f2R[s]+=f1R[s];}this.filt(v,1,f2L,f2R,m,P);
      for(let s=0;s<m;s++){oL[s]=f2L[s]+dL[s];oR[s]=f2R[s]+dR[s];}}
    else{this.filt(v,0,f1L,f1R,m,P);this.filt(v,1,f2L,f2R,m,P);for(let s=0;s<m;s++){oL[s]=f1L[s]+f2L[s]+dL[s];oR[s]=f1R[s]+f2R[s]+dR[s];}}
    // amp
    this.envP(v,0);const e=v.e[0],ep=v.ep[0],AI=this.AI;
    const lvl=this.ev(v,AI.level)*.42,vs=this.ev(v,AI.vel),vg=1-vs*(1-v.vel),ap=this.ev(v,AI.pan),aa=(ap+1)*Math.PI/4,pl=Math.cos(aa)*1.4142*lvl*vg,pr=Math.sin(aa)*1.4142*lvl*vg;
    const mL=this.mixL,mR=this.mixR;
    for(let s=0;s<m;s++){eAdv(e,ep,1);let g=eVal(e,ep);e.v=g;
      if(v.kill){g*=v.kill/64;v.kill--;if(v.kill<=0){v.active=false;break;}}
      mL[off+s]+=oL[s]*g*pl;mR[off+s]+=oR[s]*g*pr;}
    if(e.st===6)v.active=false;
    v.age+=m;
  }
  toBus(r,m,ser){const B=this.bus,tL=this.tL,tR=this.tR;
    if(r===0||(r===2&&ser)){const a=B[0],b=B[1];for(let s=0;s<m;s++){a[s]+=tL[s];b[s]+=tR[s];}}
    else if(r===1){const a=B[2],b=B[3];for(let s=0;s<m;s++){a[s]+=tL[s];b[s]+=tR[s];}}
    else if(r===2){const a=B[0],b=B[1],c=B[2],d=B[3];for(let s=0;s<m;s++){const l=tL[s]*.7071,rr=tR[s]*.7071;a[s]+=l;b[s]+=rr;c[s]+=l;d[s]+=rr;}}
    else{const a=B[4],b=B[5];for(let s=0;s<m;s++){a[s]+=tL[s];b[s]+=tR[s];}}}
  unison(v,I,f,U,stack){
    const det=this.ev(v,I.det),bl=this.ev(v,I.blend),wd=this.ev(v,I.width),sr=sampleRate;
    const inc=this.uInc,gl=this.uGl,gr=this.uGr,cents=det*det*100,stk=STACKS[stack]||STACKS[0];let mx=0,norm=0;
    for(let i=0;i<U;i++){const d=U===1?0:i/(U-1)*2-1;const x=f*Math.pow(2,(d*cents/100+stk[i%stk.length])/12)/sr;inc[i]=x;if(x>mx)mx=x;
      const centre=U===1||(U%2===1&&i===(U-1)/2)||(U%2===0&&(i===U/2-1||i===U/2));const g=U===1?1:(centre?1-bl*.5:bl);
      const pp=d*wd;gl[i]=g*(pp>0?1-pp:1);gr[i]=g*(pp<0?1+pp:1);norm+=g*g;}
    this.uNorm=1/Math.sqrt(norm||1);return mx;}
  wt(v,o,I,f,m){
    const tb=this.tables[o],raw=v.raw[o],tL=this.tL,tR=this.tR;
    if(!tb){raw.fill(0,0,m);tL.fill(0,0,m);tR.fill(0,0,m);return;}
    const pe=this.pe,ph=v.os[o].ph;
    const posN=this.ev(v,I.pos),w1=this.ev(v,I.w1),w2=this.ev(v,I.w2),m1=pe[I.ewm1]|0,m2=pe[I.ewm2]|0;
    const U=Math.max(1,Math.min(16,Math.round(this.bv(I.uni))));
    const mx=this.unison(v,I,f,U,pe[I.estack]|0),norm=this.uNorm,inc=this.uInc,gl=this.uGl,gr=this.uGr;
    const Fr=tb.F,pos=posN*(Fr-1),f1=Math.min(Fr-1,pos|0),fr=pos-f1,f2=f1+1<Fr?f1+1:Fr-1;
    let mult=1;
    if(m1===1||m1===2)mult*=1+w1*15;else if(m1>=13&&m1<=17)mult*=1+w1*w1*3;
    if(m2===1||m2===2)mult*=1+w2*15;else if(m2>=13&&m2<=17)mult*=1+w2*w2*3;
    const maxH=.5/Math.max(1e-9,mx*mult);let lv=maxH>=1024?0:Math.ceil(Math.log2(1024/maxH));if(lv>NL-1)lv=NL-1;if(lv<0)lv=0;
    const tab=tb.m[lv],o1=f1*N,o2=f2*N;
    const s1=WSRC[m1]>=0?v.raw[WSRC[m1]]:null,s2=WSRC[m2]>=0?v.raw[WSRC[m2]]:null;
    const p1=WPH[m1],p2=WPH[m2],q1=WOUT[m1],q2=WOUT[m2],iu=1/U;
    for(let s=0;s<m;s++){let l=0,r=0,mo=0;const a1=s1?s1[s]:0,a2=s2?s2[s]:0;
      for(let i=0;i<U;i++){let p=ph[i]+inc[i];if(p>=1)p-=Math.floor(p);ph[i]=p;let q=p,g=1;
        if(p1){q=wph(m1,w1,q,a1);if(q<0){g=0;q=0;}}
        if(p2&&g){q=wph(m2,w2,q,a2);if(q<0){g=0;q=0;}}
        let val=0;
        if(g){const x=q*N;let j=x|0;if(j>=N)j=N-1;const fx=x-j,j2=(j+1)&2047;
          const A=tab[o1+j]+(tab[o1+j2]-tab[o1+j])*fx,Bv=tab[o2+j]+(tab[o2+j2]-tab[o2+j])*fx;val=A+(Bv-A)*fr;
          if(q1)val=wout(m1,w1,val,p,a1);if(q2)val=wout(m2,w2,val,p,a2);}
        l+=val*gl[i];r+=val*gr[i];mo+=val;}
      tL[s]=l*norm;tR[s]=r*norm;raw[s]=mo*iu;}
  }
  smp(v,o,I,f,m){
    const sm=this.samples[o],raw=v.raw[o],tL=this.tL,tR=this.tR;
    if(!sm){raw.fill(0,0,m);tL.fill(0,0,m);tR.fill(0,0,m);return;}
    const d=sm.d,len=d.length,st=v.os[o],sp=st.sp,loop=this.pe[I.eloop]>.5,ls=Math.min(st.ls,len-8),span=len-ls;
    const U=Math.max(1,Math.min(16,Math.round(this.bv(I.uni))));
    const ratio=261.6256>0?sm.sr/sampleRate/261.6256:0;
    this.unison(v,I,f*ratio*sampleRate,U,this.pe[I.estack]|0);const inc=this.uInc,gl=this.uGl,gr=this.uGr,norm=this.uNorm,iu=1/U;
    for(let s=0;s<m;s++){let l=0,r=0,mo=0;
      for(let i=0;i<U;i++){let p=sp[i],val=0;
        if(p<len){const j=p|0,fx=p-j;const a=d[j],b=j+1<len?d[j+1]:(loop?d[ls|0]:0);val=a+(b-a)*fx;}
        p+=inc[i];if(p>=len&&loop&&span>8)p=ls+((p-ls)%span);sp[i]=p;
        l+=val*gl[i];r+=val*gr[i];mo+=val;}
      tL[s]=l*norm;tR[s]=r*norm;raw[s]=mo*iu;}
  }
  grn(v,o,I,f,m){
    const sm=this.samples[o],raw=v.raw[o],tL=this.tL,tR=this.tR;
    if(!sm){raw.fill(0,0,m);tL.fill(0,0,m);tR.fill(0,0,m);return;}
    const d=sm.d,len=d.length,st=v.os[o],G=st.g,sr=sampleRate;
    const posN=this.ev(v,I.pos),sz=this.ev(v,I.w1),size=.01+sz*sz*.6,dens=2*Math.pow(40,this.ev(v,I.w2)),spray=this.ev(v,I.det),wd=this.ev(v,I.width);
    const ratio=f/261.6256*sm.sr/sr,glen=Math.max(32,size*sr),amp=1/Math.sqrt(Math.max(1,dens*size));
    for(let s=0;s<m;s++){
      st.gn-=1;
      if(st.gn<=0){st.gn+=sr/dens;let k=-1;for(let j=0;j<G.length;j++)if(!G[j].on){k=j;break;}
        if(k>=0){const g=G[k];g.on=true;g.age=0;g.len=glen;let p=posN+(Math.random()-.5)*spray*.6;p-=Math.floor(p);g.p=p*len;
          g.inc=ratio*Math.pow(2,(Math.random()-.5)*spray*.04);const pp=(Math.random()*2-1)*wd;g.gl=pp>0?1-pp:1;g.gr=pp<0?1+pp:1;}}
      let l=0,r=0;
      for(let j=0;j<G.length;j++){const g=G[j];if(!g.on)continue;const w=HANN[(g.age/g.len*1024)|0];let p=g.p+g.age*g.inc;if(p>=len)p%=len;
        const val=d[p|0]*w;l+=val*g.gl;r+=val*g.gr;g.age++;if(g.age>=g.len)g.on=false;}
      tL[s]=l*amp;tR[s]=r*amp;raw[s]=(l+r)*.5*amp;}
  }
  sub(v,P,tune,m){
    const SI=this.SI,lvl=this.ev(v,SI.level),pan=this.ev(v,SI.pan),sh=this.pe[SI.shape]|0;
    const f=tune*Math.pow(2,(P+12*Math.round(this.ev(v,SI.oct))-69)/12),dt=f/sampleRate,a=(pan+1)*Math.PI/4,gL=lvl*Math.cos(a)*1.4142,gR=lvl*Math.sin(a)*1.4142;
    let p=v.subPh;const raw=v.raw[3],tL=this.tL,tR=this.tR;
    for(let s=0;s<m;s++){p+=dt;if(p>=1)p-=1;let x;
      switch(sh){case 0:x=Math.sin(TAU*p);break;case 1:x=p<.5?4*p-1:3-4*p;break;case 2:x=2*p-1-blep(p,dt);break;
        case 3:{let q=p+.5;if(q>=1)q-=1;x=(p<.5?1:-1)+blep(p,dt)-blep(q,dt);break;}
        case 4:{let q=p+.75;if(q>=1)q-=1;x=(p<.25?1:-1)+blep(p,dt)-blep(q,dt);break;}
        default:x=ft(2.5*Math.sin(TAU*p));}
      raw[s]=x;tL[s]=x*gL;tR[s]=x*gR;}
    v.subPh=p;
  }
  noise(v,m){
    const NI=this.NI,ty=this.pe[NI.type]|0,pt=this.ev(v,NI.pitch),lvl=this.ev(v,NI.level),pan=this.ev(v,NI.pan),z=v.nz,raw=v.raw[4],sr=sampleRate;
    const a=(pan+1)*Math.PI/4,gL=lvl*Math.cos(a)*1.4142,gR=lvl*Math.sin(a)*1.4142,tL=this.tL,tR=this.tR;
    const c=pt>.985?1:1-Math.exp(-TAU*(60*Math.pow(300,pt))/sr);
    for(let s=0;s<m;s++){let x;
      switch(ty){
        case 0:x=Math.random()*2-1;break;
        case 1:{const w=Math.random()*2-1;z[0]=.99765*z[0]+w*.099046;z[1]=.963*z[1]+w*.2965164;z[2]=.57*z[2]+w*1.0526913;x=(z[0]+z[1]+z[2]+w*.1848)*.22;break;}
        case 2:{z[3]=(z[3]+.02*(Math.random()*2-1))/1.02;x=z[3]*3.5;break;}
        case 3:{if(Math.random()<.0002+pt*pt*.02)z[4]=(Math.random()<.5?-1:1)*(.5+Math.random()*.5);else z[4]*=.55;x=z[4];break;}
        default:{v.nzh-=1;if(v.nzh<=0){z[5]=Math.random()*2-1;v.nzh+=sr/(40*Math.pow(sr/80,pt));}x=z[5];}}
      if(ty<3){z[6]+=(x-z[6])*c;x=z[6];}
      raw[s]=x;tL[s]=x*gL;tR[s]=x*gR;}
  }
  filt(v,fi,L,R,m,P){
    const I=this.FI[fi];if(this.pe[I.on]<.5)return;const ty=this.pe[I.type]|0,sr=sampleRate;
    let fc=this.ev(v,I.cut)*Math.pow(2,(P-60)/12*this.ev(v,I.key));fc=fc<15?15:fc>sr*.45?sr*.45:fc;
    const res=this.ev(v,I.res),dr=this.ev(v,I.drive),vr=this.ev(v,I.vr),mix=this.ev(v,I.mix),st=v.fl[fi];
    if(ty<=10)this.svf(st,L,R,m,fc,res,dr,vr,mix,ty);
    else if(ty<=12){const g=Math.tan(Math.PI*fc/sr),G=g/(1+g),four=ty===11,k=res*(four?4.1:2.1),drv=1+dr*6,comp=1+res*(four?1.3:.6);
      ladCh(st.s,8,L,m,G,k,drv,vr,mix,four?4:2,comp);ladCh(st.s,14,R,m,G,k,drv,vr,mix,four?4:2,comp);}
    else if(ty<=14)this.comb(st,L,R,m,fc,res,dr,vr,mix,ty===13?1:-1);
    else if(ty===15){for(let j=0;j<4;j++){const f=Math.min(sr*.45,fc*Math.pow(2,(j-1.5)*(.2+vr*1.4)));const t=Math.tan(Math.PI*f/sr);this.pc[j]=(t-1)/(t+1);}
      phCh(st.s,24,L,m,this.pc,res*.92,mix);phCh(st.s,29,R,m,this.pc,res*.92,mix);}
    else{let n=this.pn[I.cut]+v.mod[I.cut];n=n<0?0:n>1?1:n;this.formant(st,L,R,m,n,res,dr,vr,mix);}
  }
  svf(st,L,R,m,fc,res,dr,vr,mix,ty){
    const sr=sampleRate,k=2-1.96*res,s=st.s,sp=(ty<=6||ty===8)?vr:0;
    const fL=Math.min(fc*Math.pow(2,-sp),sr*.45),fR=Math.min(fc*Math.pow(2,sp),sr*.45);
    const gL1=Math.tan(Math.PI*fL/sr),gR1=Math.tan(Math.PI*fR/sr),gL0=st.gL<0?gL1:st.gL,gR0=st.gR<0?gR1:st.gR;st.gL=gL1;st.gR=gR1;
    const A2=(ty===7||ty===9||ty===10)?Math.pow(10,(vr*2-1)*24/20):1,drv=dr>.002?1+dr*8:0,dn=drv?1/(1+dr*2):1;
    svfCh(s,0,L,m,gL0,(gL1-gL0)/m,k,ty,A2,drv,dn,mix);svfCh(s,4,R,m,gR0,(gR1-gR0)/m,k,ty,A2,drv,dn,mix);
  }
  comb(st,L,R,m,fc,res,dr,vr,mix,sign){
    const sr=sampleRate,D=Math.min(4090,Math.max(2,sr/fc)),fb=sign*res*.97,dmp=vr*.9,s=st.s,bl=st.cL,br=st.cR,drv=dr>.002?1+dr*6:0,nm=1-Math.abs(fb)*.5;
    let w=st.cw,zl=s[20],zr=s[21];
    for(let i=0;i<m;i++){const rp=w-D;let j=Math.floor(rp);const fx=rp-j;j&=4095;const j2=(j+1)&4095;
      const dl=bl[j]+(bl[j2]-bl[j])*fx,dR=br[j]+(br[j2]-br[j])*fx;zl+=(dl-zl)*(1-dmp);zr+=(dR-zr)*(1-dmp);
      const xl=drv?ft(L[i]*drv):L[i],xr=drv?ft(R[i]*drv):R[i],yl=xl+fb*zl,yr=xr+fb*zr;bl[w]=ft(yl);br[w]=ft(yr);w=(w+1)&4095;
      L[i]+=(yl*nm-L[i])*mix;R[i]+=(yr*nm-R[i])*mix;}
    st.cw=w;s[20]=zl;s[21]=zr;
  }
  formant(st,L,R,m,n,res,dr,vr,mix){
    const sr=sampleRate,s=st.s,pos=n*4,i0=Math.min(3,Math.floor(pos)),u=pos-i0,sh=Math.pow(2,(vr-.5)*1.5),k=1/(2.5+res*22);
    const gs=[1,.7,.45];const G=[0,0,0];
    for(let j=0;j<3;j++){const f=Math.min(sr*.45,(VOW[i0][j]*(1-u)+VOW[i0+1][j]*u)*sh);G[j]=Math.tan(Math.PI*f/sr);}
    const drv=dr>.002?1+dr*6:0;
    for(let c=0;c<2;c++){const X=c?R:L,o=c?40:34;
      for(let i=0;i<m;i++){const dry=X[i],x=drv?ft(dry*drv):dry;let y=0;
        for(let j=0;j<3;j++){const g=G[j],a1=1/(1+g*(g+k)),a2=g*a1,a3=g*a2,c1=s[o+2*j],c2=s[o+2*j+1];
          const v3=x-c2,v1=a1*c1+a2*v3,v2=c2+a2*c1+a3*v3;s[o+2*j]=2*v1-c1;s[o+2*j+1]=2*v2-c2;y+=k*v1*gs[j];}
        X[i]=dry+(y*2.2-dry)*mix;}}
  }
  // ---------- FX ----------
  fxInit(){const sr=sampleRate,dl=Math.ceil(sr*4)+8;
    this.FX={hy:{bL:new Float32Array(8192),bR:new Float32Array(8192),w:0,tp:new Float64Array(8)},
      di:{z:[0,0],x1:[0,0],y1:[0,0],h:[0,0],c:[0,0]},
      fl:{bL:new Float32Array(4096),bR:new Float32Array(4096),w:0,ph:0},
      ph:{z:new Float64Array(26),ph:0,c:new Float64Array(2)},
      ch:{bL:new Float32Array(8192),bR:new Float32Array(8192),w:0,ph:0,zl:0,zr:0},
      dl:{bL:new Float32Array(dl),bR:new Float32Array(dl),n:dl,w:0,tL:-1,tR:-1,s:new Float64Array(8)},
      cp:{env:0,e:new Float64Array(3),g:new Float64Array(3),s:new Float64Array(24)},
      rv:{lines:[0,1,2,3,4,5,6,7].map(()=>new Float32Array(32768)),w:0,dz:new Float64Array(8),pre:new Float32Array(Math.ceil(sr*.3)+4),pw:0,ap:[0,1,2,3].map(()=>new Float32Array(4096)),aw:0,hp:new Float64Array(4),len:new Int32Array(8),g:new Float64Array(8)},
      eq:{c:new Float64Array(10),s:new Float64Array(8),key:''},
      ft:{s:new Float64Array(8),g:-1},
      sh:{s:new Float64Array(80),ph:0,last:[0,0]},
      cr:{c:[0,0],h:[0,0]}};
  }
  fxClear(){this.fxInit();}
  rd(b,M,pos){const j0=Math.floor(pos),fx=pos-j0,j=j0&M,j2=(j+1)&M;return b[j]+(b[j2]-b[j])*fx;}
  fxRun(L,R,n){
    for(const idx of this.order){const id=this.FXIDS[idx],X=this.XI[id];if(!X||this.pe[X.on]<.5)continue;
      switch(id){case 'hyper':this.fHyper(L,R,n,X);break;case 'dist':this.fDist(L,R,n,X);break;case 'flanger':this.fFlanger(L,R,n,X);break;
        case 'phaser':this.fPhaser(L,R,n,X);break;case 'chorus':this.fChorus(L,R,n,X);break;case 'delay':this.fDelay(L,R,n,X);break;
        case 'comp':this.fComp(L,R,n,X);break;case 'reverb':this.fReverb(L,R,n,X);break;case 'eq':this.fEq(L,R,n,X);break;
        case 'filter':this.fFilter(L,R,n,X);break;case 'shift':this.fShift(L,R,n,X);break;case 'crush':this.fCrush(L,R,n,X);break;case 'util':this.fUtil(L,R,n,X);break;}}
  }
  fHyper(L,R,n,X){const s=this.FX.hy,sr=sampleRate,rate=this.gv(X.rate),det=this.gv(X.det),U=Math.max(2,Math.round(this.gv(X.uni))),dim=this.gv(X.dim),mix=this.gv(X.mix);
    const bL=s.bL,bR=s.bR,M=8191,ms=sr/1000,tp=s.tp,nrm=1/Math.sqrt(U*.5),dA=Math.round(13*ms),dB=Math.round(17.3*ms);let w=s.w;
    for(let i=0;i<n;i++){const xl=L[i],xr=R[i];bL[w]=xl;bR[w]=xr;let wl=0,wr=0;
      for(let u=0;u<U;u++){tp[u]+=rate*(1+u*.17)/sr;if(tp[u]>=1)tp[u]-=1;const d=(5+u*1.9+det*4*(1+fsin(tp[u]+u/U)))*ms;
        if(u&1)wr+=this.rd(bR,M,w-d);else wl+=this.rd(bL,M,w-d);}
      if(dim>0){wl+=dim*.7*bR[(w-dA)&M];wr+=dim*.7*bL[(w-dB)&M];}
      w=(w+1)&M;L[i]=xl*(1-mix)+wl*nrm*mix;R[i]=xr*(1-mix)+wr*nrm*mix;}
    s.w=w;}
  fDist(L,R,n,X){const s=this.FX.di,mode=this.pe[X.mode]|0,drv=this.gv(X.drive),bias=this.gv(X.bias),tone=this.gv(X.tone),mix=this.gv(X.mix);
    const g=Math.pow(10,drv*36/20),tc=1-Math.exp(-TAU*tone/sampleRate),H=1+drv*drv*40,out=(mode===2||mode===4||mode===5)?.8:1;
    for(let c=0;c<2;c++){const B=c?R:L;let z=s.z[c],x1=s.x1[c],y1=s.y1[c],h=s.h[c],cnt=s.c[c];
      for(let i=0;i<n;i++){const dry=B[i];const x=mode===7?dry:dry*g+bias;let y;
        switch(mode){case 0:y=ft(x);break;case 1:y=x/(1+Math.abs(x));break;case 2:y=x>1?1:x<-1?-1:x;break;case 3:y=x>0?ft(x):ft(x*.3)*.6;break;
          case 4:{let t=(x+1)*.25;t-=Math.floor(t);y=t<.5?4*t-1:3-4*t;break;}case 5:y=Math.sin(x*Math.PI*.5);break;case 6:y=ft(x*Math.abs(x));break;
          case 7:{cnt+=1;if(cnt>=H){cnt-=H;h=x;}y=h;break;}case 8:y=ft(x+.35*x*x);break;default:y=Math.abs(ft(x))*1.6-.5;}
        const dc=y-x1+.995*y1;x1=y;y1=dc;z+=(dc-z)*tc;B[i]=dry+(z*out-dry)*mix;}
      s.z[c]=z;s.x1[c]=x1;s.y1[c]=y1;s.h[c]=h;s.c[c]=cnt;}}
  fFlanger(L,R,n,X){const s=this.FX.fl,sr=sampleRate,rate=this.gv(X.rate),dep=this.gv(X.depth),fb=this.gv(X.fb)*.95,mix=this.gv(X.mix),M=4095,ms=sr/1000;let w=s.w,ph=s.ph;
    for(let i=0;i<n;i++){ph+=rate/sr;if(ph>=1)ph-=1;
      const dl=(.3+dep*4*(.5+.5*fsin(ph)))*ms,dr=(.3+dep*4*(.5+.5*fsin(ph+.25)))*ms;
      const yl=this.rd(s.bL,M,w-dl),yr=this.rd(s.bR,M,w-dr);s.bL[w]=ft(L[i]+fb*yl);s.bR[w]=ft(R[i]+fb*yr);w=(w+1)&M;
      L[i]=L[i]*(1-mix*.5)+yl*mix;R[i]=R[i]*(1-mix*.5)+yr*mix;}
    s.w=w;s.ph=ph;}
  fPhaser(L,R,n,X){const s=this.FX.ph,sr=sampleRate,rate=this.gv(X.rate),dep=this.gv(X.depth),fq=this.gv(X.freq),fb=this.gv(X.fb)*.9,S=Math.max(2,Math.min(12,Math.round(this.gv(X.stages)))),mix=this.gv(X.mix);
    for(let o=0;o<n;o+=32){const m=Math.min(32,n-o);s.ph+=rate*m/sr;s.ph-=Math.floor(s.ph);
      for(let c=0;c<2;c++){const f=Math.min(sr*.45,fq*Math.pow(2,dep*2*Math.sin(TAU*(s.ph+c*.25))));const t=Math.tan(Math.PI*f/sr),a=(t-1)/(t+1);
        const B=c?R:L,z=s.z,zo=c*13;
        for(let i=o;i<o+m;i++){const dry=B[i];let x=dry+fb*z[zo+12];
          for(let k=0;k<S;k++){const y=a*x+z[zo+k];z[zo+k]=x-a*y;x=y;}
          z[zo+12]=ft(x);B[i]=dry*(1-mix)+(dry+x)*.5*mix;}}}}
  fChorus(L,R,n,X){const s=this.FX.ch,sr=sampleRate,rate=this.gv(X.rate),dep=this.gv(X.depth),dly=this.gv(X.dly),fb=this.gv(X.fb),lp=this.gv(X.lpf),mix=this.gv(X.mix);
    const M=8191,ms=sr/1000,tc=1-Math.exp(-TAU*lp/sr);let w=s.w,ph=s.ph,zl=s.zl,zr=s.zr;
    for(let i=0;i<n;i++){ph+=rate/sr;if(ph>=1)ph-=1;
      const a=(dly+dep*5*(.5+.5*fsin(ph)))*ms,b=(dly+dep*5*(.5+.5*fsin(ph+.334)))*ms,c2=(dly*1.3+dep*5*(.5+.5*fsin(ph+.668)))*ms;
      const yl=(this.rd(s.bL,M,w-a)+this.rd(s.bR,M,w-c2))*.5,yr=(this.rd(s.bR,M,w-b)+this.rd(s.bL,M,w-c2))*.5;
      s.bL[w]=L[i]+fb*yl;s.bR[w]=R[i]+fb*yr;w=(w+1)&M;zl+=(yl-zl)*tc;zr+=(yr-zr)*tc;
      L[i]=L[i]*(1-mix*.5)+zl*mix;R[i]=R[i]*(1-mix*.5)+zr*mix;}
    s.w=w;s.ph=ph;s.zl=zl;s.zr=zr;}
  fDelay(L,R,n,X){const s=this.FX.dl,sr=sampleRate,bpm=this.bv(this.GI.bpm),ping=(this.pe[X.mode]|0)===1;
    const TL=Math.min(3.9,60/bpm*DIVB[Math.round(this.gv(X.tL))])*sr,TR=Math.min(3.9,60/bpm*DIVB[Math.round(this.gv(X.tR))])*sr;
    if(s.tL<0){s.tL=TL;s.tR=TR;}
    const fb=this.gv(X.fb),lc=1-Math.exp(-TAU*this.gv(X.lc)/sr),hc=1-Math.exp(-TAU*this.gv(X.hc)/sr),mix=this.gv(X.mix),bl=s.bL,br=s.bR,Nn=s.n,st=s.s;let w=s.w,tl=s.tL,tr=s.tR;
    for(let i=0;i<n;i++){tl+=(TL-tl)*.0006;tr+=(TR-tr)*.0006;
      let pl=w-tl;if(pl<0)pl+=Nn;let pr=w-tr;if(pr<0)pr+=Nn;
      const jl=pl|0,fl=pl-jl,jr=pr|0,fr=pr-jr;let dl=bl[jl]+(bl[(jl+1)%Nn]-bl[jl])*fl,dr=br[jr]+(br[(jr+1)%Nn]-br[jr])*fr;
      st[0]+=(dl-st[0])*hc;st[1]+=(st[0]-st[1])*lc;dl=st[0]-st[1];st[2]+=(dr-st[2])*hc;st[3]+=(st[2]-st[3])*lc;dr=st[2]-st[3];
      if(ping){bl[w]=(L[i]+R[i])*.5+fb*dr;br[w]=fb*dl;}else{bl[w]=L[i]+fb*dl;br[w]=R[i]+fb*dr;}
      w++;if(w>=Nn)w=0;L[i]+=dl*mix;R[i]+=dr*mix;}
    s.w=w;s.tL=tl;s.tR=tr;}
  fComp(L,R,n,X){const s=this.FX.cp,sr=sampleRate,mode=this.pe[X.mode]|0,att=this.gv(X.att)/1000,rel=this.gv(X.rel)/1000,mk=this.gv(X.gain);
    const ca=1-Math.exp(-1/(att*sr)),cr=1-Math.exp(-1/(rel*sr));
    if(mode===0){const thr=this.gv(X.thr),ratio=this.gv(X.ratio),sl=1-1/ratio;let env=s.env;
      for(let i=0;i<n;i++){const x=Math.max(Math.abs(L[i]),Math.abs(R[i]));env+=(x-env)*(x>env?ca:cr);const lv=20*Math.log10(env+1e-9),ov=lv-thr;
        const g=Math.pow(10,((ov>0?-ov*sl:0)+mk)/20);L[i]*=g;R[i]*=g;}
      s.env=env;return;}
    const dep=this.gv(X.depth),up=this.gv(X.up),dn=this.gv(X.dn),T=-26,st=s.s,e=s.e,gg=s.g,mg=Math.pow(10,mk/20);
    const k=1.414,gl=Math.tan(Math.PI*120/sr),gh=Math.tan(Math.PI*2500/sr);
    const al1=1/(1+gl*(gl+k)),al2=gl*al1,al3=gl*al2,ah1=1/(1+gh*(gh+k)),ah2=gh*ah1,ah3=gh*ah2;
    const sv=(o,x,a1,a2,a3,hp)=>{const c1=st[o],c2=st[o+1],v3=x-c2,v1=a1*c1+a2*v3,v2=c2+a2*c1+a3*v3;st[o]=2*v1-c1;st[o+1]=2*v2-c2;return hp?x-k*v1-v2:v2;};
    for(let i=0;i<n;i++){const xl=L[i],xr=R[i];
      const lL=sv(2,sv(0,xl,al1,al2,al3,0),al1,al2,al3,0),lR=sv(6,sv(4,xr,al1,al2,al3,0),al1,al2,al3,0);
      const hL=sv(10,sv(8,xl,ah1,ah2,ah3,1),ah1,ah2,ah3,1),hR=sv(14,sv(12,xr,ah1,ah2,ah3,1),ah1,ah2,ah3,1);
      const mL=xl-lL-hL,mR=xr-lR-hR;
      if((i&7)===0){
        for(let b=0;b<3;b++){const a=b===0?lL:b===1?mL:hL,c=b===0?lR:b===1?mR:hR,p=(a*a+c*c)*.5;
          e[b]+=(p-e[b])*(p>e[b]?ca*8:cr*8);if(e[b]<0)e[b]=0;
          const db=10*Math.log10(e[b]+1e-12);let gd=0;if(db>T)gd=-(db-T)*dn*.85;else if(db>-75)gd=Math.min(30,(T-db)*up*.7);
          const tg=Math.pow(10,(gd*dep)/20);gg[b]+=(tg-gg[b])*.016;}}
      L[i]=(lL*gg[0]+mL*gg[1]+hL*gg[2])*mg;R[i]=(lR*gg[0]+mR*gg[1]+hR*gg[2])*mg;}}
  fReverb(L,R,n,X){const s=this.FX.rv,sr=sampleRate,ty=this.pe[X.type]|0,size=this.gv(X.size),dec=this.gv(X.decay),pre=Math.round(this.gv(X.pre)/1000*sr),damp=this.gv(X.damp),
    lc=1-Math.exp(-TAU*this.gv(X.lc)/sr),wd=this.gv(X.width),mix=this.gv(X.mix);
    const scale=(.35+size*1.65)*(ty?1.4:1),rt=.25+dec*dec*(ty?16:9),M=32767,len=s.len,g=s.g;
    for(let j=0;j<8;j++){len[j]=Math.min(32000,Math.round(REVB[j]*scale*sr/1000));g[j]=Math.pow(10,-3*len[j]/(rt*sr));}
    const apl=APL[ty].map(x=>Math.min(4000,Math.round(x*sr/44100*(.6+size*.6)))),dc=1-damp*.88,lines=s.lines,dz=s.dz,P=s.pre,PL=P.length,hp=s.hp;let w=s.w,pw=s.pw,aw=s.aw;
    for(let i=0;i<n;i++){const xl=L[i],xr=R[i];P[pw]=(xl+xr)*.5;let rp=pw-Math.min(pre,PL-2);if(rp<0)rp+=PL;let d=P[rp];pw++;if(pw>=PL)pw=0;
      for(let a=0;a<4;a++){const buf=s.ap[a],bv=buf[(aw-apl[a])&4095],y=-.62*d+bv;buf[aw]=d+.62*y;d=y;}aw=(aw+1)&4095;
      let sum=0;const o=this.rvo||(this.rvo=new Float64Array(8));
      for(let j=0;j<8;j++){const x=lines[j][(w-len[j])&M];dz[j]+=(x-dz[j])*dc;o[j]=dz[j];sum+=dz[j];}
      const f=sum*.25;
      for(let j=0;j<8;j++)lines[j][w]=(o[j]-f)*g[j]+d*((j&1)?-.35:.35);
      w=(w+1)&M;
      let ol=(o[0]+o[2]+o[4]+o[6])*.3,or=(o[1]+o[3]+o[5]+o[7])*.3;const mid=(ol+or)*.5,sd=(ol-or)*.5*wd;ol=mid+sd;or=mid-sd;
      hp[0]+=(ol-hp[0])*lc;hp[1]+=(or-hp[1])*lc;ol-=hp[0];or-=hp[1];
      L[i]=xl*(1-mix*.6)+ol*mix;R[i]=xr*(1-mix*.6)+or*mix;}
    s.w=w;s.pw=pw;s.aw=aw;}
  fEq(L,R,n,X){const s=this.FX.eq,sr=sampleRate,t1=this.pe[X.t1]|0,t2=this.pe[X.t2]|0,f1=this.gv(X.f1),g1=this.gv(X.g1),q1=this.gv(X.q1),f2=this.gv(X.f2),g2=this.gv(X.g2),q2=this.gv(X.q2);
    const key=t1+','+t2+','+f1.toFixed(1)+','+g1.toFixed(2)+','+q1.toFixed(3)+','+f2.toFixed(1)+','+g2.toFixed(2)+','+q2.toFixed(3);
    if(key!==s.key){s.key=key;rbj(t1?1:0,f1,g1,q1,sr,s.c,0);rbj(t2?1:2,f2,g2,q2,sr,s.c,5);}
    const c=s.c,z=s.s;
    for(let b=0;b<2;b++){const o=b*5,b0=c[o],b1=c[o+1],b2=c[o+2],a1=c[o+3],a2=c[o+4];
      for(let ch=0;ch<2;ch++){const B=ch?R:L,zo=b*4+ch*2;let z1=z[zo],z2=z[zo+1];
        for(let i=0;i<n;i++){const x=B[i],y=b0*x+z1;z1=b1*x-a1*y+z2;z2=b2*x-a2*y;B[i]=y;}z[zo]=z1;z[zo+1]=z2;}}}
  fFilter(L,R,n,X){const s=this.FX.ft,sr=sampleRate,ty=this.pe[X.type]|0,fc=Math.min(this.gv(X.cut),sr*.45),res=this.gv(X.res),dr=this.gv(X.drive),mix=this.gv(X.mix);
    const g1=Math.tan(Math.PI*fc/sr),g0=s.g<0?g1:s.g;s.g=g1;const map=[0,2,4,6,7][ty]||0,drv=dr>.002?1+dr*8:0;
    svfCh(s.s,0,L,n,g0,(g1-g0)/n,2-1.96*res,map,3.98,drv,drv?1/(1+dr*2):1,mix);svfCh(s.s,4,R,n,g0,(g1-g0)/n,2-1.96*res,map,3.98,drv,drv?1/(1+dr*2):1,mix);}
  fShift(L,R,n,X){const s=this.FX.sh,sr=sampleRate,hn=this.gv(X.hz),hz=Math.sign(hn)*2000*Math.pow(Math.abs(hn),3),fb=this.gv(X.fb),mix=this.gv(X.mix),z=s.s;let ph=s.ph;
    for(let i=0;i<n;i++){ph+=hz/sr;ph-=Math.floor(ph);const co=fsin(ph+.25),si=fsin(ph);
      for(let c=0;c<2;c++){const B=c?R:L,o=c*40;const x=B[i]+fb*s.last[c];let a=x,b=x;
        for(let k=0;k<4;k++){const q=o+k*4,y=HIL1[k]*(a+z[q+3])-z[q+1];z[q+1]=z[q];z[q]=a;z[q+3]=z[q+2];z[q+2]=y;a=y;}
        for(let k=0;k<4;k++){const q=o+16+k*4,y=HIL2[k]*(b+z[q+3])-z[q+1];z[q+1]=z[q];z[q]=b;z[q+3]=z[q+2];z[q+2]=y;b=y;}
        const ad=z[o+32];z[o+32]=a;const out=ad*co-b*si;s.last[c]=ft(out);B[i]=B[i]*(1-mix)+out*mix;}}
    s.ph=ph;}
  fCrush(L,R,n,X){const s=this.FX.cr,rt=this.gv(X.rate),bits=this.gv(X.bits),mix=this.gv(X.mix),H=1+rt*rt*63,q=Math.pow(2,bits-1);
    for(let c=0;c<2;c++){const B=c?R:L;let cnt=s.c[c],h=s.h[c];
      for(let i=0;i<n;i++){cnt+=1;if(cnt>=H){cnt-=H;h=Math.round(B[i]*q)/q;}B[i]=B[i]*(1-mix)+h*mix;}s.c[c]=cnt;s.h[c]=h;}}
  fUtil(L,R,n,X){const g=Math.pow(10,this.gv(X.gain)/20),wd=this.gv(X.width),pn=this.gv(X.pan),a=(pn+1)*Math.PI/4,gl=Math.cos(a)*1.4142*g,gr=Math.sin(a)*1.4142*g;
    for(let i=0;i<n;i++){const m=(L[i]+R[i])*.5,sd=(L[i]-R[i])*.5*wd;L[i]=(m+sd)*gl;R[i]=(m-sd)*gr;}}
  // ---------- global ----------
  globalMods(){
    const src=this.gsrc,v=this.lastV&&this.lastV.active?this.lastV:null;
    if(v)src.set(v.src);else{src.fill(0);for(let i=0;i<10;i++){const t=this.lfoT[i];let ph=this.gp[i]+this.bv(this.LI[i].phase);ph-=Math.floor(ph);src[4+i]=t[Math.min(1024,(ph*1024)|0)];}}
    src[17]=this.mw;src[18]=(this.pb+1)*.5;for(let i=0;i<8;i++)src[19+i]=this.pn[this.MI[i]];
    const T=this.gtouched,M=this.gmod;for(let j=0;j<T.length;j++)M[T[j]]=0;const R=this.gr;
    for(let r=0;r<R.n;r++){let x=src[R.s[r]];if(R.e[r]!==1)x=Math.pow(x>0?x:0,R.e[r]);if(R.bi[r])x=2*x-1;const a=R.a[r];if(a>=0)x*=src[a];M[R.d[r]]+=x*R.amt[r];}
  }
  events(fr){const q=this.q;if(!q.length)return;const sr=sampleRate;
    for(let i=0;i<q.length;i++){const d=q[i];if(d.at!=null&&Math.round(d.at*sr)>fr)continue;q.splice(i,1);i--;
      if(d.t==='on')this.noteOn(d.n,d.v==null?.8:d.v);else this.noteOff(d.n);}}
  process(inp,out){
    const o=out[0];if(!o||!o[0])return true;if(!this.ok){return true;}
    const Lo=o[0],Ro=o[1]||o[0],n=Lo.length,sr=sampleRate,mL=this.mixL,mR=this.mixR;
    mL.fill(0,0,n);mR.fill(0,0,n);
    const bpm=this.bv(this.GI.bpm);
    for(let off=0;off<n;off+=CH){const m=Math.min(CH,n-off);
      this.events(currentFrame+off+m);
      for(let i=0;i<10;i++){const I=this.LI[i];const hz=this.pe[I.sync]>.5?bpm/60/DIVB[Math.round(this.bv(I.div))]:this.bv(I.rate);this.gp[i]+=hz*m/sr;if(this.gp[i]>1e6)this.gp[i]-=Math.floor(this.gp[i]);}
      for(const v of this.V)if(v.active)this.voice(v,off,m);}
    this.globalMods();
    this.fxRun(mL,mR,n);
    const mg=this.bv(this.GI.master);
    let dxL=this.dxL,dxR=this.dxR,dcL=this.dcL,dcR=this.dcR;
    for(let i=0;i<n;i++){let l=mL[i]*mg,r=mR[i]*mg;
      const yl=l-dxL+.9995*dcL;dxL=l;dcL=yl;const yr=r-dxR+.9995*dcR;dxR=r;dcR=yr;l=yl;r=yr;
      if(l>.85||l<-.85){const a=Math.abs(l);l=Math.sign(l)*(.85+.15*ft((a-.85)/.15));}
      if(r>.85||r<-.85){const a=Math.abs(r);r=Math.sign(r)*(.85+.15*ft((a-.85)/.15));}
      if(!(l===l))l=0;if(!(r===r))r=0;Lo[i]=l;Ro[i]=r;}
    this.dxL=dxL;this.dxR=dxR;this.dcL=dcL;this.dcR=dcR;
    if(!(dcL===dcL)||!(dcR===dcR)){this.dxL=this.dxR=this.dcL=this.dcR=0;this.fxInit();}
    this.vizC+=n;if(this.vizC>=1500){this.vizC=0;this.viz();}
    return true;
  }
  viz(){
    let v=null;for(const x of this.V)if(x.active&&!x.rel&&(!v||x.id>v.id))v=x;if(!v&&this.lastV&&this.lastV.active)v=this.lastV;
    let cnt=0;for(const x of this.V)if(x.active)cnt++;
    const T=this.touched,G=this.gtouched,mods=new Float32Array((T.length+G.length)*2);let k=0;
    for(let j=0;j<T.length;j++){const i=T[j];mods[k++]=i;let nn=this.pn[i]+(v?v.mod[i]:0);mods[k++]=nn<0?0:nn>1?1:nn;}
    for(let j=0;j<G.length;j++){const i=G[j];mods[k++]=i;let nn=this.pn[i]+this.gmod[i];mods[k++]=nn<0?0:nn>1?1:nn;}
    const env=new Float32Array(12),lfo=new Float32Array(20);
    if(v){for(let i=0;i<4;i++){const e=v.e[i];const d=eDur(e,v.ep[i]);env[i*3]=e.st;env[i*3+1]=d>0?Math.min(1,e.t/d):0;env[i*3+2]=e.v;}}
    for(let i=0;i<10;i++){const I=this.LI[i],mode=this.pe[I.mode]|0;let ph;const off=this.bv(I.phase);
      if(mode===0||!v){ph=this.gp[i]+off;ph-=Math.floor(ph);}else if(mode===1){ph=v.lph[i]+off;ph-=Math.floor(ph);}else ph=Math.min(1,v.lph[i]+off);
      lfo[i*2]=ph;const t=this.lfoT[i];lfo[i*2+1]=t[Math.min(1024,(ph*1024)|0)];}
    this.port.postMessage({t:'viz',n:cnt,mods,env,lfo,live:v?1:0});
  }
}
registerProcessor('wt1',WT1);
