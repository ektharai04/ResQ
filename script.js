const KEY='resq_v2',STALE=120000,BASE=2.2,GRID=[10,30,50,70,90],TAB=Math.random().toString(36).slice(2);
const $=id=>document.getElementById(id),now=()=>Date.now();
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const d=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const ago=t=>{const s=Math.round((now()-t)/1000);return s<60?s+' s ago':Math.round(s/60)+' min ago'};
const setH=(el,h)=>{if(el._h!==h){el._h=h;el.innerHTML=h}};
const DONE=['Closed','Arrived at hospital'],STEPS=['Received','Ambulance assigned','On the way','Patient picked up','Arrived at hospital'];
const USERS={'TRF-001':'trf','DRV-001':'amb','HST-001':'hos'};

/* ---------- road network: 5x5 grid of junctions ---------- */
const NID=(i,j)=>i+','+j,NP=n=>{const[i,j]=n.split(',');return{x:GRID[i],y:GRID[j]}},JL=n=>{const[i,j]=n.split(',');return'ABCDE'[i]+(+j+1)};
const ek=(a,b)=>a<b?a+'|'+b:b+'|'+a;
const NODES=[],EDGES=[],ADJ={};
GRID.forEach((x,i)=>GRID.forEach((y,j)=>{const n=NID(i,j);NODES.push(n);ADJ[n]=[]}));
GRID.forEach((x,i)=>GRID.forEach((y,j)=>{const n=NID(i,j);[[i+1,j],[i,j+1]].forEach(([a,b])=>{if(a<5&&b<5){const m=NID(a,b),k=ek(n,m);EDGES.push({k,a:n,b:m});ADJ[n].push({n:m,k});ADJ[m].push({n,k})}})}));
const POSTS=[{id:'T1',n:'1,1'},{id:'T2',n:'3,1'},{id:'T3',n:'1,3'},{id:'T4',n:'3,3'},{id:'T5',n:'2,2'}];
const unitOf=n=>POSTS.reduce((b,p)=>d(NP(n),NP(p.n))<d(NP(n),NP(b.n))?p:b).id;
const snap=p=>NODES.reduce((b,n)=>d(p,NP(n))<d(p,NP(b))?n:b);

/* ---------- state ---------- */
function seed(){const t=now(),c={},b={};EDGES.forEach(e=>{c[e.k]=b[e.k]=Math.random()*.8});
 return{hos:[{id:'H1',name:'City General',x:72,y:28,gen:10,icu:2,er:3,vent:1,trauma:1,upd:t},{id:'H2',name:'Lakeview Clinic',x:18,y:78,gen:6,icu:0,er:2,vent:0,trauma:0,upd:t},{id:'H3',name:'Sunrise Trauma Centre',x:82,y:82,gen:8,icu:3,er:4,vent:2,trauma:1,upd:t}],
 amb:[{id:'A1',x:52,y:48,st:'available',sync:t},{id:'A2',x:14,y:26,st:'available',sync:t},{id:'A3',x:88,y:58,st:'available',sync:t}],
 dead:{x:50,y:72,r:14},req:[],log:[],tr:{c,b,j:{}},clear:{},junc:{},pol:{},cleared:0}}
function load(){try{return JSON.parse(localStorage.getItem(KEY))||seed()}catch(e){return seed()}}
let S=load(),cur='pub',me=sessionStorage.getItem('resq_me'),inc={x:35,y:40},gps='',myAmb='A1',myHos='H1',myPol='T1',tId='',sim=null,sosT=null,RP=false;
if(!Object.hasOwn(USERS,me))me=null;
if(!S.req.some(r=>!DONE.includes(r.status)))S.hos.forEach(h=>h.upd=now());
const mine=()=>{try{return JSON.parse(localStorage.getItem('resq_mine'))||[]}catch(e){return[]}};
function save(){localStorage.setItem(KEY,JSON.stringify(S));render()}
addEventListener('storage',e=>{if(e.key===KEY){S=load();render()}});
const log=m=>{S.log.unshift(new Date().toLocaleTimeString()+' - '+m);S.log=S.log.slice(0,60)};
const H=id=>S.hos.find(h=>h.id===id),A=id=>S.amb.find(a=>a.id===id),R=id=>S.req.find(r=>r.id===id);
const inDark=a=>d(a,S.dead)<S.dead.r,stale=h=>now()-h.upd>STALE;
const cong=k=>(S.tr.j[k]>now())?1:(S.tr.c[k]||0);
const rankHos=(p,skip,tr)=>S.hos.filter(h=>h.er>0&&h.id!==skip).map(h=>({h,sc:d(p,h)+(stale(h)?25:0)+(tr&&!h.trauma?20:0)})).sort((a,b)=>a.sc-b.sc);
const nearAmb=(p,skip)=>S.amb.filter(a=>a.st==='available'&&a.id!==skip&&!(a.hold>now())).sort((a,b)=>d(p,a)-d(p,b))[0];

/* ---------- routing (Dijkstra on the junction grid; traffic makes a road costlier, police-cleared roads are free) ---------- */
function routeNodes(s,tgt){const e=snap(tgt),t=now(),dist={},prev={},todo=new Set(NODES);NODES.forEach(n=>dist[n]=1e9);dist[s]=0;
 while(todo.size){let u=null;todo.forEach(n=>{if(u===null||dist[n]<dist[u])u=n});todo.delete(u);if(u===e)break;
  ADJ[u].forEach(({n,k})=>{const c=S.clear[k]>t?0:cong(k),nd=dist[u]+20*(1+2.5*c);if(nd<dist[n]){dist[n]=nd;prev[n]=u}})}
 const p=[];for(let n=e;n!==undefined;n=prev[n]){p.unshift(n);if(n===s)break}return p}
const mkPath=(nodes,tgt)=>nodes.map(n=>({...NP(n),n})).concat([{x:tgt.x,y:tgt.y,n:null}]);
const tgtOf=r=>r.status==='Patient picked up'?H(r.hos):r;
function etaR(r,toHos){const a=A(r.amb);if(!a||!r.path)return 1;let p=a,t=0;for(let i=r.wi;i<r.path.length;i++){t+=d(p,r.path[i]);p=r.path[i]}
 if(toHos&&r.status!=='Patient picked up'&&r.hos)t+=d(r,H(r.hos))*1.3;return Math.max(1,Math.round(t*.35))}

/* ---------- navigation and login ---------- */
function show(p){if(['trf','amb','hos'].includes(p)&&USERS[me]!==p)p=me?USERS[me]:'login';cur=p;document.querySelectorAll('.page').forEach(x=>x.classList.toggle('on',x.id===p));render();scrollTo(0,0)}
function login(e){e.preventDefault();const id=$('uid').value.trim().toUpperCase();if(Object.hasOwn(USERS,id)&&$('pw').value==='demo123'){me=id;sessionStorage.setItem('resq_me',id);$('lmsg').textContent='';goDash()}else $('lmsg').textContent='Wrong ID or password. Use a demo login shown below.'}
function goDash(){show(USERS[me])}
function logout(){me=null;sessionStorage.removeItem('resq_me');show('pub')}
function resetAll(){if(confirm('Delete all demo data?')){localStorage.removeItem(KEY);localStorage.removeItem('resq_mine');S=seed();save();show('pub')}}

/* ---------- live map: persistent elements, so pins glide and animations never restart ---------- */
const LEG='<p class="m legend"><span class="lg g"></span>free<span class="lg y"></span>slow<span class="lg r"></span>jam<span class="lg b"></span>police-cleared corridor · 🏥 hospital · 🚑 ambulance · 🆘 incident · 👮 traffic police · 🚦 signals · dashed circle = no network</p>';
function initMap(el){let s='<svg class="roads" viewBox="0 0 100 100" preserveAspectRatio="none">';
 EDGES.forEach((e,i)=>{const a=NP(e.a),b=NP(e.b),xy=`x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}"`;s+=`<g class="rd c0${i%2?' rev':''}" data-k="${e.k}"><line class="rb" ${xy}/><line class="rc" ${xy}/><line class="rf" ${xy}/></g>`});
 s+='<g class="rr"></g>'+NODES.map(n=>{const p=NP(n);return`<circle class="jn n" data-n="${n}" cx="${p.x}" cy="${p.y}" r="1.8" style="animation-delay:-${(Math.random()*7).toFixed(1)}s"/>`}).join('')+'</svg><div class="dz">No network</div><div class="layer"></div>';
 el.innerHTML=s;el._m={e:{},j:{},p:{},rs:'',layer:el.querySelector('.layer'),rr:el.querySelector('.rr')};
 el.querySelectorAll('.rd').forEach(g=>el._m.e[g.getAttribute('data-k')]=g);el.querySelectorAll('.jn').forEach(c=>el._m.j[c.getAttribute('data-n')]=c)}
function drawMap(el,showInc){if(!el)return;if(!el._m)initMap(el);const m=el._m,t=now();
 EDGES.forEach(e=>{const cl=S.clear[e.k]>t,c=cong(e.k),cls='rd '+(cl?'clr':c>.66?'c2':c>.33?'c1':'c0')+(m.e[e.k].getAttribute('class').includes('rev')?' rev':'');if(m.e[e.k].getAttribute('class')!==cls)m.e[e.k].setAttribute('class',cls)});
 Object.keys(m.j).forEach(n=>{const cls='jn '+((S.junc[n]||{}).st||'n');if(m.j[n]._c!==cls){m.j[n]._c=cls;m.j[n].setAttribute('class',cls)}});
 const dl=-((t%1000)/1000).toFixed(2);let rs='';
 S.req.forEach(r=>{if(DONE.includes(r.status)||!r.amb||!r.path)return;const a=A(r.amb);rs+=`<polyline class="route${r.status==='Patient picked up'?' hs':''}" style="animation-delay:${dl}s" points="${[a].concat(r.path.slice(r.wi)).map(p=>p.x+','+p.y).join(' ')}"/>`});
 if(m.rs!==rs){m.rs=rs;m.rr.innerHTML=rs}
 const items=[];
 S.hos.forEach(h=>items.push({k:'h'+h.id,e:'🏥',x:h.x,y:h.y,t:h.name,c:'pin'}));
 S.amb.forEach(a=>items.push({k:'a'+a.id,e:'🚑',l:a.id,x:a.x,y:a.y,t:a.id+' '+a.st,c:'pin'+(a.st==='busy'?' sir':'')}));
 S.req.filter(q=>!DONE.includes(q.status)).forEach(q=>items.push({k:'q'+q.id,e:'🆘',x:q.x,y:q.y,t:q.id,c:'pin sos'}));
 POSTS.forEach(p=>{const c=S.pol[p.id]||NP(p.n);items.push({k:'p'+p.id,e:'👮',l:p.id,x:c.x,y:c.y,t:'Traffic police '+p.id,c:'pin'+(c.on?' act':'')})});
 if(showInc)items.push({k:'inc',e:'📍',x:inc.x,y:inc.y,t:'Selected location',c:'pin'});
 const seen=new Set();
 items.forEach(it=>{let p=m.p[it.k];if(!p){p=m.p[it.k]=document.createElement('i');m.layer.appendChild(p)}seen.add(it.k);
  const h=it.e+(it.l?'<small>'+it.l+'</small>':'');if(p._h!==h){p._h=h;p.innerHTML=h}if(p.className!==it.c)p.className=it.c;p.style.left=it.x+'%';p.style.top=it.y+'%';p.title=it.t});
 Object.keys(m.p).forEach(k=>{if(!seen.has(k)){m.p[k].remove();delete m.p[k]}})}

/* ---------- public: SOS, simulator, tracking, updates ---------- */
function newReq(type,level,why){const id='RSQ-'+(1001+S.req.length);S.req.push({id,x:inc.x,y:inc.y,type,level,why,gps,status:'Received',amb:null,hos:null,ack:'Your alert was received. The system is arranging help automatically.',t:now(),ups:[]});log(id+' created ('+type+', '+level+')');const m=mine();m.push(id);localStorage.setItem('resq_mine',JSON.stringify(m));tId=id;save();return id}
function sos(){const b=$('sosBtn');if(sosT){clearTimeout(sosT);sosT=null;b.textContent='SEND SOS';$('sosMsg').textContent='SOS cancelled.';return}
 $('sosMsg').textContent='';b.textContent='Sending in 5 s - tap to cancel';
 sosT=setTimeout(()=>{sosT=null;b.textContent='SEND SOS';const id=newReq('Manual SOS','Dispatch','Person pressed SOS');$('sosMsg').textContent='SOS sent. Your request ID is '+id+'. Track it below.';$('tid').value=id;track()},5000)}
function startSim(){if(sim)return;sim={end:now()+10000,ok:false};simTick();sim.i=setInterval(simTick,500)}
function simTick(){const l=Math.ceil((sim.end-now())/1000);if(l<=0)return endSim();$('simOut').innerHTML='Buzzer on. Press "I\'m OK" within <b>'+l+' s</b> or the alert is sent.'}
function imOk(){if(sim){sim.ok=true;endSim()}}
function endSim(){clearInterval(sim.i);const g=+$('simG').value,st=$('simStop').checked,ti=$('simTilt').checked,ok=sim.ok;sim=null;
 const s=(g>=6?3:g>=3?1:0)+(st?1:0)+(ti?2:0)+(ok?0:2),lv=s>=5?'Dispatch':s>=3?'Call owner':'Monitor';
 const why=`impact ${g} g, stopped: ${st?'yes':'no'}, tilted: ${ti?'yes':'no'}, "I'm OK" pressed: ${ok?'yes':'no'}, score ${s}/8`;
 let h=`<b>Alert level: ${lv}</b><br>${why}<br>`;
 if(lv==='Dispatch'){const id=newReq('Auto crash alert',lv,why);h+='Full alert sent. Request ID: <b>'+id+'</b>';$('tid').value=id;track()}
 else if(lv==='Call owner')h+='Warning only. No ambulance sent.';else h+='No ambulance sent. This looks like a minor event.';
 $('simOut').innerHTML=h}
function trackH(r){if(!r)return'<p class="m">Request not found.</p>';const i=STEPS.indexOf(r.status),a=r.amb&&A(r.amb),h=r.hos&&H(r.hos),act=!DONE.includes(r.status),jn=a?Object.values(S.junc).filter(j=>j.amb===r.amb&&j.st!=='ok').length:0;
 return`<div class="steps">${STEPS.map((s,k)=>`<span class="${k<=i?'done':''}">${s}</span>`).join('')}</div><p class="ack">Message to you: ${esc(r.ack)}</p>`+
 (a?`<p>Ambulance <b>${a.id}</b>${act&&r.path&&r.status!=='Patient picked up'?' - ETA about '+etaR(r)+' min':''}${inDark(a)?' <span class="bad">in a network dead zone, last update '+ago(a.sync)+'</span>':''}</p>`:'')+(act&&jn?`<p>🚦 Traffic police are clearing ${jn} junction${jn>1?'s':''} ahead.</p>`:'')+(h?`<p>Hospital: <b>${esc(h.name)}</b></p>`:'')+(r.status==='Closed'?'<p class="warn">This request is closed.</p>':'')}
function track(){tId=$('tid').value.trim().toUpperCase();renderTrack()}
function renderTrack(){if(tId)setH($('trackOut'),trackH(R(tId)))}
function sendUp(){const id=$('pSel').value;if(!id){$('upMsg').textContent='Select a request first.';return}const r=R(id);
 if(DONE.includes(r.status)){$('upMsg').textContent='This request is already finished.';return}
 const ty=$('pType').value,closes=ty!=='Pickup location changed'&&ty!=='Other emergency update';
 r.ups.push({type:ty,msg:$('pMsg').value,t:now(),ack:closes});
 if(closes){r.status='Closed';r.ack='Request closed: '+ty+'.';const a=r.amb&&A(r.amb);if(a){a.st='available';a.hold=0}r.path=null;log(id+' closed after patient update ('+ty+')');$('upMsg').textContent='Request closed. The ambulance was stood down.'}
 else{log(id+' patient update: '+ty);$('upMsg').textContent='Update sent to the ambulance team.'}
 $('pMsg').value='';save()}
function renderPub(){drawMap($('pubMap'),true);setH($('pubLeg'),LEG);const m=mine().filter(id=>R(id)),sel=$('pSel'),v=sel.value,o='<option value="">Select your request</option>'+m.map(id=>`<option>${id}</option>`).join('');
 if(sel._h!==o){sel._h=o;sel.innerHTML=o;sel.value=v}
 setH($('hist'),m.slice().reverse().map(id=>`<p><b>${id}</b> - ${R(id).status} - ${esc(R(id).type)}</p>`).join('')||'<p class="m">No requests yet.</p>');renderTrack()}
$('pubMap').addEventListener('click',e=>{const b=e.currentTarget.getBoundingClientRect();inc={x:Math.round((e.clientX-b.left)/b.width*100),y:Math.round((e.clientY-b.top)/b.height*100)};renderPub()});
if(navigator.geolocation)navigator.geolocation.getCurrentPosition(p=>{gps=p.coords.latitude.toFixed(4)+', '+p.coords.longitude.toFixed(4);$('gps').textContent='GPS captured: '+gps},()=>{$('gps').textContent='GPS not available. The map point is used.'});

/* ---------- automatic dispatch engine (the old coordinator, now in the background) ---------- */
function lead(){let l={};try{l=JSON.parse(localStorage.getItem('resq_lead'))||{}}catch(e){}
 if(!l.id||l.id===TAB||now()-l.t>3000){localStorage.setItem('resq_lead',JSON.stringify({id:TAB,t:now()}));return true}return false}
function autoAssign(r){const a=nearAmb(r),hs=rankHos(r,null,r.level==='Dispatch')[0];
 if(!a||!hs){if(!r.wait){r.wait=1;log(r.id+': waiting for a free ambulance or an ER bed')}return}
 r.wait=0;r.amb=a.id;r.hos=hs.h.id;a.st='busy';a.hold=0;r.status='Ambulance assigned';r.pre=null;r.delayed=false;r.path=mkPath(routeNodes(snap(a),r),r);r.wi=0;
 r.ack=`Ambulance ${a.id} dispatched automatically. ETA about ${etaR(r)} min. Destination: ${hs.h.name}.`;
 log(`Auto-dispatch ${r.id}: ${a.id} sent, destination ${hs.h.name}`)}
function reviewHos(r){const a=A(r.amb),h=H(r.hos),tr=r.level==='Dispatch',rk=rankHos(a,null,tr),cur=rk.find(x=>x.h.id===h.id),best=rk[0];
 if(!best){if(!r.noBed){r.noBed=1;log(r.id+': no hospital has an ER bed, keeping '+h.name)}return}
 r.noBed=0;
 if(best.h.id!==h.id&&(!cur||(stale(h)&&!stale(best.h)))){const why=h.er<=0?'no emergency bed':'bed data stale';
  r.hos=best.h.id;r.pre=null;r.ack=`Destination changed to ${best.h.name} (${why} at ${h.name}). Rerouted automatically.`;log(`Auto-reroute ${r.id}: ${h.name} to ${best.h.name} (${why})`);
  if(r.status==='Patient picked up'){r.path=mkPath(routeNodes(snap(a),best.h),best.h);r.wi=0}}}
function backup(r){const o=A(r.amb),na=nearAmb(r,r.amb);r.delayed=false;
 if(!na){log(r.id+': delay reported, no backup ambulance is free');return}
 o.st='available';na.st='busy';r.amb=na.id;r.status='Ambulance assigned';r.path=mkPath(routeNodes(snap(na),r),r);r.wi=0;
 r.ack='The first ambulance was delayed. Backup ambulance '+na.id+' dispatched automatically.';log(`Auto-backup ${r.id}: ${na.id} replaces ${o.id}`)}
function replan(r){const w=r.path[r.wi];if(!w||!w.n)return;const t=tgtOf(r);r.path=mkPath(routeNodes(w.n,t),t);r.wi=0}
function spd(r){const p=r.path[r.wi],q=r.wi>0&&r.path[r.wi-1];if(!q||!q.n||!p.n)return 1;const k=ek(q.n,p.n);return S.clear[k]>now()?1.15:1-.7*cong(k)}
function arrive(r,a){if(r.status==='Patient picked up'){r.status='Arrived at hospital';r.ack='Arrived at '+H(r.hos).name+'. Handover started.';a.st='available';r.path=null;log(r.id+': arrived at hospital');return}
 r.status='Patient picked up';r.ack='Patient picked up. Heading to '+H(r.hos).name+'. Traffic police are clearing the way.';log(r.id+': patient picked up');const h=H(r.hos);r.path=mkPath(routeNodes(snap(a),h),h);r.wi=0}
function step(r){const a=A(r.amb),t=now();if(!a||!r.path)return;
 if(r.status==='Ambulance assigned'){r.status='On the way';r.ack='Ambulance '+a.id+' is on the way. Traffic police are clearing the route.';log(r.id+': '+a.id+' departed')}
 if(!r.pre&&d(a,S.dead)<S.dead.r+14){r.pre={er:H(r.hos).er,t};log(r.id+': pre-blackout check, '+H(r.hos).name+' has '+H(r.hos).er+' ER beds; plan cached on driver phone')}
 if(r.delayed){if(r.status==='On the way')backup(r);else{r.delayed=false;log(r.id+': delay noted, patient already on board')}}
 if(!r.path||r.status==='Ambulance assigned')return;
 if(!inDark(a)){reviewHos(r);if(r.path&&((r.tk=(r.tk||0)+1)%8===0||RP))replan(r)}
 if(!inDark(a))a.sync=t;
 if(a.hold>t)return;
 let mv=BASE*spd(r);
 while(mv>0&&r.wi<r.path.length){const w=r.path[r.wi],dd=d(a,w);if(dd<=mv){a.x=w.x;a.y=w.y;mv-=dd;r.wi++}else{a.x+=(w.x-a.x)/dd*mv;a.y+=(w.y-a.y)/dd*mv;mv=0}}
 if(r.wi>=r.path.length)arrive(r,a)}

/* ---------- traffic police: clear junctions and roads ahead of every ambulance ---------- */
function trafficOps(t){const nw={};
 S.req.forEach(r=>{if(DONE.includes(r.status)||!r.amb||!r.path)return;const a=A(r.amb);let p=a,acc=0;
  for(let i=r.wi;i<r.path.length;i++){const w=r.path[i],start=acc;acc+=d(p,w);p=w;
   if(i>0&&r.path[i-1].n&&w.n&&start<=30)S.clear[ek(r.path[i-1].n,w.n)]=t+4500;
   if(w.n&&acc<=45&&!nw[w.n])nw[w.n]={st:acc<=20?'cl':'al',req:r.id,amb:r.amb,eta:Math.max(1,Math.round(acc/BASE*.8))}}});
 const old=S.junc,nj={};
 Object.keys(nw).forEach(n=>{const o=old[n],same=o&&o.req===nw[n].req;nj[n]={...nw[n],ack:!!(same&&o.ack)};
  if(!o||o.st!==nw[n].st||!same)log(nw[n].st==='cl'?`${unitOf(n)} is clearing junction ${JL(n)} for ${nw[n].amb}`:`${unitOf(n)} alerted: ${nw[n].amb} approaching ${JL(n)}`)});
 Object.keys(old).forEach(n=>{if(nw[n])return;const o=old[n];
  if(o.st==='cl'){nj[n]={...o,st:'ok',t};S.cleared++;log(`Junction ${JL(n)} cleared, ${o.amb} passed`)}else if(o.st==='ok'&&t-(o.t||0)<4000)nj[n]=o});
 S.junc=nj;
 POSTS.forEach(p=>{const js=Object.keys(S.junc).filter(n=>unitOf(n)===p.id&&S.junc[n].st!=='ok').sort((x,y)=>(S.junc[x].st==='cl'?0:1)-(S.junc[y].st==='cl'?0:1)),
  to=NP(js[0]||p.n),c=S.pol[p.id]||NP(p.n),dd=d(c,to),mv=Math.min(dd,4);
  S.pol[p.id]=dd<.1?{x:to.x,y:to.y,on:!!js.length}:{x:c.x+(to.x-c.x)/dd*mv,y:c.y+(to.y-c.y)/dd*mv,on:!!js.length}})}
function ackJ(n){if(S.junc[n]){S.junc[n].ack=true;log(unitOf(n)+' confirmed lane clear at '+JL(n));save()}}
function jam(n){const t=now();ADJ[n].forEach(({k})=>S.tr.j[k]=t+25000);S.rp=true;log(unitOf(n)+' reported heavy traffic at junction '+JL(n));save()}

/* ---------- main loop (runs in one open tab at a time) ---------- */
function tick(){if(!lead())return;S=load();const t=now();RP=!!S.rp;
 EDGES.forEach(e=>{const c=S.tr.c[e.k]||0;S.tr.c[e.k]=Math.min(1,Math.max(0,c+((S.tr.b[e.k]||0)-c)*.03+(Math.random()-.5)*.08))});
 if(Math.random()<.05)S.tr.b[EDGES[Math.floor(Math.random()*EDGES.length)].k]=Math.random()*.9;
 Object.keys(S.tr.j).forEach(k=>{if(S.tr.j[k]<t)delete S.tr.j[k]});Object.keys(S.clear).forEach(k=>{if(S.clear[k]<t)delete S.clear[k]});
 S.req.forEach(r=>{if(DONE.includes(r.status))return;if(!r.amb)autoAssign(r);else step(r)});
 trafficOps(t);S.rp=false;save()}
setInterval(tick,800);

/* ---------- traffic police dashboard ---------- */
let trfInit=false;
function cards(el,items,empty){const ks=items.map(i=>i.k).join(',');
 if(el._k!==ks){el._k=ks;el.innerHTML=items.map(i=>`<div class="req"><div class="dyn"></div><div class="bt"></div></div>`).join('')||empty}
 items.forEach((i,x)=>{const c=el.children[x];if(!c||!c.firstChild)return;const dyn=c.firstChild,bt=c.lastChild;if(dyn._h!==i.dyn){dyn._h=i.dyn;dyn.innerHTML=i.dyn}if(bt._h!==i.bt){bt._h=i.bt;bt.innerHTML=i.bt}})}
function renderTrf(){if(!trfInit||!$('tstats')){
 $('trfBody').innerHTML=`<div id="tstats" class="stats"></div><div class="grid"><div><div class="card"><h3>Live traffic map</h3><div class="map" id="trfMap"></div>${LEG}</div><div class="card"><h3>Activity log</h3><div class="log" id="tlog"></div></div></div>
 <div><div class="card"><label for="tu">Officer unit (demo)</label><select id="tu" onchange="myPol=this.value;renderTrf()">${POSTS.map(p=>`<option ${p.id===myPol?'selected':''}>${p.id}</option>`).join('')}</select><h3>Junctions in your zone</h3><div id="tj"></div></div>
 <div class="card"><h3>Active emergency routes</h3><div id="tr"></div></div>
 <div class="card"><h3>Demo: report heavy traffic</h3><label for="jn">Junction</label><select id="jn">${NODES.map(n=>`<option value="${n}">Junction ${JL(n)} (unit ${unitOf(n)})</option>`).join('')}</select><button class="d" onclick="jam($('jn').value)">Report jam</button><p class="m">Roads at that junction jam for 25 s. Ambulances reroute around them.</p></div></div></div>`;trfInit=true}
 const act=S.req.filter(r=>r.amb&&!DONE.includes(r.status)),J=S.junc,js=Object.keys(J);
 setH($('tstats'),`<div class="card"><b>${act.length}</b>Ambulances escorted</div><div class="card"><b>${js.filter(n=>J[n].st==='cl').length}</b>Junctions clearing now</div><div class="card"><b>${S.cleared}</b>Junctions cleared</div><div class="card"><b>${EDGES.filter(e=>cong(e.k)>.66).length}</b>Heavy-traffic roads</div>`);
 drawMap($('trfMap'),false);
 setH($('tlog'),S.log.map(l=>'<div>'+esc(l)+'</div>').join('')||'<p class="m">Nothing yet. Send an SOS or run the crash simulator on the public page.</p>');
 const mj=js.filter(n=>unitOf(n)===myPol&&J[n].st!=='ok').sort((x,y)=>(J[x].st==='cl'?0:1)-(J[y].st==='cl'?0:1));
 cards($('tj'),mj.map(n=>({k:n+J[n].req,dyn:`<b>Junction ${JL(n)}</b> <span class="tag">${J[n].st==='cl'?'CLEARING':'ALERT'}</span><br>Ambulance ${J[n].amb} (${J[n].req}) arrives in about ${Math.round(J[n].eta/5)*5} s`,bt:J[n].ack?'<span class="ok">Lane clear confirmed ✓</span>':`<button class="g" onclick="ackJ('${n}')">Confirm lane clear</button>`})),'<p class="m">No ambulance is approaching your junctions.</p>');
 setH($('tr'),act.map(r=>`<div class="req"><b>${r.id}</b> · ${r.status}<br>Ambulance ${r.amb} to ${esc(H(r.hos).name)} · ETA about ${etaR(r)} min</div>`).join('')||'<p class="m">No active emergency routes.</p>')}

/* ---------- ambulance dashboard (driver view: journey is automatic) ---------- */
function delay(id){const r=R(id);if(!r||!r.amb)return;r.delayed=true;A(r.amb).hold=now()+12000;log(id+': driver reported delay');save()}
function ackUp(id,i){const u=R(id).ups[i];u.ack=true;log(id+': update acknowledged');save()}
let ambInit=false;
function renderAmb(){if(!ambInit||!$('abst')){
 $('ambBody').innerHTML=`<div class="card"><label for="asel">Driver's ambulance (demo)</label><select id="asel" onchange="myAmb=this.value;renderAmb()">${S.amb.map(x=>`<option ${x.id===myAmb?'selected':''}>${x.id}</option>`).join('')}</select><p id="abst"></p></div>
 <div class="grid"><div class="card"><h3>Assigned requests (auto-dispatched)</h3><div id="arq"></div></div><div class="card"><h3>Patient and family updates</h3><div id="aup"></div></div></div>
 <div class="card"><h3>Map</h3><div class="map" id="ambMap"></div>${LEG}</div>`;ambInit=true}
 const a=A(myAmb),rs=S.req.filter(r=>r.amb===myAmb&&!DONE.includes(r.status));
 setH($('abst'),`Status: <b>${a.st}</b> · ${inDark(a)?'<span class="bad">No network here. Last sync '+ago(a.sync)+'</span>':'<span class="ok">Network OK</span>'}`);
 cards($('arq'),rs.map(r=>{const jn=Object.values(S.junc).filter(j=>j.amb===r.amb&&j.st!=='ok').length;
  return{k:r.id,dyn:`<b>${r.id}</b> · ${r.status}<br>Destination: <b>${esc(H(r.hos).name)}</b> · ETA about ${etaR(r)} min<br>${inDark(a)&&r.pre?'<span class="ok">Driving on cached plan from '+new Date(r.pre.t).toLocaleTimeString()+' ('+r.pre.er+' ER beds)</span>':'<span class="m">🚦 Traffic police clearing '+jn+' junction'+(jn===1?'':'s')+' ahead</span>'}${a.hold>now()?'<br><span class="warn">Delay reported. Backup being arranged.</span>':''}`,bt:`<button onclick="delay('${r.id}')">Report delay</button>`}}),'<p class="m">No assigned requests. You will be dispatched automatically.</p>');
 const ups=[];S.req.filter(r=>r.amb===myAmb).forEach(r=>r.ups.forEach((u,i)=>{if(!u.ack)ups.push({k:r.id+i,dyn:`<b>${r.id}</b>: ${esc(u.type)}<br>${esc(u.msg)}`,bt:`<button class="g" onclick="ackUp('${r.id}',${i})">Acknowledge</button>`})}));
 cards($('aup'),ups,'<p class="m">No updates.</p>');
 drawMap($('ambMap'),false)}

/* ---------- hospital ---------- */
const nn=v=>Math.max(0,Math.floor(+v||0));
function fillHos(){const h=H(myHos);$('fg').value=h.gen;$('fi').value=h.icu;$('fe').value=h.er;$('fv').value=h.vent}
function updHos(lost){const h=H(myHos);if(lost){h.er=0}else{h.gen=nn($('fg').value);h.icu=nn($('fi').value);h.er=nn($('fe').value);h.vent=nn($('fv').value)}h.upd=now();log(h.name+(lost?': emergency beds taken (0 left)':': capacity updated'));save();fillHos()}
function pickHos(v){myHos=v;fillHos();renderHos()}
let hosInit=false;
function renderHos(){if(!hosInit||!$('fg')){
 $('hosBody').innerHTML=`<div class="grid"><div class="card"><label for="hsel">Hospital (demo)</label><select id="hsel" onchange="pickHos(this.value)">${S.hos.map(x=>`<option value="${x.id}" ${x.id===myHos?'selected':''}>${esc(x.name)}</option>`).join('')}</select>
 <label for="fg">General beds</label><input id="fg" type="number" min="0"><label for="fi">ICU beds</label><input id="fi" type="number" min="0"><label for="fe">Emergency beds</label><input id="fe" type="number" min="0"><label for="fv">Ventilators</label><input id="fv" type="number" min="0">
 <button class="p" onclick="updHos(false)">Save and confirm</button> <button class="d" onclick="updHos(true)">Demo: emergency beds taken</button><p class="m">Saving refreshes the "confirmed" time. Data older than 2 minutes is marked stale. If a hospital runs out of beds, incoming ambulances are rerouted automatically.</p></div>
 <div class="card"><h3>Incoming ambulances</h3><div id="inc"></div></div></div>`;hosInit=true;fillHos()}
 setH($('inc'),S.req.filter(r=>r.hos===myHos&&!DONE.includes(r.status)).map(r=>`<div class="req"><b>${r.id}</b> · ${esc(r.type)} · ${r.level}<br>Ambulance ${r.amb} · ${r.status}${r.amb&&r.path?' · ETA about '+etaR(r,true)+' min':''}</div>`).join('')||'<p class="m">No incoming ambulances.</p>')}

function render(){$('navDash').hidden=$('navOut').hidden=!me;$('navLogin').hidden=!!me;
 if(cur==='pub')renderPub();else if(cur==='trf')renderTrf();else if(cur==='amb')renderAmb();else if(cur==='hos'){if(!$('inc'))hosInit=false;renderHos()}}
render();