
(()=>{
 const config=window.PAGE_CONFIG,manifest=window.ATLAS_CATALOG,root=document.getElementById('plot');
 const loaded=new Map(),decoded=new Map();let active=0,sequence=0;
 function script(url){if(!loaded.has(url))loaded.set(url,new Promise((res,rej)=>{const s=document.createElement('script');s.src=url;s.onload=res;s.onerror=()=>rej(Error('Unable to load '+url));document.head.append(s)}));return loaded.get(url)}
 function unpack(p){const bytes=Uint8Array.from(atob(p.data),c=>c.charCodeAt(0));return new Float32Array(bytes.buffer)}
 function geometry(id){if(decoded.has(id))return decoded.get(id);const g=window.ATLAS_GEOMETRY[id],v=unpack(g.points),shape=g.points.shape;
   let out={};if(shape.length===3){const n=shape[0],m=shape[1];out.x=[];out.y=[];out.z=[];for(let i=0;i<n;i++){let x=[],y=[],z=[];for(let j=0;j<m;j++){const k=(i*m+j)*3;x.push(v[k]);y.push(v[k+1]);z.push(v[k+2])}out.x.push(x);out.y.push(y);out.z.push(z)}if(g.color){const c=unpack(g.color);out.surfacecolor=Array.from({length:n},(_,i)=>Array.from(c.slice(i*m,(i+1)*m)))}}
   else{out.x=[];out.y=[];out.z=[];for(let k=0;k<v.length;k+=3){out.x.push(v[k]);out.y.push(v[k+1]);out.z.push(v[k+2])}}decoded.set(id,out);return out}
 function trace(t){const data=geometry(t.geometry),g=structuredClone(data);if(t.type==='surface')return {...g,type:'surface',name:t.name,showscale:!!t.bar,colorscale:g.surfacecolor?t.scale:[[0,t.color],[1,t.color]],opacity:t.opacity,contours:{x:{show:false},y:{show:false},z:{show:false}},lighting:{ambient:.6,diffuse:.82,roughness:.65,specular:.16,fresnel:.12},lightposition:{x:120,y:-170,z:220},colorbar:{title:{text:t.bar,font:{size:12}},tickfont:{size:10},len:.6,thickness:10},hovertemplate:'x %{x:.6g}<br>y %{y:.6g}<br>z %{z:.6g}<extra>'+t.name+'</extra>'};
   if(t.segments){for(const k of ['x','y','z']){let out=[];for(let i=0;i<g[k].length;i+=2)out.push(g[k][i],g[k][i+1],null);g[k]=out}}
   return {...g,type:'scatter3d',mode:t.mode||'lines',name:t.name,line:{color:t.color,width:t.width},marker:{color:t.color,size:4},showlegend:false,hoverinfo:'skip'}}
 function setupMesh(m){
   const cb=document.getElementById('meshgrid'),lab=document.getElementById('meshgrid-label');
   if(!cb)return;const belts=m.traces.filter(t=>t.belt);lab.hidden=!belts.length;
   let extra=[];let request=0;
   const update=async()=>{const ticket=++request;
     if(extra.length){const ids=extra;extra=[];await Plotly.deleteTraces(root,ids);}
     if(!cb.checked||!belts.length||ticket!==request)return;
     const out=belts.map(t=>{const p=geometry(t.geometry),n=p.x.length,q=p.x[0].length,g={x:[],y:[],z:[]};
       function point(i,j){for(const k of ['x','y','z'])g[k].push(p[k][i][j]);}
       function end(){for(const k of ['x','y','z'])g[k].push(null);}
       for(let j=0;j<q;j++){for(let i=0;i<n;i++)point(i,j);end();}
       for(let i=0;i<n;i+=Math.max(1,Math.ceil(n/40))){for(let j=0;j<q;j++)point(i,j);end();}
       return {...g,type:'scatter3d',mode:'lines',line:{color:'#d7e4eb',width:1},opacity:.3,showlegend:false,hoverinfo:'skip',name:'Actual belt mesh'};
     });
     const start=root.data.length;await Plotly.addTraces(root,out);extra=out.map((_,i)=>start+i);
   };
   cb.onchange=update;update();
 }
 function setupCircuit(m){
   const box=document.getElementById('circuit'),input=document.getElementById('circuit-progress'),label=document.getElementById('circuit-label');
   if(!box)return;const indices=m.traces.map((t,i)=>t.circuit?i:-1).filter(i=>i>=0);box.hidden=!indices.length;
   if(!indices.length){input.oninput=null;return;}
   let busy=false,pending=null;
   const update=async()=>{if(busy){pending=true;return;}busy=true;const k=Number(input.value);
     label.textContent=(k/2400).toFixed(3)+' of one circuit';
     const x=[],y=[],z=[];for(const i of indices){const p=geometry(m.traces[i].geometry);x.push(p.x.slice(0,k+1));y.push(p.y.slice(0,k+1));z.push(p.z.slice(0,k+1));}
     await Plotly.restyle(root,{x,y,z},indices);
     const e=m.traces.findIndex(t=>t.endpoint);if(e>=0)await Plotly.restyle(root,{visible:k===2400},[e]);
     busy=false;if(pending){pending=null;update();}
   };
   input.oninput=update;update();
 }

 async function show(index){active=index;let ticket=++sequence;const id=config.models[index],m=manifest.models[id];document.querySelectorAll('[data-model]').forEach((b,i)=>{b.classList.toggle('selected',i===index);b.setAttribute('aria-pressed',String(i===index))});document.getElementById('modelstatus').textContent=m.status;document.getElementById('modelnote').textContent=m.note;document.getElementById('modelresolution').textContent='Loading cached geometry…';
   const legend=document.getElementById('modellegend');legend.replaceChildren();const labels=new Set();for(const t of m.traces){if(t.legendLabel&&!labels.has(t.legendLabel)){labels.add(t.legendLabel);const s=document.createElement('span');s.style.cssText='display:inline-block;margin:4px 15px 6px 0;color:'+t.color;s.textContent='● '+t.legendLabel;legend.append(s)}}
   try{await script(manifest.plotly);await Promise.all(m.traces.map(t=>script(manifest.geometry[t.geometry])));if(ticket!==sequence)return;
     const traces=m.traces.map(trace);const grid={showbackground:false,gridcolor:'#2a3e54',zerolinecolor:'#466078',color:'#a7b8c8',showspikes:false,tickfont:{size:10},title:{font:{size:11}}};
     const scene={bgcolor:'#101d2e',aspectmode:'data',camera:m.camera,xaxis:{...grid,title:{text:m.axes[0]}},yaxis:{...grid,title:{text:m.axes[1]}},zaxis:{...grid,title:{text:m.axes[2]}}};
     if(m.fixed_units&&m.ranges){const d=m.ranges.map(r=>r[1]-r[0]),s=Math.max(...d);scene.aspectmode='manual';scene.aspectratio={x:d[0]/s,y:d[1]/s,z:d[2]/s};}
     if(m.ranges)for(let i=0;i<3;i++)scene[['xaxis','yaxis','zaxis'][i]].range=m.ranges[i];
     root.querySelector('.loading')?.remove();
     await Plotly.react(root,traces,{paper_bgcolor:'#101d2e',plot_bgcolor:'#101d2e',font:{color:'#bccedd'},margin:{l:8,r:8,t:8,b:8},scene,showlegend:false,uirevision:id},{responsive:true,displaylogo:false,scrollZoom:true,displayModeBar:true,modeBarButtonsToRemove:['resetCameraLastSave3d'],toImageButtonOptions:{format:'png',filename:'ver500-'+config.slug+'-'+id,width:1800,height:1300,scale:1}});
     const shapes=m.traces.filter(t=>t.type==='surface').map(t=>manifest.shapes[t.geometry].shape.slice(0,2).join(' × '));const count=m.traces.reduce((a,t)=>a+manifest.shapes[t.geometry].vertices,0);document.getElementById('modelresolution').textContent=(shapes.length?shapes.slice(0,2).join(' + ')+(shapes.length>2?' + '+(shapes.length-2)+' patches':'')+' · ':'')+count.toLocaleString()+' vertices · cached';
     window.ATLAS_READY={model:id,vertices:count,surfaces:shapes.length}; setupCircuit(m); setupMesh(m);
   }catch(e){root.innerHTML='<div class="error">The 3D view could not load. '+String(e.message).replace(/[<>&]/g,'')+'<br>Use the evidence and source links below; all explanation remains available.</div>';document.getElementById('modelresolution').textContent='3D unavailable';console.error(e)}
 }
 document.querySelectorAll('[data-model]').forEach((b,i)=>b.addEventListener('click',()=>show(i)));
 document.getElementById('resetview').addEventListener('click',()=>{if(window.Plotly)Plotly.relayout(root,{'scene.camera':manifest.models[config.models[active]].camera})});
 document.getElementById('fullscreen').addEventListener('click',async()=>{const v=document.querySelector('.viewer');if(!document.fullscreenElement)await v.requestFullscreen();else await document.exitFullscreen()});
 document.addEventListener('fullscreenchange',()=>{root.style.height=document.fullscreenElement?'calc(100vh - 160px)':'';if(window.Plotly)Plotly.Plots.resize(root)});
 document.getElementById('downloadview').addEventListener('click',()=>{if(window.Plotly)Plotly.downloadImage(root,{format:'png',filename:'ver500-'+config.slug+'-'+config.models[active],width:1800,height:1300})});
 document.querySelector('.menu').addEventListener('click',()=>document.body.classList.toggle('menuopen'));
 document.addEventListener('keydown',e=>{if(e.target.matches('input,textarea,select'))return;if(e.key==='ArrowRight'&&config.next)location.href=config.next;if(e.key==='ArrowLeft'&&config.prev)location.href=config.prev});
 if(location.protocol==='file:')document.querySelector('a[download]')?.remove();
 show(0);
})();
