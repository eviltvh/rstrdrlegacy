"use strict";

// ════════════════════════════════════════════════════════════
//  CONFIG
// ════════════════════════════════════════════════════════════
// El self se detecta auto: el usuario cuyo origen literal es 'self'.
// Si querés forzar otro id como centro, ponelo aquí (string), si no, null.
const SELF_OVERRIDE = null;
const RING_BASE = 220;          // distancia del primer anillo (lvl 1)
const RING_GROWTH = 1.3;        // 1.0 = anillos lineales; >1 = se expanden

// ════════════════════════════════════════════════════════════
//  STATE
// ════════════════════════════════════════════════════════════
const state = {
  nodes: [],
  links: [],
  nodeMap: new Map(),
  adj: new Map(),     // undirected
  outAdj: new Map(),  // origen -> target
  inAdj: new Map(),   // target -> origenes
  levels: new Map(),  // id -> nivel BFS desde self
  maxLevel: 0,
  selfId: null,       // detectado del CSV (el que tiene origen='self')
  filter: 'all',
  selectedId: null,
  pathIds: new Set(),
  pathOrdered: [],
  showLabels: true,
  frozen: false,
};

// ════════════════════════════════════════════════════════════
//  CSV PARSER
// ════════════════════════════════════════════════════════════
function parseCSV(text) {
  const lines = [];
  let cur = '';
  let inQuotes = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (c === '"') {
      if (inQuotes && text[i+1] === '"') { cur += '"'; i++; }
      else inQuotes = !inQuotes;
    } else if (c === '\n' && !inQuotes) {
      lines.push(cur); cur = '';
    } else if (c === '\r' && !inQuotes) {
      // skip
    } else {
      cur += c;
    }
  }
  if (cur) lines.push(cur);

  const parseLine = (line) => {
    const out = []; let f = ''; let q = false;
    for (let i = 0; i < line.length; i++) {
      const c = line[i];
      if (c === '"') {
        if (q && line[i+1] === '"') { f += '"'; i++; }
        else q = !q;
      } else if (c === ',' && !q) { out.push(f); f = ''; }
      else f += c;
    }
    out.push(f);
    return out;
  };

  if (!lines.length) return { headers: [], rows: [] };
  const headers = parseLine(lines[0]).map(h => h.trim());
  const rows = lines.slice(1)
    .filter(l => l.trim())
    .map(l => {
      const vals = parseLine(l);
      const obj = {};
      headers.forEach((h, i) => obj[h] = (vals[i] ?? '').trim());
      return obj;
    });
  return { headers, rows };
}

// ════════════════════════════════════════════════════════════
//  BUILD GRAPH
//  Reglas:
//   1. selfId = username cuyo origen === 'self' (case-insensitive)
//   2. Para cada row:
//      - si origen === 'self' → este user ES el self, sin edge
//      - si origen es un username real → edge origen → user (jerarquía normal)
//      - si origen es un ghost (solo aparece como origen) → edge origen → user
//        Y ADEMÁS edge selfId → ghost (los ghosts cuelgan del self)
// ════════════════════════════════════════════════════════════
function findSelfId(rows) {
  if (SELF_OVERRIDE) return SELF_OVERRIDE;
  for (const row of rows) {
    if ((row.origen || '').trim().toLowerCase() === 'self') {
      const u = (row.username || '').trim();
      if (u) return u;
    }
  }
  return null;
}

function buildGraph(rows) {
  const nodeMap = new Map();
  const selfId = findSelfId(rows);

  // set de usernames reales (los que aparecen en la columna username)
  const realUsernames = new Set(
    rows.map(r => (r.username || '').trim()).filter(Boolean)
  );

  const ensureNode = (id, isGhost = false) => {
    if (!id) return null;
    if (!nodeMap.has(id)) {
      nodeMap.set(id, {
        id,
        username: id,
        ghost: isGhost,
        isSelf: id === selfId,
        status: isGhost ? 'origin' : 'unknown',
        mutual: false,
        origen: '',
        followed_at: '',
        mutual_checked_at: '',
        profile_followers: '',
        profile_following: '',
        profile_ratio: '',
        stand_type: '',
        days_active: '',
      });
    } else if (!isGhost) {
      const n = nodeMap.get(id);
      n.ghost = false;
      if (id === selfId) n.isSelf = true;
    }
    return nodeMap.get(id);
  };

  // pase 1: nodos reales con sus datos
  rows.forEach(row => {
    const u = (row.username || '').trim();
    if (!u) return;
    const node = ensureNode(u, false);
    Object.assign(node, {
      followed_at: row.followed_at || '',
      status: (row.status || 'unknown').toLowerCase(),
      mutual: String(row.mutual || '').toLowerCase() === 'true',
      mutual_checked_at: row.mutual_checked_at || '',
      origen: (row.origen || '').trim(),
      profile_followers: row.profile_followers || '',
      profile_following: row.profile_following || '',
      profile_ratio: row.profile_ratio || '',
      stand_type: row.stand_type || '',
      days_active: row.days_active || '',
    });
  });

  // pase 2: edges
  const links = [];
  rows.forEach(row => {
    const u = (row.username || '').trim();
    if (!u) return;
    const o = (row.origen || '').trim();
    if (!o) return;
    if (o.toLowerCase() === 'self') return;     // este user ES el self
    if (o.toLowerCase() === 'unknown') return;
    if (o === u) return;

    const isGhostOrigin = !realUsernames.has(o);
    ensureNode(o, isGhostOrigin);

    // edge origen → user
    links.push({ source: o, target: u });

    // ghost origins cuelgan del self
    if (isGhostOrigin && selfId && o !== selfId) {
      links.push({ source: selfId, target: o });
    }
  });

  // dedupe edges
  const seen = new Set();
  const dedup = [];
  links.forEach(l => {
    const k = `${l.source}|${l.target}`;
    if (!seen.has(k)) { seen.add(k); dedup.push(l); }
  });

  return { nodes: Array.from(nodeMap.values()), links: dedup, selfId };
}

// ════════════════════════════════════════════════════════════
//  ADJACENCY
// ════════════════════════════════════════════════════════════
function indexGraph(nodes, links) {
  const adj = new Map();
  const outAdj = new Map();
  const inAdj = new Map();
  const nodeMap = new Map();
  nodes.forEach(n => {
    adj.set(n.id, new Set());
    outAdj.set(n.id, new Set());
    inAdj.set(n.id, new Set());
    nodeMap.set(n.id, n);
  });
  links.forEach(l => {
    const s = typeof l.source === 'object' ? l.source.id : l.source;
    const t = typeof l.target === 'object' ? l.target.id : l.target;
    adj.get(s)?.add(t);
    adj.get(t)?.add(s);
    outAdj.get(s)?.add(t);
    inAdj.get(t)?.add(s);
  });
  return { adj, outAdj, inAdj, nodeMap };
}

// ════════════════════════════════════════════════════════════
//  BFS LEVELS DESDE SELF
// ════════════════════════════════════════════════════════════
function computeLevels(adj, rootId) {
  const levels = new Map();
  let maxLevel = 0;
  if (!rootId || !adj.has(rootId)) return { levels, maxLevel };
  levels.set(rootId, 0);
  const queue = [rootId];
  while (queue.length) {
    const cur = queue.shift();
    const lvl = levels.get(cur);
    adj.get(cur)?.forEach(nb => {
      if (!levels.has(nb)) {
        const newLvl = lvl + 1;
        levels.set(nb, newLvl);
        if (newLvl > maxLevel) maxLevel = newLvl;
        queue.push(nb);
      }
    });
  }
  return { levels, maxLevel };
}

function connectedComponents(nodes, adj) {
  const seen = new Set();
  let count = 0;
  for (const n of nodes) {
    if (seen.has(n.id)) continue;
    count++;
    const stack = [n.id];
    while (stack.length) {
      const x = stack.pop();
      if (seen.has(x)) continue;
      seen.add(x);
      adj.get(x)?.forEach(y => { if (!seen.has(y)) stack.push(y); });
    }
  }
  return count;
}

// ════════════════════════════════════════════════════════════
//  SHORTEST PATH
// ════════════════════════════════════════════════════════════
function shortestPath(adj, fromId, toId) {
  if (!adj.has(fromId) || !adj.has(toId)) return null;
  if (fromId === toId) return [fromId];
  const prev = new Map();
  const queue = [fromId];
  prev.set(fromId, null);
  while (queue.length) {
    const cur = queue.shift();
    if (cur === toId) {
      const path = [];
      let x = cur;
      while (x !== null) { path.unshift(x); x = prev.get(x); }
      return path;
    }
    adj.get(cur)?.forEach(nb => {
      if (!prev.has(nb)) {
        prev.set(nb, cur);
        queue.push(nb);
      }
    });
  }
  return null;
}

// ════════════════════════════════════════════════════════════
//  LEVEL → RADIUS
// ════════════════════════════════════════════════════════════
function levelRadius(level) {
  if (level == null || level === 0) return 0;
  return RING_BASE * Math.pow(RING_GROWTH, level - 1) * level;
}

// ════════════════════════════════════════════════════════════
//  D3 RENDERING
// ════════════════════════════════════════════════════════════
let svg, gZoom, gRings, gLinks, gNodes, simulation, zoomBehavior;

function initSvg() {
  svg = d3.select('#graph');
  svg.selectAll('*').remove();

  const defs = svg.append('defs');
  const mkArrow = (id, color) => {
    defs.append('marker')
      .attr('id', id)
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 14).attr('refY', 0)
      .attr('markerWidth', 6).attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', color);
  };
  mkArrow('arrow', '#444');
  mkArrow('arrow-hl', '#E8FF00');
  mkArrow('arrow-path', '#FF00B3');

  gZoom = svg.append('g').attr('class', 'zoom-layer');
  gRings = gZoom.append('g').attr('class', 'rings');
  gLinks = gZoom.append('g').attr('class', 'links');
  gNodes = gZoom.append('g').attr('class', 'nodes');

  zoomBehavior = d3.zoom()
    .scaleExtent([0.1, 8])
    .on('zoom', (e) => gZoom.attr('transform', e.transform));
  svg.call(zoomBehavior);
}

function drawLevelRings(cx, cy) {
  gRings.selectAll('*').remove();
  if (!state.selfId || !state.levels.has(state.selfId)) return;
  for (let lvl = 1; lvl <= state.maxLevel; lvl++) {
    const r = levelRadius(lvl);
    gRings.append('circle')
      .attr('class', 'level-ring')
      .attr('cx', cx).attr('cy', cy)
      .attr('r', r);
    gRings.append('text')
      .attr('class', 'level-label')
      .attr('x', cx + r)
      .attr('y', cy - 6)
      .attr('text-anchor', 'middle')
      .text(`lvl ${lvl}`);
  }
}

function nodeColor(d) {
  if (d.isSelf) return '#FF00B3';
  if (d.ghost) return 'transparent';
  if (d.mutual) return '#E8FF00';
  if (d.status === 'unfollowed') return '#444';
  return '#f5f5f5';
}
function nodeStroke(d) {
  if (d.isSelf) return '#FF00B3';
  if (d.ghost) return '#666';
  if (d.mutual) return '#E8FF00';
  if (d.status === 'unfollowed') return '#444';
  return '#f5f5f5';
}
function nodeRadius(d) {
  if (d.isSelf) return 18;
  const deg = state.adj.get(d.id)?.size || 1;
  return Math.min(12, 4 + Math.sqrt(deg) * 1.5);
}

function pinSelf() {
  if (!state.selfId) return null;
  const selfNode = state.nodeMap.get(state.selfId);
  if (!selfNode) return null;
  const { width, height } = svg.node().getBoundingClientRect();
  selfNode.fx = width / 2;
  selfNode.fy = height / 2;
  return selfNode;
}

function render() {
  const { width, height } = svg.node().getBoundingClientRect();
  const cx = width / 2, cy = height / 2;

  drawLevelRings(cx, cy);

  // ── LINKS ──
  const linkSel = gLinks.selectAll('line.link')
    .data(state.links, d => `${(d.source.id||d.source)}|${(d.target.id||d.target)}`);
  linkSel.exit().remove();
  const linkEnter = linkSel.enter().append('line')
    .attr('class', 'link')
    .attr('marker-end', 'url(#arrow)');
  const allLinks = linkEnter.merge(linkSel);

  // ── NODES ──
  const nodeSel = gNodes.selectAll('g.node').data(state.nodes, d => d.id);
  nodeSel.exit().remove();
  const nodeEnter = nodeSel.enter().append('g').attr('class', 'node');
  nodeEnter.append('circle');
  nodeEnter.append('text').attr('dy', 18);
  const allNodes = nodeEnter.merge(nodeSel);

  allNodes
    .classed('self', d => d.isSelf)
    .select('circle')
    .attr('r', nodeRadius)
    .attr('fill', nodeColor)
    .attr('stroke', nodeStroke)
    .attr('stroke-width', d => d.isSelf ? 3 : 1.5)
    .attr('stroke-dasharray', d => (d.ghost && !d.isSelf) ? '2,2' : null);
  allNodes.select('text')
    .attr('dy', d => d.isSelf ? 32 : 18)
    .text(d => d.id)
    .style('display', state.showLabels ? null : 'none');

  allNodes
    .on('click', (e, d) => { e.stopPropagation(); selectNode(d.id); })
    .on('mouseenter', (e, d) => showTooltip(e, d))
    .on('mousemove', moveTooltip)
    .on('mouseleave', hideTooltip)
    .call(d3.drag()
      .on('start', (e, d) => {
        if (!e.active) simulation.alphaTarget(0.3).restart();
        d.fx = d.x; d.fy = d.y;
      })
      .on('drag', (e, d) => { d.fx = e.x; d.fy = e.y; })
      .on('end', (e, d) => {
        if (!e.active) simulation.alphaTarget(0);
        if (!state.frozen && !d.isSelf) { d.fx = null; d.fy = null; }
      }));

  // ── SIMULATION ──
  if (simulation) simulation.stop();

  simulation = d3.forceSimulation(state.nodes)
    .force('link', d3.forceLink(state.links).id(d => d.id)
      .distance(l => {
        const sLvl = state.levels.get(l.source.id ?? l.source);
        const tLvl = state.levels.get(l.target.id ?? l.target);
        if (sLvl == null || tLvl == null) return 80;
        return Math.max(40, Math.abs(levelRadius(tLvl) - levelRadius(sLvl)));
      })
      .strength(0.4))
    .force('charge', d3.forceManyBody().strength(d => d.isSelf ? -800 : -180))
    .force('collide', d3.forceCollide().radius(d => nodeRadius(d) + 6));

  if (state.selfId && state.nodeMap.has(state.selfId)) {
    simulation.force('radial', d3.forceRadial(
      d => {
        const lvl = state.levels.get(d.id);
        return lvl != null ? levelRadius(lvl) : levelRadius(state.maxLevel + 2);
      },
      cx, cy
    ).strength(d => {
      if (d.isSelf) return 0; // pinned
      return state.levels.has(d.id) ? 0.85 : 0.05;
    }));
    pinSelf();
  } else {
    simulation.force('center', d3.forceCenter(cx, cy));
  }

  simulation.alpha(1).alphaDecay(0.025);

  simulation.on('tick', () => {
    allLinks
      .attr('x1', d => d.source.x).attr('y1', d => d.source.y)
      .attr('x2', d => d.target.x).attr('y2', d => d.target.y);
    allNodes.attr('transform', d => `translate(${d.x},${d.y})`);
  });

  svg.on('click', () => selectNode(null));
}

function applyHighlights() {
  const sel = state.selectedId;
  const path = state.pathIds;
  const filter = state.filter;
  const search = (document.getElementById('searchInput').value || '').toLowerCase().trim();

  gNodes.selectAll('g.node').each(function(d) {
    const el = d3.select(this);
    let dim = false;
    let highlight = false;

    if (filter !== 'all') {
      if (filter === 'mutual' && !d.mutual) dim = true;
      else if (filter === 'active' && d.status !== 'active') dim = true;
      else if (filter === 'unfollowed' && d.status !== 'unfollowed') dim = true;
      else if (filter === 'origin' && !d.ghost && state.outAdj.get(d.id)?.size === 0) dim = true;
    }
    if (search && !d.id.toLowerCase().includes(search)) dim = true;

    if (sel) {
      const neighbors = state.adj.get(sel) || new Set();
      if (d.id === sel || neighbors.has(d.id)) { dim = false; highlight = (d.id !== sel); }
      else dim = true;
    }
    const inPath = path.has(d.id);
    if (inPath) dim = false;

    el.classed('dim', dim);
    el.classed('highlight', highlight && !inPath);
    el.classed('selected', d.id === sel && !inPath);
    el.classed('path', inPath);
  });

  gLinks.selectAll('line.link').each(function(d) {
    const el = d3.select(this);
    const sId = d.source.id || d.source;
    const tId = d.target.id || d.target;
    let dim = false;
    let highlight = false;
    let inPath = false;

    if (path.size > 1) {
      const ordered = state.pathOrdered || [];
      for (let i = 0; i < ordered.length - 1; i++) {
        const a = ordered[i], b = ordered[i+1];
        if ((sId === a && tId === b) || (sId === b && tId === a)) { inPath = true; break; }
      }
    }

    if (sel) {
      if (sId === sel || tId === sel) highlight = true;
      else dim = true;
    }
    if (filter !== 'all' || search) {
      const sNode = gNodes.selectAll('g.node').filter(n => n.id === sId).node();
      const tNode = gNodes.selectAll('g.node').filter(n => n.id === tId).node();
      const sDim = sNode && d3.select(sNode).classed('dim');
      const tDim = tNode && d3.select(tNode).classed('dim');
      if (sDim || tDim) dim = true;
    }
    if (inPath) { dim = false; highlight = false; }

    el.classed('dim', dim);
    el.classed('highlight', highlight && !inPath);
    el.classed('path', inPath);
    el.attr('marker-end', inPath ? 'url(#arrow-path)' : (highlight ? 'url(#arrow-hl)' : 'url(#arrow)'));
  });
}

// ════════════════════════════════════════════════════════════
//  TOOLTIP
// ════════════════════════════════════════════════════════════
const tooltipEl = document.getElementById('tooltip');
function showTooltip(e, d) {
  const inDeg = state.inAdj.get(d.id)?.size || 0;
  const outDeg = state.outAdj.get(d.id)?.size || 0;
  const lvl = state.levels.get(d.id);
  const lvlStr = lvl != null ? `lvl ${lvl}` : 'unreachable';
  const prefix = d.isSelf ? '◉ ' : '@';
  const typeLabel = d.isSelf
    ? '[ self · centro ]'
    : (d.ghost ? '[ origin ghost ]' : (d.status || '—'));
  tooltipEl.innerHTML = `
    <div class="tooltip-name">${prefix}${d.id}</div>
    <div>${typeLabel}${d.mutual ? ' · mutual' : ''}</div>
    <div style="color:var(--muted);margin-top:2px;">in ${inDeg} · out ${outDeg} · ${lvlStr}</div>
  `;
  tooltipEl.classList.add('show');
  moveTooltip(e);
}
function moveTooltip(e) {
  tooltipEl.style.left = (e.pageX + 14) + 'px';
  tooltipEl.style.top = (e.pageY + 14) + 'px';
}
function hideTooltip() { tooltipEl.classList.remove('show'); }

// ════════════════════════════════════════════════════════════
//  SELECT NODE
// ════════════════════════════════════════════════════════════
function selectNode(id) {
  state.selectedId = id;
  renderNodeInfo();
  applyHighlights();
}

function renderNodeInfo() {
  const box = document.getElementById('nodeInfo');
  if (!state.selectedId) {
    box.innerHTML = '<div class="node-info-empty">click any node in the graph</div>';
    return;
  }
  const d = state.nodeMap.get(state.selectedId);
  if (!d) { box.innerHTML = '<div class="node-info-empty">node not found</div>'; return; }

  const ins = Array.from(state.inAdj.get(d.id) || []);
  const outs = Array.from(state.outAdj.get(d.id) || []);
  const lvl = state.levels.get(d.id);

  let html = `<div class="node-info-name ${d.isSelf ? 'is-self' : ''}">${d.id}</div>`;
  html += '<dl>';

  if (d.isSelf) {
    html += `<dt>type</dt><dd class="pink">◉ self · center</dd>`;
    html += `<dt>level</dt><dd class="accent">0</dd>`;
    html += `<dt>status</dt><dd>${d.status||'—'}</dd>`;
    if (d.profile_followers) html += `<dt>followers</dt><dd>${d.profile_followers}</dd>`;
    if (d.profile_following) html += `<dt>following</dt><dd>${d.profile_following}</dd>`;
    if (d.profile_ratio) html += `<dt>ratio</dt><dd>${d.profile_ratio}</dd>`;
    if (d.stand_type) html += `<dt>stand</dt><dd>${d.stand_type}</dd>`;
    html += `<dt>spawned</dt><dd class="accent">${outs.length}</dd>`;
  } else if (d.ghost) {
    html += `<dt>type</dt><dd class="accent">origin ghost</dd>`;
    html += `<dt>level</dt><dd>${lvl != null ? lvl : '—'}</dd>`;
    html += `<dt>incoming</dt><dd>${ins.length}</dd>`;
    html += `<dt>spawned</dt><dd class="accent">${outs.length}</dd>`;
  } else {
    html += `<dt>status</dt><dd class="${d.status==='active'?'accent':''}">${d.status||'—'}</dd>`;
    html += `<dt>level</dt><dd>${lvl != null ? lvl : '—'}</dd>`;
    html += `<dt>mutual</dt><dd class="${d.mutual?'accent':''}">${d.mutual?'yes':'no'}</dd>`;
    html += `<dt>origen</dt><dd class="pink">${d.origen||'—'}</dd>`;
    if (d.followed_at) html += `<dt>followed</dt><dd>${(d.followed_at||'').slice(0,10)}</dd>`;
    if (d.days_active !== '') html += `<dt>days</dt><dd>${d.days_active}</dd>`;
    if (d.profile_followers) html += `<dt>followers</dt><dd>${d.profile_followers}</dd>`;
    if (d.profile_following) html += `<dt>following</dt><dd>${d.profile_following}</dd>`;
    if (d.profile_ratio) html += `<dt>ratio</dt><dd>${d.profile_ratio}</dd>`;
    if (d.stand_type) html += `<dt>stand</dt><dd>${d.stand_type}</dd>`;
    html += `<dt>incoming</dt><dd>${ins.length}</dd>`;
    html += `<dt>outgoing</dt><dd class="accent">${outs.length}</dd>`;
  }
  html += '</dl>';

  if (ins.length || outs.length) {
    html += '<div class="neighbors">';
    if (ins.length) {
      html += '<div class="neighbors-title">← incoming (origenes)</div>';
      ins.slice(0, 30).forEach(n => html += `<span class="neighbor-chip in" data-jump="${n}">@${n}</span>`);
      if (ins.length > 30) html += `<span class="neighbor-chip">+${ins.length-30}</span>`;
    }
    if (outs.length) {
      html += '<div class="neighbors-title" style="margin-top:8px;">→ outgoing (spawned)</div>';
      outs.slice(0, 30).forEach(n => html += `<span class="neighbor-chip out" data-jump="${n}">@${n}</span>`);
      if (outs.length > 30) html += `<span class="neighbor-chip">+${outs.length-30}</span>`;
    }
    html += '</div>';
  }

  box.innerHTML = html;
  box.querySelectorAll('[data-jump]').forEach(el => {
    el.addEventListener('click', () => selectNode(el.getAttribute('data-jump')));
  });
}

// ════════════════════════════════════════════════════════════
//  SEARCH
// ════════════════════════════════════════════════════════════
function runSearch() {
  const q = document.getElementById('searchInput').value.toLowerCase().trim();
  const box = document.getElementById('searchResults');
  if (!q) { box.innerHTML = ''; applyHighlights(); return; }

  const filter = state.filter;
  const matches = state.nodes.filter(n => {
    if (!n.id.toLowerCase().includes(q)) return false;
    if (filter === 'mutual') return n.mutual;
    if (filter === 'active') return n.status === 'active';
    if (filter === 'unfollowed') return n.status === 'unfollowed';
    if (filter === 'origin') return n.ghost || (state.outAdj.get(n.id)?.size > 0);
    return true;
  }).slice(0, 50);

  box.innerHTML = matches.map(n => {
    const tag = n.isSelf ? 'self' : (n.ghost ? 'origin' : (n.mutual ? 'mutual' : (n.status||'—')));
    const prefix = n.isSelf ? '◉' : '@';
    return `<div class="search-result" data-id="${n.id}">
      <span>${prefix}${n.id}</span><span class="badge">${tag}</span>
    </div>`;
  }).join('');
  box.querySelectorAll('.search-result').forEach(el => {
    el.addEventListener('click', () => {
      const id = el.getAttribute('data-id');
      selectNode(id);
      focusNode(id);
    });
  });
  applyHighlights();
}

function focusNode(id) {
  const n = state.nodeMap.get(id);
  if (!n || n.x == null) return;
  const { width, height } = svg.node().getBoundingClientRect();
  const k = 1.6;
  const t = d3.zoomIdentity.translate(width/2 - n.x*k, height/2 - n.y*k).scale(k);
  svg.transition().duration(500).call(zoomBehavior.transform, t);
}

// ════════════════════════════════════════════════════════════
//  PATH FINDING
// ════════════════════════════════════════════════════════════
function tracePath() {
  const fromId = document.getElementById('pathFrom').value.trim();
  const toId   = document.getElementById('pathTo').value.trim();
  const out = document.getElementById('pathResult');

  if (!fromId || !toId) {
    out.innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
    return;
  }
  if (!state.nodeMap.has(fromId)) { out.innerHTML = `<div class="path-fail">@${fromId} not in graph</div>`; return; }
  if (!state.nodeMap.has(toId))   { out.innerHTML = `<div class="path-fail">@${toId} not in graph</div>`; return; }

  const path = shortestPath(state.adj, fromId, toId);
  if (!path) {
    out.innerHTML = `<div class="path-fail">no path · disconnected</div>`;
    state.pathIds = new Set();
    state.pathOrdered = [];
    applyHighlights();
    return;
  }

  state.pathIds = new Set(path);
  state.pathOrdered = path;

  const hops = path.length - 1;
  let html = `<div class="path-success">${hops} hop${hops!==1?'s':''} · ${path.length} nodes</div>`;
  path.forEach((id, i) => {
    const n = state.nodeMap.get(id);
    const prefix = n?.isSelf ? '◉ ' : '@';
    html += `<div class="path-step" data-id="${id}">
      <span class="num">${String(i+1).padStart(2,'0')}</span><span>${prefix}${id}</span>
    </div>`;
    if (i < path.length - 1) {
      const a = path[i], b = path[i+1];
      const forward = state.outAdj.get(a)?.has(b);
      html += `<div class="path-arrow">${forward ? '↓ spawned' : '↑ origen of'}</div>`;
    }
  });
  out.innerHTML = html;
  out.querySelectorAll('.path-step').forEach(el => {
    el.addEventListener('click', () => {
      const id = el.getAttribute('data-id');
      selectNode(id);
      focusNode(id);
    });
  });
  applyHighlights();
}

function clearPath() {
  document.getElementById('pathFrom').value = '';
  document.getElementById('pathTo').value = '';
  state.pathIds = new Set();
  state.pathOrdered = [];
  document.getElementById('pathResult').innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
  applyHighlights();
}

// ════════════════════════════════════════════════════════════
//  STATS
// ════════════════════════════════════════════════════════════
function renderStats() {
  document.getElementById('statNodes').textContent = state.nodes.length;
  document.getElementById('statEdges').textContent = state.links.length;
  const mutuals = state.nodes.filter(n => n.mutual).length;
  document.getElementById('statMutuals').textContent = mutuals;
  let originCount = 0;
  state.outAdj.forEach((s) => { if (s.size > 0) originCount++; });
  document.getElementById('statOrigins').textContent = originCount;
  document.getElementById('statComponents').textContent = connectedComponents(state.nodes, state.adj);
  const avgDeg = state.nodes.length ? (2 * state.links.length / state.nodes.length).toFixed(2) : 0;
  document.getElementById('statDegree').textContent = avgDeg;
}

// ════════════════════════════════════════════════════════════
//  LOAD CSV
// ════════════════════════════════════════════════════════════
function loadCSVText(text, filename) {
  try {
    const parsed = parseCSV(text);
    if (!parsed.headers.includes('username')) {
      toast('CSV missing "username" column');
      return;
    }
    const { nodes, links, selfId } = buildGraph(parsed.rows);
    if (!nodes.length) { toast('no nodes parsed'); return; }

    state.nodes = nodes;
    state.links = links;
    state.selfId = selfId;
    const idx = indexGraph(nodes, links);
    state.adj = idx.adj;
    state.outAdj = idx.outAdj;
    state.inAdj = idx.inAdj;
    state.nodeMap = idx.nodeMap;

    const lvlRes = computeLevels(state.adj, selfId);
    state.levels = lvlRes.levels;
    state.maxLevel = lvlRes.maxLevel;

    state.selectedId = null;
    state.pathIds = new Set();
    state.pathOrdered = [];

    document.getElementById('emptyState').classList.add('hidden');
    document.getElementById('app').classList.remove('hidden');
    const fileLabel = filename || 'csv loaded';
    document.getElementById('metaFile').textContent =
      selfId ? `${fileLabel} · self: @${selfId}` : `${fileLabel} · no self detected`;

    initSvg();
    render();
    renderStats();
    renderNodeInfo();
    runSearch();

    if (!selfId) {
      toast('no user with origen=self · using default layout');
    }

    setTimeout(applyHighlights, 100);
  } catch (err) {
    console.error(err);
    toast('error parsing CSV: ' + err.message);
  }
}

// ════════════════════════════════════════════════════════════
//  TOAST
// ════════════════════════════════════════════════════════════
function toast(msg) {
  const el = document.getElementById('toast');
  el.textContent = msg;
  el.classList.add('show');
  setTimeout(() => el.classList.remove('show'), 3500);
}

// ════════════════════════════════════════════════════════════
//  EVENTS
// ════════════════════════════════════════════════════════════
function setupEvents() {
  const dropzone = document.getElementById('dropzone');
  const fileInput = document.getElementById('fileInput');

  dropzone.addEventListener('click', () => fileInput.click());
  fileInput.addEventListener('change', (e) => {
    const f = e.target.files[0]; if (!f) return;
    f.text().then(t => loadCSVText(t, f.name));
  });

  ['dragenter', 'dragover'].forEach(ev =>
    dropzone.addEventListener(ev, e => { e.preventDefault(); dropzone.classList.add('drag'); }));
  ['dragleave', 'drop'].forEach(ev =>
    dropzone.addEventListener(ev, e => { e.preventDefault(); dropzone.classList.remove('drag'); }));
  dropzone.addEventListener('drop', e => {
    const f = e.dataTransfer.files[0]; if (!f) return;
    f.text().then(t => loadCSVText(t, f.name));
  });

  window.addEventListener('dragover', e => e.preventDefault());
  window.addEventListener('drop', e => {
    e.preventDefault();
    if (document.getElementById('app').classList.contains('hidden')) return;
    const f = e.dataTransfer.files[0]; if (!f) return;
    f.text().then(t => loadCSVText(t, f.name));
  });

  document.getElementById('reloadBtn').addEventListener('click', () => fileInput.click());

  document.getElementById('searchInput').addEventListener('input', runSearch);

  document.querySelectorAll('.chip').forEach(c => {
    c.addEventListener('click', () => {
      document.querySelectorAll('.chip').forEach(x => x.classList.remove('active'));
      c.classList.add('active');
      state.filter = c.getAttribute('data-filter');
      runSearch();
      applyHighlights();
    });
  });

  document.getElementById('pathBtn').addEventListener('click', tracePath);
  document.getElementById('pathClearBtn').addEventListener('click', clearPath);
  document.getElementById('pathFrom').addEventListener('keydown', e => { if (e.key === 'Enter') tracePath(); });
  document.getElementById('pathTo').addEventListener('keydown', e => { if (e.key === 'Enter') tracePath(); });

  document.getElementById('resetBtn').addEventListener('click', () => {
    svg.transition().duration(400).call(zoomBehavior.transform, d3.zoomIdentity);
    if (simulation) simulation.alpha(0.6).restart();
  });
  document.getElementById('freezeBtn').addEventListener('click', (e) => {
    state.frozen = !state.frozen;
    e.target.classList.toggle('active', state.frozen);
    if (state.frozen) {
      state.nodes.forEach(n => { n.fx = n.x; n.fy = n.y; });
      simulation?.stop();
    } else {
      state.nodes.forEach(n => {
        if (!n.isSelf) { n.fx = null; n.fy = null; }
      });
      pinSelf();
      simulation?.alpha(0.3).restart();
    }
  });
  document.getElementById('labelsBtn').addEventListener('click', (e) => {
    state.showLabels = !state.showLabels;
    e.target.classList.toggle('active', state.showLabels);
    gNodes.selectAll('g.node text').style('display', state.showLabels ? null : 'none');
  });
  const recenterBtn = document.getElementById('recenterBtn');
  if (recenterBtn) {
    recenterBtn.addEventListener('click', () => {
      const selfNode = pinSelf();
      if (!selfNode) { toast('no self node in graph'); return; }
      const { width, height } = svg.node().getBoundingClientRect();
      const k = 1;
      const t = d3.zoomIdentity.translate(width/2 - selfNode.x*k, height/2 - selfNode.y*k).scale(k);
      svg.transition().duration(500).call(zoomBehavior.transform, t);
      simulation?.alpha(0.5).restart();
    });
  }

  window.addEventListener('resize', () => {
    if (!simulation) return;
    const { width, height } = svg.node().getBoundingClientRect();
    drawLevelRings(width/2, height/2);
    if (state.selfId && state.nodeMap.has(state.selfId)) {
      simulation.force('radial', d3.forceRadial(
        d => {
          const lvl = state.levels.get(d.id);
          return lvl != null ? levelRadius(lvl) : levelRadius(state.maxLevel + 2);
        },
        width/2, height/2
      ).strength(d => {
        if (d.isSelf) return 0;
        return state.levels.has(d.id) ? 0.85 : 0.05;
      }));
      pinSelf();
    } else {
      simulation.force('center', d3.forceCenter(width/2, height/2));
    }
    simulation.alpha(0.3).restart();
  });
}

setupEvents();
