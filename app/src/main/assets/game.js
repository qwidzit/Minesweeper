'use strict';
(() => {

const $ = id => document.getElementById(id);

const MIN_SIZE = 4, MAX_COLS = 30, MAX_ROWS = 40;
const DEFAULTS = { cols: 9, rows: 9, mines: 30 };
// The first dig keeps its 3x3 neighbourhood mine-free, so that many cells can never hold a mine.
const SAFE = 9;

const C = {
  bg: '#14171d',
  hidden: '#5a6887',
  hiddenLip: '#3b4660',
  open: '#dfe3ea',
  boom: '#ff5a5f',
  ink: '#151821',
  flag: '#ff4046',
  hint: '#3ecf8e',
};
// The original hues, with 1 and 3 brightened so they stand apart from the darker 4 and 5 at a glance
const NUM_COLORS = [null, '#1447e6', '#008a1c', '#e0101a', '#000080', '#800000', '#008080', '#000000', '#6e6e6e'];

// ---------- storage ----------
// Inside the app the archive is a file written through the Android bridge;
// in a plain browser it falls back to localStorage.

const STORE_KEY = 'minesweeper-archive';

function loadData() {
  let d = null;
  try {
    const raw = window.Android ? window.Android.load() : localStorage.getItem(STORE_KEY);
    d = raw ? JSON.parse(raw) : null;
  } catch (e) { d = null; }
  if (!d || !Array.isArray(d.entries)) d = { v: 1, nextId: 1, tapRestart: true, entries: [] };
  if (!d.bests) d.bests = {};   // best winning time per setup, keyed by "cols x rows x mines"
  for (const e of d.entries) {
    if (e.best != null) continue;
    const wins = e.results.filter(r => r.outcome === 'win').map(r => r.ms);
    if (wins.length) e.best = Math.min(...wins);
  }
  return d;
}

function saveData() {
  const s = JSON.stringify(data);
  try {
    if (window.Android) window.Android.save(s);
    else localStorage.setItem(STORE_KEY, s);
  } catch (e) { /* storage unavailable: keep playing */ }
}

// ---------- state ----------

const data = loadData();
let cfg = { ...DEFAULTS };
let cfgChosen = false;
let g = null;          // current game
let prev = null;       // the game that was on screen before the last restart
let flagMode = false;
let replayId = null;   // archive entry being replayed, if any
let cellPx = 0;
let menuAt = 0, menuGame = null;
let viewing = null;    // { entryId, index } of the result open in the viewer

const elSetup = $('setup'), elGame = $('game'), elMenu = $('menu'),
      elArchive = $('archive'), elViewer = $('viewer');
const board = $('board'), stage = $('stage');

// ---------- game logic (same rules as the original pygame version) ----------

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
const maxMines = (cols, rows) => cols * rows - SAFE;
const randInt = n => Math.floor(Math.random() * n);

function countNeighbours(game) {
  const { rows, cols, field } = game;
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      if (field[r * cols + c] === -1) continue;
      let cnt = 0;
      for (let dr = -1; dr <= 1; dr++) {
        for (let dc = -1; dc <= 1; dc++) {
          const nr = r + dr, nc = c + dc;
          if (nr >= 0 && nr < rows && nc >= 0 && nc < cols && field[nr * cols + nc] === -1) cnt++;
        }
      }
      field[r * cols + c] = cnt;
    }
  }
}

function makeGame(entry) {
  const rows = entry ? entry.rows : cfg.rows;
  const cols = entry ? entry.cols : cfg.cols;
  const n = rows * cols;
  const game = {
    rows, cols,
    mines: entry ? entry.mines : cfg.mines,
    field: new Int8Array(n),
    revealed: new Uint8Array(n),
    flagged: new Uint8Array(n),
    over: false, win: false,
    replay: !!entry,
    firstClick: !entry,      // a replayed field already has its mines
    started: false,          // true once the first dig has happened
    hit: -1,                 // the mine that ended the game
    start: entry ? entry.start : -1,
    entryId: entry ? entry.id : null,
    resultSaved: false,
    t0: 0, pausedMs: 0, ms: 0, endedAt: 0,
    isBest: false, bestBefore: null,
  };
  if (entry) {
    for (let i = 0; i < n; i++) if (entry.layout[i] === '1') game.field[i] = -1;
    countNeighbours(game);
  }
  return game;
}

function placeMines(game, sr, sc) {
  const { rows, cols, field } = game;
  field.fill(0);
  let m = 0;
  while (m < game.mines) {
    const r = randInt(rows), c = randInt(cols);
    if (field[r * cols + c] === -1 || (Math.abs(r - sr) <= 1 && Math.abs(c - sc) <= 1)) continue;
    field[r * cols + c] = -1;
    m++;
  }
  countNeighbours(game);
}

function reveal(game, r, c) {
  const { rows, cols, field, revealed, flagged } = game;
  const stack = [r * cols + c];
  while (stack.length) {
    const i = stack.pop();
    if (revealed[i] || flagged[i]) continue;
    revealed[i] = 1;
    if (field[i] !== 0) continue;
    const cr = Math.floor(i / cols), cc = i % cols;
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        const nr = cr + dr, nc = cc + dc;
        if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) stack.push(nr * cols + nc);
      }
    }
  }
}

function checkWin(game) {
  for (let i = 0; i < game.field.length; i++) {
    if (game.field[i] !== -1 && !game.revealed[i]) return false;
  }
  return true;
}

function tapCell(r, c) {
  const i = r * g.cols + c;
  if (flagMode) {
    if (!g.revealed[i]) g.flagged[i] ^= 1;
  } else if (!g.flagged[i]) {
    if (g.firstClick) {
      g.firstClick = false;
      placeMines(g, r, c);
      g.start = i;
      reveal(g, r, c);
    } else if (g.field[i] === -1) {
      for (let k = 0; k < g.field.length; k++) if (g.field[k] === -1) g.revealed[k] = 1;
      g.over = true;
      g.hit = i;
    } else {
      reveal(g, r, c);
    }
    if (!g.started) { g.started = true; g.t0 = Date.now(); }
    if (!g.over) g.win = checkWin(g);
    if (g.over || g.win) {
      g.endedAt = Date.now();
      g.ms = g.endedAt - g.t0 - g.pausedMs;
      if (g.win) recordBest(g);
    }
  }
  render();
}

const setupKey = game => `${game.cols}x${game.rows}x${game.mines}`;

// Best time to compare against: the field's own when replaying, otherwise the setup's.
function bestFor(game) {
  if (!game.replay) return data.bests[setupKey(game)] ?? null;
  const e = entryById(game.entryId);
  return e && e.best != null ? e.best : null;
}

function recordBest(game) {
  const e = game.entryId != null ? entryById(game.entryId) : null;
  if (game.replay && !e) return;   // the replayed field was deleted meanwhile
  game.bestBefore = bestFor(game);
  game.isBest = game.bestBefore == null || game.ms < game.bestBefore;
  if (!game.replay && game.isBest) data.bests[setupKey(game)] = game.ms;
  if (e && (e.best == null || game.ms < e.best)) e.best = game.ms;
  saveData();
}

function replayEntry() {
  if (replayId == null) return null;
  const e = entryById(replayId);
  if (!e) replayId = null;
  return e;
}

function restart() {
  if (g.started) prev = g;
  const old = g;
  g = makeGame(replayEntry());
  if (g.rows !== old.rows || g.cols !== old.cols) fitBoard();
  render();
}

// ---------- drawing ----------

function tile(ctx, x, y, w, h, rad, color) {
  ctx.fillStyle = color;
  if (rad > 0 && ctx.roundRect) {
    ctx.beginPath();
    ctx.roundRect(x, y, w, h, rad);
    ctx.fill();
  } else {
    ctx.fillRect(x, y, w, h);
  }
}

function drawMine(ctx, cx, cy, s) {
  const R = s * 0.22;
  ctx.fillStyle = C.ink;
  ctx.beginPath();
  ctx.arc(cx, cy, R, 0, Math.PI * 2);
  ctx.fill();
  if (s < 10) return;
  ctx.strokeStyle = C.ink;
  ctx.lineWidth = Math.max(1, s * 0.075);
  ctx.lineCap = 'round';
  ctx.beginPath();
  for (let k = 0; k < 4; k++) {
    const a = k * Math.PI / 4, len = (k % 2 ? 0.29 : 0.34) * s;
    ctx.moveTo(cx - Math.cos(a) * len, cy - Math.sin(a) * len);
    ctx.lineTo(cx + Math.cos(a) * len, cy + Math.sin(a) * len);
  }
  ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,0.85)';
  ctx.beginPath();
  ctx.arc(cx - R * 0.35, cy - R * 0.35, R * 0.24, 0, Math.PI * 2);
  ctx.fill();
}

function drawFlag(ctx, cx, cy, s) {
  if (s < 10) {
    ctx.fillStyle = C.flag;
    ctx.fillRect(cx - s * 0.25, cy - s * 0.25, s * 0.5, s * 0.5);
    return;
  }
  const px = cx + s * 0.07;
  ctx.fillStyle = C.ink;
  ctx.fillRect(px - s * 0.035, cy - s * 0.28, s * 0.07, s * 0.52);
  ctx.fillRect(cx - s * 0.2, cy + s * 0.2, s * 0.42, s * 0.08);
  ctx.fillStyle = C.flag;
  ctx.beginPath();
  ctx.moveTo(px + s * 0.035, cy - s * 0.3);
  ctx.lineTo(px - s * 0.31, cy - s * 0.14);
  ctx.lineTo(px + s * 0.035, cy + s * 0.02);
  ctx.closePath();
  ctx.fill();
}

function drawCross(ctx, cx, cy, s) {
  const d = s * 0.31;
  ctx.strokeStyle = C.ink;
  ctx.lineWidth = Math.max(1, s * 0.055);
  ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.moveTo(cx - d, cy - d); ctx.lineTo(cx + d, cy + d);
  ctx.moveTo(cx + d, cy - d); ctx.lineTo(cx - d, cy + d);
  ctx.stroke();
}

function drawCell(ctx, v, i, x, y, s) {
  const gap = s >= 14 ? Math.max(1, Math.round(s * 0.035)) : (s >= 6 ? 1 : 0);
  const w = s - 2 * gap, x0 = x + gap, y0 = y + gap;
  const rad = s >= 18 ? Math.round(s * 0.13) : 0;
  const cx = x + s / 2, cy = y + s / 2;

  if (v.revealed[i]) {
    const n = v.field[i];
    tile(ctx, x0, y0, w, w, rad, n === -1 && i === v.hit ? C.boom : C.open);
    if (n === -1) {
      drawMine(ctx, cx, cy, s);
    } else if (n > 0 && s >= 6) {
      ctx.fillStyle = NUM_COLORS[n];
      ctx.fillText(String(n), cx, cy + numDy);
    }
    return;
  }

  // Unopened tile: a raised key with a darker lip along the bottom
  const lip = s >= 14 ? Math.max(1, Math.round(s * 0.09)) : 0;
  if (lip) tile(ctx, x0, y0, w, w, rad, C.hiddenLip);
  tile(ctx, x0, y0, w, w - lip, rad, C.hidden);
  const fy = cy - lip / 2;
  if (v.flagged[i]) {
    drawFlag(ctx, cx, fy, s);
    if (v.over && v.field[i] !== -1) drawCross(ctx, cx, fy, s);   // flag on a cell with no mine
  } else if (i === v.hint) {
    ctx.strokeStyle = C.hint;
    ctx.lineWidth = Math.max(1, s * 0.08);
    ctx.beginPath();
    ctx.arc(cx, fy, s * 0.2, 0, Math.PI * 2);
    ctx.stroke();
  }
}

const NUM_SIZE = 0.5;   // digit height as a share of the cell
let numDy = 0;

// v: { rows, cols, field, revealed, flagged, over, hit, hint }, s: cell size in device pixels
function paint(cv, v, s) {
  const ctx = cv.getContext('2d');
  ctx.fillStyle = C.bg;
  ctx.fillRect(0, 0, cv.width, cv.height);
  ctx.font = `700 ${Math.round(s * NUM_SIZE)}px Roboto, system-ui, "Segoe UI", sans-serif`;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'alphabetic';
  numDy = ctx.measureText('8').actualBoundingBoxAscent / 2;   // centres the digits exactly
  for (let r = 0; r < v.rows; r++) {
    for (let c = 0; c < v.cols; c++) {
      drawCell(ctx, v, r * v.cols + c, c * s, r * s, s);
    }
  }
}

// Sizes a canvas to whole device pixels per cell so tile edges stay sharp. Returns the cell size.
function fitCanvas(cv, cols, rows, cssW, cssH, maxCellCss) {
  const dpr = window.devicePixelRatio || 1;
  let s = Math.floor(Math.min(cssW * dpr / cols, cssH * dpr / rows));
  s = Math.max(2, Math.min(s, Math.floor(maxCellCss * dpr)));
  cv.width = cols * s;
  cv.height = rows * s;
  cv.style.width = cv.width / dpr + 'px';
  cv.style.height = cv.height / dpr + 'px';
  return s;
}

function fitBoard() {
  cellPx = fitCanvas(board, g.cols, g.rows, stage.clientWidth - 12, stage.clientHeight - 8, 72);
}

const MODE_DIG = 'DIG';
const MODE_FLAG = '<svg viewBox="0 0 24 24"><rect x="13" y="3" width="2.2" height="16" fill="#23180a"/>' +
  '<rect x="6" y="18.5" width="13" height="2.5" fill="#23180a"/><path d="M15.2 2.5L4.5 7.5l10.7 5z" fill="#c8102e"/></svg>FLAG';

function render() {
  paint(board, {
    rows: g.rows, cols: g.cols, field: g.field, revealed: g.revealed, flagged: g.flagged,
    over: g.over, hit: g.hit,
    hint: g.replay && !g.started ? g.start : -1,   // where this field was first opened
  }, cellPx);

  let flags = 0;
  for (let i = 0; i < g.flagged.length; i++) flags += g.flagged[i];
  $('minesLeft').textContent = g.mines - flags;

  const st = $('status');
  const again = data.tapRestart ? ' · tap to restart' : '';
  if (g.over) { st.className = 'lost'; st.textContent = 'Game over' + again; }
  else if (g.win) {
    // the only place the timer is ever shown
    st.className = 'won';
    st.textContent = 'Won in ' + fmtTime(g.ms) +
      (g.isBest ? ' · new best!' : g.bestBefore != null ? ' · best ' + fmtTime(g.bestBefore) : '');
  } else {
    st.className = '';
    const e = g.replay ? entryById(g.entryId) : null;
    const best = bestFor(g);
    st.textContent = (e ? 'Replay · ' + e.name : `${g.cols}×${g.rows} · ${g.mines} mines`) +
      (best != null ? ' · best ' + fmtTime(best) : '');
  }

  const mode = $('btnMode');
  mode.className = flagMode ? 'flag' : '';
  mode.innerHTML = flagMode ? MODE_FLAG : MODE_DIG;
}

// ---------- archive data ----------

const entryById = id => data.entries.find(e => e.id === id) || null;

function bits(arr, test) {
  let s = '';
  for (let i = 0; i < arr.length; i++) s += test(arr[i]) ? '1' : '0';
  return s;
}
const fromBits = str => Uint8Array.from(str, ch => ch === '1' ? 1 : 0);

// The game the archive button acts on: the current one, or - right after a restart,
// before the new game's first dig - the one that was just on screen.
const archiveTarget = () => g.started ? g : (prev || g);

function archiveState(t) {
  if (!t.started) return 'none';
  const ended = t.over || t.win;
  if (t.entryId == null || !entryById(t.entryId)) return ended ? 'field+result' : 'field';
  return ended && !t.resultSaved ? 'result' : 'done';
}

function doArchive() {
  const t = archiveTarget();
  const state = archiveState(t);
  if (state === 'none' || state === 'done') return;
  let e = t.entryId != null ? entryById(t.entryId) : null;
  if (!e) {
    const id = data.nextId++;
    e = {
      id, name: 'Field ' + id,
      rows: t.rows, cols: t.cols, mines: t.mines,
      layout: bits(t.field, x => x === -1),
      start: t.start,
      created: Date.now(),
      results: [],
    };
    data.entries.push(e);
    t.entryId = id;
    t.resultSaved = false;
  }
  if ((t.over || t.win) && !t.resultSaved) {
    e.results.push({
      date: t.endedAt,
      outcome: t.win ? 'win' : 'loss',
      revealed: bits(t.revealed, x => x),
      flagged: bits(t.flagged, x => x),
      hit: t.hit,
      ms: t.ms,
    });
    if (t.win && (e.best == null || t.ms < e.best)) e.best = t.ms;
    t.resultSaved = true;
  }
  saveData();
  updateMenu();
}

// ---------- pause menu ----------

function updateMenu() {
  const t = archiveTarget();
  const which = t === g ? 'this' : 'previous';
  const btn = $('mArchive');
  const state = archiveState(t);
  btn.disabled = state === 'none' || state === 'done';
  btn.textContent = {
    'none': 'Nothing to archive yet',
    'field': `Archive ${which} field`,
    'field+result': `Archive ${which} field + result`,
    'result': `Save ${which} result to archive`,
    'done': 'Archived ✓',
  }[state];
  $('mOpenArchive').textContent = `Open archive (${data.entries.length})`;
  $('mExitReplay').hidden = replayId == null;
  $('mTapRestart').textContent = 'Tap board to restart after a game ends: ' + (data.tapRestart ? 'ON' : 'OFF');
}

function openMenu() {
  menuAt = Date.now();
  menuGame = g;
  updateMenu();
  elMenu.hidden = false;
}

function closeMenu() {
  if (elMenu.hidden) return;
  elMenu.hidden = true;
  // time spent in the menu does not count towards the result's time
  if (menuGame === g && g.started && !g.over && !g.win) g.pausedMs += Date.now() - menuAt;
}

// ---------- setup screen ----------

const inCols = $('inCols'), inRows = $('inRows'), inMines = $('inMines');

function readSetup() {
  const num = (el, fallback) => { const v = parseInt(el.value, 10); return Number.isNaN(v) ? fallback : v; };
  const cols = clamp(num(inCols, DEFAULTS.cols), MIN_SIZE, MAX_COLS);
  const rows = clamp(num(inRows, DEFAULTS.rows), MIN_SIZE, MAX_ROWS);
  const mines = clamp(num(inMines, DEFAULTS.mines), 1, maxMines(cols, rows));
  return { cols, rows, mines };
}

function syncSetup() {
  const v = readSetup();
  inCols.value = v.cols;
  inRows.value = v.rows;
  inMines.value = v.mines;
  $('setupHint').textContent =
    `Width ${MIN_SIZE}–${MAX_COLS}, height ${MIN_SIZE}–${MAX_ROWS}. ` +
    `Up to ${maxMines(v.cols, v.rows)} mines fit a ${v.cols}×${v.rows} field.`;
  const best = data.bests[setupKey(v)];
  $('setupBest').textContent = best != null ? 'Best time for this setup: ' + fmtTime(best) : '';
}

function showSetup(values) {
  inCols.value = values.cols;
  inRows.value = values.rows;
  inMines.value = values.mines;
  syncSetup();
  $('btnSetupArchive').textContent = `Archive (${data.entries.length})`;
  elMenu.hidden = true;
  elGame.hidden = true;
  elSetup.hidden = false;
}

function showGame() {
  elSetup.hidden = true;
  elMenu.hidden = true;
  elArchive.hidden = true;
  elViewer.hidden = true;
  elGame.hidden = false;
  fitBoard();
  render();
}

function startConfigured() {
  cfg = readSetup();
  cfgChosen = true;
  replayId = null;
  if (g && g.started) prev = g;
  g = makeGame(null);
  showGame();
}

function startReplay(id) {
  if (!entryById(id)) return;
  if (g && g.started) prev = g;
  replayId = id;
  g = makeGame(entryById(id));
  showGame();
}

function exitReplay() {
  replayId = null;
  if (!cfgChosen) { showSetup(DEFAULTS); return; }
  if (g.started) prev = g;
  g = makeGame(null);
  showGame();
}

// ---------- archive screen ----------

const fmtDate = ts => new Date(ts).toLocaleDateString('en-GB', { day: 'numeric', month: 'short', year: 'numeric' });
const fmtTime = ms => {
  const cs = Math.max(0, Math.round(ms / 10));
  const two = n => String(n).padStart(2, '0');
  return Math.floor(cs / 6000) + ':' + two(Math.floor(cs / 100) % 60) + '.' + two(cs % 100);
};

function el(tag, cls, text) {
  const node = document.createElement(tag);
  if (cls) node.className = cls;
  if (text != null) node.textContent = text;
  return node;
}

// Two-tap confirmation: the first tap arms the button, the second one deletes.
function confirmTap(btn, label, action) {
  let timer = 0;
  btn.textContent = label;
  btn.classList.remove('armed');
  btn.onclick = () => {
    if (btn.classList.contains('armed')) { clearTimeout(timer); action(); return; }
    btn.classList.add('armed');
    btn.textContent = 'Tap again to delete';
    timer = setTimeout(() => { btn.classList.remove('armed'); btn.textContent = label; }, 3000);
  };
}

function entryField(e) {
  const game = { rows: e.rows, cols: e.cols, field: new Int8Array(e.rows * e.cols) };
  for (let i = 0; i < game.field.length; i++) if (e.layout[i] === '1') game.field[i] = -1;
  countNeighbours(game);
  return game.field;
}

const resultView = (e, res, field) => ({
  rows: e.rows, cols: e.cols, field,
  revealed: fromBits(res.revealed), flagged: fromBits(res.flagged),
  over: res.outcome === 'loss', hit: res.hit, hint: -1,
});

function entryCard(e) {
  const card = el('div', 'card');

  const name = el('input', 'name');
  name.type = 'text';
  name.maxLength = 40;
  name.value = e.name;
  name.onchange = () => {
    e.name = name.value.trim() || 'Field ' + e.id;
    name.value = e.name;
    saveData();
  };
  card.appendChild(name);

  const wins = e.results.filter(r => r.outcome === 'win').length;
  const losses = e.results.length - wins;
  card.appendChild(el('div', 'meta',
    `${e.cols}×${e.rows} · ${e.mines} mines · saved ${fmtDate(e.created)}` +
    (e.results.length ? ` · ${wins} won, ${losses} lost` : '')));
  if (e.best != null) card.appendChild(el('div', 'best', 'Best time ' + fmtTime(e.best)));

  if (e.results.length) {
    const field = entryField(e);
    const strip = el('div', 'results');
    for (let k = e.results.length - 1; k >= 0; k--) {
      const res = e.results[k];
      const b = el('button', 'res');
      b.type = 'button';
      const cv = el('canvas');
      const s = fitCanvas(cv, e.cols, e.rows, 104, 104, 104);
      paint(cv, resultView(e, res, field), s);
      b.appendChild(cv);
      b.appendChild(el('span', 'outcome ' + (res.outcome === 'win' ? 'won' : 'lost'),
        res.outcome === 'win' ? 'Won · ' + fmtTime(res.ms) : 'Lost'));
      b.appendChild(el('span', '', fmtDate(res.date)));
      b.onclick = () => openViewer(e.id, k);
      strip.appendChild(b);
    }
    card.appendChild(strip);
  } else {
    card.appendChild(el('div', 'no-results', 'No results saved for this field yet'));
  }

  const actions = el('div', 'actions');
  const replay = el('button', 'btn primary', 'Replay');
  replay.type = 'button';
  replay.onclick = () => startReplay(e.id);
  const del = el('button', 'btn danger');
  del.type = 'button';
  confirmTap(del, 'Delete', () => {
    data.entries.splice(data.entries.indexOf(e), 1);
    saveData();
    renderArchive();
  });
  actions.appendChild(replay);
  actions.appendChild(del);
  card.appendChild(actions);
  return card;
}

function renderArchive() {
  const list = $('archiveList');
  list.textContent = '';
  if (!data.entries.length) {
    list.appendChild(el('div', 'empty',
      'Nothing archived yet. Open the pause menu during or after a game and choose “Archive this field”.'));
    return;
  }
  for (let k = data.entries.length - 1; k >= 0; k--) list.appendChild(entryCard(data.entries[k]));
}

function openArchive() {
  renderArchive();
  elArchive.hidden = false;
}

function closeArchive() {
  elArchive.hidden = true;
  if (!elMenu.hidden) updateMenu();
  if (!elSetup.hidden) $('btnSetupArchive').textContent = `Archive (${data.entries.length})`;
  if (!elGame.hidden) render();   // an entry may have been renamed
}

// ---------- result viewer ----------

function paintViewer() {
  const e = viewing && entryById(viewing.entryId);
  const res = e && e.results[viewing.index];
  if (!res) return;
  const box = $('vStage');
  const cv = $('vCanvas');
  const s = fitCanvas(cv, e.cols, e.rows, box.clientWidth - 12, box.clientHeight - 8, 72);
  paint(cv, resultView(e, res, entryField(e)), s);
}

function openViewer(entryId, index) {
  const e = entryById(entryId);
  const res = e && e.results[index];
  if (!res) return;
  viewing = { entryId, index };
  $('vTitle').textContent = e.name;
  const meta = $('vMeta');
  meta.textContent = '';
  meta.appendChild(el('span', res.outcome === 'win' ? 'won' : 'lost', res.outcome === 'win' ? 'Won' : 'Lost'));
  meta.appendChild(document.createTextNode(
    (res.outcome === 'win' ? ' · ' + fmtTime(res.ms) : '') +
    ` · ${fmtDate(res.date)} · ${e.cols}×${e.rows}, ${e.mines} mines`));
  confirmTap($('vDelete'), 'Delete result', () => {
    e.results.splice(index, 1);
    saveData();
    closeViewer();
    renderArchive();
  });
  elViewer.hidden = false;
  paintViewer();
}

function closeViewer() {
  elViewer.hidden = true;
  viewing = null;
}

// ---------- input ----------

// In-game controls act on touch-down, like the original's MOUSEBUTTONDOWN handling.
const onDown = (node, fn) => node.addEventListener('pointerdown', ev => { ev.preventDefault(); fn(ev); });

onDown(stage, ev => {
  if (g.over || g.win) {
    if (data.tapRestart) restart();
    return;
  }
  const rect = board.getBoundingClientRect();
  const c = Math.floor((ev.clientX - rect.left) / rect.width * g.cols);
  const r = Math.floor((ev.clientY - rect.top) / rect.height * g.rows);
  if (r >= 0 && r < g.rows && c >= 0 && c < g.cols) tapCell(r, c);
});
onDown($('btnMode'), () => { flagMode = !flagMode; render(); });
onDown($('btnRestart'), restart);
$('btnMenu').onclick = openMenu;   // on release, so the same tap cannot also land on a menu item
stage.addEventListener('contextmenu', ev => ev.preventDefault());

$('mResume').onclick = closeMenu;
$('mRestart').onclick = () => { restart(); closeMenu(); };
$('mArchive').onclick = doArchive;
$('mOpenArchive').onclick = openArchive;
$('mExitReplay').onclick = exitReplay;
$('mSetup').onclick = () => showSetup(cfg);
$('mTapRestart').onclick = () => {
  data.tapRestart = !data.tapRestart;
  saveData();
  updateMenu();
  render();
};

$('aBack').onclick = closeArchive;
$('vBack').onclick = closeViewer;
$('vReplay').onclick = () => { if (viewing) startReplay(viewing.entryId); };

for (const btn of document.querySelectorAll('.stepper button')) {
  btn.onclick = () => {
    const input = $(btn.dataset.for);
    const v = parseInt(input.value, 10);
    input.value = (Number.isNaN(v) ? 0 : v) + Number(btn.dataset.step);
    syncSetup();
  };
}
for (const input of [inCols, inRows, inMines]) input.onchange = syncSetup;
$('btnStart').onclick = startConfigured;
$('btnSetupArchive').onclick = openArchive;

window.addEventListener('resize', () => {
  if (!elGame.hidden) { fitBoard(); render(); }
  if (!elViewer.hidden) paintViewer();
});

// Android back button. Returns 'handled', 'ignore' (stay in the game) or 'exit'.
window.handleBack = () => {
  if (!elViewer.hidden) { closeViewer(); return 'handled'; }
  if (!elArchive.hidden) { closeArchive(); return 'handled'; }
  if (!elMenu.hidden) { closeMenu(); return 'handled'; }
  return elGame.hidden ? 'exit' : 'ignore';
};

showSetup(DEFAULTS);

})();
