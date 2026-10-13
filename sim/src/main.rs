//! Minesweeper win-rate simulator for the rules of the phone game:
//! the first dig keeps its 3x3 neighbourhood mine-free, mines are uniform everywhere else,
//! and the game is won once every mine-free cell is open.
//!
//! The simulated player:
//!   1. opens every cell that is provably safe. "Provably" is exact: all mine layouts that fit
//!      the visible numbers and the total mine count are counted, so no deduction is ever missed;
//!   2. when nothing is safe and at most `--endgame` layouts remain, searches the whole game tree
//!      and takes the move with the highest chance of winning (truly optimal from there on);
//!   3. when at most `--rollout` layouts remain, tries every cell and plays each resulting
//!      position out over all layouts (safest-cell guesses, then exact search), taking the best;
//!   4. otherwise digs the cell least likely to be a mine.
//!
//! Steps 2 and 3 only ever add wins, so every result is a lower bound on perfect play.

use std::collections::HashMap;
use std::env;
use std::thread;
use std::time::Instant;

type Mask = u128;
const MAX_CELLS: usize = 128;
const HIST: usize = 16;

#[inline]
fn bit(i: usize) -> Mask {
    1u128 << i
}

struct Bits(Mask);
impl Iterator for Bits {
    type Item = usize;
    #[inline]
    fn next(&mut self) -> Option<usize> {
        if self.0 == 0 {
            return None;
        }
        let i = self.0.trailing_zeros() as usize;
        self.0 &= self.0 - 1;
        Some(i)
    }
}

// ---------- random numbers (xoshiro256**) ----------

struct Rng([u64; 4]);
impl Rng {
    fn new(seed: u64) -> Rng {
        let mut z = seed;
        let mut next = || {
            z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            x ^ (x >> 31)
        };
        Rng([next(), next(), next(), next()])
    }
    fn next(&mut self) -> u64 {
        let s = &mut self.0;
        let r = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        r
    }
    fn below(&mut self, n: usize) -> usize {
        (((self.next() >> 32) * n as u64) >> 32) as usize
    }
}

// ---------- board geometry ----------

struct Geo {
    w: usize,
    h: usize,
    n: usize,
    nb: Vec<Mask>,
    binom: Vec<Vec<u128>>,
}

impl Geo {
    fn new(w: usize, h: usize) -> Geo {
        let n = w * h;
        let mut nb = vec![0; n];
        for r in 0..h {
            for c in 0..w {
                for dr in -1i32..=1 {
                    for dc in -1i32..=1 {
                        let (nr, nc) = (r as i32 + dr, c as i32 + dc);
                        if (dr, dc) != (0, 0) && nr >= 0 && nr < h as i32 && nc >= 0 && nc < w as i32 {
                            nb[r * w + c] |= bit(nr as usize * w + nc as usize);
                        }
                    }
                }
            }
        }
        let mut binom = vec![vec![0u128; n + 1]; n + 1];
        for i in 0..=n {
            binom[i][0] = 1;
            for j in 1..=i {
                binom[i][j] = binom[i - 1][j - 1].saturating_add(if j < i { binom[i - 1][j] } else { 0 });
            }
        }
        Geo { w, h, n, nb, binom }
    }

    /// C(n, k), zero when k is out of range.
    fn c(&self, n: usize, k: i64) -> u128 {
        if k < 0 || k as usize > n {
            0
        } else {
            self.binom[n][k as usize]
        }
    }

    /// One start cell per symmetry class of the board.
    fn distinct_starts(&self) -> Vec<usize> {
        let mut out = Vec::new();
        for r in 0..(self.h + 1) / 2 {
            for c in 0..(self.w + 1) / 2 {
                if self.w != self.h || c >= r {
                    out.push(r * self.w + c);
                }
            }
        }
        out
    }
}

// ---------- enumeration of mine layouts ----------

/// Order cells so that constraints become fully assigned as early as possible (better pruning).
fn order_cells(cons: &[(Mask, u8)]) -> Vec<u8> {
    let mut ordered: Mask = 0;
    let mut out = Vec::new();
    loop {
        let mut best: Option<(u32, Mask)> = None;
        for &(m, _) in cons {
            let fresh = m & !ordered;
            if fresh != 0 && best.map_or(true, |(cnt, _)| fresh.count_ones() < cnt) {
                best = Some((fresh.count_ones(), fresh));
            }
        }
        match best {
            None => return out,
            Some((_, fresh)) => {
                out.extend(Bits(fresh).map(|i| i as u8));
                ordered |= fresh;
            }
        }
    }
}

/// Backtracking over `cells`; every constraint (mask, need) must end with exactly `need` mines.
struct Enumerator {
    cells: Vec<u8>,
    cell_cons: Vec<Vec<u8>>,
    need: Vec<i16>,
    left: Vec<i16>,
    nodes: u64,
    budget: u64,
    over: bool,
}

impl Enumerator {
    fn new(cells: Vec<u8>, cons: &[(Mask, u8)], budget: u64) -> Enumerator {
        let cell_cons = cells
            .iter()
            .map(|&cell| {
                (0..cons.len()).filter(|&j| cons[j].0 & bit(cell as usize) != 0).map(|j| j as u8).collect()
            })
            .collect();
        Enumerator {
            cells,
            cell_cons,
            need: cons.iter().map(|c| c.1 as i16).collect(),
            left: cons.iter().map(|c| c.0.count_ones() as i16).collect(),
            nodes: 0,
            budget,
            over: false,
        }
    }

    fn run<F: FnMut(Mask, usize)>(&mut self, pos: usize, mask: Mask, k: usize, leaf: &mut F) {
        self.nodes += 1;
        if self.nodes > self.budget {
            self.over = true;
        }
        if self.over {
            return;
        }
        if pos == self.cells.len() {
            leaf(mask, k);
            return;
        }
        let ncons = self.cell_cons[pos].len();

        // this cell is safe
        let mut ok = true;
        for j in 0..ncons {
            let c = self.cell_cons[pos][j] as usize;
            self.left[c] -= 1;
            ok &= self.need[c] <= self.left[c];
        }
        if ok {
            self.run(pos + 1, mask, k, leaf);
        }

        // this cell is a mine
        ok = true;
        for j in 0..ncons {
            let c = self.cell_cons[pos][j] as usize;
            self.need[c] -= 1;
            ok &= self.need[c] >= 0 && self.need[c] <= self.left[c];
        }
        if ok {
            self.run(pos + 1, mask | bit(self.cells[pos] as usize), k + 1, leaf);
        }

        for j in 0..ncons {
            let c = self.cell_cons[pos][j] as usize;
            self.need[c] += 1;
            self.left[c] += 1;
        }
    }
}

fn convolve(a: &[u128], b: &[u128], cap: usize) -> Vec<u128> {
    let mut out = vec![0u128; (a.len() + b.len() - 1).min(cap + 1)];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            if i + j < out.len() {
                out[i + j] += x * y;
            }
        }
    }
    out
}

// ---------- game state as the player sees it ----------

struct Analysis {
    /// Number of mine layouts consistent with everything visible.
    total: u128,
    /// For each unknown cell: in how many of those layouts it is a mine.
    mine_cnt: [u128; MAX_CELLS],
    unknown: Mask,
    remaining: usize,
    cons: Vec<(Mask, u8)>,
}

struct Game<'a> {
    geo: &'a Geo,
    total_mines: usize,
    mines: Mask,
    revealed: Mask,
    /// Cells the player has proven to be mines.
    known: Mask,
    num: [u8; MAX_CELLS],
}

impl<'a> Game<'a> {
    fn new(geo: &'a Geo, total_mines: usize, rng: &mut Rng, start: usize) -> Game<'a> {
        // same rule as the game: no mine on the first cell or any of its neighbours
        let forbidden = geo.nb[start] | bit(start);
        let mut mines: Mask = 0;
        let mut placed = 0;
        while placed < total_mines {
            let b = bit(rng.below(geo.n));
            if (mines | forbidden) & b == 0 {
                mines |= b;
                placed += 1;
            }
        }
        Game { geo, total_mines, mines, revealed: 0, known: 0, num: [0; MAX_CELLS] }
    }

    /// Opens a cell (flooding from zeros). The caller checks for mines first.
    fn reveal(&mut self, cell: usize) {
        let mut stack = vec![cell];
        while let Some(i) = stack.pop() {
            if self.revealed & bit(i) != 0 {
                continue;
            }
            self.revealed |= bit(i);
            let n = (self.geo.nb[i] & self.mines).count_ones() as u8;
            self.num[i] = n;
            if n == 0 {
                stack.extend(Bits(self.geo.nb[i] & !self.revealed));
            }
        }
    }

    fn unknown(&self) -> Mask {
        !(self.revealed | self.known) & (!0u128 >> (128 - self.geo.n))
    }

    /// Cheap single-number deductions. Returns safe cells; proven mines go into `known`.
    fn trivial(&mut self) -> Mask {
        loop {
            let unknown = self.unknown();
            let mut safe: Mask = 0;
            let mut found_mines: Mask = 0;
            for i in Bits(self.revealed) {
                let m = self.geo.nb[i] & unknown;
                if m == 0 {
                    continue;
                }
                let need = self.num[i] as u32 - (self.geo.nb[i] & self.known).count_ones();
                if need == 0 {
                    safe |= m;
                } else if need == m.count_ones() {
                    found_mines |= m;
                }
            }
            self.known |= found_mines;
            if safe != 0 {
                return safe & !self.known;
            }
            if found_mines == 0 {
                return 0;
            }
        }
    }

    /// Exact count of consistent layouts, overall and per cell. None if the node budget ran out.
    fn analyze(&self, budget: u64) -> Option<Analysis> {
        let geo = self.geo;
        let unknown = self.unknown();
        let remaining = self.total_mines - self.known.count_ones() as usize;

        let mut cons: Vec<(Mask, u8)> = Vec::new();
        for i in Bits(self.revealed) {
            let m = geo.nb[i] & unknown;
            if m != 0 && !cons.iter().any(|c| c.0 == m) {
                cons.push((m, self.num[i] - (geo.nb[i] & self.known).count_ones() as u8));
            }
        }

        // independent groups of constraints
        let mut comps: Vec<(Mask, Vec<(Mask, u8)>)> = Vec::new();
        for &con in &cons {
            let mut merged = (con.0, vec![con]);
            let mut k = 0;
            while k < comps.len() {
                if comps[k].0 & con.0 != 0 {
                    let (m, list) = comps.swap_remove(k);
                    merged.0 |= m;
                    merged.1.extend(list);
                } else {
                    k += 1;
                }
            }
            comps.push(merged);
        }

        // per group: number of solutions by mine count, and per cell
        struct Comp {
            cells: Vec<u8>,
            counts: Vec<u128>,
            cell_cnt: Vec<u64>,
        }
        let mut frontier: Mask = 0;
        let mut solved: Vec<Comp> = Vec::with_capacity(comps.len());
        for (mask, list) in &comps {
            frontier |= mask;
            let cells = order_cells(list);
            let n = cells.len();
            let mut loc = [0u8; MAX_CELLS];
            for (j, &cell) in cells.iter().enumerate() {
                loc[cell as usize] = j as u8;
            }
            let mut counts = vec![0u128; n + 1];
            let mut cell_cnt = vec![0u64; (n + 1) * n];
            let mut en = Enumerator::new(cells.clone(), list, budget);
            en.run(0, 0, 0, &mut |m, k| {
                counts[k] += 1;
                for i in Bits(m) {
                    cell_cnt[k * n + loc[i] as usize] += 1;
                }
            });
            if en.over {
                return None;
            }
            solved.push(Comp { cells, counts, cell_cnt });
        }

        let interior = (unknown & !frontier).count_ones() as usize;
        let r = remaining as i64;
        let mut mine_cnt = [0u128; MAX_CELLS];
        let mut total: u128 = 0;

        let mut all = vec![1u128];
        for comp in &solved {
            all = convolve(&all, &comp.counts, remaining);
        }
        for (t, &ways) in all.iter().enumerate() {
            total += ways * geo.c(interior, r - t as i64);
        }

        for (ci, comp) in solved.iter().enumerate() {
            let mut others = vec![1u128];
            for (cj, other) in solved.iter().enumerate() {
                if cj != ci {
                    others = convolve(&others, &other.counts, remaining);
                }
            }
            let n = comp.cells.len();
            for k in 0..=n.min(remaining) {
                // layouts of everything outside this group, given it holds k mines
                let mut weight: u128 = 0;
                for (j, &ways) in others.iter().enumerate() {
                    weight += ways * geo.c(interior, r - k as i64 - j as i64);
                }
                if weight == 0 {
                    continue;
                }
                for (j, &cell) in comp.cells.iter().enumerate() {
                    mine_cnt[cell as usize] += comp.cell_cnt[k * n + j] as u128 * weight;
                }
            }
        }

        if interior > 0 {
            let mut cnt: u128 = 0;
            for (t, &ways) in all.iter().enumerate() {
                cnt += ways * geo.c(interior - 1, r - t as i64 - 1);
            }
            for i in Bits(unknown & !frontier) {
                mine_cnt[i] = cnt;
            }
        }

        Some(Analysis { total, mine_cnt, unknown, remaining, cons })
    }

    /// Safest cell; ties go to the cell with the fewest unknown neighbours (most informative number).
    fn greedy(&self, a: &Analysis) -> usize {
        let mut best = (u128::MAX, u32::MAX, 0usize);
        for i in Bits(a.unknown) {
            let key = (a.mine_cnt[i], (self.geo.nb[i] & a.unknown).count_ones(), i);
            if key < best {
                best = key;
            }
        }
        best.2
    }
}

// ---------- exact endgame search ----------

/// FxHash-style hasher: the memo is keyed by lists of layout indices and hashed very often.
#[derive(Default)]
struct FastHasher(u64);
impl std::hash::Hasher for FastHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut buf = [0u8; 8];
            buf[..chunk.len()].copy_from_slice(chunk);
            self.0 = (self.0.rotate_left(5) ^ u64::from_le_bytes(buf)).wrapping_mul(0x517C_C1B7_2722_0A95);
        }
    }
}
type Memo = HashMap<Vec<u32>, u32, std::hash::BuildHasherDefault<FastHasher>>;

/// Game-tree search over an explicit list of the remaining layouts.
/// `value(set)` = in how many layouts of `set` the best possible play wins.
struct Endgame<'a> {
    geo: &'a Geo,
    known: Mask,
    sols: Vec<Mask>,
    cand: Mask,
    memo: Memo,
    budget: usize,
    over: bool,
    /// Sets up to this size are searched exactly inside a rollout.
    leaf: usize,
}

impl<'a> Endgame<'a> {
    #[inline]
    fn number(&self, cell: usize, s: u32) -> usize {
        (self.geo.nb[cell] & (self.known | self.sols[s as usize])).count_ones() as usize
    }

    /// Splits the layouts where `cell` is safe by the number it would show.
    fn split(&self, set: &[u32], cell: usize) -> [Vec<u32>; 9] {
        let mut groups: [Vec<u32>; 9] = Default::default();
        for &s in set {
            if self.sols[s as usize] & bit(cell) == 0 {
                groups[self.number(cell, s)].push(s);
            }
        }
        groups
    }

    fn value(&mut self, set: &[u32]) -> u32 {
        if set.len() <= 1 {
            return set.len() as u32;
        }
        if self.over {
            return 0;
        }
        if let Some(&v) = self.memo.get(set) {
            return v;
        }
        let (mut any, mut all): (Mask, Mask) = (0, !0);
        for &s in set {
            any |= self.sols[s as usize];
            all &= self.sols[s as usize];
        }

        // A cell that is safe in every layout costs nothing to open: take its information first.
        for cell in Bits(self.cand & !any) {
            let first = self.number(cell, set[0]);
            if set.iter().any(|&s| self.number(cell, s) != first) {
                let groups = self.split(set, cell);
                let v = groups.iter().map(|g| self.value(g)).sum();
                self.remember(set, v);
                return v;
            }
        }

        let v = self.best_guess(set, any & !all, true).1;
        self.remember(set, v);
        v
    }

    /// In how many layouts of `set` the fast player wins: safest-cell guesses while the set is
    /// large, exact search once it is small. Used to score moves when `set` is too big to search.
    fn rollout(&mut self, set: &[u32], mut opened: Mask) -> u32 {
        if set.len() <= self.leaf {
            if self.memo.len() > self.budget / 2 {
                self.memo.clear();
            }
            return self.value(set);
        }
        let mut any: Mask = 0;
        let mut cnt = [0u32; MAX_CELLS];
        for &s in set {
            any |= self.sols[s as usize];
        }
        for cell in Bits(self.cand & !any & !opened) {
            opened |= bit(cell);
            let first = self.number(cell, set[0]);
            if set.iter().any(|&s| self.number(cell, s) != first) {
                let groups = self.split(set, cell);
                return groups.iter().map(|g| self.rollout(g, opened)).sum();
            }
        }
        for &s in set {
            for i in Bits(self.sols[s as usize]) {
                cnt[i] += 1;
            }
        }
        let cell = Bits(any).min_by_key(|&i| cnt[i]).unwrap();
        if cnt[cell] as usize == set.len() {
            return 0; // only certain mines are left, yet the layouts differ: cannot happen
        }
        let groups = self.split(set, cell);
        groups.iter().map(|g| self.rollout(g, opened | bit(cell))).sum()
    }

    /// Best risky cell among `cells`: (cell, layouts won).
    fn best_guess(&mut self, set: &[u32], cells: Mask, exact: bool) -> (usize, u32) {
        let mut options: Vec<(u32, usize)> = Bits(cells)
            .map(|cell| (set.iter().filter(|&&s| self.sols[s as usize] & bit(cell) == 0).count() as u32, cell))
            .collect();
        options.sort_unstable_by(|a, b| b.cmp(a));
        let mut best = (usize::MAX, 0u32);
        for (survive, cell) in options {
            if survive <= best.1 && best.0 != usize::MAX {
                break; // cannot beat the best found even if every surviving layout were won
            }
            let mut groups = self.split(set, cell);
            groups.sort_unstable_by_key(|g| g.len()); // cheap groups first, so hopeless cells are dropped early
            let mut v = 0u32;
            let mut potential = survive;
            for g in &groups {
                if potential <= best.1 && best.0 != usize::MAX {
                    break;
                }
                let got = if exact { self.value(g) } else { self.rollout(g, bit(cell)) };
                potential -= g.len() as u32 - got;
                v += got;
            }
            if potential > best.1 || best.0 == usize::MAX {
                best = (cell, v);
            }
        }
        best
    }

    fn remember(&mut self, set: &[u32], v: u32) {
        if self.memo.len() >= self.budget {
            self.over = true;
        } else if !self.over {
            self.memo.insert(set.to_vec(), v);
        }
    }
}

/// The move with the highest win probability, or None if the search grew too large.
fn endgame_move(g: &Game, a: &Analysis, cfg: &Cfg) -> Option<usize> {
    // list every remaining layout: all numbers plus the total mine count as one more constraint
    let mut cells = order_cells(&a.cons);
    let mut seen: Mask = 0;
    for &c in &cells {
        seen |= bit(c as usize);
    }
    cells.extend(Bits(a.unknown & !seen).map(|i| i as u8));
    let mut cons = a.cons.clone();
    cons.push((a.unknown, a.remaining as u8));
    let mut sols: Vec<Mask> = Vec::with_capacity(a.total as usize);
    let mut en = Enumerator::new(cells, &cons, cfg.node_budget);
    en.run(0, 0, 0, &mut |m, _| sols.push(m));
    if en.over {
        return None;
    }
    debug_assert_eq!(sols.len() as u128, a.total);

    let set: Vec<u32> = (0..sols.len() as u32).collect();
    let mut eg = Endgame {
        geo: g.geo,
        known: g.known,
        sols,
        cand: a.unknown,
        memo: Memo::default(),
        budget: cfg.endgame_memo,
        over: false,
        leaf: cfg.leaf,
    };
    let (cell, _) = eg.best_guess(&set, a.unknown, a.total <= cfg.endgame);
    if eg.over || cell == usize::MAX {
        None
    } else {
        Some(cell)
    }
}

// ---------- playing games ----------

#[derive(Clone)]
struct Cfg {
    w: usize,
    h: usize,
    mines: usize,
    games: u64,
    endgame: u128,
    rollout: u128,
    leaf: usize,
    endgame_memo: usize,
    node_budget: u64,
    threads: usize,
    seed: u64,
}

#[derive(Default, Clone)]
struct Stats {
    games: u64,
    wins: u64,
    skipped: u64,
    guesses: u64,
    risk_sum: f64,
    cleared_at_death: f64,
    win_guesses: [u64; HIST],
    death_at: [u64; HIST],
    endgame_searches: u64,
    endgame_fallbacks: u64,
}

impl Stats {
    fn add(&mut self, o: &Stats) {
        self.games += o.games;
        self.wins += o.wins;
        self.skipped += o.skipped;
        self.guesses += o.guesses;
        self.risk_sum += o.risk_sum;
        self.cleared_at_death += o.cleared_at_death;
        self.endgame_searches += o.endgame_searches;
        self.endgame_fallbacks += o.endgame_fallbacks;
        for i in 0..HIST {
            self.win_guesses[i] += o.win_guesses[i];
            self.death_at[i] += o.death_at[i];
        }
    }
}

fn play(geo: &Geo, cfg: &Cfg, rng: &mut Rng, start: usize, st: &mut Stats) {
    let mut g = Game::new(geo, cfg.mines, rng, start);
    g.reveal(start);
    let target = (geo.n - cfg.mines) as u32;
    let mut guesses = 0usize;
    loop {
        if g.revealed.count_ones() == target {
            st.games += 1;
            st.wins += 1;
            st.win_guesses[guesses.min(HIST - 1)] += 1;
            return;
        }
        let mut safe = g.trivial();
        if safe == 0 {
            let a = match g.analyze(cfg.node_budget) {
                Some(a) => a,
                None => {
                    st.skipped += 1;
                    return;
                }
            };
            for i in Bits(a.unknown) {
                if a.mine_cnt[i] == 0 {
                    safe |= bit(i);
                } else if a.mine_cnt[i] == a.total {
                    g.known |= bit(i);
                }
            }
            if safe == 0 {
                // nothing is certain: a guess is forced
                let mut cell = usize::MAX;
                if a.total <= cfg.endgame.max(cfg.rollout) {
                    st.endgame_searches += 1;
                    match endgame_move(&g, &a, cfg) {
                        Some(c) => cell = c,
                        None => st.endgame_fallbacks += 1,
                    }
                }
                if cell == usize::MAX {
                    cell = g.greedy(&a);
                }
                guesses += 1;
                st.guesses += 1;
                st.risk_sum += a.mine_cnt[cell] as f64 / a.total as f64;
                if g.mines & bit(cell) != 0 {
                    st.games += 1;
                    st.death_at[guesses.min(HIST - 1)] += 1;
                    st.cleared_at_death += g.revealed.count_ones() as f64 / target as f64;
                    return;
                }
                g.reveal(cell);
                continue;
            }
        }
        assert!(safe & g.mines == 0 && g.known & !g.mines == 0, "solver made a wrong deduction");
        for i in Bits(safe) {
            g.reveal(i);
        }
    }
}

/// Compares the solver's layout counts with a plain count over every possible layout,
/// on positions reached by random play on a small board.
fn selftest(cfg: &Cfg) {
    let geo = Geo::new(cfg.w, cfg.h);
    assert!(geo.n <= 30, "--selftest needs a board of at most 30 cells");
    let mut rng = Rng::new(cfg.seed);
    let (mut positions, mut cells_checked) = (0u64, 0u64);
    for _ in 0..cfg.games {
        let start = rng.below(geo.n);
        let mut g = Game::new(&geo, cfg.mines, &mut rng, start);
        g.reveal(start);
        loop {
            let a = g.analyze(cfg.node_budget).expect("budget");
            // brute force: every way to put the mines on the board
            let mut total = 0u128;
            let mut cnt = [0u128; MAX_CELLS];
            let mut m: u64 = (1u64 << cfg.mines) - 1;
            while m < (1u64 << geo.n) {
                let layout = m as Mask;
                let fits = layout & g.revealed == 0
                    && Bits(g.revealed).all(|i| (geo.nb[i] & layout).count_ones() as u8 == g.num[i]);
                if fits {
                    total += 1;
                    for i in Bits(layout) {
                        cnt[i] += 1;
                    }
                }
                let low = m & m.wrapping_neg();
                let ripple = m + low;
                m = (((ripple ^ m) >> 2) / low) | ripple;
            }
            assert_eq!(total, a.total, "layout count differs");
            for i in Bits(a.unknown) {
                assert_eq!(cnt[i], a.mine_cnt[i], "mine count differs for cell {i}");
                cells_checked += 1;
            }
            for i in Bits(g.known) {
                assert_eq!(cnt[i], total, "cell {i} was wrongly proven a mine");
            }
            positions += 1;
            // continue with a random move so that odd positions get covered too
            let options: Vec<usize> = Bits(a.unknown).collect();
            if options.is_empty() {
                break;
            }
            let cell = options[rng.below(options.len())];
            if g.mines & bit(cell) != 0 {
                break;
            }
            g.reveal(cell);
            g.trivial();
        }
    }
    println!("selftest passed: {positions} positions, {cells_checked} cell probabilities identical to brute force");
}

fn simulate(geo: &Geo, cfg: &Cfg, start: usize, games: u64) -> Stats {
    let mut total = Stats::default();
    thread::scope(|scope| {
        let handles: Vec<_> = (0..cfg.threads)
            .map(|t| {
                let share = games / cfg.threads as u64 + u64::from((t as u64) < games % cfg.threads as u64);
                scope.spawn(move || {
                    let mut rng = Rng::new(cfg.seed ^ ((start as u64) << 32) ^ (t as u64).wrapping_mul(0xA24B_AED4_963E_E407));
                    let mut st = Stats::default();
                    for _ in 0..share {
                        play(geo, cfg, &mut rng, start, &mut st);
                    }
                    st
                })
            })
            .collect();
        for hnd in handles {
            total.add(&hnd.join().unwrap());
        }
    });
    total
}

/// 95% Wilson interval, in percent.
fn wilson(wins: u64, n: u64) -> (f64, f64) {
    if n == 0 {
        return (0.0, 0.0);
    }
    let (z, n) = (1.96f64, n as f64);
    let p = wins as f64 / n;
    let centre = p + z * z / (2.0 * n);
    let half = z * (p * (1.0 - p) / n + z * z / (4.0 * n * n)).sqrt();
    let denom = 1.0 + z * z / n;
    (100.0 * (centre - half) / denom, 100.0 * (centre + half) / denom)
}

fn rate(wins: u64, n: u64) -> String {
    let (lo, hi) = wilson(wins, n);
    format!("{:>8.4}%  (95% CI {:.4}% - {:.4}%)", 100.0 * wins as f64 / n.max(1) as f64, lo, hi)
}

fn report(geo: &Geo, cfg: &Cfg, start: usize, st: &Stats, secs: f64) {
    let losses = st.games - st.wins;
    println!();
    println!("=== {}x{}, {} mines, first dig at row {}, column {} ===", cfg.w, cfg.h, cfg.mines, start / geo.w + 1, start % geo.w + 1);
    println!("games played        {}   ({:.1}s, {:.0} games/s)", st.games, secs, st.games as f64 / secs.max(1e-9));
    println!("games won           {}", st.wins);
    println!("win rate           {}", rate(st.wins, st.games));
    if st.wins > 0 && st.wins * 2 < st.games {
        println!("  about 1 win in {:.0} games", st.games as f64 / st.wins as f64);
    }
    println!("won without a single guess   {}  ({:.4}% of games)", st.win_guesses[0], 100.0 * st.win_guesses[0] as f64 / st.games.max(1) as f64);
    println!("forced guesses per game      {:.2}", st.guesses as f64 / st.games.max(1) as f64);
    println!("average risk of a guess      {:.1}% chance of hitting a mine", 100.0 * st.risk_sum / st.guesses.max(1) as f64);
    if losses > 0 {
        println!("board cleared at death       {:.1}% of the safe cells on average", 100.0 * st.cleared_at_death / losses as f64);
    }
    println!("losses by the guess that killed (share of all games):");
    for i in 1..HIST {
        if st.death_at[i] > 0 {
            let label = if i == HIST - 1 { format!("{}+", i) } else { format!("{}", i) };
            println!("  guess {:>3}   {:>7.3}%", label, 100.0 * st.death_at[i] as f64 / st.games as f64);
        }
    }
    if st.wins > 0 {
        println!("wins by number of guesses survived (share of wins):");
        for i in 0..HIST {
            if st.win_guesses[i] > 0 {
                let label = if i == HIST - 1 { format!("{}+", i) } else { format!("{}", i) };
                println!("  {:>3} guesses   {:>6.2}%", label, 100.0 * st.win_guesses[i] as f64 / st.wins as f64);
            }
        }
    }
    println!("endgame searches    {}  (fell back to safest-cell: {})", st.endgame_searches, st.endgame_fallbacks);
    // If the computed probabilities are right, the risks taken must add up to the deaths that happened.
    println!("self-check          deaths predicted from the risks taken: {:.0}, actual: {}", st.risk_sum, losses);
    if st.skipped > 0 {
        println!("WARNING: {} games skipped because a position was too large to analyse", st.skipped);
    }
}

fn main() {
    let mut cfg = Cfg {
        w: 9,
        h: 9,
        mines: 30,
        games: 1_000_000,
        endgame: 300,
        rollout: 0,
        leaf: 200,
        endgame_memo: 400_000,
        node_budget: 50_000_000,
        threads: thread::available_parallelism().map_or(4, |n| n.get()),
        seed: 20261012,
    };
    let mut start_arg = String::from("all");
    let mut scan_games: u64 = 0;
    let mut selftest_mode = false;

    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        let val = args.get(i + 1).cloned().unwrap_or_default();
        match args[i].as_str() {
            "--w" => cfg.w = val.parse().expect("--w"),
            "--h" => cfg.h = val.parse().expect("--h"),
            "--mines" => cfg.mines = val.parse().expect("--mines"),
            "--games" => cfg.games = val.parse().expect("--games"),
            "--scan-games" => scan_games = val.parse().expect("--scan-games"),
            "--start" => start_arg = val,
            "--endgame" => cfg.endgame = val.parse().expect("--endgame"),
            "--rollout" => cfg.rollout = val.parse().expect("--rollout"),
            "--leaf" => cfg.leaf = val.parse().expect("--leaf"),
            "--threads" => cfg.threads = val.parse().expect("--threads"),
            "--seed" => cfg.seed = val.parse().expect("--seed"),
            "--selftest" => {
                selftest_mode = true;
                i += 1;
                continue;
            }
            other => {
                eprintln!("unknown option {other}");
                eprintln!("usage: minesim [--w 9] [--h 9] [--mines 30] [--games 1000000] [--start all|ROW,COL]");
                eprintln!("               [--scan-games N] [--endgame 300] [--rollout 0] [--leaf 200] [--threads N] [--seed N]");
                eprintln!("               [--selftest]");
                eprintln!("  --start all   try every distinct first cell with --scan-games each, then run --games on the best");
                eprintln!("  --endgame N   search the full game tree once at most N layouts remain (0 = never)");
                eprintln!("  --rollout N   above that, up to N layouts, score every move by playing it out (0 = off; slow)");
                eprintln!("  --selftest    check the solver against brute force on a small board (e.g. --w 5 --h 5 --mines 7)");
                std::process::exit(2);
            }
        }
        i += 2;
    }
    assert!(cfg.w * cfg.h <= MAX_CELLS, "at most {MAX_CELLS} cells are supported");
    assert!(cfg.w >= 4 && cfg.h >= 4 && cfg.mines >= 1 && cfg.mines + 9 <= cfg.w * cfg.h, "invalid field / mine count");
    assert!(cfg.endgame.max(cfg.rollout) <= 5_000_000, "--endgame / --rollout are limited to 5 million layouts");
    cfg.threads = cfg.threads.max(1);
    if selftest_mode {
        selftest(&cfg);
        return;
    }

    let geo = Geo::new(cfg.w, cfg.h);
    println!("Minesweeper simulation: {}x{} field, {} mines, {} threads", cfg.w, cfg.h, cfg.mines, cfg.threads);
    println!("player: exact logic; optimal search once <= {} layouts remain; move-by-move playouts up to {} layouts; otherwise safest cell", cfg.endgame, cfg.rollout);

    let start = if start_arg == "all" {
        let starts = geo.distinct_starts();
        let per = if scan_games > 0 { scan_games } else { (cfg.games / 5).max(1) };
        println!();
        println!("Choosing the first dig: {} games for each of the {} distinct cells", per, starts.len());
        let mut best = (starts[0], -1.0f64);
        for &s in &starts {
            let t = Instant::now();
            let st = simulate(&geo, &cfg, s, per);
            let p = st.wins as f64 / st.games.max(1) as f64;
            println!("  row {}, column {}   {}   [{:.1}s]", s / geo.w + 1, s % geo.w + 1, rate(st.wins, st.games), t.elapsed().as_secs_f64());
            if p > best.1 {
                best = (s, p);
            }
        }
        best.0
    } else {
        let parts: Vec<usize> = start_arg.split(',').map(|x| x.trim().parse().expect("--start ROW,COL")).collect();
        assert!(parts.len() == 2 && parts[0] >= 1 && parts[0] <= cfg.h && parts[1] >= 1 && parts[1] <= cfg.w, "--start ROW,COL (1-based)");
        (parts[0] - 1) * cfg.w + parts[1] - 1
    };

    let t = Instant::now();
    let mut main_cfg = cfg.clone();
    main_cfg.seed ^= 0x5DEE_CE66_D1CE_4E5B; // fresh games, independent of the scan
    let st = simulate(&geo, &main_cfg, start, cfg.games);
    report(&geo, &cfg, start, &st, t.elapsed().as_secs_f64());
}
