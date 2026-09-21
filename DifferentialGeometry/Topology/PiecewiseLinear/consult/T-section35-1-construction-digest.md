# T — the construction inside the proof of Moise 35.1, in order (read-only, 2026-09-21)

Source: Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, printed pp. 247–252
(PDF 257–262; **book page + 10 = one-based PDF page**), plus §34 pp. 239–241 and 27.3 on p. **198**
(not 199 — see D13). All statements below are paraphrase in this project's notation.

**Purpose.** Replace re-reading the page images. Companion to `A-section34-lemma-list.md`, whose
§4.2 lists the fourteen steps and §0 the citation census; that is **not repeated** here. This file
adds what the four review rounds disputed: the `v`/`w` asymmetry, the quantifier order, the
per-condition margins, the support of one surgery, what the book does with the infinite family, and
a discrepancy list against the Lean predicates and against digest `S`.
Flags: **[P]** printed as such; **[A]** asserted without argument; **[G]** a gap the formalisation
must fill itself; **[R]** my reading of a garbled or ambiguous line.

## 1. Statement, and the controlled deviations

**35.1 as printed (p. 248).** `K` a 1-dimensional polyhedron (possibly infinite) in a PL 3-manifold
`M₁`; `U` open with `K ⊆ U`; `h : U → M₂` a homeomorphism into a PL 3-manifold `M₂`; `φ` a
**strongly positive** function on `U` — everywhere positive and bounded away from `0` on each
compact set (p. 247; **continuity not required**). Then there are a regular neighbourhood `N` of
`K` **in `U`** and a PLH `f : N ↔ X ⊆ M₂` with (1) `X` a neighbourhood of `K' = h(K)` and (2) `f`
a `φ`-approximation of `h|N`. Regular neighbourhoods of a non-closed `K` are defined on p. 247 by
triangulating `U` rectilinearly with respect to `M₁`.

**Controlled form** (`B-support-chain-scope.md` §2): carriers `H α` and the triangulation `𝒦` are
quantified **first**, then `W` and a *continuous* tolerance `ψ` freely, then `N`, the whole source
cut diagram (`C_v, D_e, d_σ, Q_t, X_{tv}`) and `f₁` in **one** existential — plain `Moise351`
exposes only `N` and `f`, from which no diagram is recoverable. Added to the conclusion: §34 L1's
incidence clauses, §34 L2's generator clause, `h '' ∂σ ⊆ interior T_σ`, and
`h '' C v ∪ f₁ '' C v ⊆ H v`, which is what must carry the final estimate.

**Cited by number inside the proof.** 34.1 (p. 239; used p. 249): a homeomorphism of a polyhedral
3-cell in `ℝ³` into `ℝ³` has PL `ε`-approximations. 27.3 (p. 198; used p. 250): a polygon in the
*interior* of a PL annulus `A` either bounds a 2-cell in `A` or carries a generator of `H₁(A)` and
of `π(A)`. 33.1 (p. 230) appears on p. 247 in the introductory remark only. Used but uncited:
PL Schönflies inside a 3-cell and general position of two PL surfaces, both p. 250.

## 2. Object table (order of introduction)

`Int`/`Bd` on a cell or annulus are **cell-theoretic**, not ambient. "pierced" = the cell whose
face is punctured; "piercing" = the cell poking through.

| Book | Project | What it is | After | Before | p. |
|---|---|---|---|---|---|
| `ε(A)` = inf of `φ` on compact `A ⊆ M₁` | — | positive real per compact set | the reduction | `E_v` | 248 |
| `N`, dual cells `C_v` | `section34CutNeighborhood src`, `src (.vertexBall v)` | regular nbhd of `K` in `M₁`; `C_v` polyhedral 3-cells, one per vertex | a fine subdivision of `M₁` | `E_v` | 248 |
| `D_e = C_v ∩ C_w`, `e = vw` | `src (.splitDisk e)` | splitting disk | `N` | the alteration | 248 |
| `E_v` | `Q v` | **polyhedral 3-cell in `M₂`**, `h(C_v) ⊆ Int E_v`, `E_v ⊆ N(h(v), ε(C_v))` = condition (1) **[A]** | `C_v, h, φ` | all later steps | 248 |
| `C'_v` | `Cp v` | altered dual cells; per edge **one** end, say `C_w`, is altered | `E_v` | `S_e, T_e` | 248 |
| `J_e` | `CpBd (ends e).1 ∩ CpBd (ends e).2` | 1-sphere in which `Bd C'_w` pierces **`Int D_e`** | the alteration | `S_e, T_e` | 248 |
| `S_e ⊇ T_e` | `Sn e`, `Tn e` | small **regular nbhds of `J_e` in `M₁`**, `T_e ⊆ Int S_e`; the four sets `S_e ∩ Bd C'_v`, `S_e ∩ Bd C'_w`, `T_e ∩ Bd C'_v`, `T_e ∩ Bd C'_w` are annuli | `J_e` | `A_e, B_e, C''_v` | 249 |
| `A_e = Bd C'_v ∩ T_e` | `Aa e` | annulus on the boundary of the **pierced** cell (`v`-side) | `T_e` | `ε_v` | 249 |
| `B_e` | `Bb e`, rim `Bb₀ ∪ Bb₁` | annulus **in `Bd C'_w`**, the **piercing** cell (`w`-side), with `T_e ∩ Bd C'_w ⊆ Int B_e`, `B_e ⊆ Int S_e`, `Bd B_e ⊆ S_e − T_e` | `T_e` | `ε_v` | 249 |
| `C''_v` | `Cc v` | `C'_v` together with the `S_e` of its incident edges — **the domain of the vertex approximation** | `S_e` | `ε_v` | 249 |
| `ε_v > 0` | `ε v` | tolerance per vertex | the **entire** source family above | `f_v` | 249 |
| `f_v : C''_v → M₂` | `G v` | PLH, an `ε_v`-approximation of `h` on `C''_v`, from **34.1** | `ε_v` | (2)–(8) | 249 |
| `A'_e, B'_e, T'_e, S'_e` | `G (ends e).1 '' Aa e`, `G (ends e).2 '' Bb e`, `Tp e`, `Sp e` | `A'_e = f_v(A_e)`, `T'_e = f_v(T_e)`, `S'_e = f_v(S_e)`, **`B'_e = f_w(B_e)`** — three uses of `f_v`, one of `f_w` **[P]** | `f_v, f_w` | Lemmas 1–3 | 249 |
| `J`, `J₀` | `Pg e i`, `cnt e` | polygons of `A'_e ∩ B'_e` | (8) | Lemmas 1–3 | 250 |
| `D_J, E_J` / `B'', A'', C` | — | surgery data of Lemmas 2 / 3 | minimality | — | 250–251 |
| `D_v` | — | `f_w(C'_w)` with `f_w(C'_w) ∩ Int f_v(C'_v)` deleted, over all edges | Lemmas 1–3 | `f` | 251 |
| `f : N ↔ ⋃ D_v` | the `G'` of `exists_section34EdgeMatching` | the output; **domain is the original `N`, with the original `C_v`** | `D_v` | — | 251 |

**Three points the reviews kept contesting.**
* **`C_v ⊆ C'_v` is NOT asserted (p. 248).** Asserted is exactly: (a) `Bd C'_w` pierces `Int D_e` in
  the circle `J_e`; (b) `⋃_v C'_v` is still a neighbourhood of `K`; (c) `C'_w` may be taken inside
  **any prescribed neighbourhood of `C_w`**, so (1) survives. No inclusion either way between `C_v`
  and `C'_v` is stated or used; the endgame returns to the *original* `C_v`.
* **Domain of the approximation is `C''_v`**, not `C_v` or `C'_v`; and (2) mentions `f_w(S_e)`, so
  each `S_e` lies in **both** `C''_v` and `C''_w` (Q1).
* **Every regular neighbourhood here is taken in `M₁`**: `N` of `K`, `S_e`/`T_e` of `J_e`; `S'_e`,
  `T'_e` are images. The nested solid tori of §34 L2 occur nowhere in pp. 248–251.

## 3. Timeline of choices (the quantifier order is the content)

1. (248) Reduce: `K` closed relative to `U`, replace `M₁` by `U`; `h, φ` on all of `M₁`.
2. (248) `ε(A) :=` inf of `φ` on compact `A`; positive by strong positivity.
3. (248) Choose the subdivision **fine** and `N` **small**; this fixes `C_v` and `D_e`.
4. (248) Choose `E_v` = condition (1) **[A]**, from `C_v, h, ε(C_v)`. **This fixes the only metric
   control that survives to step 14.**
5. (248) Alter `C_w ↦ C'_w` per edge inside a prescribed nbhd of `C_w`; fixes `J_e` and the `v`/`w`
   role assignment per edge. (1) preserved.
6. (249) Choose `S_e ⊇ T_e` inside prescribed nbhds of `J_e`; fixes `A_e`, `B_e`.
7. (249) Form `C''_v`; (1) still preserved, as `S_e` may be taken arbitrarily near `J_e`.
8. (249) **Only now** choose `ε_v`. It depends on the whole family of steps 3–7; the conditions
   couple `ε_v` **and** `ε_w` per edge, so the bound is per-edge, not per-vertex. Globally: because
   `K` is a locally finite complex the `ε_v` can be chosen for all of `K` at once **[A]** — one
   sentence on p. 250, no argument.
9. (249) Apply **34.1** for `f_v : C''_v → M₂`, an `ε_v`-approximation. Printed 34.1 has Euclidean
   target, so this is the unwritten chart-transport step.
10. (249–250) (2)–(7) hold for `ε_v, ε_w` small; **(8) is a further small general position move**
    after `f_v` exists.
11. (250) **Forget** that the `f_v` were `ε_v`-approximations. Regard `f_v(C'_v), S'_e, T'_e, A'_e,
    B'_e` as sets subject only to (2)–(8), and choose them so as to **minimise** the total number of
    components of all the `A'_e ∩ B'_e` — the *Minimality condition*.
12. (250–251) Lemmas 1, 2, 3 ⇒ each `A'_e ∩ B'_e` is a single polygon carrying a generator of
    `H₁(A'_e)` and of `H₁(B'_e)`.
13. (251) Delete `f_w(C'_w) ∩ Int f_v(C'_v)` from `f_w(C'_w)`, for every `v, w`; get `D_v`.
14. (251) Build `f` on `Bd N`, extend over `C_v ∩ C_w`, then over `C_v`; the `φ`-estimate is read
    off **(2) alone**.

**Verified: the final maps need not stay close to the initial `f_v`.** Step 11 discards the
approximation property explicitly and step 14 cites only (2). Closeness to `h` survives solely
through `E_v ⊆ N(h(v), ε(C_v))`. The reviewer is right.

## 4. Conditions (1)–(8): margins and consumers

Margins are stated on the **source** side, where a producer must find room; "beats `ε_v + ε_w`"
means the two sides are moved by different maps.

| # | Paraphrase | Mentions | Used at | Margin |
|---|---|---|---|---|
| (1) 248 | `h(C_v) ⊆ Int E_v`, `E_v` a polyhedral 3-cell inside the `ε(C_v)`-ball about `h(v)` | `C_v, h, φ, E_v` | (2); L2; **step 14** | compact-in-open on the source, ball radius on the target. **Open**; its existence is [A] |
| (2) 249 | `E_v ⊇ f_v(C''_v)`, and `E_v ⊇ f_w(S_e)` for every `e = vw` | `E_v, C''_v, S_e, f_v, f_w` | L2 (new sphere bounds a 3-cell **in `E_w`**); step 14 | `dist(h(C''_v), Bd E_v) > 0`; also needs `S_e ⊆ C''_w`. **Open** |
| (3) 249 | `f_v(Bd C'_v) ∩ f_w(Bd C'_w) ⊆ Int A'_e ∩ Int B'_e` (hence `⊆ Int T'_e`) | both image spheres, `A'_e, B'_e, T'_e` | L1 (separation); makes `A'_e ∩ B'_e` **equal** the sphere–sphere intersection, needed at step 13 | source fact `Bd C'_v ∩ Bd C'_w ⊆ Int A_e ∩ Int B_e ⊆ Int T_e` **[P]**, plus positive distance from it to the rest of both spheres and to `Bd A_e`, `Bd B_e`; beats `ε_v + ε_w`. **Open** |
| (4) 249 | one component of `Bd A'_e` in `Int f_w(C'_w)`, the other in `M₂ − f_w(C'_w)` | `Bd A_e`, `C'_w` | L1 | source: the two circles of `Bd A_e` lie on opposite sides of `Bd C'_w` **[P]**. A **marked** inside/outside condition, not a distance: the producer must label the rim circles. **Open** once marked |
| (5) 249 | `B'_e ⊆ Int S'_e` and `Bd B'_e ⊆ M₂ − T'_e` | `B_e, S_e, T_e` | L1 (the `∼ 0 on S'_e` step); L2–L3 (surgery stays in `S'_e`) | source `B_e ⊆ Int S_e`, `Bd B_e ⊆ S_e − T_e`: two collars. `B_e` moves by `f_w`, `S_e, T_e` by `f_v`, so beats `ε_v + ε_w`. **Open** |
| (6) 249 | `⋃_v f_v(C'_v)` a neighbourhood of `h(K)`; no `S'_e` meets `h(K)` | `C'_v, S_e, K` | steps 13–14; protects the graph core through the L2/L3 surgeries | source: `⋃ Int C'_v ⊇ K`, `S_e ∩ K = ∅` with positive distance. Second half **open**; the neighbourhood half is **not local** — it needs local finiteness of the `C'_v` |
| (7) 250 | `T'_e` contains all but one component of `B'_e ∩ f_v(C'_v)`, and all but one of `B'_e − f_v(C'_v)` | `B_e, C'_v, T_e` | **L3** (forces `B'' ⊆ Int T'_e`) | a **connectivity certificate**, not a distance: each of `B_e ∩ C'_v`, `B_e − C'_v` has exactly one component reaching outside `T_e`, and it must stay connected under the move |
| (8) 250 | `A'_e ∩ B'_e` a finite disjoint union of polygons at which `Int A'_e`, `Int B'_e` **cross** | `A_e, B_e` | L1–L3; step 13 | **NOT open** — a final general position adjustment, itself small enough to preserve (2)–(7). Tangency is a real failure mode (digest `P`'s `{z=0}`/`{y=0}` model) |

Open under small moves: (1)–(6). Connectivity certificate: (7). General position: (8).
Non-emptiness of `A'_e ∩ B'_e` is **not** a condition — it is derived inside L1 (see D8).

## 5. Lemmas

### Inside the proof of 35.1

* **L1 (250).** Every polygon `J ⊆ A'_e ∩ B'_e` either bounds a disk in `A'_e` **and** one in
  `B'_e`, or carries a generator of `H₁(A'_e)` **and** one of `H₁(B'_e)`; the two *mixed* cases are
  excluded. Homological input, exactly: `H₁(A'_e) ≅ H₁(B'_e) ≅ H₁(T'_e) ≅ H₁(S'_e) ≅ ℤ`; each
  component of `Bd A'_e` carries a generator of `H₁(T'_e)`; by **(4)** `Bd f_w(C'_w)` separates
  those components in `M₂`, hence in `A'_e`; by **(3)** `Int A'_e ∩ Int B'_e` separates them, so
  some component `J₀` carries a generator `Z_{J₀}` of `H₁(T'_e)`. Mixed case: if `J` bounds in
  `A'_e` and generates `H₁(B'_e)`, then `Z_{J₀} ∼ p Z_J` in `B'_e` **[R]** while `Z_J ∼ 0` in
  `S'_e` (via `A'_e ⊆ T'_e ⊆ S'_e`), so `Z_{J₀} ∼ 0` in `S'_e` — impossible, since `Z_{J₀}`
  generates `H₁(S'_e)` and **(5)** gives `B'_e ⊆ Int S'_e`. The other mixed case is symmetric.
  External input: **27.3**, for the dichotomy on each annulus separately.
* **L2 (250).** Every component `J` of `A'_e ∩ B'_e` carries a generator of `H₁(A'_e)` and of
  `H₁(B'_e)`. Else by L1 `J` bounds `D_J ⊆ A'_e` and `E_J ⊆ B'_e`; take `D_J` innermost
  (`Int D_J ∩ B'_e = ∅`); replace `E_J` by `D_J` in `B'_e` and push the resulting annulus slightly
  off `A'_e`; the sphere `Bd f_w(C'_w)` becomes a new 2-sphere, which by **(2)** bounds a polyhedral
  3-cell `C ⊆ E_w` **[A: PL Schönflies inside a 3-cell, uncited]**. Replacing `f_w(C'_w)` by `C`
  preserves (2)–(8) and lowers the count — contradiction.
* **L3 (251).** Every `A'_e ∩ B'_e` is connected. Else there is an annulus `B'' ⊆ B'_e` with
  `Bd B'' ⊆ A'_e`, `Int B'' ∩ A'_e = ∅` (uses L2: the components are parallel core circles);
  `Bd B''` bounds an annulus `A'' ⊆ Int A'_e`; as `A'' ∩ Bd A'_e = ∅`, **(7)** gives
  `B'' ⊆ Int T'_e`, so `A'' ∪ B''` bounds a compact 3-manifold `C ⊆ Int T'_e`. Replace `B''` by
  `A''` in `Bd f_w(C'_w)` and push off `A'_e` near `A''`; same verifications; contradicts minimality.

### §34 Lemmas 1–3 (p. 240), whose conclusions the controlled form imports

* **L1.** From **33.1**: a regular nbhd `N` of `K¹` and a PLH `f₁ : N ↔ N'' ⊆ ℝ³` with (1) `N''` a
  nbhd of `h(K¹)`; (2) `D''_e ∩ σ' ≠ ∅` only if `e` is an edge of `σ`; (3) `C''_v ∩ σ' ≠ ∅` only if
  `v` is a vertex of `σ`; (4) `N''_σ` a nbhd of `J' = Bd σ'`; (5) `f₁` an `ε/3`-approximation.
  (2)–(5) hold whenever `f₁` is close enough; `N`, `f₁` can be put in prescribed nbhds.
* **L2.** `f₁` can be chosen so that `J' = Bd σ'` carries a generator of `π(N''_σ)`; via **30.8**
  and the shell configuration `S₁ ⊆ Int S₂` with `J = Bd σ` a spine of `N_σ`. **L3.** Each `σ'` has
  arbitrarily small polyhedral 3-cell nbhds `C_σ` with `Bd C_σ` in general position to `N''` and
  `Bd C_σ ∩ Bd N''` in general position to each `Bd D''_e`; via **30.5**.

## 6. The circle-removal / minimality argument — and what the book does not do

* **Quantity.** *The total number of components of all sets of the type `A'_e ∩ B'_e`* — a single
  global number over **all** edges (p. 250).
* **One operation.** A disk swap (L2) or annulus swap (L3) on the sphere `Bd f_w(C'_w)` inside
  `B'_e`. Its realisation is stated precisely (p. 250): to pass from `f_w(C'_w)` to `C` one
  **inserts or deletes a polyhedral 3-cell lying in `S'_e`**, then moves the closure by a
  homeomorphism **differing from the identity only in `Int S'_e`**. One step is therefore supported
  in `S'_e`, one edge's tube.
* **Why other edges are untouched: no argument is given [G].** It follows from the support statement
  only if `S'_e` misses every other edge's `A'_d, B'_d, T'_d, S'_d` and the other cells' boundaries.
  The `S_e` *can* be taken pairwise disjoint (small regular nbhds of circles on distinct splitting
  disks), but the book never says so, and (6) protects only `K`.
* **The infinite family.** Moise **minimises globally, in one sentence**, over the whole locally
  finite family, addressing neither that the total count is generically `∞` for infinite `K`, nor
  existence of a minimiser, nor that infinitely many surgeries compose to a map. For finite `K` the
  minimum is trivial. **For locally finite `K` this is a real gap [G]**, and digest `S` §3's remedy
  (label-wise finite descent with **fixed compact envelopes** `K_w ⊇ Q w`, so each label is operated
  on finitely often and each `G v` stops changing on `C''_v`) is a *replacement*, not a reading.

## 7. The final matching / deletion, and the output

1. (251) For every edge delete `f_w(C'_w) ∩ Int f_v(C'_v)` from `f_w(C'_w)`. Result **[A]**:
   polyhedral 3-cells `D_v` with `⋃ D_v` a neighbourhood of `h(K)`; `D_v ∩ D_w ≠ ∅` **iff** `v, w`
   are the ends of an edge, and then `D_v ∩ D_w` is a polyhedral **disk**; different such
   intersections are disjoint. No proof is written; this is where L3 + L2 + (8) + (3) are consumed —
   `A'_e ∩ B'_e` is one transverse circle, so each sphere is cut into two disks.
2. Choose a PLH `f : Bd N ↔ Bd ⋃ D_v` with `f(Bd (C_v ∩ C_w)) = Bd (D_v ∩ D_w)`; extend to
   `f(C_v ∩ C_w) = D_v ∩ D_w`; extend to `f(C_v) = D_v`. Three stages, on the **original** cells.
3. **Output:** `f : N → M₂` a PLH, `f(N)` a nbhd of `h(K)`, by **(2)** a `φ`-approximation. Markers
   downstream: `D_v ∩ D_w ≠ ∅ ↔ vw ∈ edges`, `f(D_e) = D_v ∩ D_w`, `f(C_v) = D_v`, the nbhd clause.
   **Not** available: §34 L1(2)–(4)'s simplexwise incidences, §34 L2's generator clause, the face
   tori, or any splitting-/face-disk data — exactly what `B-support-chain-scope.md` §2 adds.
4. **§34 L2's order (p. 240) is not in this proof.** There the **outer** torus `S₂` is fixed
   *before* `f₁` (margin (e): `N''_σ ⊆ Int S'₂`) and the **inner** torus `S₁` *after* `f₁`
   (clause (f): `S'₁ ⊆ Int N''_σ`). 35.1's only before/after pattern is "all source geometry and all
   `E_v` first, then `ε_v`, then `f_v`", plus (8)'s move. The nested torus certificate in
   `exists_section34EdgeMatching` is therefore an import from p. 240, and digest `S` §4 is right to
   put its choice before the quantifier over the approximation.

## 8. Discrepancy list

**(a) Lean predicates vs. the book.**
* **D1.** `Section34VertexPreparation` has **no clause bounding `Q w`** by a metric ball about `h w`
  or by `ψ`; the book's (1) is `E_v ⊆ N(h(v), ε(C_v))` and the whole final estimate is read off it
  (p. 251). As written the predicate cannot yield a `ψ`-approximation.
* **D2.** `src (.vertexBall w) ⊆ Cp w` asserts `C_v ⊆ C'_v`, which p. 248 does **not** assert and
  the book nowhere uses — an extra producer obligation, not a transcription.
* **D3.** The two "may be chosen inside any prescribed neighbourhood" clauses (`C'_w` near `C_w`,
  p. 248; `S_e` near `J_e`, p. 249) are what make (1) survive steps 5 and 7; with no counterpart for
  `Cp`, `Sn`, (1)-preservation is postulated rather than produced.
* **D4.** The `v`/`w` **role asymmetry is unrecorded**: nothing says `(ends e).2` is the *piercing*
  end, yet a vertex is pierced for one incident edge and piercing for another, and both the
  alteration (p. 248) and the deletion (p. 251) depend on that labelling.
* **D5.** `J_e ⊆ src (.splitDisk e)` records membership in the disk; p. 248 says **`Int D_e`**.
* **D6.** `G w '' Cc w ⊆ Q w` carries no margin, whereas (1) uses `Int E_v`; L2 needs room inside
  `E_w` after the `S'_e` surgery (p. 250).
* **D7.** Nothing asks the tubes to be **pairwise disjoint** (`Disjoint (Sp e) (Sp d)`, `e ≠ d`),
  which is what makes the p. 250 support statement isolate one edge.
* **D8.** `0 < cnt e` is asserted inside `Section34PiercingConditions`; in the book non-emptiness of
  `A'_e ∩ B'_e` is *derived* inside L1 ((3)+(4), p. 250) — a consequence moved into the interface.
* **D9.** Book (7) says *all but one*; the Lean form permits **zero** exceptional components (`y₀`
  is not required outside `Tp e`). Harmless for L3, weaker than printed (p. 250).
* **D10.** Correctly matched (all p. 249), worth keeping: `Sp e = G (ends e).1 '' Sn e`,
  `Tp e = G (ends e).1 '' Tn e` — the `v`-side map, i.e. "three uses of `f_v`, one of `f_w`";
  `Aa e = CpBd (ends e).1 ∩ Tn e`; `Bb e ⊆ CpBd (ends e).2`; `Bb₀ ∪ Bb₁ ⊆ Sn e \ Tn e`;
  `Tn e ∩ CpBd (ends e).2 ⊆ Bb e \ (Bb₀ ∪ Bb₁)`.
* **D11.** Book (6) is printed as "no `S'_e` intersects `K`" where `h(K)` must be meant
  (`S'_e ⊆ M₂`), p. 249; the Lean `Disjoint (Sp e) (h '' graphSkeletonSpace 𝒦)` reads it right.

**(b) Digest `S` vs. the book.**
* **D12.** `S` §1 "the alteration does not claim `C_v ⊆ C'_v`" — **confirmed**, p. 248.
* **D13.** `S` §2 "the three `CarriesFundamentalGroupOnto` fields suffice for L1" is incomplete:
  p. 250 also needs **(5)** for the `∼ 0 on S'_e` step and **27.3** for the per-annulus dichotomy.
  Also `A-section34-lemma-list.md` §0 cites 27.3 as p. 199; it is on **p. 198**.
* **D14.** `S` §3's fixed compact envelopes / per-label finite descent has **no counterpart in the
  book**: p. 250 minimises one global count. Sound, but record it as a formalisation-only device.
* **D15.** `S` §4's "outer torus before the universal quantifier" is p. **240** (§34 L2), not
  anywhere in pp. 248–251.
* **D16.** `S`'s "the final maps need not remain close to the initial approximations" —
  **confirmed**, p. 250 (forgetting paragraph) and p. 251 (the estimate cites (2) only).

## 9. Open questions

1. **249.** "Adding each `S_e` to the corresponding `C'_v`" is singular, but (2)'s `f_w(S_e)` forces
   `S_e ⊆ C''_w` too. Intended reading `C''_v = C'_v ∪ ⋃_{e ∋ v} S_e`?
2. **250.** The sets left free under minimality are `f_v(C'_v), S'_e, T'_e, A'_e, B'_e`, yet (2)
   also constrains `f_v(C''_v)` and `f_w(S_e)`, absent from that list. Which stay fixed?
3. **250.** Is the total component count finite for locally finite `K`? As printed the minimisation
   is ill-posed in the infinite case.
4. **251.** (1) puts both `h(C_v)` and `E_v ⊇ D_v` inside the `ε(C_v)`-ball about `h(v)`, so the
   triangle inequality gives `2ε(C_v)`. Was `E_v` meant to lie in the `ε/2`-ball?
5. **251.** No proof that each `D_v` is a 3-cell and each `D_v ∩ D_w` a disk. Is (3)+(8)+L2+L3
   enough, and what makes "different intersections are disjoint" true?
6. **250.** In L2, the step "new sphere inside `E_w`" ⇒ "bounds a polyhedral 3-cell `C`" cites
   nothing. Is `C ⊆ E_w` needed, or only `Bd C ⊆ E_w`?
