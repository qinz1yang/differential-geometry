# AA — the construction inside the proof of Moise 33.1, in order (read-only, 2026-09-21)

Source: Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, printed pp. 230–238 (§33),
219–222 (§31), 223–229 (§32), 214–218 (§30), plus the cited statements in §§5, 17–18, 22, 26, 28.
**Book page + 10 = one-based PDF page.** Everything below is paraphrase in this project's notation.

**Purpose.** Replace re-reading the page images before `Skeleton/Section33Approximation.lean` is
written. Companion to `B-support-chain-scope.md` (§1 statement audit, §3 dependency table, §4
surface classification, §6 skeleton proposals) and `SECTION32_RESEARCH_20260919.md` (pseudo-cell
representation, 32.1's real difficulty); **neither is repeated here.** Style model: `T-…-digest.md`.
Flags: **[P]** printed as such; **[A]** asserted with no argument; **[G]** a gap the formalisation
must own; **[R]** my reading of an ambiguous line.

## 1. Statement of 33.1, and how `Moise331` renders it

**33.1 as printed (p. 230).** `K` a **finite, connected, 1-dimensional** polyhedron in `ℝ³` with
**no end-points**; `U` open with `K ⊆ U`; `h : U → ℝ³` a homeomorphism into `ℝ³`; `ε > 0` a
**constant**. Then there are a **regular neighbourhood `N` of `K` lying in `U`** and a PLH
`f : N ↔ X ⊆ ℝ³` with (1) `X` a neighbourhood of `K' = h(K)` and (2) `d(h P, f P) < ε` for every
`P ∈ N`. Remarks on the same page: the statement transfers to `K, U` inside the star of a vertex of
a triangulated `M₁³` and `h` into the star of a vertex of `M₂³`; "no end-points" is convenient, not
logically necessary, and is consumed exactly once, in Lemma 8; 33.1 is later superseded by 35.1.

**`Moise331` (`MoiseChain.lean:136`).** Faithful (B §1 rates it **F**, confirmed): finiteness,
`s.card ≤ 2`, an edge exists, `IsConnected L.space`, `neighborSet v |>.ncard ≠ 1` for "no
end-points", open `U ⊇ L.space`, `IsEmbedding (U.domRestrict h)`, constant `ε`, Euclidean source and
target. Deviations: (i) "regular neighbourhood" is spelled `derivedNeighborhood T L'` for an
explicit subdivision — more specific than the book, and what §34 Lemma 1 wants anyway; (ii) the
conclusion exposes only `N` and `f`, so the **dual cells `C_v`, splitting disks `D_e` and the
incidence markers that §34 Lemma 1 reads off 33.1 are not recoverable** — the same defect B §2
diagnoses for `Moise351`, so §33 will need a controlled form too, and the proposed leaf cut in §7
below is written so that the frame is an output; (iii) the manifold remark of p. 230 is not
rendered (harmless — the book explicitly declines that generality here).

## 2. Object table (order of introduction)

**Notation warning.** In §33 the prime means **`h`-image**: `C'_v = h(C_v)`, `K' = h(K)`,
`v' = h(v)`, `D' = h(D)`. This is *not* §35.1's prime (there `C'_v` is the altered dual cell). The
double prime `C''_v` is the handle piece of the tube, not the §35.1 `C''_v = C'_v ∪ ⋃ S_e`.
`Int E`, `Bd E` on a pseudo-cell are **cell-theoretic**, never ambient `interior`/`frontier`.

| Book | What it is | Chosen after | p. |
|---|---|---|---|
| `K`, `U`, `h`, `ε` | the data; `K` regarded as a finite complex | — | 230 |
| `St v` | star of `v` in `K`; subdivide so `δ|St v|` and `δh(|St v|) < ε/4` (uniform continuity on the compact `K`) | the data | 230 |
| `N`, dual cells `C_v`, splitting disks `D_e` | regular nbhd of `K` in `U` and its §32 cut data; `N` small enough that `δC'_v < ε/4` | the subdivision | 231 (defs 223) |
| `N' = h(N)` | the **tube**; carries images of the `D_e`, `C_v` as its splitting/dual cells | `N` | 223, 231 |
| `E = E_e`, center `P'_e = K' ∩ E` | a **pseudo-cell** per splitting disk, from 32.1–32.3 | `N'` | 231 (224–228) |
| `C''_v` | the handle pieces: `N' = ⋃ C''_v`, one vertex `v'` each, `C''_u ∩ C''_v ≠ ∅` iff `uv` is an edge and then `= E_{uv}`; by **32.3(8)** they can be put in arbitrarily small nbhds of `C'_v` | the `E_e` | 231 (228) |
| `X` | polyhedral 3-manifold with boundary, nbhd of `K'`, `X ⊆ Int N'`, `Bd X` in general position to each `E` | the `C''_v` | 231 |
| `J`, `D_J`, `A` | a component of `E ∩ Bd X`; the disk it bounds in `E − {P'}`; the annulus between two such | `X` | 231–232 |
| `X'`, `B` | the connectivity repair of L5 and the separating component of `Bd X'` | `X` | 232 |
| `X_v`, `A'_v = C''_v ∩ Bd X` | component of `X ∩ C''_v` containing `v'`; the surface piece over `v` | `X` | 232, 236 |
| LTD `Δ` | polyhedral disk with `Δ ⊆ Int N' − K'`, `Δ ∩ Bd X = Bd Δ`, `Bd Δ` not contractible in `Bd X` | `X` | 232 |
| `M²`, `M²₁` | the split surface of L7 and the component that separates | `Δ` | 233 |
| `i* : π(Bd X) → π(N' − K')` | the inclusion-induced map | the final `X` | 234 |
| `φ : Bd N × (0,1) ↔ Int N' − K'` | the tube's product structure; "straightforwardly demonstrable" **[A]** | `N`, `h` only | 235 |
| `X₁ = X − K'`, `X₂ = Int N' − Int X₁` | `X₁ ∪ X₂ = Int N' − K'`, `X₁ ∩ X₂ = Bd X` | `X`, `φ` | 235 |
| `ψ : [0,1]² → Int N' − K'`, `G = ψ⁻¹(|ψ| ∩ Bd X)`, `G₁`, `r` | the square-of-a-homotopy apparatus of Figure 33.1 | `X₁, X₂` | 235–236 |
| `A_v = Bd C_v ∩ Bd N` | the **source** surface piece over `v` | `N` | 236 |
| `f : Bd N ↔ Bd X`, `f(A_v) = A'_v` | the boundary matching (L13), built by an ordering `v₁,…,v_n` with `⋃_{i≤j} A_i` connected | L12 | 236–237 |
| `E'` | polyhedral disk replacing `E ∩ X`, differing from it only near `P'`, from **32.4** | `f` (see §7 risk 3) | 238 |
| `f : N ↔ X` | the output: extend over the `D_e` onto the `E'`, then over each `C_v` | `E'` | 238 |

**Imported from §31 (pp. 220–221), all inside §32's proofs, never named in §33.** Points `P_j`,
segments `P_jP_{j+1}`, 2-cells `D_j` with `D_j ∩ D_{j+1}` a 2-cell and `D_j ∩ D_{j+2} = ∅`, in the
right half-plane; rotate about the `y`-axis to get circles `J_j`, annuli `A_j`, solid tori `S_j`
with `T_j = Bd S_j` and `A_j ⊆ Int S_j`; `N = ⋃_{j=i}^{i+2} S_j`; `h : N ↔ N' ⊆ ℝ³`; the images
`A'_j, J'_j, S'_j, T'_j`; polyhedral solid tori `S''_j` with `T''_j = Bd S''_j`,
`A'_j ⊆ Int S''_j ⊆ S''_j ⊆ Int S'_j`, the `T''_j` pairwise in general position. That whole
apparatus is a **canonical configuration** (p. 221).

**Imported from §32.** Tube, splitting disk, dual cell (p. 223); open 2-cell and **pseudo-cell**
`E = U ∪ J` with center `P` (p. 223); the neighbourhood `W_e` of `Int D'_e − {P'_e}` that 32.1–32.3
take as input (pp. 224, 228); the handle pieces `C''_i` (p. 228).

## 3. Timeline of choices (the quantifier order is the content)

1. (230) Regard `K` as a finite complex; subdivide so that every `δ|St v|` is as small as wanted.
2. (230) `h|K` uniformly continuous on the compact `K` ⇒ may assume `δh(|St v|) < ε/4` for all `v`.
3. (230–231) **The whole `ε`-budget is fixed here, before any map exists:** the scheme is
   (1) `δC'_v < ε/4` and (2) `δf(C_v) < ε/4` with `v' ∈ Int f(C_v)`, whence
   `d(h P, f P) < ε/2` by the triangle inequality through `v'`.
4. (231) Choose `N` small; this fixes `C_v`, `D_e`, `N' = h(N)` and gives `δC'_v < ε/4`, because
   for `N` small the `C'_v` lie in preassigned neighbourhoods of the sets `h(|St v|)`.
5. (231) Per splitting disk choose `W_e` and the pseudo-cell `E_e` (32.1–32.3); by **32.3(8)** the
   resulting `C''_v` lie in arbitrarily small nbhds of the `C'_v`, giving **Lemma 1**:
   `δC''_v < ε/4`. Steps 4 and 5 are **one joint choice against one `ε/4`** (see §7 risk 1).
6. (231–233) Choose `X`, then re-choose it five times (L2 → L3 → L4 → L5 → L6/L7). Each re-choice
   is a **finite descent**: L3 and L4 lower the total number of components of the sets `E ∩ Bd X`,
   L7 lowers `p¹(Bd X)`. All seven properties are to hold of **one** `X`.
7. (233) **Lemma 8 modifies nothing** — a standalone technical lemma, used only inside L9.
8. (234) L9 is another finite descent, on the number of components of all `E ∩ Δ`.
9. (234–236) With `X` now fixed, read off `π(Bd X) ≅ π(N' − K') ≅ π(Bd N)` (L10), hence equal
   first Betti numbers, hence (L12) each `A'_v` is a disk with holes.
10. (236–238) Build `f : Bd N ↔ Bd X` with `f(A_v) = A'_v` (L13). **Everything metric is forgotten
    from step 6 onward**; the `ε`-estimate is never revisited — see §8 Q2.
11. (238) Replace each `E ∩ X` by the polyhedral disk `E'` (32.4); extend `f` over the splitting
    disks onto the `E'`; each `f(Bd C_v)` is then a PL 2-sphere; extend over each `C_v`.

**Where general position is invoked:** L2 (`Bd X` against every pseudo-cell, p. 231, **[A]**); L9
(the LTD `Δ` against every pseudo-cell, p. 234); 32.4 internally (`Bd C³` against `E`, p. 229);
§31's `T''_j` pairwise (p. 221). **What is forgotten at the end:** the `W_e`, the `X` of the
intermediate lemmas, the LTD machinery, and `Bd N`'s product structure.

## 4. The thirteen lemmas of §33

`P'` is always the center `K' ∩ E` of the pseudo-cell `E`. "PL-geometric" = no algebraic topology.

| # | p. | Paraphrase | Inputs | Applied at | Kind |
|---|---|---|---|---|---|
| 1 | 231 | the `C_v` and the `C''_v` can be chosen with `δC''_v < ε/4` | 32.1–32.3, **32.3(8)**, step 2 | the final estimate | PL-geometric |
| 2 | 231 | **[A] "evident", no proof.** There is a polyhedral 3-manifold-with-boundary `X`: a nbhd of `K'`, inside `Int N'`, with `Bd X` crossing every `E` in a 1-manifold | — | base of L3–L7 | **[G]** general position against a pseudo-cell |
| 3 | 231 | `X` can be chosen so no component `J` of `E ∩ Bd X` bounds a disk in `Int E − {P'}` | splitting `D_J ∪ Bd X` at `D_J` keeping `E` fixed; finite descent on the component count | L4, L6 | PL-geometric |
| 4 | 232 | each `E ∩ Bd X` is a **single polygon** | L3 + **[A]** "the components sit in `E` like concentric circles in a disk"; split off an annulus `A`; finite descent | L6, L8, endgame | PL-geometric + [G] |
| 5 | 232 | `X` and `Bd X` can both be taken connected | `K` connected; **30.2**; **26.6** | L6, L11, L13 | carries topology |
| 6 | 232 | each `A'_v = C''_v ∩ Bd X` is a connected 2-manifold with boundary, `Bd A'_v` inside the union of the `E` lying in `C''_v` | **30.2** (twice, via a "point at infinity" separation **[R]**), L4, L5 | L12, L13 | carries topology |
| 7 | 232–3 | no `C''_v` contains an LTD | splitting at `Δ`; `χ(M²) = χ(Bd X)+2`, `p¹(M²) = p¹(Bd X)−2`, and `p¹(M²₁) ≤ p¹(Bd X)−2` if `M²` splits; finite descent on `p¹(Bd X)` | L9 | surface `χ`/`p¹` bookkeeping |
| 8 | 233 | a polyhedral disk in `C''_{v₁} ∩ Int N'` whose boundary is its whole trace on `E₁` and encircles `P'₁`, and which misses every other `C''_{v₂}`, must meet `K'` | **32.4**; **`K` has no end-points** (this is the one use); a 2-sphere separation argument | L9 | PL-geometric |
| 9 | 234 | `Int N'` contains no LTD | general position of `Δ` against the `E`; L8 to kill polygon traces; a PLH dragging `Δ` for broken-line traces; finite descent; contradicts L7 | L10 | PL-geometric + descent |
| 10 | 234–6 | `i* : π(Bd X) ↔ π(N' − K')` is an isomorphism | injective: L9 + **26.4** (extended Loop theorem). surjective: the product structure `φ` **[A]**, the `X₁/X₂` decomposition, PL approximation of paths, **30.2** applied inside `[0,1]²` (Figure 33.1: a separating broken line in `G`) | L11, L12 | **carries the topology** |
| 11 | 236 | `Bd X ≅ Bd N` | L10 ⇒ `H₁` iso ⇒ equal `p¹`; **26.8** (orientability in `ℝ³`); **22.9** | **nowhere — see §5** | classification |
| 12 | 236 | each `A'_v` is a disk or a disk with holes | **[A]** "evidently a sphere with holes and possible handles"; the `p¹(Bd X) = p¹(Bd N)` equality of L10; a "direct computation" **[G]** | L13 | `p¹` counting |
| 13 | 236–8 | there is a PLH `f : Bd N ↔ Bd X` with `f(A_v) = A'_v` for every `v` | an ordering with `⋃_{i≤j} A_i` connected **[G]**; `A_i ∩ A_j ≠ ∅ ⇔ A'_i ∩ A'_j ≠ ∅ ⇔ v_iv_j` an edge, each such intersection a polygon; equal hole counts; **5.4** repeatedly (Figures 33.2, 33.3); the cyclic order `P',Q',R',S'` forced because otherwise `Bd X` would contain a Möbius band (**26.8** again) | endgame | PL, with one orientability input |

**"Easy to see" / unproved, i.e. formalisation obligations:** L2 entirely; L4's concentricity; L6's
"which is a disk" for `X_v ∩ E`; L10's product structure `φ`; L12's "evidently … possible handles"
and the "direct computation"; L13's vertex ordering; the endgame's claim that `E ∩ X` is a disk and
that `f(Bd C_v)` is a 2-sphere; and **the entire `ε`-estimate of step 3**, which is announced on
p. 231 and never returned to.

## 5. Exactly what is used from §31, §32, §30, §27–28, §22

**Directly cited by number inside pp. 230–238 — the complete census.** I read every page; there is
**no citation of §27 or §28 anywhere in §33**, and none of §31 either.

| cited | p. | statement in one line | used where in §33 | avoidable / weakenable? |
|---|---|---|---|---|
| 32.1 | 224 | given a splitting disk `D`, its dual cells `C₁,C₂`, and a closed nbhd `W` of `Int D' − {P'}` inside `C'₁ ∪ C'₂` with `W ∩ Bd(C'₁∪C'₂) = Bd D'` and `W ∩ K' = {P'}`: there is a pseudo-cell `E` with center `P'`, `Bd E = Bd D'`, `E ⊆ W`, `Int E` separating `v'₁` from `v'₂` in `Int(C'₁∪C'₂)`, hence `E ∩ K' = {P'}` | p. 231, once, for every splitting disk | **no** — this is the barrier that tames `h`'s oscillation; existence-only already |
| 32.2 | 227 | the same `E` can be chosen with `(C'₁∪C'₂) − E` having exactly two components `U_i`, each with `E ⊆ Fr U_i` and `Bd C'_i ∩ Bd N' ⊆ Fr U_i` | p. 231, with 32.1 | **no** — 32.3's `C''_i` are the `Ū_i` |
| 32.3 | 228 | disjoint `W_e` can be chosen so that the resulting `C''_i` (closures of the components of `N' − ⋃ E_e`) satisfy (7) one vertex each, **(8) inside arbitrarily small nbhds of `C'_i`**, (9) `N' = ⋃ C''_i`, (10) `C''_i ∩ C''_j = E_e` exactly on edges | p. 231; (8) is quoted explicitly | **no**; (8) is the only metric clause in the whole chain |
| 32.4 | 228–9 | for a pseudo-cell `E` with center `P'` in `ℝ³` and `δ>0` there is a polyhedral 2-cell `Δ₁ ⊆ N(P',δ)` with `Bd Δ₁ = Δ₁ ∩ E`, bounding a 2-cell in `E` that contains `P'` in its interior | L8 (p. 233) and the endgame (p. 238) | **no**; independent of 32.1 (`SECTION32_RESEARCH` §6) |
| 30.2 | 215 | a closed set with finitely many components separating `H` from `K` in a simply connected, locally connected `X` has a component that separates | L5, L6, L10 | no, but it is cheap and general |
| 26.6 | 194 | a compact connected polyhedral 2-manifold in `ℝ³` is 2-sided and `ℝ³ − M²` has exactly two components | L5 | no |
| 26.4 | 193 | extended Loop theorem: `M²` compact polyhedral, 2-sided in `Int M³`, `ker i*` non-trivial ⇒ a polyhedral 2-cell `Δ ⊆ Int M³` with `Bd Δ = Δ ∩ M²` not contractible in `M²` | L10, injectivity of `i*` | **no** — B §0.2 already puts a confined orientable `Moise264` on the goal path |
| 26.8 | 195 | a compact connected 2-manifold that is a polyhedron in a triangulation of `ℝ³` is orientable | L11 **and** L13 | **not removable**: L13's Möbius exclusion survives the deletion of L11 |
| 22.9 | 163 | two compact connected 2-manifolds are homeomorphic iff both orientable or both not **and** `χ` agrees | **L11 only, once** | **YES — removable, see the verdict below** |
| 5.4 | 43–4 | a PLH between the boundaries of two polyhedral disks extends to a PLH between the disks | L13, repeatedly | no; B §3 rates the bridge **S** |
| "18.2" | — | **misprint** (see §8 Q1) | endgame, p. 238 | replace by the ℝ³ analogue of 5.4 |

**Not cited by §33 but standing under §31/§32, for the skeleton's import list.** 31.1 (p. 221,
existence of the `S''_j`, by repeated **30.7**); 31.2 (p. 221, each `J'_j`, `J'_{j+1}` carries a
generator of `π(S''_j)`, by repeated **30.8**); 31.3 (p. 221, `S''_i ∩ S''_{i+2} = ∅`); 31.4
(pp. 221–2, a polygon in `T''_j ∩ T''_{j+1}` either carries generators of both `π(S''_j)` and
`π(S''_{j+1})` or bounds 2-cells in both, via **28.9** p. 204, **28.6** p. 204 and commutativity of
`π` of a solid torus). §32's proof of 32.1 consumes 31.4, plus **30.1/30.3** (splitting a
2-manifold apart at a 2-cell keeping a named surface fixed, pp. 214–215), **26.7** (p. 195),
**28.6**, **26.1**, **30.1**. §30 itself: **30.5** (p. 216: nested topological 3-cells with a
spherical shell between them admit a polyhedral 3-cell in between), **30.6** (p. 216: a toroidal
shell contains a polyhedral torus separating its two boundary tori), **30.7** (p. 217: nested
topological solid tori with a toroidal shell between them admit a CST in between), **30.8**
(p. 218: with `S₁ ⊆ Int S ⊆ S ⊆ Int S₂` as in 30.7 and `J` a spine of `S₁`, a loop traversing `J`
once generates `π(S)` — and the book stresses that **every** `S` from 30.7 qualifies, not merely
some `S`).

**Verdict on the project's 22.9 claim (B §4, `FREE_INPUTS.md` B1.d, `HANDOFF_CODEX_H` §H-M2):
CONFIRMED on both halves.** (i) 22.9 appears in §33 exactly once, on p. 236 inside Lemma 11; no
other §33 page cites §22. (ii) The use is avoidable, because **Lemma 11 has no consumer**: Lemma 12
uses only `p¹(Bd X) = p¹(Bd N)`, which Lemma 10 supplies directly by abelianising the `π₁`
isomorphism, and Lemma 13 builds its own, strictly stronger PLH `Bd N ↔ Bd X` carrying `A_v` to
`A'_v` out of 5.4 — it never consumes Lemma 11's unstructured homeomorphism. Three caveats the
claim should carry: (a) **26.8 is not deleted with 22.9** (L13's Möbius exclusion); (b) the capping
route replaces not only 22.9 but also L12's *unproved* "sphere with holes and possible handles", so
it is a repair of a gap, not only a substitution; (c) its own obligations are real — the χ/`b₁`
bookkeeping across the vertex graph (a Mayer–Vietoris count over the circles `A_u ∩ A_v`), the
capping complex and cap deletion, and a 1-dimensional Hurewicz/abelianisation bridge that must not
route through the sorried `Topology/Homology/HurewiczLowDegrees.lean`. The endpoint the route
lands on, `isPLSphere_two_of_faceEulerChar_eq_two` (`SurfaceSphereRecognition.lean:467`), is
indeed proved unconditionally in the tree.

## 6. Definitional prerequisites, and what the tree has

| object | p. | one-line paraphrase | compact? | in the tree |
|---|---|---|---|---|
| **pseudo-cell** | 223 | `E = U ∪ J` with `U` an open 2-cell, `J` a 1-sphere, `U ∩ J = ∅`, `closure U = U ∪ J`; a distinguished center `P ∈ U`; only `U − {P}` need be a polyhedron. `Bd E := J`, `Int E := U`, as **cell** notions. Need not be a 2-cell and is generally not locally connected at `J` | **`E` itself is compact** (it is `closure U` inside a compact bi-cell); what is *not* compact is the regular part `U − {P}`, which is neither closed nor bounded away from `J` | **absent**; `IsPolyhedron` is compact by construction (`Polyhedra.lean:13`, `isCompact` at `:23`), so the regular part must use `IsLocallyPolyhedral`. This refines the scoping line "§32's pseudo-cells are not compact": the cell is, its polyhedral part is not |
| **tube** | 223 | `N' = h(N)` for `h` a (merely topological) homeomorphism of a regular nbhd `N` of a 1-complex, carrying the images of `N`'s splitting disks and dual cells as marked data | yes for finite `K` | **absent**; the two `Tube` names in the tree belong to the loop-theorem lane |
| **splitting disk / dual cell of `N`** | 223 | a 2-cell `D` orthogonal to an edge at its midpoint with `D ∩ K = {P}`; the `D` cut `N` into 3-cells `C_v`, one vertex each | yes | `DualCells.lean`, `DualCellDecomposition.lean`, `LocallyFiniteSplittingDisks.lean` |
| **handle decomposition of a tube** | 228 | 32.3's output: `N' = ⋃ C''_i`, one vertex each, `C''_i ∩ C''_j = E_e` exactly on edges | yes | **absent** (`HandleCount`, `IsPLThreeHandleAttachment` are unrelated) |
| **canonical configuration** | 220–1 | the rotated chain `A_j, D_j, J_j, S_j, T_j` with `h` and the interpolating `S''_j, T''_j` in pairwise general position (see §2) | yes | **absent** |
| **LTD** ("Loop theorem disk") | 232 | a polyhedral disk `Δ ⊆ Int N' − K'` with `Δ ∩ Bd X = Bd Δ` and `Bd Δ` not contractible in `Bd X` | yes | **absent**; a §33-local definition, easy but it must be named |
| **combinatorial solid torus** | 201 | Moise's CST is the image of `σ² × [0,1]` under a PL identification of the two ends giving an orientable 3-manifold with boundary — i.e. exactly a **cylindrical diagram**. Separately, his "polyhedral solid torus" is a cyclic chain of polyhedral 3-cells (used in 28.1's proof, p. 201, and in §31 p. 221) | yes | **both, under swapped names.** `HasCylindricalDiagram` (`MoiseChain.lean:124`) is the faithful rendering of the book's CST; `IsCombinatorialSolidTorus` (`CombinatorialSolidTorus.lean:19`) is the cyclic-chain object. So the scoping line "`Moise307` concludes the wrong one" should be re-read as: 30.7's printed conclusion *is* the cylindrical-diagram object, and the real mismatch is with `Moise308Nested`'s hypothesis `IsCombinatorialSolidTorus S`; the bridge (28.1-style) goes one way or the other, and the choice must be made once |
| **toroidal shell** | 216 | `Y ≅ (torus) × [0,1]`, `Bd Y = T₀ ∪ T₁` | yes | `IsToroidalShell` (`MoiseChain.lean:112`) |
| **spine** | 218 | `φ : Δ × S¹ ↔ S`, `P ∈ Int Δ`, `J = φ(P × S¹)` | yes | `IsSpine` (`MoiseChain.lean:250`) |
| **carries a generator** | 218, 204 | a loop traversing `J` once generates `π(S)` (and `π(Int S)`); the `H₁` form in §28 | — | `Moise308` uses `Subgroup.closure (range …) = ⊤`; `Moise308Nested` (**proved**, `:389`) uses `Function.Bijective` of the induced map — the stronger and correct form |

## 7. Proposed cut for `Skeleton/Section33Approximation.lean`

Leaves at the natural joints, with the page range each covers. Every leaf that produces geometry
**outputs** it; nothing below takes a jointly-chosen object as a hypothesis.

| leaf | content | consumes | pp. |
|---|---|---|---|
| A. `frame` | from `K, U, h, ε`: subdivision, `N ⊆ U`, `C_v`, `D_e`, `N' = h N`, `E_e` with centers, `C''_v`, the incidence (10), **and** `δC'_v < ε/4`, `δC''_v < ε/4` | 32.1–32.3 incl. (8), uniform continuity | 230–1 |
| B. `initialX` | a polyhedral 3-manifold-with-boundary `X`: nbhd of `K'`, `⊆ Int N'`, `Bd X` crossing each `E` in a 1-manifold | general position against the regular part of a pseudo-cell | 231 |
| C. `normalizeTrace` | re-choose `X` so every `E ∩ Bd X` is one polygon encircling the center (L3 ∧ L4) | two nested finite descents on component counts | 231–2 |
| D. `connectPieces` | re-choose `X` so `X`, `Bd X` connected and each `A'_v` is a connected surface-with-boundary whose boundary circles are exactly the `E_e ∩ Bd X` at `v` (L5 ∧ L6) | 30.2, 26.6 | 232 |
| E. `noLocalLTD` | no `C''_v` contains an LTD (L7) | `χ`/`p¹` of a split surface; descent on `p¹(Bd X)` | 232–3 |
| F. `diskMeetsGraph` | Lemma 8 | 32.4, no end-points, 2-sphere separation | 233 |
| G. `noLTD` | `Int N'` contains no LTD (L9) | E, F, general position, descent | 234 |
| H. `tubeProduct` | `Bd N × (0,1) ≅ Int N' − K'` | `N`, `h` only | 235 |
| I. `piIso` | `π(Bd X) ≅ π(N' − K')` (L10) | G + 26.4; H + 30.2 + PL path approximation | 234–6 |
| J. `piecesAreDisksWithHoles` | each `A'_v` a PL disk with exactly `deg v` holes (L12, **without** L11/22.9) | I abelianised; capping + Euler/Betti over the vertex graph; `isPLSphere_two_of_faceEulerChar_eq_two` | 236 |
| K. `boundaryMatch` | PLH `f : Bd N ↔ Bd X` with `f(A_v) = A'_v` (L13) | J, 5.4, 26.8, a spanning-tree vertex ordering | 236–8 |
| L. `endgame` | `E'` from 32.4 with `Bd E' = E_e ∩ Bd X`; extend `f` over the `D_e`, then over each `C_v`; **and prove `δ f(C_v) < ε/4`, hence the `ε`-estimate** | 32.4, K, the ℝ³ analogue of 5.4 | 238 |

**Riskiest joints** — the "can be chosen jointly" pattern that burnt the project five times:

1. **A.** `N` (hence `C_v`, hence `C'_v`) and the `W_e` (hence `C''_v`) are chosen against *one*
   `ε/4` in one breath (p. 231, "the dual cells `C_v`, **and** the sets `C''_v`, can be chosen so
   that…"). A leaf that takes `N` as given and demands small `C''_v` is unprovable as stated; the
   frame must be a single existential, and it is also what the §34 consumer needs to read off.
2. **B–E.** Five consecutive "`X` can *also* be chosen so that…" statements. They must yield **one**
   `X` with L2 ∧ L3 ∧ L4 ∧ L5 ∧ L6 ∧ L7 at once, with the descent measures ordered so that a later
   repair cannot undo an earlier one (the book asserts this only for L3→L4 and for L7). Splitting
   them into independent leaves each producing "some `X`" makes the assembly false.
3. **K/L.** `f` is built on `Bd N` *before* the `E'` exist, then extended onto them. The `E'` must
   be produced from `(E, X)` with the clause `Bd E' = E ∩ Bd X` (available from L4 plus 32.4), and
   the endgame leaf must carry the **`ε`-estimate**, which the book states in its scheme on p. 231
   and never proves. If the estimate is a hypothesis anywhere below A, the endpoint is hollow.

## 8. Open questions

1. **p. 238.** "By repeated applications of Theorem 18.2" cannot be right: §18 is the Antoine set
   and its Theorem 2 (p. 129) says a loop in `ℝ³ − T₁` nullhomotopic in `ℝ³ − T₂` is nullhomotopic
   in `ℝ³ − T₁`. The step needs the ℝ³ analogue of 5.4 (a PLH between the boundaries of two
   polyhedral 3-cells extends over the cells) — PL Schönflies in `ℝ³`, §17, whose 17.12 the book
   does cite by name on p. 201. `PHASE3_APPROXIMATION_PLAN.md` R6 already substitutes S.7; this
   digest confirms the misprint from the source. Which printed theorem, if any, was meant?
2. **pp. 230–231, 238.** The `ε`-estimate is announced as a two-part scheme and never verified.
   `δ f(C_v) < ε/4` in particular: does it follow from `f(Bd C_v) ⊆ C''_v`, Lemma 1 and "the
   bounded complementary component of a small 2-sphere in `ℝ³` is small", and where does
   `v' ∈ Int f(C_v)` come from — only from `X` being a neighbourhood of `K'`?
3. **p. 231 (L2).** What is "general position relative to a pseudo-cell"? `X ⊆ Int N'` forces
   `Bd X ∩ Bd N' = ∅` hence `Bd X ∩ J = ∅`, and `K' ⊆ Int X` forces `P' ∉ Bd X`, so the trace
   lies in the polyhedral part `Int E − {P'}` and only finite PL general position is involved
   (this is `SECTION32_RESEARCH_20260919.md` §6's reading). Is that the intended proof of L2?
4. **p. 232 (L4).** "The components of `E ∩ Bd X` appear in `E` like concentric circles in a disk."
   Is this exactly L3 plus Schönflies inside the open 2-cell `Int E`, or is more needed at `J`?
5. **pp. 234–235.** The displayed map is `i* : π(Bd X) → π(N' − K')`, but the product structure and
   the `X₁/X₂` decomposition live in `Int N' − K'`. What identifies the two fundamental groups
   across `Bd N'`?
6. **p. 236 (L12).** "Evidently each `A'_v` is a sphere with holes and possible handles" and "a
   direct computation gives `p¹(Bd X) = p¹(Bd N)`". What is the computation — a Mayer–Vietoris
   count over the graph whose edges are the circles `E_e ∩ Bd X`? And what fixes the number of
   holes of `A'_v` as `deg v` (L4 + L6, presumably)?
7. **p. 237 (L13).** The ordering with `⋃_{i≤j} A_i` connected is asserted; for a finite connected
   graph this is a spanning-tree order. Does the inductive step handle **more than two** boundary
   components of `A_j` already lying in `⋃_{i<j} A_i` simultaneously, or only pairwise?
8. **pp. 201, 217, 221.** §31 calls the `S''_j` "polyhedral solid tori" while 30.7 delivers CSTs
   (cylindrical-diagram objects). Are they identified via 28.1, and which of the two does 30.8/31.2
   actually consume? The tree currently has one name for each and they are not connected.
