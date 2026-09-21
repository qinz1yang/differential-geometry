# AD — the constructions inside Moise §31 and §32, in order (read-only, 2026-09-21)

Source: Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, printed **pp. 220–222 (§31)**
and **pp. 223–229 (§32)**, plus the statements consumed: §30 pp. 214–218, §28 pp. 201–205,
§26 pp. 193–195. **Book page + 10 = one-based PDF page.** Everything is paraphrase in this
project's notation; formulas and letters are the book's.

**Purpose.** Replace re-reading the page images before any §31/§32 skeleton is cut, and audit the
definitional layer `CanonicalConfiguration.lean` / `PseudoCell.lean` against the source. Style
model: `T-section35-1-construction-digest.md`, `AA-section33-construction-digest.md`; §33's own
object table and lemma list are **not repeated** (see `AA`).
Flags: **[P]** printed as such; **[A]** asserted with no argument or read off a figure;
**[G]** a gap the formalisation must own; **[R]** my reading of an ambiguous or garbled line;
**[SLIP]** the printed symbol or cross-reference appears wrong.

## 1. Statements, and the standing notation

**The canonical configuration (pp. 220–221) [P].** Four points `P_i,…,P_{i+3}` in the *right-hand
half of the `xy`-plane* of `ℝ³`; segments `P_jP_{j+1}`; 2-cells `D_j` (`j = i,i+1,i+2`) with
`P_jP_{j+1} ⊆ Int D_j`, `D_j ∩ D_{j+1}` a 2-cell, `D_j ∩ D_{j+2} = ∅`. Revolve about the **`y`-axis**:
`P_j ↦` circles `J_j`, segments `↦` annuli `A_j`, `D_j ↦` solid tori `S_j` with `T_j = Bd S_j` and
`A_j ⊆ Int S_j`. Put `N = ⋃_{j=i}^{i+2} S_j` and let `h : N ↔ N' ⊆ ℝ³` be a homeomorphism;
`A'_j = h(A_j)`, `J'_j = h(J_j)`, `S'_j = h(S_j)`, `T'_j = h(T_j)`. Finally, for each `j`, a
**polyhedral solid torus** `S''_j` with `Bd S''_j = T''_j`, `A'_j ⊆ Int S''_j`, `S''_j ⊆ Int S'_j`,
the `T''_j` in **general position relative to one another**: each `T''_j ∩ T''_{j+1}` is a finite
union of disjoint polygons, **at which `T''_j` and `T''_{j+1}` cross one another**.

* **31.1 (p. 221).** Given `A_j, D_j, h` as in the definition, polyhedral solid tori `S''_j`
  completing a canonical configuration exist. *Proof: repeated applications of 30.7.*
* **31.2 (p. 221).** In a canonical configuration each of `J'_j` and `J'_{j+1}` carries a generator
  of `π(S''_j)`. *Proof: repeated applications of 30.8.*
* **31.3 (p. 221).** In a canonical configuration `S''_i ∩ S''_{i+2} = ∅`.
* **31.4 (pp. 221–222).** In a canonical configuration, let `J` be a polygon in `T''_j ∩ T''_{j+1}`.
  Then either **(1)** `J` carries a generator of `π(S''_j)` and a generator of `π(S''_{j+1})`, or
  **(2)** `J` bounds a 2-cell in `T''_j` **and** a 2-cell in `T''_{j+1}`.

**Tubes, pseudo-cells (p. 223) [P].** `K` a 1-dimensional complex in a PL 3-manifold `M`, `N` a
regular neighbourhood of `K`. For each edge `σ¹` a 2-cell `D`, "orthogonal to `σ¹` at its midpoint
`P`" (the quotation marks are the book's), with `D ∩ K = {P}`; the `D` cut `N` into polyhedral
3-cells `C_v`, one vertex each. `D` = *splitting disk*, `C_v` = *dual cell*. For `h : N → M'` a
merely topological homeomorphism, `N' = h(N)` is a **tube**, with splitting disks `h(D)` and dual
cells `h(C_v)`. If `U` is an open 2-cell, `J` a 1-sphere, `U ∩ J = ∅`, `Ū = U ∪ J`, `P ∈ U` and
`U − P` a polyhedron, then `E = U ∪ J` is a **pseudo-cell**, `Bd E := J`, `Int E := U`, `P` the
*center*. The case of interest is `U` **not** a polyhedron; then `P` is determined by `U`, and the
`E` built below are not even locally connected at `Bd E`.

**§32 prime convention.** `C'_i = h(C_i)`, `D'_e = h(D_e)`, `P'_e = h(D_e ∩ |K|)`, `K' = h(|K|)`,
`v'_i = h(v_i)`. (This is **not** §35.1's prime.) `C''_i = V̄_i`, `V_i` the component of
`N' − ⋃_e E_e` containing `v'_i`: the **handle pieces**.

* **32.1 (p. 224).** `N, K, h : N ↔ N' ⊆ ℝ³` a tube; `D` a splitting disk, `{P} = D ∩ |K|`,
  `C₁, C₂` the dual cells with `C₁ ∩ C₂ = D`, `v₁, v₂` their vertices. Let `W` be a closed
  neighbourhood of `Int D' − {P'}` lying in `C'₁ ∪ C'₂` with `W ∩ Bd(C'₁ ∪ C'₂) = Bd D'` and
  `W ∩ |K'| = {P'}`. Then there is a pseudo-cell `E` with center `P'` such that **(1)**
  `Bd E = Bd D'`, **(2)** `E ⊆ W`, **(3)** `Int E` separates `v'₁` from `v'₂` in `Int(C'₁ ∪ C'₂)`;
  hence **(4)** `E ∩ |K'| = {P'}`.
* **32.2 (p. 227).** Under the conditions of 32.1, `E` can be chosen so that `(C'₁ ∪ C'₂) − E` has
  **exactly two** components `U₁, U₂`, with, for `i = 1,2`: **(5)** `E ⊆ Fr U_i` and **(6)**
  `Bd C'_i ∩ Bd N' ⊆ Fr U_i`.
* **32.3 (p. 228).** With `W_e` chosen per edge satisfying 32.1/32.2 and pairwise disjoint, and
  `E_e`, `C''_i` as above: the `W_e` can be chosen so that **(7)** each `C''_i` contains only one
  vertex of `K'`, **(8)** the `C''_i` lie in **arbitrarily small neighbourhoods of the `C'_i`**,
  **(9)** `N' = ⋃_i C''_i`, **(10)** `C''_i ∩ C''_j ≠ ∅` (`i ≠ j`) only if `v_iv_j` is an edge `e`,
  and then `C''_i ∩ C''_j = E_e`.
* **32.4 (pp. 228–229).** `E` a pseudo-cell with center `P'` in `ℝ³`, `δ > 0`. Then there is a
  **polyhedral** 2-cell `Δ₁ ⊆ N(P', δ)` with **(1)** `J = Bd Δ₁ = Δ₁ ∩ E` and **(2)** `J` bounds a
  2-cell `D_J` **in `E`** containing `P'` in its interior. (`D_J` is *not* asserted polyhedral.)

## 2. Object table (order of introduction)

| Book | What it is | Chosen after | p. |
|---|---|---|---|
| `P_j, D_j` | 4 points, 3 planar 2-cells in the open right `xy`-half-plane, consecutive overlaps 2-cells, `D_j ∩ D_{j+2} = ∅` | — | 220 |
| `J_j, A_j, S_j, T_j` | their revolutions about the `y`-axis; `A_j ⊆ Int S_j` **[A]** | the `D_j` | 220 |
| `N = ⋃_{j} S_j`, `h`, `N'` | the three-torus chain and a topological embedding | `S_j` | 220 |
| `A'_j, J'_j, S'_j, T'_j` | `h`-images | `h` | 221 |
| `S''_j, T''_j` | polyhedral solid tori interpolating `A'_j ⊆ Int S''_j ⊆ S''_j ⊆ Int S'_j`, consecutive `T''` in general position | **all of the above** | 221 |
| `D` (32.1), `C₁, C₂`, `v₁, v₂` | splitting disk and its two dual cells | the tube | 223–4 |
| `W` | closed nbhd of `Int D' − {P'}` in `C'₁ ∪ C'₂`, meeting `Bd(C'₁∪C'₂)` in `Bd D'` and `K'` in `P'` | `h`, `D` | 224 |
| `A_i (i ∈ ℤ)`, `J_i` | bi-infinite concentric annuli exhausting `Int D − {P}`, `J_i = A_i ∩ A_{i+1}` | the model reduction | 224 |
| `S_i, S'_i, S''_i, T''_i` | a **bi-infinite** canonical-configuration family, every three successive as in §31; `S'_i ⊆ W`; `Cl(⋃S_i) = ⋃S_i ∪ {P} ∪ Bd D` | `A_i`, `W` | 224 |
| `K = ⋃_i T''_{2i}`, `L = ⋃_i T''_{2i+1} − ⋃_i Int S''_{2i}`, `M₁ = K ∪ L ∪ {P'}` | the initial separating surface | `S''_i` | 225 |
| `M₂ … M₆` | after Step 1 (disk splittings) and Steps 2–4 (deletions of Type 1/2/3 components) | `M₁` | 225–7 |
| `B_{2i+1}` | the surviving annuli, one per odd index, ends in `T''_{2i}` and `T''_{2i+2}` | `M₆` | 227 |
| `U`, `E = U ∪ Bd D'` | half of each `T''_{2i}` plus the `B_{2i+1}` plus `{P'}`: an **open 2-cell** **[A]**; the pseudo-cell | `M₆` | 227 |
| `U₁, U₂`, `B_i` | the two components of `(C'₁∪C'₂) − E`; auxiliary arcs `v'_i ↦ Bd C'_i ∩ Bd N'` | `E` | 227 |
| `W_e, E_e, P'_e`, `C''_i` | per-edge data and the handle pieces | all of the above, per edge | 228 |
| `C_{e,1}, C_{e,2}` | the 3-cell pair around `D_e` used to reduce 32.3 to 32.1/32.2 | `N` | 228 |
| `C³`, `Δ`, `D_J`, `Δ₁` | 32.4's polyhedral 3-cell about `P'`, the irreducible disk in `Bd C³`, the innermost disks, the output | `E`, `δ` | 228–9 |

## 3. Timeline of choices (the quantifier order is the content)

**§31.** (a) `P_j, D_j` and hence `J_j, A_j, S_j, T_j, N`; (b) `h`, hence all primed sets;
(c) **only then** `S''_j`, all three **jointly** (the general-position clause couples them).
31.2–31.4 quantify over a configuration already complete.

**§32.1.** 1. (224) Reduce to `C₁ ∪ C₂`; WLOG `D` is a round disk centred at the origin of the
`xz`-plane **[A: an ambient-PL-homeomorphism WLOG]**. 2. Exhaust `Int D − {P}` by concentric annuli
`A_i`, `i ∈ ℤ`. 3. Choose the solid tori `S_i` — **one sentence, one joint choice over the whole
bi-infinite family**: every three successive as in §31, `S'_i ⊆ W` (hence `S''_i ⊆ W`), and the
`S_i` inside neighbourhoods of the `A_i` small enough that `Cl(⋃S_i) = ⋃S_i ∪ {P} ∪ Bd D`.
4. (225) `S''_i` from 31.1; form `K, L, M₁`. 5. Lemmas 1–3. 6. (225–6) **Step 1**: split off
innermost disks `D_J ⊆ T''_{2i}` by 30.3 inside `Int S'_{2i}`, keeping `T''_{2i}` fixed; finitely
many per even index, indices taken in the order `0, 1, −1, 2, −2, …`. 7. (226) **Steps 2–4**: delete
Type-1 components `C'`, then Type-2 `Int C'`, then all but one Type-3 `Int C'` per odd index.
8. (227) Delete one of the two annuli of each `T''_{2i}`; the remainder plus `{P'}` is `U`.
**Everything metric is forgotten after step 3**; nothing in §32 is an approximation statement — the
only smallness clause in the whole chain is 32.3(8), and it is produced by choosing the `W_e`.

**§32.2** re-chooses `W` *after* the arcs `B_i` are drawn ("for appropriate choice of `W` we have
`B_i ∩ E = ∅`", p. 227) — the `W` of 32.1 is therefore not free at that point (**[G]**, see §7.13).
**§32.3** chooses all `W_e` at once, pairwise disjoint, each admissible for 32.1 and 32.2.
**§32.4** chooses `C³` after `E, δ`, then `Δ` irreducible, then finitely many innermost removals.

## 4. Proof structure, step by step

**31.1 (p. 221).** One line: repeated **30.7**. 30.7 needs `S₁ ⊆ Int S₂` topological solid tori with
`Cl(S₂ − S₁)` a toroidal shell and delivers a **CST** `S` with `S₁ ⊆ Int S ⊆ S ⊆ Int S₂`. Here
`S₂ = S'_j`; **the inner torus `S₁ ⊇ A'_j` and the toroidal shell are never produced** **[G]**, and
neither is the joint general position of the three `T''_j` that "repeated" is supposed to give.

**31.2 (p. 221).** One line: repeated **30.8**, in the form the book stresses on p. 218 — *every*
`S` as in 30.7 works, not merely some. Inputs: `J'_k` a spine of an inner solid torus,
`S₁ ⊆ Int S''_j ⊆ S''_j ⊆ Int S'_j`, the shell.

**31.3 (p. 221).** `D_i ∩ D_{i+2} = ∅ ⇒ S_i ∩ S_{i+2} = ∅ ⇒ S'_i ∩ S'_{i+2} = ∅` (`h` injective)
`⇒ S''_i ∩ S''_{i+2} = ∅` since `S''_k ⊆ S'_k`. Three lines, no external input.

**31.4 (pp. 221–222).** (i) `p_k` traverses `J'_k` once; by **31.2** `p_j` generates `π(S''_j)` and
`p_{j+1}` generates both `π(S''_j)` and `π(S''_{j+1})`. (ii) PL-approximate to `p'_j, p'_{j+1}`
"with the same properties" **[A]**; cycles `Z¹_j` on `S''_j − S''_{j+1}`, `Z¹_{j+1}` on
`S''_j ∩ S''_{j+1}`. (iii) The homotopy gives `Z¹_{j+1} ± Z¹_j = ∂C²` on `S''_j`; put
`Y¹_{j+1} = Z¹_{j+1} − ∂(C² ∧ S''_{j+1})` — this is the chain-intersection device of **28.11**,
cited only implicitly. (iv) `Y¹_{j+1}` generates `H₁(S''_{j+1})` and lives on
`T''_{j+1} ∩ Int S''_j`, so `|Y¹_{j+1}|` carries a generator. (v) For `J` a component of
`T''_j ∩ T''_{j+1}` we have `J ∩ |Y¹_{j+1}| = ∅`, whence `J` bounds a 2-cell in `T''_{j+1}` **or**
carries a generator of `H₁(S''_{j+1})`. The book cites **28.9**; the disjunction is **28.10**
(with `K = |Y¹_{j+1}|`), which itself rests on 28.7, 28.8, 28.9 **[SLIP/R]**. (vi) `H₁ ⇒ π` because
`π` of a solid torus is commutative. (vii) Symmetric argument in the other direction. (viii) The
mixed cases are excluded: if `J` bounded a 2-cell in `T''_j` and carried a generator of
`π(S''_{j+1})`, then `ker(i_* : π(S''_{j+1}) → π(S'_j ∪ S'_{j+1}))` would be everything, impossible
because `S'_j ∪ S'_{j+1}` is a solid torus **[A: it is `h` of the revolution of `D_j ∪ D_{j+1}`, a
figure fact]** and `J'_{j+1} ⊆ S''_{j+1}` carries a generator of `π(S'_j ∪ S'_{j+1})` **[R: the
printed last clause is a non-sequitur as written]**.

**32.1 (pp. 224–227).** *Lemma 1* (p. 225): `X ⊆ ⋃S'_i ∪ {P'}` with each `X ∩ S'_i` closed has
`Cl X ⊆ X ∪ Bd D'`, hence `X` closed in `Int(C'₁ ∪ C'₂)`; proof by local finiteness of the `S'_i`
away from `Bd D'` and `P'`. Also records that `Int(C'₁ ∪ C'₂)` is a PL 3-manifold for a rectilinear
triangulation of `ℝ³`. *Lemma 2* = **31.4**. *Lemma 3* (p. 225): `M₁` is closed in `Int(C'₁∪C'₂)`
(Lemma 1) and separates `v'₁` from `v'₂` there, because `Int D` separates `v₁` from `v₂` in
`Int(C₁∪C₂)` and the property is carried by `h`; `⋃S''_i ∪ {P'}` is a neighbourhood of
`Int D' − {P'}`, so its frontier separates, and `Fr V ⊆ M₁`. (Printed `{P}` for `{P'}` **[SLIP]**.)
*Step 1* (225–6): split `M₁` at innermost 2-cells `D_J ⊆ T''_{2i}` bounded by components of
`T''_{2i} ∩ T''_{2i±1}`, by **30.3** inside `Int S'_{2i}`, keeping `T''_{2i}` fixed; finite descent
per even index; separation survives because a broken line from `v'₁` to `v'₂` avoids a neighbourhood
of `Bd D'` and so would fail after finitely many steps. *Step 2* (226–7): classify each component
`C` of `L` in `T''_{2i+1}` by the number `k` of boundary circles carrying generators of
`H₁(S''_{2i+1})`; `k = 1` is impossible (a generator would bound) and `k > 2` by **28.6**, so
`k ∈ {0, 2}`. Type 1 (`k = 0`): after Step 1 `C` becomes a compact 2-manifold `C'` not separating;
delete by **30.1**. Type 2 (`k = 2`, both circles in the same `T''_{2i}`): **28.6** makes `C'` an
annulus and splits `T''_{2i}` into annuli `B₁, B₂`; **26.7** puts `Int B₁` in the bounded component
of `ℝ³ − (B₂ ∪ C')`, which contains neither `v'_i`; delete `Int C'`. Type 3 (`k = 2`, circles in
`T''_{2i}` and `T''_{2i+2}`): keep exactly one per odd index. *Endgame* (227): `M₆` is
`⋃T''_{2i} ∪ ⋃B_{2i+1} ∪ {P'}`; each `T''_{2i}` is cut by `Bd B_{2i−1} ∪ Bd B_{2i+1}` into two
annuli, delete one; the result `U` is **an open 2-cell with `U − {P'}` a polyhedron [A, no proof]**,
`Ū = U ∪ Bd D'` **[A]**, and `E = U ∪ Bd D'`.

**32.2 (pp. 227–228).** Arcs `B_i ⊆ C'_i − D'` from `v'_i` to `Bd C'_i ∩ Bd N'`, disjoint from `E`
for suitable `W`; `Int(Bd C'_i ∩ Bd N')` connected **[A]**, so it lies in the component `U_i`
containing `v'_i`, giving (6). Then `Int E − {P'}` is a polyhedral 2-manifold, so each of its points
has a 3-cell neighbourhood `C_Q = C_{Q,1} ∪ C_{Q,2}` split by a 2-cell `D_Q ⊆ Int E − {P'}`; each
`Fr U_i` contains all or none of each `Int D_Q`, hence (connectedness of `Int E − {P'}`) all or none
of `Int E − {P'}`; "none" contradicts 32.1(3). This gives (5), and the two halves of every `C_Q`
lying in `Ū₁, Ū₂` exclude a third component.

**32.3 (p. 228).** "It ought to be evident…"; the formal proof is four sentences: per edge take
3-cells `C_{e,1}, C_{e,2}` meeting in `D_e` whose union is a neighbourhood of `D_e` in `N`, small,
with `Cl(N − ⋃(C_{e,1} ∪ C_{e,2}))` a **finite** disjoint union of 3-cells (one per vertex); apply
32.1/32.2 with `C_{e,1}, C_{e,2}` as `C₁, C₂`; assemble each `C''_i` from one vertex component and
the appropriate "halves". **(7)–(10) are never verified and (8) is not argued at all** **[G]**.

**32.4 (pp. 228–229).** Take a polyhedral 3-cell `C³ ⊆ N(P',δ)` with `P' ∈ Int C³`, `C³ ∩ E` inside
a 2-cell of `E ∩ N(P',δ)`, and `Bd C³` in general position to `E` (finitely many disjoint polygons
at which they "cross") **[A: no definition of general position against a non-polyhedral `E`]**.
`Bd C³ ∩ E` separates `P'` from `Bd E` in `E`, so (30.2-style) one polygon does; it bounds a 2-cell
`Δ ⊆ Bd C³`; take `Δ` **irreducible** **[A: no well-founded measure given]**. Every other component
of `Δ ∩ E` bounds a 2-cell `D_J ⊆ (E − P') ∩ N(P',δ)`; remove them by splitting `Δ ∪ D_J` at
innermost `D_J`, finitely often. Output `Δ₁`.

## 5. What is consumed, and the tree status of each

| consumed | p. | one line | used at | tree status |
|---|---|---|---|---|
| **30.1** | 214 | Phragmén–Brouwer: `C ∪ D` separates ⇒ `C` or `D` does | 32.1 Step 2 Type 1 | **PROVED**: `separates_or_separates_of_union`, `Connected/PhragmenBrouwer.lean:12` (extra `hpath` hypothesis) |
| **30.2** | 215 | a closed separator with finitely many components has a separating component | 32.4 (implicitly), §33 L5/L6/L10 | **PROVED**: `exists_separates_of_finite_iUnion`, `Connected/SeparatingComponent.lean:9` |
| **30.3** | 215 | splitting a closed separator apart at a 2-cell, one side fixed, preserves separation | 32.1 Step 1 | **absent** as such; nearest are `Separates.of_frontier_replacement` / `.of_frontier_subset_replacement` (`Connected/Separation.lean:214,251`) — coverage [unverified] |
| **30.7** | 217 | nested topological solid tori with a toroidal shell admit a CST in between | 31.1 | **named only**: `Moise307`, `MoiseChain.lean:128`, concluding `HasCylindricalDiagram` (faithful to the printed CST) |
| **30.8** | 218 | for *every* `S` as in 30.7, a loop traversing a spine of `S₁` generates `π(S)` | 31.2 | `Moise308` (`MoiseChain.lean:257`) named only; **`Moise308Nested` PROVED** (`Moise308Nested.lean:310`, `moise308Nested` at `:389`), in the stronger `Function.Bijective` form, hypothesis `IsCombinatorialSolidTorus S` |
| **28.1** | 201 | a polyhedral torus (cyclic ring of four polyhedral 3-cells) in `ℝ³` is a CST | the notional bridge for 31.1 | **absent**; the two objects exist (`IsCombinatorialSolidTorus`, `CombinatorialSolidTorus.lean:19`; `HasCylindricalDiagram`, `MoiseChain.lean:124`) and are unconnected. Producers of the chain object exist for derived neighbourhoods: `isCombinatorialSolidTorus_derivedNeighborhood_circle`, `NeighborhoodSolidTorus.lean:81` |
| **28.6** | 204 | disjoint essential polygons on `T = Bd S`: every complementary component is an annulus bounded by two of them | 32.1 Step 2 (Types 2, 3; and `k > 2`) | **absent** for a CST boundary; `AnnulusComplement.lean:22`, `SurfaceAnnulusComplement.lean:22` give bicollar/complement facts for closed PL surfaces, not the annulus dichotomy |
| **28.9 / 28.10** | 204–5 | `J ∼ 0` on `T` ⇒ `J` bounds a 2-cell in `T`; with `K ⊆ T` carrying a generator of `H₁(S)`, a polygon in `T − K` not bounding carries a generator | 31.4 (v) | **absent** |
| **28.11** | 205 | chain intersection: `Z ∼ 0` on `K₁ ∪ K₂`, `Z` on `K₁` ⇒ a cycle on `K₁ ∩ K₂` homologous to it | 31.4 (iii), uncited | **absent** |
| **26.6** | 194 | a compact connected polyhedral 2-manifold in `ℝ³` is 2-sided, complement exactly two components | 32.2 (via 26.7), §33 L5 | **PROVED**: `IsPolyhedralManifold.isTwoSided`, `.not_isPreconnected_compl`, `.exists_connectedComponentIn_pair_compl` (`PolyhedralSurfaceComplement.lean:29,8,16`) |
| **26.7** | 195 | three connected polyhedral 2-manifolds with the same boundary and disjoint interiors: the unbounded frontier is two of them, the third's interior lies inside the union | 32.1 Step 2 Type 2 | **absent** |
| commutativity of `π` of a solid torus | 221 | — | 31.4 (vi) | available via `fundamentalGroupSolidTorusEquivInt` (used inside `Moise308Nested.lean`) |
| `Moise264` (26.4) | 193 | extended loop theorem | **not** in §31/§32 (it enters via 30.7's proof and §33) | named only, `MoiseChain.lean:57` |

Nothing in §31 or §32 cites §27, §5, §17, §22, or §33–§35. **31.1–31.4 are cited only inside §32**
(pp. 224–226); **§32 is cited only inside §33** (pp. 231, 233, 238).

## 6. The definitional layer, checked against the source

`CanonicalConfiguration.lean`, `PseudoCell.lean`, same directory, both listed under `FREE_INPUTS.md`
B1.d as definitions only, none of the eight propositions proved.

| declaration | verdict |
|---|---|
| `IsPlanarCellChain` | **faithful.** `halfPlane : p 2 = 0 ∧ 0 < p 0` is the printed "right-hand half of the `xy`-plane" plus the strictness the rotation needs; `segmentSubset`, `overlap`, `apart` are the three printed clauses; `Dint` carried as a parameter avoids ambient planar `interior`. Tested (`isPlanarCellChain_standard`) |
| `revolutionOf` | **faithful**: revolution about coordinate `1` = the `y`-axis |
| `IsRevolvedTorusChain` | **deviates (harmlessly, but UNTESTED).** `isSolidTorus : ∀ j, IsTopologicalSolidTorus (S j)` is a *conclusion* of the printed construction ("the 2-cells `D_j` give solid tori"), carried here as a **field**; likewise `annulusSubset`. As hypotheses of `Moise311` they weaken it; as a promise they need the missing brick "the revolution of a planar 2-cell in the open half-plane is a solid torus" |
| `IsCanonicalConfiguration` | **deviates on one clause (Q2).** `isPolyhedralSolidTorus : IsCombinatorialSolidTorus (S'' j)` is **stronger than the printed "polyhedral solid torus"** and is **not** the object 30.7 delivers. Everything else — `unionEq`, `isEmbedding`, `boundaryEq`, `annulusImageSubset`, `innerSubset`, `crossing`, `polygons` — is faithful |
| `Moise311` | faithful to p. 221; carries the unresolved CST/chain bridge |
| `Moise312` | faithful; the surjectivity spelling matches the `Subgroup.closure … = ⊤` form of `Moise308` and is implied by `moise308Nested`'s bijectivity |
| `Moise313` | faithful |
| `Moise314` | faithful, including the order of the disjunction and "bounds a 2-cell in `T'' k`" via an intrinsic PL parametrisation |
| `IsPseudoCell` | **faithful.** `IsLocallyPolyhedral (Eint \ {P})` together with `closureEq` and `disjointRim` is exactly "a (locally finite) polyhedron in `ℝ³ − ({P} ∪ Ebd)`": closedness in that open set follows from `closure Eint = Eint ∪ Ebd`. Caveat: the inhabitant `isPseudoCell_planarSquare` is **tame** (`Int E` is a polyhedron), i.e. the printed "case of no interest", so it does not test the definition against the objects §32 builds |
| `IsTube` | **deviates by omission.** Dropping "orthogonal" is correct (see below). Missing, and used by §32: (a) `Int D_e` **separates** the two vertices in `Int(C_i ∪ C_j)` (p. 225, Lemma 3); (b) `Int(Bd C'_i ∩ Bd N')` is **connected** (p. 227); (c) `Dbd e ⊆ frontier N`, without which `Moise321`'s `W ∩ frontier(h''C u ∪ h''C v) = h '' Dbd` may be unsatisfiable and `Moise321` vacuous [derivability from the present fields unverified]. `facesFinite` matches 32.3's proof but not p. 223 |
| `IsHandleDecompositionOfTube` | **deviates by omission.** Fields match 32.3(7),(9),(10) and 32.1(1),(4). Missing: 32.1(3) (`Int E_e` separates), and any relation of `Ec e` to `frontier (Cpp v)` — but `Fr C''_i = (Bd C'_i ∩ Bd N') ∪ ⋃_{e ∋ v_i} E_e` is exactly what 32.2(5)+(6) is for, and it is what §33's Lemmas 6 and 8 consume |
| `Moise321` | **faithful.** The `W` hypotheses render the four printed conditions correctly, including "closed neighbourhood of `Int D' − {P'}`" as `IsClosed W ∧ … ⊆ interior W`, and the separation is taken **inside the subspace**, as printed |
| `Moise322` | **deviates, and the deviation matters.** It drops 32.1(3) and 32.1(4) from the conclusion, and never says `h u ∈ U₁`, `h v ∈ U₂`. The book's `U_i` is *the component containing `v'_i`*; as stated, `U₁` and `U₂` are unlabelled and the separation of `v'₁` from `v'₂` is not recoverable, so 32.3's `oneVertex` field cannot be built from `Moise322`. And since `Moise321` and `Moise322` are separate `∀`-statements, their `E`s may differ — the classic joint-choice defect; the book says "*`E` can be chosen so that* …", i.e. one `E` with (1)–(6) |
| `Moise323` | **faithful**, and the quantifier order of (8) is right: the prescribed neighbourhoods `V v` are universally quantified **before** the data |
| `Moise324` | **wrong.** The book's `D_J` is a 2-cell *in `E`*; `Moise324` demands `IsPLHomeomorphOn s (stdSimplex ℝ (Fin 3)) DJ`, i.e. a **polyhedral** `D_J ⊆ Ec` with `P` in its intrinsic interior. `Eint` is an open 2-cell and is open in `Ec`, so by invariance of domain such a `D_J` would be a neighbourhood of `P` in `Eint`, making `Eint` locally polyhedral at `P` — i.e. making `E` tame, the case p. 223 calls uninteresting. So the clause is unsatisfiable on exactly the pseudo-cells §32 produces **[R: the invariance-of-domain step is my inference, not the book's]**. Fix: keep `Δ`/`Δbd` PL, state `D_J` as a topological 2-cell (or as `IsTopologicalCellWithInterior 2 DJ DJint` with `P ∈ DJint`) |

**The five recorded questions, answered.**

1. **p. 220 — must the `P_j` lie on the `x`-axis?** **No.** The printed text places only *the
   configuration* in the right-hand half of the `xy`-plane; `P_j` on the `x`-axis is a feature of
   Figure 31.1 only, and no clause of 31.1–31.4 or of 32.1's use (p. 224) needs it. The Lean
   `halfPlane` (which reaches the `P_j` through `segmentSubset : segment ⊆ Dint j ⊆ D j`) is
   exactly right; adding `P j 1 = 0` would be a strengthening with no consumer.
2. **pp. 217/221 — which solid torus?** Three distinct notions are in play. p. 201: a *polyhedral
   solid torus* is any polyhedron homeomorphic to `D² × S¹` ("every one is a CST, but we are not in
   a position to prove it"); a *polyhedral torus* (28.1) is the cyclic ring of four polyhedral
   3-cells = `IsCombinatorialSolidTorus`; a *CST* is the cylindrical-diagram object =
   `HasCylindricalDiagram`. p. 221 writes the **weakest** of the three. But 31.1's proof delivers a
   **CST** (30.7) and 31.2's proof consumes a **CST** (30.8, "`S` as in Theorem 7"). So: the printed
   *definition* consumes only "PL solid torus"; **30.8 and 31.2 consume the CST**. Using
   `IsCombinatorialSolidTorus` in the structure is therefore a deliberate re-aiming at
   `moise308Nested`'s hypothesis, and what 31.1 owes is **CST ⇒ cyclic ring** — the *easy* direction
   (slice the cylinder into `n ≥ 3` slabs; `CylinderCut.lean`,
   `exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint` are the machinery), **not** 28.1,
   which proves the hard converse. The module docstring's "31.1 still owes the bridge of 28.1" names
   the wrong direction.
3. **p. 221 — is "cross one another" asserted at every point?** **Yes.** The printed clause is:
   each `T''_j ∩ T''_{j+1}` *is* a finite union of disjoint polygons, **at which** the two surfaces
   cross; since the intersection equals that union, the crossing condition holds at every point of
   it. Only **consecutive** pairs are constrained; non-consecutive pairs are empty by 31.3. The Lean
   `crossing : ∀ j : Fin 2, ∀ x ∈ T'' j.castSucc ∩ T'' j.succ, HasPLCrossingAt …` is faithful. (One
   nuance: `HasPLCrossingAt` permits `α = 0 ∨ β = 0`, i.e. one side may be a half-plane; for two
   closed surfaces the intended case is `α = β = 0`. Weaker field ⇒ 31.1 easier, 31.2–31.4 harder.)
4. **p. 223 — is `U − P` finite or locally finite?** **Locally finite, necessarily.** `U` is an open
   2-cell, so `U − P` is never compact; Moise's polyhedra are explicitly allowed to be infinite
   (p. 214, "every simply connected polyhedron (finite or infinite)"), and in 32.1's construction
   `U − {P'}` is a countable chain of annuli, closed in `Int(C'₁ ∪ C'₂)` by Lemma 1. So
   `IsLocallyPolyhedral` is the right primitive, and — given `closureEq` — it is not a weakening.
5. **32.2(6) — is `Bd C'_i` the image or an intrinsic boundary?** **Both; they coincide.** §32's
   prime is the `h`-image (p. 228: `C'_i = h(C_i)`), so `C'_i` is a topological 3-cell; the
   cell-theoretic `Bd` is a homeomorphism invariant, hence `Bd C'_i = h(Bd C_i)`, and since `C'_i`
   has non-empty interior in `ℝ³` it also equals `frontier C'_i`. Same for `Bd N' = h(Bd N)`. So
   `Moise322`'s `h '' (frontier (C u) ∩ frontier N) ⊆ frontier U₁` is faithful on this point.

**Extra question — orthogonality and regularity.** "Orthogonal to `σ¹` at the midpoint" is in the
book's own quotation marks and is **used nowhere** in §32 or §33; all that is used is
`D_e ∩ |K| = {P_e}` and `C_i ∩ C_j = D_e`. "Regular neighbourhood", however, is used **beyond** the
cut properties `IsTube` records: in §32 for (a) `Int D` separating the two vertices (p. 225) and
(b) `Int(Bd C'_i ∩ Bd N')` connected (p. 227); in §33 for (c) the product structure
`Bd N × (0,1) ≅ Int N' − K'` (p. 235, Lemma 10) and (d) `A_v = Bd C_v ∩ Bd N` being a disk with
`deg v` holes (Lemmas 12–13). Also **smallness** — "if `K` is appropriately subdivided … the `C_v`
are of arbitrarily small diameter" (p. 223) — is a producer property, consumed only by §33 Lemma 1.

## 7. Discrepancy list (what our setting will not get for free)

1. **220 [A]** "The 2-cells `D_j` give solid tori `S_j`" and `A_j ⊆ Int S_j`: read off Figure 31.1.
2. **221 [G]** 31.1 = "repeated 30.7", but no inner solid torus around `A'_j` and no toroidal shell
   inside `S'_j` is produced; 30.7's hypotheses are never verified. This is the largest single gap
   in §31.
3. **221 [G]** "repeated" also hides that the three `S''_j` must be chosen *jointly*, since the
   general-position clause is a condition on pairs.
4. **221 [G]** The CST / cyclic-ring / PL-solid-torus trichotomy of Q2; no bridge is stated.
5. **221–2 [A]** 31.4: PL approximations `p'_k` "have the same properties"; **[SLIP]** the citation
   "28.9" should be 28.10; **[A]** `S'_j ∪ S'_{j+1}` is a solid torus (a figure fact about
   `D_j ∪ D_{j+1}`); **[R]** the closing sentence does not follow as printed.
6. **224 [A]** "We may regard `D` as a closed circular region … in the `xz`-plane": an ambient WLOG.
   In the project's chart-local, locally finite setting (digest `T` §1) this is a real transport
   lemma, and `C₁ ∪ C₂` is only a PL ball in a chart, not `ℝ³`.
7. **224 [G]** The **bi-infinite** family `S_i` is chosen in one sentence, against three conditions
   at once (canonical configuration on every successive triple, `S'_i ⊆ W`, the closure equation).
   Consecutive triples overlap, so 31.1's outputs must be compatible across `i`.
8. **225 [A]** Lemma 1's local finiteness, and "`K` is a 2-manifold; and by general position `L` is
   a 2-manifold with boundary" — general position of an infinite family of non-compact surfaces.
9. **225–6 [G]** Step 1 is a **finite descent per index inside an infinite process**, ordered
   `0, 1, −1, 2, −2, …`, with the limit object `M₃` and its separation property justified by the
   three-line "a broken line avoids a neighbourhood of `Bd D'`". This is the principal
   non-compactness gap of §32 and has the same shape as digest `T` §6's infinite-minimisation gap.
10. **226–7 [G]** Steps 2–4 delete infinitely many components "one at a time", with the same
    limit argument. No convergence of the sequence `M₃ → M₄ → M₅ → M₆` is established.
11. **227 [A]** `Bd B_{2i−1}` and `Bd B_{2i+1}` cut `T''_{2i}` into two annuli: another 28.6 use.
12. **227 [A]** The crux: "`U` is an open 2-cell and `U − {P'}` is a polyhedron", and
    "`Ū = U ∪ Bd D'`". `U` is an increasing union of disks only because `{P'}` compactifies the
    inner end, via the closure equation chosen on p. 224. No proof is written.
13. **227 [G]** 32.2 re-chooses `W` after the arcs `B_i` exist, although the statement is "under the
    conditions of Theorem 1" with `W` already fixed. The honest form is: `W` may be shrunk, or the
    arcs must be produced first. The Lean pair `Moise321`/`Moise322` inherits this: they must be
    **one** statement producing one `E` with (1)–(6).
14. **227 [A]** "the sets `Int(Bd C'_i ∩ Bd N')` are connected": a regular-neighbourhood fact not in
    `IsTube`.
15. **228 [G]** 32.3's proof is a sketch; (7)–(10) are unverified and **(8), the only metric clause
    in the §31–§33 chain and the input of §33 Lemma 1, is not argued at all**.
16. **228** 32.3 uses finiteness of `K` ("a **finite** union of disjoint 3-cells, one per vertex").
    For the locally finite `K` of §35 this must become a local statement.
17. **228–9 [G]** 32.4: "general position relative to `E`" for a set that is **not** a polyhedron at
    `P'` is used with no definition; existence of an **irreducible** `Δ` needs a well-founded
    measure; finiteness of `Bd C³ ∩ E` rests on the undefined general position.
18. **throughout** `Int`/`Bd` on `C'_i`, `E`, `D'` are **cell** notions on possibly wild cells, while
    26.6, 26.7, 30.1, 30.2 are applied to ambient complements in `ℝ³`. Every such switch needs an
    invariance-of-domain bridge.

## 8. Who consumes §31–§32 downstream, and which clauses

* **31.1, 31.3** — p. 224, the setup of 32.1's proof (existence of the `S''_i`; `S''_i ∩ S''_{i+2} = ∅`
  is what makes `K = ⋃T''_{2i}` a 2-manifold and `L` a 2-manifold with boundary).
* **31.2** — inside 31.4 only.
* **31.4** — p. 225, Lemma 2 of 32.1's proof; consumed through the Type 1/2/3 classification.
* **32.1(1)** `Bd E = Bd D'` — §33's endgame (p. 238), extending `f` over the splitting disks.
* **32.1(2)** `E ⊆ W` — §33 p. 231, to keep the `E_e` in disjoint prescribed neighbourhoods.
* **32.1(3)** separation — §32.2's own proof and §33 Lemmas 6, 8 (via `Fr C''_v`).
* **32.1(4)** `E ∩ |K'| = {P'}` — §33 Lemmas 3, 4, 8 (the center is the only graph point on `E`).
* **32.2(5),(6)** — §33 Lemma 6 (`Bd A'_v` lies in the `E`s inside `C''_v`) and Lemma 8.
* **32.3(7),(9),(10)** — §33 Lemmas 6, 8, 12, 13 and the endgame.
* **32.3(8)** — §33 **Lemma 1**, i.e. the whole `ε`-budget of 33.1.
* **32.4** — §33 Lemma 8 (p. 233) and the endgame (p. 238).
* Then **33.1** → §34 Lemma 1 (p. 240, the only use of §33 in §34) → **34.1** (p. 249) → **35.1**
  → **35.2**. So §31–§32 reach the goal only along `33.1 → 34.1 → 35.1`, and what §34 actually reads
  off 33.1 is the `ε`-approximation plus the incidence markers (T §5, §34 L1 (1)–(5)); the §32
  clauses that survive that far are **(8)**, **(7)/(9)/(10)** and **32.1(1)** + **32.4**.

**Cross-check against `A-section34-lemma-list.md` §0.** Its census agrees line for line on 32.1–32.3
at p. 231 and 32.4 at pp. 233, 238. §31 is absent from that table because the census covers
pp. 230–252 only; the four §31 theorems are consumed at pp. 224–226, inside 32.1. Adding a row
"31.1–31.4 → pp. 224–226, in the proof of 32.1" completes it. [The §34/§35 half of the table is
taken from `A` §0 and `T`; not re-verified against pp. 239–252 for this digest.]

## 9. Proposed leaves for two sorry-first skeletons

**`Skeleton/Section31CanonicalConfiguration.lean`** (endpoints `Moise311`–`Moise314`).

| leaf | content | size |
|---|---|---|
| `isTopologicalSolidTorus_revolutionOf` | the revolution of a planar 2-cell in the open right half-plane is a topological solid torus, the revolved segment an annulus in its interior | medium; also clears the `IsRevolvedTorusChain` UNTESTED flag |
| `revolutionOf_inter` | `revolutionOf X ∩ revolutionOf Y = revolutionOf (X ∩ Y)` for sets of the closed half-plane | **short** |
| `moise313` | from the above + injectivity of `h` on `N` + `innerSubset` | **short** |
| `isCombinatorialSolidTorus_of_hasCylindricalDiagram` | slice a cylindrical diagram into `n ≥ 3` slabs; the Q2 bridge 31.1 owes | short–medium (machinery in `CylinderCut.lean`) |
| `exists_innerSolidTorus_toroidalShell_of_annulusImage` | for `A'_j ⊆ Int S'_j` produce `S₁` topological solid torus with `A'_j ⊆ Int S₁ ⊆ S₁ ⊆ Int S'_j` and `Cl(S'_j − S₁)` a toroidal shell — **the hypothesis 30.7 needs and the book never supplies** | **deep** |
| `exists_generalPosition_triple_tori` | perturb the three `T''_j` into pairwise general position, preserving `A'_j ⊆ Int S''_j ⊆ S''_j ⊆ Int S'_j` | **deep** |
| `moise311` | assembly from `Moise307` + the two above | medium |
| `moise312` | from the proved `moise308Nested` + a spine certificate for `J'_k` | medium |
| `polygon_carries_or_bounds_on_cstBoundary` | 28.6 + 28.9 + 28.10 for the boundary torus of a CST | **deep**, nothing in the tree |
| `chain_intersection_homologous` | 28.11 | short–medium |
| `moise314` | the six-step argument of §4, plus "`S'_j ∪ S'_{j+1}` is a solid torus" as its own leaf | **deep** |

**`Skeleton/Section32PseudoCell.lean`** (endpoints `Moise321`–`Moise324`). The first design decision
is to **merge `Moise321` and `Moise322` into one producer** (§6, §7.13) and to add the three missing
`IsTube` fields (§6).

| leaf | content | size |
|---|---|---|
| `exists_roundDiskModel_of_splittingDisk` | the p. 224 WLOG, as a chart transport | medium |
| `exists_concentricAnnulusExhaustion` | bi-infinite `A_i`, `J_i`, and the `S_i` with the three joint conditions incl. `Cl(⋃S_i) = ⋃S_i ∪ {P} ∪ Bd D` | **deep** |
| `isClosed_in_interior_of_meets_each_solidTorus` | Lemma 1, p. 225 | short–medium |
| `separates_of_initialSurface` | Lemma 3: `M₁` closed and separating; needs `Int D` separates as an `IsTube` field | medium |
| `exists_innermostDiskSplitting_descent` | Step 1: 30.3-splitting, finite per even index, the `0,1,−1,2,−2,…` order, separation in the limit | **deep** |
| `componentBoundaryGenerators_eq_zero_or_two` | Step 2's `k ∈ {0,2}`, from 28.6 | **deep** (28.6 absent) |
| `separates_of_deleteTypeOne / TypeTwo / TypeThree` | the three deletions; consume 30.1 and 26.7 | medium ×3; **26.7 absent** |
| `isOpenTopologicalCell_annularChain` | the endgame: the half-annulus chain plus `{P'}` is an open 2-cell with polyhedral punctured part and closure adding `Bd D'` | **deep**; wholly unproved in the book |
| `exists_pseudoCell_twoComponents` | merged 32.1 + 32.2, one `E` with (1)–(6) and `h u ∈ U₁`, `h v ∈ U₂` | medium, given the above |
| `moise323` | the `C_{e,1}, C_{e,2}` reduction, the handle assembly, and **clause (8)** | medium–deep; (8) has no printed argument |
| `crossesPseudoCell` (definition) + `exists_generalPosition_ball_pseudoCell` | general position of `Bd C³` against a pseudo-cell: the missing §32 notion | **deep** |
| `moise324` | with `D_J` restated as a **topological** 2-cell; irreducible `Δ`, innermost removal | medium once the leaf above exists |
