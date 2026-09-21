# Digest — answer to consult U and fifth review of the controlled 35.1 skeleton (snapshot `3c96610d`)

Marks: **[V]** checked by the lead; **[–]** not independently verified. The snapshot predates the
proved `IsPLCellOn` API (`PLCellOnBoundary.lean`, `PLCellOnInterior.lean`, commit `2a302ebb0`): the
reviewer's "API missing" remarks are already answered for boundary uniqueness, frontier in
codimension 0 and images of intrinsic interiors.

## Part 1 — consult U: the mixed-layer leaf is FALSE for every admissible `φ`
**Counterexample [V]** (lead recomputed both charts). Later chart
`H(x,y,t) = (x,y,t)` for `y ≤ 3x`, `(y/3, −2x+5y/3, t)` for `y ≥ 3x`. Sheet `A = {y = 0}` **completely
frozen**; old sheet `B₀ = ({y = x, x ≥ 0} ∪ {y = 3x/2, x ≤ 0}) × ℝ`. Current chart: `A` flat, `B₀`
crosses it with strict margin. Later chart: `H(A)` = the bent `L` with rays `e₁, e₂`,
`H(B₀) = {X = Y}` flat — in `u = X+Y`, `v = X−Y`: `u = |v|`, `v = 0`, margin `La·Lb = 0`. Translate
**only `B₀`** by `(−a,−a,0)`, any `a > 0`: near the origin it is the plane `y = x`, whose later-chart
rays are `e₁+e₂`, `e₂−e₁` against `A`'s `e₁, e₂` — the normal bent model with no margin. The move can
be tapered to zero on a fixed subdivision, `a < τ/√2`, placed over `Z ∩ P_m ∩ K` away from
`closure W_k`. **So: old later margin + current `hpersist` + one sheet entirely unmoved do not give
the conclusion**; and "a simplex has a frozen vertex" is far from "a whole local sheet is frozen".
* **Old points with strengthened wall conditions.** The old double line above lies *inside* the
  wall, so it does not refute a version whose old invariant records wall transversality. On an
  ordinary triangle–triangle block crossing a wall, finite mesh + strict margin + **quantitative
  transversality** do give openness; at a crossing point the "distance to the wall" is zero — use a
  transverse block with an angle bound there, distances only off the block. If a source fold line
  may coincide with a wall at a double point, the full relative stratified germ must be checked.
* **New non-free points do occur over `Z ∩ P_m ∩ K`** (one plane unmoved, the other slightly moved);
  `hsep` + full-preimage buffers keep them off `closure W_k`, not off `Z`.
* **Relative open-dense version: not refuted, not proved.** The finite conditions should come from
  the common refinement of "frozen-sheet stratification + transition stratification": movable faces
  avoid the fixed 0-strata and cross the fixed 1-strata they must meet; ordinary double curves cross
  2-dimensional walls; exclude un-forced coincidences "source fold point, other sheet, wall"; at the
  boundary the corresponding rank conditions inside `ker ℓ`, third vertex at positive height. Each
  determinant must be shown not identically zero **on the constrained parameter space**; forced
  situations (a frozen sheet containing a wall or a transition edge) need a block recognition
  modulo the fixed stratum, or full fibre retention.
* **"A finite PL transition is covered by finitely many open sets on which it is affine" is false**
  (no such neighbourhood of a wall point); refining the `W_j` does not help; ordering cannot avoid
  double curves not yet created.
* **Reviewer's preferred repair: a common protection layer.**
  `hmixedCover : AffectedNonFreeDoublePoints g ⊆ N`,
  `hfib : ∀ y ∈ N, D.domain ∩ g ⁻¹' {y} = D.domain ∩ ⇑D ⁻¹' {y}`,
  `hblocks : HasStableCrossingBlocksIn ⇑D D.domain ec_m ℓ_m BdM Q N η`; the supplier freezes the **full
  preimage** of a larger target neighbourhood with buffers; if the protection zone meets
  `closure W_k`, `hsep` must be rewritten.
  **Lead's doubt (unverified, to be put to the consultant):** over `N` nothing may move, so no
  affected non-free double point may have a moved fibre point; but the interface between moved and
  unmoved simplices (the mixed simplices) necessarily moves a little and necessarily carries double
  points — every double curve leaving `W_k` crosses the interface. Such points are non-free, not in
  any fibre-preserved `N`, and the counterexample above shows their later margin is not automatic.
  The protection layer therefore does not seem to remove the interface problem; what would is the
  *quantitative wall transversality in the invariant* of the first bullet.

## Part 2 — `Skeleton/ControlledGraphNeighborhood.lean`, fifth review
Docstring: drop "followed literally" — the order `C'_v → S_e,T_e → C''_v → ε_v → G_v → GP` is right,
but the outer torus comes from §34 p. 240 and the compact envelopes are our own device; and the
outer torus is still asked to swallow a `Q` that was chosen arbitrarily **before** it.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34CutFrame` | **OK** | the added `Q w ⊆ H s` is suppliable by finite local intersections of incident carriers |
| `exists_section34VertexPreparation` | **FALSE [–]** | a common chart does not let an arbitrary `Q` fit into a torus having the prescribed circle as spine |
| `exists_section34PiercingPackage` | **FALSE [–]** | the preparation is locally finite only in `⋃ Cc`; `hSpLF` in `h '' U` cannot be produced |
| `exists_section34ProtectedCircleRemovalStep` | **FIX** | the book's set-level surgery is not yet a relative realisation extending over all of `Cc`, protecting markers and other balls' boundaries |
| `exists_section34ProtectedCircleRemoval` | **OK** | each fixed compact `K_w` meets finitely many fixed supports; edge-wise descent stabilises every map on all of `Cc w`; no local finiteness of the `K` family needed |
| `exists_section34EdgeMatching` | **FIX** | per-ball markers, non-adjacent intersection control, and the ball/disk structure after deletion must come first |

* **Preparation counterexample:** `U = M₁ = M₂ = ℝ³`, standard locally finite triangulation and cut
  frame, `h(x,y,z) = (x+y, y, z)`, all `Q_w = ℝ³`: `hQint`, `hQchart` hold; the buffer puts all of
  `c_σ(h(σ))` inside `S_{2σ}` while its boundary must be the spine — the spine circle then bounds a
  disk in the torus, contradicting that it generates `π₁ ≅ ℤ`. **Repair:** choose `ct`, `Sd` *jointly*
  with the fine carriers `Q` and the cut neighbourhood, or give the outer torus and buffer first and
  choose `Q` afterwards. Adding `hQchart` alone is not enough.
* **Package:** `hSpLF` as a package field is fine, but the producer lacks the data: add
  `hQsub : ∀ w, Q w ⊆ h '' U` and
  `hQlfU : LocallyFinite (fun w => {y : h '' U | (y : M₂) ∈ Q w})` (the assembly has both); with
  `Sp e ⊆ Q (ends e).1` and finite vertex degree this gives `hSpLF`. The ambient is `h '' U`, **not**
  `⋃ Q`. (Counterexample mechanism: thin ball-shaped spikes on far `Sn eₙ` with tips
  `xₙ → p ∈ U \ ⋃ Cc`.)
* **(3)–(7):** the ordinary containments should come out of the package and be *proved* from the
  cell API plus a quantitative lemma "a compact subset of the interior stays in the interior of the
  image under a small C⁰ perturbation" (`image_frontier` alone does not give it). (7) needs an
  annulus collar lemma: pre-select a middle compact annulus `B_e⁰ ⋐ Int T_e` with marked inner/outer
  collars; the old `connectedComponentIn` witness cannot simply be transported.
* **Single step and matching — geometric certificates, not one more existential.** Add, supplied by
  preparation/package: per-ball marker `h '' simplexBody 𝒦' w.1 ⊆ interior (G w '' Cp w)`;
  `∀ w e, Disjoint (G w '' simplexBody 𝒦' w.1) (Sp e)`;
  `∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (Sp e) (G w '' CpBd w)`; non-adjacent balls
  disjoint. The step first proves that the relative ball replacement extends to a PL embedding of
  `Cc w`. Matching first outputs the 3-cell certificate of the `D_v` after deletion and the
  prescribed intersection disks, then uses a genuine relative PL extension theorem in three stages.

**Missing obligations:** joint choice of `Q` and outer torus; carrier local finiteness in the right
ambient; quantitative interior retention and annulus collars; relative ball replacement and the
cell structure after deletion. **Fixture:** locally finite triangulation of `ℝ³`, a non-identity
affine shear, fine carriers, standard piercing tubes, one removable extra circle in one tube.
**Biggest surprise:** "in one chart" is far weaker than "inside a torus with the prescribed circle
as spine"; and the ambient of a local finiteness statement was wrong once more.
