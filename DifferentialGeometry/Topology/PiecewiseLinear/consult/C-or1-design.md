# Lane C-or1 — design (statements only, phase 1). 2026-09-20

Target: in an orientable ambient 3-manifold the one-circle closed case of Lemma 2 cannot occur.
Route (c): produce a tube adapted to the two sheets and call the **already verified** endpoint
`IsCylindricalDiagram.not_closedBranchCase1` (`ClosedBranchOrientability.lean:289`).
No orientation theory for charts is built anywhere: orientability is consumed only inside that
endpoint (via `CylindricalMonodromy.lean:78` → `MobiusEmbedding.lean:56` → `MobiusBand.lean:333`).

Notation used throughout. `E` a finite dimensional real normed space, `L : SimplicialComplex ℝ E`
with `[Finite L.faces]`, `hL : IsCombinatorialManifold 3 L`, `hor : IsOrientable 3 L`,
`M := ↥L.space`, `letI := combinatorialChartedSpace L hL` (`VertexChart.lean:267`),
`D : SingularTwoCell M`, `BdM B : Set M`, `hD : NormalSingularCellData D BdM B`,
`c : hD.singularSet.Branch`, `hc : ¬hD.singularSet.IsBoundaryBranch c`,
`J : Set (EuclideanSpace ℝ (Fin 2))`, `hJ : IsPLSphere 1 J`, `hpre : hD.branchPreimage c = J`,
`Γ := hD.singularSet.branchCarrier c`, `ι : M → E` the coercion, `Dv := ι ∘ ⇑D`.
**Coercion discipline.** Every simplicial/cylindrical statement lives in `E`; every
`NormalSingularCellData` statement lives in `M`. Cross only through `ι`, never by `rw`.

---

## 1. Settling item (8): which tube

**Answer to the lead's question: the diagram must be re-chosen; the trace is not met in four
points per level.**

`exists_cylindricalDiagram_derivedNeighborhood_circle` (`NeighborhoodCylinder.lean:55`) is built
from `exists_ball_pair_with_boundary_cover_derivedNeighborhood_circle` (ibid.:21) plus
`exists_cylindricalDiagram_of_ball_pair` (`CylindricalDiagram.lean:87`), whose engine is
`exists_isPLHomeomorphOn_prism_map_ends` (`PrismDiskPair.lean:12`). I read that statement: its
conclusion controls **only the two end disks** —
`IsPLHomeomorphOn G (P ×ˢ Icc a b) K.space ∧ (∀ x ∈ P, G (x,a) = g x) ∧ G '' (P ×ˢ {b}) = D₁`.
The interior levels are an arbitrary existential PL homeomorphism of a ball pair; nothing forbids
the level disks from meeting the sheet trace in an arc, in six points, or in a whole 1-complex.
So option 2 is out, and the lead's option 3 is out **as a way of keeping the existing diagram**.

Option 3's *subdivision* is nevertheless kept, because it buys three things:
(i) the trace `Dv '' D.domain ∩ N` becomes a subcomplex, so all intersections are polyhedra;
(ii) `exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint`
(`NeighborhoodSolidTorus.lean:19`) gives `n ≥ 3` PL 3-balls `N_0..N_{n-1}` cyclically arranged,
with `N_i ∩ N_{i+1}` a PL **2-ball** contained in both intrinsic boundaries and all triple and
non-adjacent intersections empty — the skeleton of the tube, already proved;
(iii) each `N_i` is a derived-neighbourhood cell, i.e. a **cone**, and
`geometricLink_derivedNeighborhood_eq_of_subset` (`DerivedNeighborhoodLink.lean:306`) identifies
its link with the link in `secondDerived R`. So per-cell normalisation is a **cone-pair**
problem whose base is 2-dimensional, where `exists_isPLHomeomorphOn_of_fourSpokeChart`
(`FourSpokeAbstract.lean:53`) applies directly: it normalises a PL 2-ball with four spokes onto
another, with a prescribed boundary homeomorphism, a prescribed **page permutation `π`** and
prescribed spoke maps. `π` is literally the sheet exchange.

**Chosen: re-derive the tube carrying the sheets**, over the cyclic cell decomposition, with the
per-cell step done as a cone-pair extension of a four-spoke normalisation of the link pair.
Estimate for item 8: **1700–2600 lines** (down from 1800–3000: the four-spoke and marked-sector
machinery removes the two hardest sub-steps). Candidate reuse for the cone step, to be confirmed
in phase 2 before writing: `ConeDiskPairExtension.lean`, `ConePairExtension.lean`,
`BallPairRelativeGluing.lean`, `SphericalDiskPair.lean`, `BallMarkedExtension.lean`.

---

## 2. Statements

### Interface predicate A — `IsMarkedBranchCollar` (W-A endpoint, seam; see §3)

```lean
def IsMarkedBranchCollar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L)
    (D : SingularTwoCell (letI := combinatorialChartedSpace L hL; ↥L.space))
    (BdM B : Set ↥L.space) (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch)
    (J : Set (EuclideanSpace ℝ (Fin 2)))
    (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (κ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
    (sheet : ↥L.space → OpenPartialHomeomorph ↥L.space (ℝ × ℝ × ℝ)) : Prop :=
  hD.branchPreimage c = J ∧ IsPLSphere 1 J ∧
  -- (2) deck involution
  (ContinuousOn τ J ∧ MapsTo τ J J ∧ (∀ x ∈ J, τ (τ x) = x) ∧ (∀ x ∈ J, τ x ≠ x) ∧
    (∀ x ∈ J, ⇑D (τ x) = ⇑D x) ∧ (∀ x ∈ J, ∀ y ∈ J, ⇑D y = ⇑D x → y = x ∨ y = τ x)) ∧
  -- (3) two-sided source collar, t < 0 is the Q side
  (IsPLHomeomorphOn κ (J ×ˢ Icc (-1 : ℝ) 1) (κ '' (J ×ˢ Icc (-1 : ℝ) 1)) ∧
    κ '' (J ×ˢ Icc (-1 : ℝ) 1) ⊆ interior D.domain ∧ (∀ x ∈ J, κ (x, 0) = x) ∧
    doublePointPreimage (⇑D) D.domain ∩ κ '' (J ×ˢ Icc (-1 : ℝ) 1) = J) ∧
  -- (4) marked crossing chart at every point of the branch carrier
  (∀ y ∈ hD.singularSet.branchCarrier c, ∀ a ∈ J, ⇑D a = y →
      IsMarkedCrossingChartAt hD c J τ κ y a (sheet y)) ∧
  -- (5) the labelling is locally constant along the branch
  (∀ y ∈ hD.singularSet.branchCarrier c, ∀ y' ∈ hD.singularSet.branchCarrier c,
      ∀ z ∈ (sheet y).source ∩ (sheet y').source ∩ hD.singularSet.branchCarrier c,
      ∀ a ∈ J, ⇑D a = z →
        markedRayLabel hD c J τ κ (sheet y) z a = markedRayLabel hD c J τ κ (sheet y') z a)
```

### Interface predicate B — `IsMarkedCrossingChartAt` (item 4)

```lean
def IsMarkedCrossingChartAt … (y : ↥L.space) (a : EuclideanSpace ℝ (Fin 2))
    (e : OpenPartialHomeomorph ↥L.space (ℝ × ℝ × ℝ)) : Prop :=
  y ∈ e.source ∧ e y = 0 ∧ IsPiecewiseAffineOn e e.source ∧
    IsPiecewiseAffineOn e.symm e.target ∧
    ∃ A Bs : Set (EuclideanSpace ℝ (Fin 2)),
      a ∈ A ∧ τ a ∈ Bs ∧ Disjoint A Bs ∧ A ⊆ D.domain ∧ Bs ⊆ D.domain ∧
      A ∈ 𝓝 a ∧ Bs ∈ 𝓝 (τ a) ∧ InjOn ⇑D A ∧ InjOn ⇑D Bs ∧
      MapsTo ⇑D A e.source ∧ MapsTo ⇑D Bs e.source ∧
      (∀ᶠ z in 𝓝 y, z ∈ ⇑D '' A ↔ (e z).2.2 = 0) ∧
      (∀ᶠ z in 𝓝 y, z ∈ ⇑D '' Bs ↔ (e z).2.1 = 0) ∧
      (∀ᶠ z in 𝓝 y, z ∈ hD.singularSet.branchCarrier c ↔ (e z).2 = 0) ∧
      (∀ x ∈ A, (e (⇑D x)).2.1 < 0 ↔ ∃ s ∈ Ico (-1 : ℝ) 0, ∃ w ∈ J, x = κ (w, s)) ∧
      (∀ x ∈ Bs, (e (⇑D x)).2.2 < 0 ↔ ∃ s ∈ Ico (-1 : ℝ) 0, ∃ w ∈ J, x = κ (w, s))
```

`markedRayLabel … : Fin 2 × Bool` returns `(sheet index, inward?)` of the ray of `e` through a
given nearby point; spelled out in phase 2 as a `Fin 2 × Bool`-valued `def` on the four
half-axes of the chart.

**Deliberate non-requirement (this is the main risk reduction found in phase 1).** The predicate
does **not** pin which of the two cyclic orders `(a_in, b_in, a_out, b_out)` or
`(a_in, b_out, a_out, b_in)` occurs. Both discharge `IsSheetExchange` and `hsq` (checked in §2,
item 9), so no orientation convention is needed anywhere in W-A. Attempting to pin it would
require exactly the chart-orientation bridge that does not exist in this tree.

### Item 2 — deck involution

```lean
theorem NormalSingularCellData.exists_deckInvolution_branchPreimage [T2Space ↥L.space]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) :
    ∃ τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContinuousOn τ J ∧ MapsTo τ J J ∧ (∀ x ∈ J, τ (τ x) = x) ∧ (∀ x ∈ J, τ x ≠ x) ∧
        (∀ x ∈ J, ⇑D (τ x) = ⇑D x) ∧
        (∀ x ∈ J, ∀ y ∈ J, ⇑D y = ⇑D x → y = x ∨ y = τ x)
```
Producer: `branchProjection_fiber_encard_eq_two` (`BranchPreimage.lean:622`) defines `τ` as the
other element of `D.domain ∩ D ⁻¹' {D x}`; continuity from
`branchProjection_isLocalHomeomorph` (:449) / `branchProjection_isCoveringMap` (:608);
non-emptiness `branchPreimage_nonempty` (:666).
Junction/extreme tests. At a **vertex of Γ** nothing changes: the fibre bound `fiber_le_two` and
the crossing field are pointwise, so `τ` is defined there too. `τ x = x` is impossible: it would
make the fibre a singleton against `encard = 2`. Evaluate `τ` at a point of `J` lying over a
vertex and at one over an edge interior — same construction, no case split. Connectedness of `J`
is *not* used here (it is used only in item 9), so the lemma also holds in Case 2 — deliberate.
~250 lines.

### Item 3 — two-sided source collar

```lean
theorem exists_plCollar_of_frontier_isPLBall
    {P Q J : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (hQP : Q ⊆ interior P) (hfrontQ : frontier Q = J) :
    ∃ κ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn κ (J ×ˢ Icc (-1 : ℝ) 1) (κ '' (J ×ˢ Icc (-1 : ℝ) 1)) ∧
        κ '' (J ×ˢ Icc (-1 : ℝ) 1) ⊆ interior P ∧ (∀ x ∈ J, κ (x, 0) = x) ∧
        κ '' (J ×ˢ Icc (-1 : ℝ) 0) ⊆ Q ∧ κ '' (J ×ˢ Icc (0 : ℝ) 1) ∩ Q = J
```
Producer: `IsPLHomeomorphOn.exists_annulus_complex` (`AnnulusBoundary.lean:20`) for the two
one-sided annuli, glued along `J`; sides separated by `PlanarJordan` /
`Schoenflies.jordan_curve_theorem` as already used at `BranchPreimage.lean:334–350`; see also
`NestedCircleBicollar.lean`, `CircleAnnulusIsotopy.lean`.
Tests. Extremes `t = ±1` must land in `interior P` (shrink by compactness), `t = 0` is `J`
itself. The clause `κ '' (J ×ˢ Icc 0 1) ∩ Q = J` is the non-degeneracy check: it forbids the
"collar" from folding back into `Q`. Evaluate at a vertex of the polygon `J`: the collar is
built from the annulus complex, not from a normal line field, so corners of `J` are fine.
~300 lines.

### Item 4 — marked crossing chart producer

```lean
theorem NormalSingularCellData.exists_isMarkedCrossingChartAt
    (hD : NormalSingularCellData D BdM B) {c} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J τ κ} (hcollar : …(item 3 conclusion, objects fixed)…)
    (hτ : …(item 2 conclusion, objects fixed)…)
    {y : ↥L.space} (hy : y ∈ hD.singularSet.branchCarrier c)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) (hay : ⇑D a = y) :
    ∃ e, IsMarkedCrossingChartAt hD c J τ κ y a e
```
Producer chain: `branchCarrier_disjoint_boundary_of_not_isBoundaryBranch`
(`LoopTheorem/BranchCarrier.lean:471`) gives `y ∉ BdM`;
`NormalSingularCellData.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary`
(`LoopTheorem/InteriorTwoSided.lean:232`) gives the two-sided double crossing;
`HasPLTwoSidedCrossingAt.exists_openPartialHomeomorph_slab_interior_isImage`
(`BoundaryCrossingChart.lean:303`) gives the chart with `e.IsImage A {z | z.2.2 = 0}`,
`e.IsImage B {z | z.2.1 = 0}`, `e.IsImage (A ∩ B) {z | z.2 = 0}`; the two `<0` clauses are
then read off from the collar by continuity on each connected half-sheet.
Tests. **Vertex of Γ:** no special case — `crossing` holds at every double point, and the
upgrade needs only `y ∉ BdM`. **Corner of a sheet along Γ:** harmless, the whole crossing API is
PL-with-corners (charts are PL homeomorphisms of open sets, never affine). **Markings swapped:**
the predicate is symmetric under `a ↔ τ a` together with swapping the roles of `z.2.1` and
`z.2.2`; it is *not* symmetric under swapping only in/out, which is what makes item 10 true —
this asymmetry must be visible in the delivered statement.
~650 lines. Risk: the two `<0` clauses (the in/out reading), not the chart itself.

### Item 5 — labelling locally constant along the branch

```lean
theorem NormalSingularCellData.markedRayLabel_eqOn_of_isPreconnected
    (hD …) {c J τ κ} (hτ hcollar) {e e' : OpenPartialHomeomorph ↥L.space (ℝ × ℝ × ℝ)}
    (he : IsMarkedCrossingChartAt hD c J τ κ y a e)
    (he' : IsMarkedCrossingChartAt hD c J τ κ y' a' e')
    (hconn : IsPreconnected (e.source ∩ e'.source ∩ hD.singularSet.branchCarrier c)) :
    ∀ z ∈ e.source ∩ e'.source ∩ hD.singularSet.branchCarrier c, ∀ b ∈ J, ⇑D b = z →
      markedRayLabel hD c J τ κ e z b = markedRayLabel hD c J τ κ e' z b
```
Proof idea: the label is a `Fin 2 × Bool`-valued function that is continuous (locally constant)
on the overlap because both defining clauses of `IsMarkedCrossingChartAt` are `∀ᶠ … 𝓝` /
half-space conditions, and `Fin 2 × Bool` is discrete; conclude by `IsPreconnected.constant`.
**No orientation statement here, and none is needed** — see the deliberate non-requirement above.
Tests. Overlap empty: vacuous, so the consumer must supply connected overlaps (achieved by
taking the chart cover from `exists_finite_crossing_chart_cover`, `BranchPreimage.lean:51`, and
refining to arcs of Γ). Two points of Γ with the same label but different `b ∈ J`: excluded by
the `∀ b ∈ J, ⇑D b = z` binder, which pins the preimage.
~450 lines.

### Item 8 — the adapted tube

```lean
def IsAdaptedBranchTube {E …} (Dv : EuclideanSpace ℝ (Fin 2) → E) (dom Γ : Set E)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (N : Geometry.SimplicialComplex ℝ E) [Finite N.faces]
    (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) [Finite Pc.faces]
    (φ : (ℝ × ℝ) × ℝ → E) (u : (ℝ × ℝ) → (ℝ × ℝ)) (ρ : Fin 4 → ℝ × ℝ) : Prop :=
  IsPLBall 2 Pc.space ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
  IsCylindricalDiagram φ Pc.space N.space ∧
  IsPLHomeomorphOn u Pc.space Pc.space ∧ (∀ x ∈ Pc.space, φ (x, 0) = φ (u x, 1)) ∧
  (∀ i, ρ i ∈ (boundaryComplex 2 Pc).space) ∧ Function.Injective ρ ∧
  Γ ⊆ N.space ∧
  (∀ t ∈ Icc (0 : ℝ) 1,
      φ '' ((boundaryComplex 2 Pc).space ×ˢ {t}) ∩ Dv '' dom = Set.range fun i => φ (ρ i, t)) ∧
  MapsTo u (Set.range ρ) (Set.range ρ)
```

```lean
theorem exists_isAdaptedBranchTube
    (hL : IsCombinatorialManifold 3 L) (hD …) (hc …)
    (hmc : IsMarkedBranchCollar hL D BdM B hD c J τ κ sheet) :
    ∃ R N Pc φ u ρ, IsSubdivision R L ∧ IsOrientable 3 N ∧
      IsAdaptedBranchTube (ι ∘ ⇑D) D.domain (ι '' hD.singularSet.branchCarrier c) R N Pc φ u ρ
```
Producer chain, in order:
`branchCarrier_isPolyhedralSphere` (`LoopTheorem/BranchCarrier.lean:289`) →
`exists_isSubdivision_restrict_space` (`Subcomplex.lean:89`) makes `Γ` **and** the trace
subcomplexes of `R` → `IsOrientable.subdivision` (`Orientation.lean:8252`) →
`exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint`
(`NeighborhoodSolidTorus.lean:19`) for the `n ≥ 3` cells → per cell,
`geometricLink_derivedNeighborhood_eq_of_subset` (`DerivedNeighborhoodLink.lean:306`) +
`exists_isPLHomeomorphOn_of_fourSpokeChart` (`FourSpokeAbstract.lean:53`) to normalise the link
pair, then a cone-pair extension → splice the cells with
`isCylindricalDiagram_piecewise` (`CylindricalDiagram.lean:18`) and
`exists_cylindricalDiagram_of_ball_pair` (ibid.:87) in its marked form →
`IsOrientable.of_le` (`Orientation.lean:3153`) for `IsOrientable 3 N`;
`IsCombinatorialManifoldWithBoundary` of `N` from `hK.derivedNeighborhood`.
Tests. **Vertex of Γ:** it is a vertex of the 1-complex `restrict R Γ`, hence carries its own
derived-neighbourhood cell; the four spokes persist because the crossing normal form holds
there too (item 4). **No general position w.r.t. `L` is assumed anywhere** — `R` is a
subdivision, and `R.space = L.space`. **Degenerate `n`:** the decomposition lemma already
delivers `3 ≤ n`, so the cyclic splice has at least three cells and is not a self-gluing of one.
~1700–2600 lines. **Riskiest statement of the lane.**

### Item 9 — the sheet exchange, with the pairing spelled out

```lean
theorem exists_sheetExchange_of_branchPreimage_eq
    (hmc : IsMarkedBranchCollar …) (htube : IsAdaptedBranchTube … Pc φ u ρ)
    (hconn : ConnectedSpace ↥(hD.branchPreimage c)) :
    ∃ (g : loopCircle → ℝ × ℝ) (α β γ δ : ℝ),
      Continuous g ∧ BijOn g univ (boundaryComplex 2 Pc).space ∧
        g (α : loopCircle) = ρ 0 ∧ g (β : loopCircle) = ρ 1 ∧
        g (γ : loopCircle) = ρ 2 ∧ g (δ : loopCircle) = ρ 3 ∧
        IsSheetExchange u g α β γ δ
```

**The pairing.** Index the four rays by `(sheet, side)`. Fix a basepoint `y₀ ∈ Γ` and its two
preimages `a, τ a ∈ J`. Then
`ρ 0 = (a, in)`, `ρ 1 = (τ a, in)`, `ρ 2 = (a, out)`, `ρ 3 = (τ a, out)`,
i.e. `α = a_in`, `β = b_in`, `γ = a_out`, `δ = b_out`, and the two **sheets** are the opposite
pairs `{α, γ}` (sheet through `a`) and `{β, δ}` (sheet through `τ a`) — exactly the convention
of `IsSheetExchange` (`ClosedBranchOrientability.lean:205`).

*Why the cyclic order alternates.* `HasPLTwoSidedCrossingAt` carries the two sheets onto two
**transverse planes** `{z₃ = 0}`, `{z₂ = 0}`; their traces on a small link circle are two pairs
of points that separate one another, so the order along `∂Pc` is `a_?, b_?, a_?, b_?`. The two
rays of one sheet are therefore never adjacent. Formally: the four spokes of
`exists_isPLHomeomorphOn_of_fourSpokeChart` with `hcut : IsCutPair (frontier D₀) (v₀ 0) (v₀ 2)`
and `hv1 : v₀ 1 ∈ A₁`, `hv3 : v₀ 3 ∈ A₂` — the cut-pair hypotheses **are** the alternation, and
they are discharged by the transversality of the two planes, not by any orientation choice.

*Why `u` exchanges the sheets.* This is the only place Case 1 is used. `u` is the end map of the
tube, so on rays it is the monodromy of going once around `Γ`. The ray labelled `(a, in)` is
carried to the ray labelled `(τ a, in)`, because the label's first component is transported by
the deck monodromy of `branchProjection` and the preimage `J` is **connected** (`hconn`, from
`hpre + hJ`), so that monodromy is the non-trivial deck transformation `τ`; the second
component is preserved because `κ` is a collar on all of `J × [-1,1]`, i.e. `J` is two-sided in
the source. Hence `u : α ↦ β, β ↦ α, γ ↦ δ, δ ↦ γ`.
In Case 2 the monodromy is trivial and `u : α ↦ α`, which satisfies **no** disjunct of
`map_fst` — that is the exact point at which the lemma stops being applicable, and it is the
check that this delivery is not vacuous.

*Which hypothesis each fact discharges.*
`lt_fst/lt_snd/lt_thd/lt_period` ← the cyclic order of the four spokes, via
`exists_isPLHomeomorphOn_marked_circle_sector_of_arc_cover` (`MarkedCircleSector.lean:54`)
building `g` from the four boundary arcs with the marked endpoints at `0 < ¼ < ½ < ¾ < 1`.
`map_fst` ← `u (g α) = g β` (left disjunct). `map_snd` ← `u (g β) = g α` (left disjunct).
`map_thd` ← `u (g γ) = g δ` (right disjunct). `map_fth` ← `u (g δ) = g γ` (right disjunct).
`ne_fst` ← `g β ≠ g δ`, from `Function.Injective ρ` and `BijOn g`.
`ne_snd` ← `g α ≠ g γ`, likewise.

*Robustness check (done in phase 1, and the reason item 4 needs no orientation convention).*
The other possible cyclic order, `α = a_in, β = b_out, γ = a_out, δ = b_in`, gives
`u : α ↦ δ, β ↦ γ, γ ↦ β, δ ↦ α`, which discharges `map_fst` by its **right** disjunct,
`map_snd` by its right, `map_thd` by its left, `map_fth` by its left, and the two `ne`s
unchanged. Both orders are reflections of the four-point configuration, hence both are
orientation reversing, which is what the endpoint needs. So the conclusion does not depend on
which order occurs — and correspondingly the phase-2 proof must present item 9 as a **case
split on the two orders**, not as an assumed normalisation. A delivery that silently picks one
order without the case split is the failure mode flagged in phase 1.
~550 lines.

### Item 10 — the square of the monodromy fixes each ray

```lean
theorem apply_apply_eq_of_isMarkedBranchCollar
    (hmc : IsMarkedBranchCollar …) (htube : IsAdaptedBranchTube … Pc φ u ρ)
    (hg : … g, α from item 9 …) : u (u (g (α : loopCircle))) = g (α : loopCircle)
```
Proof idea: by item 9, `u (g α) = g β` and `u (g β) = g α`, both read off the label transport;
compose. The geometric content is that going around `Γ` **twice** lifts to going around `J`
**once**, which returns to the same point of `J` (a circle, not an interval) and to the same
side of `J` (the collar `κ` of item 3 is a product `J × [-1,1]`, i.e. an **annulus**, not a
Möbius band).
Tests. `J` once vs `Γ` twice: this is the whole lemma, so it must be stated with both `u (g α)`
and `u (u (g α))` and never with `u` alone. If the source neighbourhood of `J` were a Möbius
band the second component of the label would flip and `u²` would send `α ↦ γ`, killing the
contradiction — so the collar's `Icc (-1) 1` product form is load bearing and may not be
weakened to a one-sided collar.
~350 lines.

### Final theorem (item 11)

```lean
theorem NormalSingularCellData.not_branchPreimage_eq_of_isOrientable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) (hor : IsOrientable 3 L)
    {D : SingularTwoCell (letI := combinatorialChartedSpace L hL; ↥L.space)}
    {BdM B : Set ↥L.space} (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) : False
```
Assembly: items 2,3,4,5 ⇒ `IsMarkedBranchCollar`; item 8 ⇒ tube with `IsOrientable 3 N`;
items 9,10 ⇒ the configuration; then one call to `IsCylindricalDiagram.not_closedBranchCase1`
(`ClosedBranchOrientability.lean:289`) with `D := Pc`, `M := N`, `hM := hR.derivedNeighborhood _`,
`hor := IsOrientable.of_le …`, `hf`, `hu`, `hfu`, `hgc`, `hgb`, `hconf`, `hsq`.
Consumer instantiation, with no further hypothesis:
`L := double 3 K`, `hL := isCombinatorialManifold_double_succ_succ K S.isManifold`,
`hor := S.isOrientable_double_manifoldComplex hor`, `BdM := Bd`, `B := B`; `c, hc, hJ, hpre`
come from `exists_innermost_cleanDisk_replacement_of_exists_not_boundaryBranch`
(`LoopTheorem/ClosedBranchNestedDescent.lean:71`), left disjunct. ~150 lines.

---

## 3. The seam

**W-A's endpoint is `IsMarkedBranchCollar hL D BdM B hD c J τ κ sheet`**, with `τ`, `κ` and
`sheet` **fixed**, and it is *equal to* the full conclusion of W-A's producer

```lean
theorem exists_isMarkedBranchCollar
    (hD : NormalSingularCellData D BdM B) {c} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J Q} (hJ : IsPLSphere 1 J) (hQ : IsPLBall 2 Q) (hQint : Q ⊆ interior D.domain)
    (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J)
    (hpre : hD.branchPreimage c = J) :
    ∃ τ κ sheet, IsMarkedBranchCollar hL D BdM B hD c J τ κ sheet
```
— no recorded-properties bundle, no `∀ sheet, (some properties) → …`. W-B consumes the
predicate with the objects fixed by `obtain`.

**W-B may assume from it, and nothing else:** `hpre`, `hJ`; the six clauses of the deck
involution `τ`; the four clauses of the collar `κ` (in particular that `t < 0` is the `Q`
side and that the collar is a full product over `J × [-1,1]`); a marked crossing chart at
**every** point of `Γ` with **every** preimage; and local constancy of the label on connected
overlaps. W-B may **not** assume: any orientation of any chart, any cyclic-order convention,
any general position of `Γ` relative to `L`, or `InjOn D J` (false — `D` is exactly 2:1 there).

**Inhabitant obligation.** `IsMarkedBranchCollar` and `IsMarkedCrossingChartAt` are new
`Prop`-valued `def`s, so each needs its inhabitant theorem: `exists_isMarkedBranchCollar` above
and `exists_isMarkedCrossingChartAt` (item 4). Note that `NormalSingularCellData` itself still
has **no** inhabitant anywhere in the tree, so the whole lane is conditional on that structure
exactly as the rest of the Lemma 2 spine is; this must be said in the delivery report and must
not be repaired by adding hypotheses.
