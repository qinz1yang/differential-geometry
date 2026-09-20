/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.StageInwardPushFrame
import DifferentialGeometry.Topology.PiecewiseLinear.TaperedInwardPushFixing

/-!
# One stage of the inward push of a locally finite polyhedral three-manifold

`InwardPushStages.lean` reduces `Moise352InwardPush n` to a *stage* push: a piecewise linear
self-map of `K` which moves one compact piece `A` of the relative boundary `K \ interior K`
into `interior K`, is the identity on one compact piece `C` of `interior K` already moved by
the earlier stages, and moves no point further than a prescribed tolerance.  This file builds
that stage push, in dimension three.

## The construction

`StageInwardPushFrame.lean` supplies a compact local model `P` agreeing with `K` on an open set
`O ⊇ A ∪ C`, with `A ⊆ frontier P` and `C ⊆ interior P`.  Inside the presenting complex of `P`
the push is the tapered collar push of `TaperedInwardPushFixing.lean`, run with

* the height of `exists_isPolyhedron_nonneg_piecewiseAffineOn_pos`, positive on the preimage of
  `A` and vanishing on a polyhedral neighbourhood of the rest of the boundary surface;
* the fixed polyhedron `D` of the tapered push taken to be a polyhedral neighbourhood of the
  preimage of `C`, cut down to the complex, *together with the part of the collar above a
  level `a`*.

The second summand of `D` is what bounds the support.  The tapered push exposes no clause about
the collar coordinate of an arbitrary point, so the only way to know that it is the identity
high up in the collar is to place that part of the collar in the fixed set; the image of a
polyhedron under a piecewise linear homeomorphism is a polyhedron, so this costs nothing.  With
that clause the moved set is contained in `ρ '' ((B \ interior Z) ×ˢ Icc 0 a)`, a compact set
which the level `a` shrinks into any prescribed open set around `B \ interior Z`, because the
collar restricts to the identity at level `0`.  That compact set is the support `S`, and
`isPLOn_of_isPLOn_local_of_eqOn_id` extends the transported push by the identity over `K`.

## Main results

* `IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_stage_inward_dist_lt`: the stage
  push inside a finite combinatorial three-manifold with boundary, with its compact support
  inside a prescribed open set.
* `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isPLOn_stage_inward_dist_lt`: the stage
  push of a locally finite polyhedral three-manifold with boundary.

## The inverse

The inverse is asked for on `K` itself and not on an open set containing the image of the push.
A stage push fixes part of the relative boundary, so its image meets `K \ interior K`, and no
open set of the ambient manifold on which the inverse is piecewise linear can contain those
fixed boundary points: there the inverse is the transported collar map on the `K` side and the
identity off `K`, which is not piecewise linear on a full neighbourhood.  Piecewise linearity on
`K` is all a stagewise construction needs, because `IsPLOn.comp_of_mapsTo` composes along a
`MapsTo` hypothesis with no openness, and `IsPLOn.mono_of_isOpen` then restricts the accumulated
inverse to the open sets of `exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The stage push inside a finite combinatorial three-manifold with boundary.**

`A` is the compact part of the boundary surface which the stage moves off the boundary, `C` is
the compact part of the complex which the stage fixes, and `U` is an open set containing `A`
outside which the stage is the identity: the support `S` is compact and contained in `U`.

Every clause is the corresponding clause of
`IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt` relativised to
`A`, except the two new ones: the push is the identity off the compact `S ⊆ U`, and it is the
identity at every point it does not move off the boundary surface.  The latter replaces the
absolute clause `f x ∉ (boundaryComplex 3 K).space` of the unrelativised push, which is false
here because the push is the identity over the zero set of its height. -/
theorem IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_stage_inward_dist_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {A C U : Set E} (hA : IsCompact A)
    (hAB : A ⊆ (@boundaryComplex E _ _ (Classical.decEq _) 3 K).space) (hC : IsCompact C)
    (hCK : C ⊆ K.space)
    (hCB : ∀ x ∈ C, x ∉ (@boundaryComplex E _ _ (Classical.decEq _) 3 K).space)
    (hU : IsOpen U) (hAU : A ⊆ U) {Y : Type*} [MetricSpace Y] {h : E → Y}
    (hh : ContinuousOn h K.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, ∃ S : Set E, IsCompact S ∧ S ⊆ K.space ∧ S ⊆ U ∧
      IsPiecewiseAffineOn f K.space ∧ InjOn f K.space ∧ MapsTo f K.space K.space ∧
      (∀ x ∈ K.space, f x ∈ (@boundaryComplex E _ _ (Classical.decEq _) 3 K).space → f x = x) ∧
      (∀ x ∈ A, f x ∉ (@boundaryComplex E _ _ (Classical.decEq _) 3 K).space) ∧
      EqOn f id C ∧ EqOn f id (K.space \ S) ∧ IsPiecewiseAffineOn f' K.space ∧
      MapsTo f' K.space K.space ∧ EqOn f' id C ∧ EqOn f' id (K.space \ S) ∧
      LeftInvOn f' f K.space ∧ ∀ x ∈ K.space, dist (h (f x)) (h x) < ε := by
  classical
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  obtain ⟨W, ρ, R, hWpoly, hWK, hρ, hbottom, -, -, hRfinite, -, hRspace, -, -⟩ :=
    hK.exists_isPLHomeomorphOn_surface_prod_Icc K B hB Subset.rfl (a := 0) (b := 1) (by norm_num)
  let _ : Finite R.faces := hRfinite.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have hBpoly : IsPolyhedron B.space := isPolyhedron_space B
  have hBW : B.space ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hcover : W ∪ R.space = K.space := by
    refine Subset.antisymm (union_subset hWK hRK) fun x hx => ?_
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hRspace.symm ▸ subset_closure ⟨hx, hxW⟩)
  have hnhds := hρ.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom
  obtain ⟨O, hO, hBO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
  have hKR : K.space \ W ⊆ Oᶜ := by
    rintro x ⟨hxK, hxW⟩ hxO
    exact hxW (hOW ⟨hxO, hxK⟩)
  have hRO : R.space ⊆ Oᶜ := by
    rw [hRspace]
    exact closure_minimal hKR hO.isClosed_compl
  have hBR : Disjoint B.space R.space :=
    Set.disjoint_left.mpr fun x hxB hxR => hRO hxR (hBO hxB)
  obtain ⟨a₁, ha₁, -, ha₁le⟩ := hρ.exists_pos_forall_le_of_disjoint hWpoly hRpoly hBR hbottom
  obtain ⟨Z, hZpoly, hZsub, g, hgpl, hg0, hgA, hgZ⟩ :=
    exists_isPolyhedron_nonneg_piecewiseAffineOn_pos hBpoly hA hU hAU
  set B' := B.space \ interior Z with hB'def
  have hB'B : B' ⊆ B.space := fun y hy => hy.1
  have hB'c : IsCompact B' := hBpoly.isCompact.diff isOpen_interior
  have hB'U : B' ⊆ U := by
    intro y hy
    by_contra hyU
    exact hy.2 (hZsub ⟨hy.1, hyU⟩)
  -- the thinness level, chosen so that the low collar over `B'` stays inside `U`
  obtain ⟨V, hVopen, hV⟩ :=
    continuousOn_iff'.mp hρ.isPiecewiseAffineOn.continuousOn U hU
  set Λ := (B' ×ˢ Icc (0 : ℝ) 1) \ V with hΛdef
  have hΛc : IsCompact Λ := (hB'c.prod isCompact_Icc).diff hVopen
  have hΛpos : ∀ z ∈ Λ, 0 < z.2 := by
    intro z hz
    rcases lt_or_eq_of_le hz.1.2.1 with hlt | heq
    · exact hlt
    · exfalso
      have hzeta : ((z.1, z.2) : E × ℝ) = z := rfl
      have hz0 : ρ z = z.1 := by
        conv_lhs => rw [← hzeta, ← heq]
        exact hbottom z.1 (hB'B hz.1.1)
      have hmem : z ∈ ρ ⁻¹' U ∩ (B.space ×ˢ Icc (0 : ℝ) 1) :=
        ⟨by simpa only [mem_preimage, hz0] using hB'U hz.1.1, hB'B hz.1.1, hz.1.2⟩
      rw [hV] at hmem
      exact hz.2 hmem.1
  obtain ⟨a₀, ha₀, ha₀le⟩ : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ z ∈ Λ, a₀ ≤ z.2 := by
    rcases Λ.eq_empty_or_nonempty with hempty | hne
    · refine ⟨1, zero_lt_one, fun z hz => ?_⟩
      rw [hempty] at hz
      exact hz.elim
    · obtain ⟨z₀, hz₀, hmin⟩ := hΛc.exists_isMinOn hne continuous_snd.continuousOn
      exact ⟨z₀.2, hΛpos z₀ hz₀, fun z hz => hmin hz⟩
  set a := min a₁ (min (a₀ / 2) 1) with hadef
  have ha : 0 < a := lt_min ha₁ (lt_min (by linarith) zero_lt_one)
  have haone : a ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have haa₁ : a ≤ a₁ := min_le_left _ _
  have haa₀ : a < a₀ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hsmall : ∀ y ∈ B', ∀ t ∈ Icc (0 : ℝ) a, ρ (y, t) ∈ U := by
    intro y hy t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans haone⟩
    have hnotΛ : ((y, t) : E × ℝ) ∉ Λ := by
      intro hmem
      have h2 : a₀ ≤ t := ha₀le _ hmem
      linarith [ht.2]
    have hmemV : ((y, t) : E × ℝ) ∈ V := by
      by_contra hV'
      exact hnotΛ ⟨⟨hy, htI⟩, hV'⟩
    have hmem : ((y, t) : E × ℝ) ∈ V ∩ (B.space ×ˢ Icc (0 : ℝ) 1) :=
      ⟨hmemV, hB'B hy, htI⟩
    rw [← hV] at hmem
    exact hmem.1
  set S := ρ '' (B' ×ˢ Icc (0 : ℝ) a) with hSdef
  have hSprod : B' ×ˢ Icc (0 : ℝ) a ⊆ B.space ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hB'B hz.1, hz.2.1, hz.2.2.trans haone⟩
  have hSc : IsCompact S :=
    (hB'c.prod isCompact_Icc).image_of_continuousOn
      (hρ.isPiecewiseAffineOn.continuousOn.mono hSprod)
  have hSU : S ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsmall z.1 hz.1 z.2 hz.2
  have hSK : S ⊆ K.space := by
    rintro _ ⟨z, hz, rfl⟩
    exact hWK (hρ.bijOn.mapsTo (hSprod hz))
  -- the fixed polyhedron: a neighbourhood of `C`, together with the collar above level `a`
  obtain ⟨D₀, hD₀poly, hCD₀, hD₀B⟩ :=
    exists_isPolyhedron_neighborhood hC hBpoly.isClosed.isOpen_compl hCB
  have hDsub : B.space ×ˢ Icc a 1 ⊆ B.space ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, le_trans ha.le hz.2.1, hz.2.2⟩
  set Dup := ρ '' (B.space ×ˢ Icc a 1) with hDupdef
  have hDuppoly : IsPolyhedron Dup :=
    (hBpoly.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron
        (hBpoly.prod isHPolytope_Icc.isPolyhedron) hDsub)
      (hρ.bijOn.injOn.mono hDsub)
  set D := D₀ ∩ K.space ∪ Dup with hDdef
  have hDpoly : IsPolyhedron D := (hD₀poly.inter (isPolyhedron_space K)).union hDuppoly
  have hBD : Disjoint B.space D := by
    refine Set.disjoint_left.mpr fun y hy hyD => ?_
    rcases hyD with ⟨hy₀, -⟩ | ⟨z, hz, hzy⟩
    · exact hD₀B hy₀ hy
    · rw [← hzy] at hy
      have h0 := (hρ.mem_bottom_iff_snd_eq_zero hbottom (hDsub hz)).mp hy
      have h1 : a ≤ z.2 := hz.2.1
      linarith
  have hDWR : D ⊆ W ∪ R.space := by
    rw [hcover]
    rintro y (⟨-, hy⟩ | ⟨z, hz, rfl⟩)
    · exact hy
    · exact hWK (hρ.bijOn.mapsTo (hDsub hz))
  have hseam : ∀ y ∈ B.space, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R.space → g y = 0 ∨ a ≤ t :=
    fun y hy t ht hmem => Or.inr (haa₁.trans (ha₁le y hy t ht hmem))
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hfR, hfD, hfix0, hf'pl, hf'map, hf'R, hf'D, hinv,
      hdist⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt hWpoly hRpoly hDpoly
      hBD hDWR hBpoly.isCompact hbottom hgpl hg0 ha haone hseam (hh.mono hWK) hε
  rw [hcover] at hfpl hfinj hfmap hfB hf'pl hf'map hinv hdist
  -- the push is the identity wherever it does not leave the boundary surface
  have hfBfix : ∀ x ∈ K.space, f x ∈ B.space → f x = x := by
    intro x hx hmem
    obtain ⟨hxB, hgx⟩ := hfB x hx hmem
    have hfx := hfix0 x hxB hgx 0 ⟨le_rfl, zero_le_one⟩
    rwa [hbottom x hxB] at hfx
  have hfA : ∀ x ∈ A, f x ∉ B.space := by
    intro x hx hmem
    obtain ⟨-, hgx⟩ := hfB x (hWK (hBW (hAB hx))) hmem
    exact (hgA x hx).ne' hgx
  have hfC : EqOn f id C := fun x hx => hfD (Or.inl ⟨interior_subset (hCD₀ hx), hCK hx⟩)
  have hf'C : EqOn f' id C := fun x hx => hf'D (Or.inl ⟨interior_subset (hCD₀ hx), hCK hx⟩)
  -- the support
  have hfS : EqOn f id (K.space \ S) := by
    intro x hx
    have hxWR : x ∈ W ∪ R.space := by rw [hcover]; exact hx.1
    rcases hxWR with hxW | hxR
    · have hτx : Function.invFunOn ρ (B.space ×ˢ Icc (0 : ℝ) 1) x ∈ B.space ×ˢ Icc (0 : ℝ) 1 :=
        hρ.symm.bijOn.mapsTo hxW
      have hrx : ρ (Function.invFunOn ρ (B.space ×ˢ Icc (0 : ℝ) 1) x) = x :=
        hρ.bijOn.invOn_invFunOn.2 hxW
      set z := Function.invFunOn ρ (B.space ×ˢ Icc (0 : ℝ) 1) x with hzdef
      have hzeta : ((z.1, z.2) : E × ℝ) = z := rfl
      by_cases hg : g z.1 = 0
      · have hfx := hfix0 z.1 hτx.1 hg z.2 hτx.2
        rw [hzeta, hrx] at hfx
        exact hfx
      · have hZmem : z.1 ∉ Z := fun hmem => hg (hgZ _ hmem)
        have hB'mem : z.1 ∈ B' := ⟨hτx.1, fun hmem => hZmem (interior_subset hmem)⟩
        by_cases hta : z.2 ≤ a
        · exact absurd ⟨z, ⟨hB'mem, hτx.2.1, hta⟩, hrx⟩ hx.2
        · exact hfD (Or.inr ⟨z, ⟨hτx.1, le_of_not_ge hta, hτx.2.2⟩, hrx⟩)
    · exact hfR hxR
  have hf'S : EqOn f' id (K.space \ S) := by
    intro x hx
    have h1 : f x = x := hfS hx
    have h2 := hinv hx.1
    rwa [h1] at h2
  exact ⟨f, f', S, hSc, hSK, hSU, hfpl, hfinj, hfmap, hfBfix, hfA, hfC, hfS, hf'pl, hf'map,
    hf'C, hf'S, hinv, hdist⟩

end Complex

section Manifold

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]

/-- **One stage of the inward push of a locally finite polyhedral three-manifold with
boundary.**

The stage moves the compact part `A` of the relative boundary into the interior, fixes the
compact part `C` of the interior pointwise, moves no point of `K` further than the prescribed
tolerance measured after `h`, and has a piecewise linear left inverse defined and piecewise
linear on the whole of `K`.

The dichotomy `p x ∈ interior K ∨ p x = x` is what a stagewise construction consumes: it says
that the stage never carries an interior point back onto the boundary, and together with the
clause for `A` it gives `MapsTo p (interior K) (interior K)` and
`p '' (A ∪ (N ∩ interior K)) ⊆ interior K` for every set `N`.

The proof runs the stage push of
`IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_stage_inward_dist_lt` inside the
presenting complex of the local model of `StageInwardPushFrame.lean`, transports it by
`PLPiece.isPLOn_transport`, and extends it by the identity through
`isPLOn_of_isPLOn_local_of_eqOn_id`; the support is inside the open set carrying the model
because the complex level statement puts it inside any prescribed open set around the preimage
of `A`. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isPLOn_stage_inward_dist_lt
    {K : Set M₁} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K) {A C : Set M₁}
    (hA : IsCompact A) (hC : IsCompact C) (hAK : A ⊆ K \ interior K) (hCK : C ⊆ interior K)
    {h : M₁ → M₂} (hh : ContinuousOn h K) {δ : M₁ → ℝ} (hδ : ContinuousOn δ K)
    (hδpos : ∀ x ∈ K, 0 < δ x) :
    ∃ p q : M₁ → M₁, IsPLOn 3 3 p K ∧ InjOn p K ∧ MapsTo p K K ∧
      (∀ x ∈ K, p x ∈ interior K ∨ p x = x) ∧ (∀ x ∈ A, p x ∈ interior K) ∧ EqOn p id C ∧
      IsPLOn 3 3 q K ∧ MapsTo q K K ∧ EqOn q id C ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < δ x := by
  classical
  obtain ⟨O, hO, hAO, hCO, P, hP, hPK, hOP, hAfr, hCint, -⟩ :=
    hK.exists_isOpen_inter_eq_frontier_of_isCompact hA hC hAK hCK
  obtain ⟨T, hT⟩ := id hP
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hbij : BijOn T.piece.map T.piece.complex.space P := T.piece.bijOn
  have hinvmap : MapsTo (Function.invFunOn T.piece.map T.piece.complex.space) P
      T.piece.complex.space := fun _ hy => hbij.surjOn.mapsTo_invFunOn hy
  have hleft : LeftInvOn (Function.invFunOn T.piece.map T.piece.complex.space) T.piece.map
      T.piece.complex.space := hbij.invOn_invFunOn.1
  have hright : RightInvOn (Function.invFunOn T.piece.map T.piece.complex.space) T.piece.map P :=
    hbij.invOn_invFunOn.2
  have hPcompact : IsCompact P := hP.isCompact
  have hPcl : IsClosed P := hPcompact.isClosed
  have hfrP : frontier P ⊆ P := by
    rw [hPcl.frontier_eq]
    exact sdiff_subset
  have hmapK : MapsTo T.piece.map T.piece.complex.space K := hbij.mapsTo.mono_right hPK
  obtain ⟨U, hUopen, hU⟩ := continuousOn_iff'.mp T.piece.continuousOn O hO
  set A' := T.piece.complex.space ∩ T.piece.map ⁻¹' A with hA'def
  set C' := T.piece.complex.space ∩ T.piece.map ⁻¹' C with hC'def
  have hA'c : IsCompact A' :=
    IsCompact.of_isClosed_subset (isPolyhedron_space T.piece.complex).isCompact
      (T.piece.continuousOn.preimage_isClosed_of_isClosed
        (isPolyhedron_space T.piece.complex).isClosed hA.isClosed) inter_subset_left
  have hC'c : IsCompact C' :=
    IsCompact.of_isClosed_subset (isPolyhedron_space T.piece.complex).isCompact
      (T.piece.continuousOn.preimage_isClosed_of_isClosed
        (isPolyhedron_space T.piece.complex).isClosed hC.isClosed) inter_subset_left
  have hA'B : A' ⊆ (@boundaryComplex _ _ _ (Classical.decEq _) 3 T.piece.complex).space := by
    intro z hz
    by_contra hmem
    have hint : T.piece.map z ∈ interior P :=
      (T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT hz.1).mpr hmem
    exact (hAK hz.2).2 (interior_mono hPK hint)
  have hC'B : ∀ z ∈ C',
      z ∉ (@boundaryComplex _ _ _ (Classical.decEq _) 3 T.piece.complex).space := fun z hz =>
    (T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT hz.1).mp (hCint hz.2)
  have hA'U : A' ⊆ U := by
    intro z hz
    have hmem : z ∈ T.piece.map ⁻¹' O ∩ T.piece.complex.space := ⟨hAO hz.2, hz.1⟩
    rw [hU] at hmem
    exact hmem.1
  obtain ⟨ε, hε, hεle⟩ :=
    exists_pos_forall_le_of_continuousOn hPcompact (hδ.mono hPK) fun x hx => hδpos x (hPK hx)
  obtain ⟨f, f', S, hSc, hSK, hSU, hfpl, hfinj, hfmap, hfBfix, hfA, hfC, hfS, hf'pl, hf'map,
      hf'C, hf'S, hfinv, hfdist⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_stage_inward_dist_lt
      T.piece.complex hT hA'c hA'B hC'c inter_subset_left hC'B hUopen hA'U
      (hh.comp T.piece.continuousOn hmapK) hε
  -- the support in the manifold
  have hSPc : IsCompact (T.piece.map '' S) :=
    hSc.image_of_continuousOn (T.piece.continuousOn.mono hSK)
  have hSPO : T.piece.map '' S ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    have hmem : z ∈ U ∩ T.piece.complex.space := ⟨hSU hz, hSK hz⟩
    rw [← hU] at hmem
    exact hmem.1
  set p : M₁ → M₁ :=
    P.piecewise (fun x => T.piece.map (f (Function.invFunOn T.piece.map
      T.piece.complex.space x))) id with hpdef
  set q : M₁ → M₁ :=
    P.piecewise (fun x => T.piece.map (f' (Function.invFunOn T.piece.map
      T.piece.complex.space x))) id with hqdef
  have hpP : ∀ x ∈ P,
      p x = T.piece.map (f (Function.invFunOn T.piece.map T.piece.complex.space x)) :=
    fun x hx => P.piecewise_eqOn _ _ hx
  have hqP : ∀ x ∈ P,
      q x = T.piece.map (f' (Function.invFunOn T.piece.map T.piece.complex.space x)) :=
    fun x hx => P.piecewise_eqOn _ _ hx
  have hpout : ∀ x ∉ P, p x = x := fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx
  have hqout : ∀ x ∉ P, q x = x := fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx
  have hplP : IsPLOn 3 3 p P := by
    intro x hx
    exact piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
      (T.isPLOn_transport hfpl hfmap x hx) (fun y hy => hpP y hy) hx
  have hqlP : IsPLOn 3 3 q P := by
    intro x hx
    exact piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
      (T.isPLOn_transport hf'pl hf'map x hx) (fun y hy => hqP y hy) hx
  have hpid : EqOn p id (K \ T.piece.map '' S) := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [hpP x hxP]
      have hfix : f (Function.invFunOn T.piece.map T.piece.complex.space x) =
          Function.invFunOn T.piece.map T.piece.complex.space x :=
        hfS ⟨hinvmap hxP, fun hmem => hx.2 ⟨_, hmem, hright hxP⟩⟩
      rw [hfix]
      exact hright hxP
    · exact hpout x hxP
  have hqid : EqOn q id (K \ T.piece.map '' S) := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [hqP x hxP]
      have hfix : f' (Function.invFunOn T.piece.map T.piece.complex.space x) =
          Function.invFunOn T.piece.map T.piece.complex.space x :=
        hf'S ⟨hinvmap hxP, fun hmem => hx.2 ⟨_, hmem, hright hxP⟩⟩
      rw [hfix]
      exact hright hxP
    · exact hqout x hxP
  refine ⟨p, q, isPLOn_of_isPLOn_local_of_eqOn_id hK hO hOP hSPc.isClosed hSPO hplP hpid, ?_,
    ?_, ?_, ?_, ?_, isPLOn_of_isPLOn_local_of_eqOn_id hK hO hOP hSPc.isClosed hSPO hqlP hqid,
    ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
    · rw [hpP x hxP, hpP y hyP] at hxy
      have h1 := hbij.injOn (hfmap (hinvmap hxP)) (hfmap (hinvmap hyP)) hxy
      have h2 := hfinj (hinvmap hxP) (hinvmap hyP) h1
      rw [← hright hxP, ← hright hyP, h2]
    · exfalso
      rw [hpP x hxP, hpout y hyP] at hxy
      exact hyP (by rw [← hxy]; exact hbij.mapsTo (hfmap (hinvmap hxP)))
    · exfalso
      rw [hpP y hyP, hpout x hxP] at hxy
      exact hxP (by rw [hxy]; exact hbij.mapsTo (hfmap (hinvmap hyP)))
    · rwa [hpout x hxP, hpout y hyP] at hxy
  · intro x hx
    by_cases hxP : x ∈ P
    · rw [hpP x hxP]
      exact hPK (hbij.mapsTo (hfmap (hinvmap hxP)))
    · rw [hpout x hxP]
      exact hx
  · intro x hx
    by_cases hxP : x ∈ P
    · by_cases hmem : f (Function.invFunOn T.piece.map T.piece.complex.space x) ∈
          (@boundaryComplex _ _ _ (Classical.decEq _) 3 T.piece.complex).space
      · refine Or.inr ?_
        rw [hpP x hxP, hfBfix _ (hinvmap hxP) hmem]
        exact hright hxP
      · refine Or.inl ?_
        rw [hpP x hxP]
        exact interior_mono hPK
          ((T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT
            (hfmap (hinvmap hxP))).mpr hmem)
    · exact Or.inr (hpout x hxP)
  · intro x hx
    have hxP : x ∈ P := hfrP (hAfr hx)
    have hxA' : Function.invFunOn T.piece.map T.piece.complex.space x ∈ A' :=
      ⟨hinvmap hxP, by rw [mem_preimage, hright hxP]; exact hx⟩
    rw [hpP x hxP]
    exact interior_mono hPK
      ((T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT
        (hfmap (hinvmap hxP))).mpr (hfA _ hxA'))
  · intro x hx
    have hxP : x ∈ P := interior_subset (hCint hx)
    have hxC' : Function.invFunOn T.piece.map T.piece.complex.space x ∈ C' :=
      ⟨hinvmap hxP, by rw [mem_preimage, hright hxP]; exact hx⟩
    rw [hpP x hxP]
    have hfix : f (Function.invFunOn T.piece.map T.piece.complex.space x) =
        Function.invFunOn T.piece.map T.piece.complex.space x := hfC hxC'
    rw [hfix]
    exact hright hxP
  · intro x hx
    by_cases hxP : x ∈ P
    · rw [hqP x hxP]
      exact hPK (hbij.mapsTo (hf'map (hinvmap hxP)))
    · rw [hqout x hxP]
      exact hx
  · intro x hx
    have hxP : x ∈ P := interior_subset (hCint hx)
    have hxC' : Function.invFunOn T.piece.map T.piece.complex.space x ∈ C' :=
      ⟨hinvmap hxP, by rw [mem_preimage, hright hxP]; exact hx⟩
    rw [hqP x hxP]
    have hfix : f' (Function.invFunOn T.piece.map T.piece.complex.space x) =
        Function.invFunOn T.piece.map T.piece.complex.space x := hf'C hxC'
    rw [hfix]
    exact hright hxP
  · intro x hx
    by_cases hxP : x ∈ P
    · have hfx : T.piece.map (f (Function.invFunOn T.piece.map T.piece.complex.space x)) ∈ P :=
        hbij.mapsTo (hfmap (hinvmap hxP))
      rw [hpP x hxP, hqP _ hfx, hleft (hfmap (hinvmap hxP)), hfinv (hinvmap hxP)]
      exact hright hxP
    · rw [hpout x hxP, hqout x hxP]
  · intro x hx
    by_cases hxP : x ∈ P
    · rw [hpP x hxP]
      have hd := hfdist _ (hinvmap hxP)
      simp only [Function.comp_apply] at hd
      rw [hright hxP] at hd
      exact hd.trans_le (hεle x hxP)
    · rw [hpout x hxP]
      simpa using hδpos x hx

end Manifold

end DifferentialGeometry.Topology.PiecewiseLinear
