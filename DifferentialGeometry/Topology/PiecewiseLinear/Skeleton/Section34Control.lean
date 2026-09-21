/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of P0, the controlled source triangulation and its carriers

The assembly `section34Control` proves the endpoint `Section34ControlStatement` for real from the
six leaves of this file; every `sorry` is a leaf and none sits inside an assembly.

P0 is the **producer** of the two hypotheses that the controlled form of Moise 35.1 takes as
given: a locally finite triangulation `𝒦` of the open set `U` with
`IsCombinatorialManifold 3 𝒦.complex`, and a carrier system `H` with
`Section34CarrierControl U 𝒦 h η H`.  The realisation ambient is existential,
`EuclideanSpace ℝ (Fin N)` with `N` produced together with `𝒦`, exactly as in
`exists_section34NormalFamily`: `LocallyFinitePLPieceIn Ea 3 M₁ U` realises **all** of `U` inside
`Ea` by its `bijOn` field, so a fixed `Ea = EuclideanSpace ℝ (Fin 3)` would ask that `U` embed in
`ℝ³` and would exclude `U = M₁ = S³`.  A fixed finite `N` keeps `Ea` in `Type 0`, which is what
`Section34CarrierControl` and the consumer's `∀ (Ea : Type)` binder require.

How the endpoint feeds the controlled 35.1 skeleton.  `ControlledGraphNeighborhoodStatement`
binds, after `hU` and `hh`, exactly
`∀ (Ea : Type) [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]`
`(𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U), IsCombinatorialManifold 3 𝒦.complex →`
`∀ (η : M₁ → ℝ) (H : Finset Ea → Set M₂), Section34CarrierControl U 𝒦 h η H → …`.
Instantiating `Ea := EuclideanSpace ℝ (Fin N)` with the `N`, `𝒦`, `H` of this endpoint and the
same `U, h, η` discharges both of those hypotheses verbatim; the `M₁ M₂` instance list, `hU` and
`hh` are the same in the two statements, and the consumer leaves `η` free, so the continuity and
positivity this endpoint assumes are not needed there.  Skeletons cannot import each other, so the
match is by textual comparison of those binders and not by a shared `def`.

The leaves, with content and review state.  All six are **unreviewed**.

`exists_locallyFinitePLPieceIn_of_isOpen` (a1): one locally finite complex in a *fixed* finite
dimensional ambient realising an arbitrary open subset of a piecewise linear `3`-manifold.  The
tree proves `exists_locallyFinitePieceTower_of_isOpen`, a tower of *compact* pieces whose ambient
dimension `(T.piece i).ambientDim` grows with `i`, glued by `IsGlueIso` maps; assembling one
locally finite complex in a single `ℝ^N` out of it is the recorded open foundational brick, not a
short consequence of the tower API, so it is a leaf.  General position embeds a locally finite
`3`-complex in `ℝ⁷`; the telescoping realisation with heights is the alternative, and the leaf
fixes neither, because `N` is existential.

`isCombinatorialManifold_of_locallyFinitePLPieceIn` (a2): the complex of *any* locally finite
piecewise linear realisation of an *open* subset of a piecewise linear `3`-manifold is a
combinatorial `3`-manifold.  Stated for every such realisation, which is the full conclusion of
(a1), so the composition needs no equation pinning the object to its producer.  It is the
classical fact that a triangulated `3`-manifold is combinatorial; openness of `U` is essential.

`locallyFinite_section34CarrierSupport` (a3): mechanical.  Each `Section34CarrierSupport 𝒦 t` lies
in `U`, and the family, indexed by the *faces*, is locally finite at every point of `U`.  The face
restriction is not cosmetic: for a `t` that is not a face but contains a vertex `w` of `𝒦` the
support still contains the closed star of `w`, and there are infinitely many such `t`.

`exists_isSubdivision_section34CarrierSupport_subset` (b): for an arbitrary open cover of `U` a
subdivision `𝒦₁` with the same realisation map, still a combinatorial `3`-manifold, each of whose
carrier supports lies in one member of the cover and **is a closed piecewise linear `3`-cell**.
The cover is arbitrary, so the subdivision is allowed to be finer and finer towards the ends of
`U`; a uniform mesh would not do.  In a simplicial complex two closed simplices meet in a common
face, so `Section34CarrierSupport 𝒦 t` is exactly the simplicial neighbourhood of `|t|`, the union
of the closed simplices meeting `|t|`; after a derived subdivision that is a regular neighbourhood
of a collapsible polyhedron, hence a ball.  The cell clause is **not** free before subdividing: in
`∂Δ⁴` triangulating `S³` the union of the stars of the two ends of an edge is all of `S³`, and then
no carrier exists at all.

`exists_isOpen_locallyFinite_superset` (c0): general topology.  A locally finite family of compact
subsets of an open set `Y` of a metrisable space has a locally finite family of open supersets
inside `Y`.  This is the swelling lemma; it is what makes the local finiteness of the carriers a
*proved* clause here instead of an output demanded of a leaf.

`exists_isPLCellOn_image_of_isPLCellOn` (c): the image of a closed piecewise linear `3`-cell of
`U` under the embedding `h` lies in the interior of a closed piecewise linear `3`-cell contained in
any prescribed open neighbourhood of that image.  `h` is only a homeomorphism, so the image is a
possibly wild topological `3`-cell; the leaf is the `3`-dimensional cellularity of cells together
with a piecewise linear approximation of the cell boundary.  It is the deep leaf of this file, and
it is where the cell clause of (b) is consumed: for a support that is not a cell the statement is
false, a small `2`-sphere being the standard obstruction.

Proved here, not leaves: `exists_section34ControlCover`, the control cover, whose member `O a`
carries `η a / 2 < η` and is sent by `h` into a chart ball of radius `r a` with `4 * r a < η a`;
`exists_section34CarrierControl_of_controlCover`, which produces the carrier system from that
cover and the four leaf outputs, and proves all six clauses of `Section34CarrierControl`, in
particular (C0a) `h '' S_t ⊆ Int H_t` with `H_t ⊆ h '' U`, (C0b) local finiteness in the subspace
`h '' U`, from the swelling `H_t ⊆ h '' W_t` together with the injectivity of `h` on `U`, and
(C0c) the diameter bound, from the two margins of the cover; the openness of `h '' V` for every
open `V ⊆ U`, which is invariance of domain and is what makes `h '' U` an open set at all; and
`section34Control` itself, which only composes the six leaves with those two lemmas.

Vacuity.  `U = ∅` forces `𝒦.complex.space = ∅`, so there are no faces, all six clauses of
`Section34CarrierControl` and `IsCombinatorialManifold` are vacuous and any `N` will do; the
endpoint allows it.  `U = M₁ = S³` is compact and needs `N ≥ 4`; nothing in the endpoint fixes
`N = 3`.  A disconnected `U` is untouched, the cover being built pointwise.  When `η` tends to `0`
at an end of `U` the members of the cover shrink there, which is why (b) is stated for an arbitrary
cover.  A non piecewise linear `h` enters only through images of the supports and through
`IsOpen (h '' V)`; no clause asks `h` to be piecewise linear anywhere.  No carrier is degenerate:
`IsPLCellOn 3 (H t) (frontier (H t))` forces a nonempty `3`-cell whose ambient frontier is its
intrinsic boundary, and `h '' S_t ⊆ interior (H t)` forces a nonempty interior.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def Section34ControlStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ η : M₁ → ℝ, ContinuousOn η U → (∀ x ∈ U, 0 < η x) →
    ∃ (N : ℕ) (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U)
      (H : Finset (EuclideanSpace ℝ (Fin N)) → Set M₂),
      IsCombinatorialManifold 3 𝒦.complex ∧ Section34CarrierControl U 𝒦 h η H

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}

theorem exists_locallyFinitePLPieceIn_of_isOpen [T2Space M₁] [SecondCountableTopology M₁]
    [HasGroupoid M₁ (plGroupoid 3)] (hU : IsOpen U) :
    ∃ N : ℕ, Nonempty (LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U) := by
  sorry

theorem isCombinatorialManifold_of_locallyFinitePLPieceIn [T2Space M₁]
    [HasGroupoid M₁ (plGroupoid 3)] (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    IsCombinatorialManifold 3 𝒦.complex := by
  sorry

theorem locallyFinite_section34CarrierSupport (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    (∀ t : Finset Ea, Section34CarrierSupport 𝒦 t ⊆ U) ∧
      ∀ x ∈ U, ∃ V ∈ 𝓝 x, {t : Finset Ea | t ∈ 𝒦.complex.faces ∧
        (Section34CarrierSupport 𝒦 t ∩ V).Nonempty}.Finite := by
  sorry

theorem exists_isSubdivision_section34CarrierSupport_subset [T2Space M₁]
    [SecondCountableTopology M₁] [HasGroupoid M₁ (plGroupoid 3)] {ι : Type*} (hU : IsOpen U)
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (O : ι → Set M₁) (hO : ∀ i, IsOpen (O i)) (hcover : U ⊆ ⋃ i, O i) :
    ∃ 𝒦₁ : LocallyFinitePLPieceIn Ea 3 M₁ U, IsSubdivision 𝒦₁.complex 𝒦.complex ∧
      𝒦₁.map = 𝒦.map ∧ IsCombinatorialManifold 3 𝒦₁.complex ∧
      (∀ t ∈ 𝒦₁.complex.faces, IsPLCellOn 3 (Section34CarrierSupport 𝒦₁ t)
        (frontier (Section34CarrierSupport 𝒦₁ t))) ∧
      ∀ t ∈ 𝒦₁.complex.faces, ∃ i, Section34CarrierSupport 𝒦₁ t ⊆ O i := by
  sorry

theorem exists_isOpen_locallyFinite_superset {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] {ι : Type*} {Y : Set X} (hY : IsOpen Y)
    (A : ι → Set X) (hAcpt : ∀ i, IsCompact (A i)) (hAY : ∀ i, A i ⊆ Y)
    (hAlf : ∀ x ∈ Y, ∃ V ∈ 𝓝 x, {i | (A i ∩ V).Nonempty}.Finite) :
    ∃ W : ι → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, A i ⊆ W i) ∧ (∀ i, W i ⊆ Y) ∧
      ∀ x ∈ Y, ∃ V ∈ 𝓝 x, {i | (W i ∩ V).Nonempty}.Finite := by
  sorry

omit [FiniteDimensional ℝ Ea] in
theorem exists_isPLCellOn_image_of_isPLCellOn [HasGroupoid M₂ (plGroupoid 3)] {S B : Set M₁}
    {V : Set M₂} (hh : Topology.IsEmbedding (U.domRestrict h)) (hSU : S ⊆ U)
    (hS : IsPLCellOn 3 S B) (hV : IsOpen V) (hSV : h '' S ⊆ V) :
    ∃ H : Set M₂, IsPLCellOn 3 H (frontier H) ∧ h '' S ⊆ interior H ∧ H ⊆ V := by
  sorry

end Leaves

theorem exists_section34ControlCover {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}
    (hU : IsOpen U) {h : M₁ → M₂} (hcont : ContinuousOn h U) (η : M₁ → ℝ)
    (hηc : ContinuousOn η U) (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ (O : U → Set M₁) (c : U → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
      (B : U → Set M₂), (∀ a, IsOpen (O a)) ∧ U ⊆ ⋃ a, O a ∧
      (∀ a, c a ∈ (plGroupoid 3).maximalAtlas M₂) ∧ (∀ a, IsOpen (B a)) ∧
      (∀ a, B a ⊆ (c a).source) ∧ (∀ (a : U), ∀ x ∈ O a, h x ∈ B a) ∧
      ∀ (a : U), ∀ x ∈ O a, ∀ y ∈ B a, ∀ z ∈ B a, dist y z < η x := by
  classical
  have hkey : ∀ a : U, ∃ (c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))) (r : ℝ),
      c ∈ (plGroupoid 3).maximalAtlas M₂ ∧ 0 < r ∧ 4 * r < η (a : M₁) ∧
        Metric.ball (h (a : M₁)) r ⊆ c.source := by
    intro a
    have hηa : 0 < η (a : M₁) := hηpos _ a.2
    obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.mp
      (chartAt (EuclideanSpace ℝ (Fin 3)) (h (a : M₁))).open_source
      (h (a : M₁)) (mem_chart_source _ _)
    refine ⟨chartAt (EuclideanSpace ℝ (Fin 3)) (h (a : M₁)), min r₀ (η (a : M₁) / 8),
      StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3) (h (a : M₁)),
      lt_min hr₀ (by linarith), ?_,
      fun y hy => hsub (Metric.ball_subset_ball (min_le_left _ _) hy)⟩
    have hle : min r₀ (η (a : M₁) / 8) ≤ η (a : M₁) / 8 := min_le_right _ _
    linarith
  choose cc rr hccmax hrrpos hrrη hccsub using hkey
  refine ⟨fun a => (U ∩ h ⁻¹' Metric.ball (h (a : M₁)) (rr a)) ∩
      (U ∩ η ⁻¹' Set.Ioi (η (a : M₁) / 2)), cc,
    fun a => Metric.ball (h (a : M₁)) (rr a), ?_, ?_, hccmax, fun a => Metric.isOpen_ball,
    hccsub, ?_, ?_⟩
  · exact fun a => (hcont.isOpen_inter_preimage hU Metric.isOpen_ball).inter
      (hηc.isOpen_inter_preimage hU isOpen_Ioi)
  · intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ⟨hx, Metric.mem_ball_self (hrrpos ⟨x, hx⟩)⟩, hx, ?_⟩
    change η x / 2 < η x
    have := hηpos x hx
    linarith
  · exact fun a x hx => hx.1.2
  · intro a x hx y hy z hz
    have hxη : η (a : M₁) / 2 < η x := hx.2.2
    have hdy : dist y (h (a : M₁)) < rr a := Metric.mem_ball.mp hy
    have hdz : dist (h (a : M₁)) z < rr a := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hz
    have htri := dist_triangle y (h (a : M₁)) z
    have hr := hrrη a
    linarith

theorem exists_section34CarrierControl_of_controlCover {Ea : Type} [NormedAddCommGroup Ea]
    [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea] {M₁ M₂ : Type u} [TopologicalSpace M₁]
    [T2Space M₁] [SecondCountableTopology M₁] [LocallyCompactSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}
    (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h)) {η : M₁ → ℝ}
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (O : U → Set M₁)
    (c : U → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))) (B : U → Set M₂)
    (hcmax : ∀ a, c a ∈ (plGroupoid 3).maximalAtlas M₂) (hBopen : ∀ a, IsOpen (B a))
    (hBsrc : ∀ a, B a ⊆ (c a).source) (hOB : ∀ (a : U), ∀ x ∈ O a, h x ∈ B a)
    (hBdiam : ∀ (a : U), ∀ x ∈ O a, ∀ y ∈ B a, ∀ z ∈ B a, dist y z < η x)
    (hScell : ∀ t ∈ 𝒦.complex.faces, IsPLCellOn 3 (Section34CarrierSupport 𝒦 t)
      (frontier (Section34CarrierSupport 𝒦 t)))
    (hSsub : ∀ t ∈ 𝒦.complex.faces, ∃ a, Section34CarrierSupport 𝒦 t ⊆ O a)
    (hSU : ∀ t : Finset Ea, Section34CarrierSupport 𝒦 t ⊆ U)
    (hSlf : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {t : Finset Ea | t ∈ 𝒦.complex.faces ∧
      (Section34CarrierSupport 𝒦 t ∩ V).Nonempty}.Finite) :
    ∃ H : Finset Ea → Set M₂, Section34CarrierControl U 𝒦 h η H := by
  classical
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have himOpen : ∀ V : Set M₁, V ⊆ U → IsOpen V → IsOpen (h '' V) := fun V hVU hV =>
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hV (hcont.mono hVU)
      (hinj.mono hVU)
  choose idx hidx using fun t : 𝒦.complex.faces => hSsub (t : Finset Ea) t.2
  have hAlf : ∀ x ∈ U, ∃ V ∈ 𝓝 x,
      {t : 𝒦.complex.faces |
        (Section34CarrierSupport 𝒦 (t : Finset Ea) ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨V, hV, hfin⟩ := hSlf x hx
    exact ⟨V, hV, (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset
      fun t ht => ⟨t.2, ht⟩⟩
  obtain ⟨W, hWopen, hSW, hWU, hWlf⟩ :=
    exists_isOpen_locallyFinite_superset (Y := U) hU
      (fun t : 𝒦.complex.faces => Section34CarrierSupport 𝒦 (t : Finset Ea))
      (fun t => (hScell (t : Finset Ea) t.2).isCompact) (fun t => hSU (t : Finset Ea)) hAlf
  have hcarrier : ∀ t : Finset Ea, ∃ Ht : Set M₂,
      ∀ ht : t ∈ 𝒦.complex.faces, IsPLCellOn 3 Ht (frontier Ht) ∧
        h '' Section34CarrierSupport 𝒦 t ⊆ interior Ht ∧
        Ht ⊆ h '' W ⟨t, ht⟩ ∩ B (idx ⟨t, ht⟩) := by
    intro t
    by_cases ht : t ∈ 𝒦.complex.faces
    · obtain ⟨Ht, hcell, hint, hsub⟩ :=
        exists_isPLCellOn_image_of_isPLCellOn hh (hSU t) (hScell t ht)
          ((himOpen (W ⟨t, ht⟩) (hWU ⟨t, ht⟩) (hWopen ⟨t, ht⟩)).inter (hBopen (idx ⟨t, ht⟩)))
          (by
            rintro _ ⟨x, hx, rfl⟩
            exact ⟨⟨x, hSW ⟨t, ht⟩ hx, rfl⟩, hOB (idx ⟨t, ht⟩) x (hidx ⟨t, ht⟩ hx)⟩)
      exact ⟨Ht, fun _ => ⟨hcell, hint, hsub⟩⟩
    · exact ⟨∅, fun ht' => absurd ht' ht⟩
  choose Hfam hHfam using hcarrier
  refine ⟨Hfam, fun t ht => (hHfam t ht).2.1, fun t ht => ?_, ?_, ?_,
    fun t ht => (hHfam t ht).1, fun t ht => ?_⟩
  · exact ((hHfam t ht).2.2.trans inter_subset_left).trans (image_mono (hWU ⟨t, ht⟩))
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hV, hfin⟩ := hWlf x hx
    refine ⟨h '' (interior V ∩ U), mem_nhdsWithin_of_mem_nhds
      ((himOpen _ inter_subset_right (isOpen_interior.inter hU)).mem_nhds
        ⟨x, ⟨mem_interior_iff_mem_nhds.mpr hV, hx⟩, rfl⟩),
      (hfin.image Subtype.val).subset ?_⟩
    rintro t ⟨ht, z, hzH, x', hx', hxz⟩
    obtain ⟨x'', hx'', hx''eq⟩ := ((hHfam t ht).2.2.trans inter_subset_left) hzH
    have hxx : x'' = x' := hinj (hWU ⟨t, ht⟩ hx'') hx'.2 (hx''eq.trans hxz.symm)
    refine ⟨⟨t, ht⟩, ⟨x'', hx'', ?_⟩, rfl⟩
    rw [hxx]
    exact interior_subset hx'.1
  · intro t ht x hx y hy z hz
    exact hBdiam (idx ⟨t, ht⟩) x (hidx ⟨t, ht⟩ hx) y ((hHfam t ht).2.2 hy).2
      z ((hHfam t ht).2.2 hz).2
  · exact ⟨c (idx ⟨t, ht⟩), hcmax (idx ⟨t, ht⟩),
      ((hHfam t ht).2.2.trans inter_subset_right).trans (hBsrc (idx ⟨t, ht⟩))⟩

theorem section34Control : Section34ControlStatement.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hlc : LocallyCompactSpace M₁ :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M₁
  obtain ⟨N, ⟨𝒦₀⟩⟩ := exists_locallyFinitePLPieceIn_of_isOpen (M₁ := M₁) hU
  obtain ⟨Ocov, cc, Bt, hOopen, hOcover, hcmax, hBopen, hBsrc, hOB, hBdiam⟩ :=
    exists_section34ControlCover hU hcont η hηc hηpos
  obtain ⟨𝒦, -, -, h𝒦, hScell, hSsub⟩ :=
    exists_isSubdivision_section34CarrierSupport_subset hU 𝒦₀
      (isCombinatorialManifold_of_locallyFinitePLPieceIn hU 𝒦₀) Ocov hOopen hOcover
  obtain ⟨hSU, hSlf⟩ := locallyFinite_section34CarrierSupport 𝒦
  obtain ⟨H, hH⟩ := exists_section34CarrierControl_of_controlCover hU hh (η := η) 𝒦 Ocov cc Bt
    hcmax hBopen hBsrc hOB hBdiam hScell hSsub hSU hSlf
  exact ⟨N, 𝒦, H, h𝒦, hH⟩

end DifferentialGeometry.Topology.PiecewiseLinear
