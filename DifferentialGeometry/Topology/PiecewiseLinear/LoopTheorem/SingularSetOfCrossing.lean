/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.EmbeddedProjection
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskOfDoubleCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InteriorTwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedDoubleInvolution

/-!
# The singular set of a crossing singular two-cell

`NormalSingularCellData` carries a triangulation of the double point set as the separate field
`singularSet`.  This file collects the part of that field which is a *consequence* of the four
Prop-shaped fields `locallyInjective`, `fiber_le_two`, `image_inter_boundary` and `crossing`,
stated with those fields as explicit hypotheses so that the results are available while a
`NormalSingularSetTriangulation` is being built.

## Main results

* `SingularTwoCell.isCompact_doublePointSet`: the double point set of a locally injective
  singular two-cell in a Hausdorff charted space is compact.
* `HasPLDoubleCrossingAt.eventually_mem_doublePointSet_iff_mem_sheets` and its boundary
  counterpart: near a crossing point the double point set *is* the intersection of the two
  sheets.  This is the "all nearby fibres lie in `A ∪ B`" clause of the crossing predicates.
* `HasPLTwoSidedDoubleCrossingAt.exists_eventually_mem_doublePointSet_iff_mem_line` and
  `HasPLBoundaryDoubleCrossingAt.exists_eventually_mem_doublePointSet_iff_mem_halfLine`:
  the resulting local normal forms.  At an interior crossing the germ of the double point set
  is a PL-flattened *line*, at a boundary crossing a PL-flattened *half-line*.  In particular
  a double point is never isolated, and a double arc never ends at an interior crossing.
* `SingularTwoCell.mem_interior_domain_of_image_inter_boundary`,
  `SingularTwoCell.exists_twoSidedCrossing_of_notMem_boundary` and
  `SingularTwoCell.preimage_boundary_eq_frontier_of_crossing`: the interior/boundary dichotomy
  and properness, derived from the fields instead of from a `NormalSingularCellData`.
* `SingularTwoCell.nonempty_boundary_of_image_inter_boundary`: the ambient boundary of a
  singular two-cell satisfying `image_inter_boundary` is never empty.
* `SingularTwoCell.nonempty_normalSingularSetTriangulation_of_isNonsingular`: the degenerate
  case of the recognition statement, with the empty complex.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- Composing with a chart moves the double point set forward: the double points of `e ∘ f` on
the part of `P` that `f` sends into `e.source` are exactly the chart images of the double
points of `f` that lie in `e.source`. -/
theorem doublePointSet_comp_openPartialHomeomorph {X Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (P : Set X)
    (e : OpenPartialHomeomorph Y Z) :
    doublePointSet (e ∘ f) (P ∩ f ⁻¹' e.source) =
      e '' (doublePointSet f P ∩ e.source) := by
  ext z
  constructor
  · rintro ⟨a, ⟨haP, hae⟩, b, ⟨hbP, hbe⟩, hab, hfa, hfb⟩
    have heq : f a = f b := e.injOn hae hbe (hfa.trans hfb.symm)
    exact ⟨f a, ⟨⟨a, haP, b, hbP, hab, rfl, heq.symm⟩, hae⟩, hfa⟩
  · rintro ⟨w, ⟨⟨a, haP, b, hbP, hab, hfa, hfb⟩, hwe⟩, rfl⟩
    refine ⟨a, ⟨haP, ?_⟩, b, ⟨hbP, ?_⟩, hab, ?_, ?_⟩
    · change f a ∈ e.source
      rw [hfa]
      exact hwe
    · change f b ∈ e.source
      rw [hfb]
      exact hwe
    · exact congrArg e hfa
    · exact congrArg e hfb

section Germ

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Near a PL double crossing the double point set coincides with the intersection of the two
sheet images.  The two sheets are disjoint and `f` is injective on each of them, so the fibre
clause of `HasPLDoubleCrossingAt` upgrades pointwise to an equality of germs. -/
theorem HasPLDoubleCrossingAt.eventually_mem_doublePointSet_iff_mem_sheets
    {f : E → F} {P : Set E} {y : F} (hc : HasPLDoubleCrossingAt f P y) :
    ∃ A B : Set E, HasPLCrossingAt (f '' A) (f '' B) y ∧
      ∀ᶠ z in 𝓝 y, (z ∈ doublePointSet f P ↔ z ∈ f '' A ∩ f '' B) := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  refine ⟨A, B, hcross, ?_⟩
  filter_upwards [hfiber] with z hz
  exact mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hdisj
    hfA.bijOn.injOn hfB.bijOn.injOn hz

/-- Near a PL boundary double crossing the double point set coincides with the intersection of
the two sheet images, for the same reason as at an interior crossing. -/
theorem HasPLBoundaryDoubleCrossingAt.eventually_mem_doublePointSet_iff_mem_sheets
    {f : E → F} {P : Set E} {N : Set F} {y : F}
    (hc : HasPLBoundaryDoubleCrossingAt f P N y) :
    ∃ A B : Set E, HasPLBoundaryCrossingAt N (f '' A) (f '' B) y ∧
      ∀ᶠ z in 𝓝 y, (z ∈ doublePointSet f P ↔ z ∈ f '' A ∩ f '' B) := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  refine ⟨A, B, hcross, ?_⟩
  filter_upwards [hfiber] with z hz
  exact mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hdisj
    hfA.bijOn.injOn hfB.bijOn.injOn hz

/-- Local normal form of the double point set at a two-sided double crossing: there is a PL
homeomorphism `h` of a neighbourhood of `y`, carrying `y` to the origin, and a line `L` such
that near `y` the double point set is exactly `h ⁻¹' L`.  In particular the double point set is
a one-dimensional germ there, so `y` is neither isolated nor an endpoint. -/
theorem HasPLTwoSidedDoubleCrossingAt.exists_eventually_mem_doublePointSet_iff_mem_line
    {f : E → F} {P : Set E} {y : F} (hc : HasPLTwoSidedDoubleCrossingAt f P y) :
    ∃ (h : F → F) (L : Submodule ℝ F), Module.finrank ℝ L = 1 ∧ h y = 0 ∧
      (∃ U V : Set F, IsOpen U ∧ IsOpen V ∧ y ∈ U ∧ IsPLHomeomorphOn h U V) ∧
        ∀ᶠ z in 𝓝 y, (z ∈ doublePointSet f P ↔ h z ∈ L) := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  obtain ⟨U, V, h, R, S, hU, hV, hyU, hh, hhy, hRdim, hSdim, hIdim, hsup, hlocal⟩ := hcross
  refine ⟨h, R ⊓ S, hIdim, hhy, ⟨U, V, hU, hV, hyU, hh⟩, ?_⟩
  filter_upwards [hfiber, hlocal] with z hz hzloc
  rw [mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hdisj
    hfA.bijOn.injOn hfB.bijOn.injOn hz, Submodule.mem_inf]
  exact ⟨fun hmem => ⟨hzloc.1.mp hmem.1, hzloc.2.mp hmem.2⟩,
    fun hmem => ⟨hzloc.1.mpr hmem.1, hzloc.2.mpr hmem.2⟩⟩

/-- Local normal form of the double point set at a boundary double crossing: there is a PL
homeomorphism `h` of a neighbourhood of `y`, a line `L` and a functional `ℓ` which is nonzero
on `L`, such that near `y` the local boundary `N` is `{ℓ ∘ h ≥ 0}` and the double point set is
the half-line `h ⁻¹' (L ∩ {ℓ ≥ 0})`.  So a boundary double point is an endpoint of a double
arc, never an isolated point. -/
theorem HasPLBoundaryDoubleCrossingAt.exists_eventually_mem_doublePointSet_iff_mem_halfLine
    {f : E → F} {P : Set E} {N : Set F} {y : F}
    (hc : HasPLBoundaryDoubleCrossingAt f P N y) :
    ∃ (h : F → F) (L : Submodule ℝ F) (ℓ : F →ₗ[ℝ] ℝ),
      Module.finrank ℝ L = 1 ∧ h y = 0 ∧ (∃ u ∈ L, ℓ u = 1) ∧
      (∃ U V : Set F, IsOpen U ∧ IsOpen V ∧ y ∈ U ∧ IsPLHomeomorphOn h U V) ∧
        (∀ᶠ z in 𝓝 y, (z ∈ N ↔ 0 ≤ ℓ (h z))) ∧
          ∀ᶠ z in 𝓝 y, (z ∈ doublePointSet f P ↔ h z ∈ L ∧ 0 ≤ ℓ (h z)) := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAnhds, hBnhds, hfA, hfB,
    hcross, hfiber⟩ := hc
  obtain ⟨U, V, h, R, S, ℓ, hU, hV, hyU, hh, hhy, hRdim, hSdim, hIdim, hsup, hu, hlocal⟩ :=
    hcross
  refine ⟨h, R ⊓ S, ℓ, hIdim, hhy, hu, ⟨U, V, hU, hV, hyU, hh⟩, ?_, ?_⟩
  · filter_upwards [hlocal] with z hzloc using hzloc.1
  · filter_upwards [hfiber, hlocal] with z hz hzloc
    rw [mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hdisj
      hfA.bijOn.injOn hfB.bijOn.injOn hz, Submodule.mem_inf]
    constructor
    · rintro ⟨hzA, hzB⟩
      exact ⟨⟨(hzloc.2.1.mp hzA).1, (hzloc.2.2.mp hzB).1⟩, (hzloc.2.1.mp hzA).2⟩
    · rintro ⟨⟨hzR, hzS⟩, hzℓ⟩
      exact ⟨hzloc.2.1.mpr ⟨hzR, hzℓ⟩, hzloc.2.2.mpr ⟨hzS, hzℓ⟩⟩

end Germ

section Cell

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

/-- The double point set of a locally injective singular two-cell in a Hausdorff charted space
is compact: it is the image of the closed double point relation of a compact domain. -/
theorem SingularTwoCell.isCompact_doublePointSet [T2Space M] (D : SingularTwoCell M)
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U) :
    IsCompact (doublePointSet D D.domain) :=
  isCompact_doublePointSet_of_isLocallyInjective D.isPLBall_domain.isPolyhedron.isCompact
    D.continuousOn (Covering.isLocallyInjective_domRestrict_iff.mpr hloc)

/-- The `image_inter_boundary` field alone forces the ambient boundary to be nonempty: the
frontier of the domain of a singular two-cell is a PL one-sphere, hence nonempty, and its
image lands in `BdM`. -/
theorem SingularTwoCell.nonempty_boundary_of_image_inter_boundary
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary) : BdM.Nonempty := by
  obtain ⟨x, hx⟩ := D.isPLSphere_frontier.nonempty
  have hrange : D x ∈ Set.range D.boundary := ⟨⟨x, hx⟩, rfl⟩
  rw [← himage] at hrange
  exact ⟨D x, hrange.2⟩

/-- Every preimage of a double point off the ambient boundary lies in the interior of the
domain.  A frontier point of the domain is sent into `Set.range D.boundary`, which
`image_inter_boundary` places inside `BdM`. -/
theorem SingularTwoCell.mem_interior_domain_of_image_inter_boundary
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary) {y : M} (hyBd : y ∉ BdM)
    {x : EuclideanSpace ℝ (Fin 2)} (hxdom : x ∈ D.domain) (hxy : D x = y) :
    x ∈ interior D.domain := by
  by_contra hxnot
  have hxfront : x ∈ frontier D.domain := (mem_frontier_iff_notMem_interior hxdom).mpr hxnot
  have hmemrange : D x ∈ Set.range D.boundary := ⟨⟨x, hxfront⟩, rfl⟩
  rw [← himage] at hmemrange
  exact hyBd (hxy ▸ hmemrange.2)

/-- At a double point off the ambient boundary the crossing datum upgrades to a two-sided
crossing: neither sheet can carry a free edge through the point, because both preimages are
interior points of the domain.  This is the field-level form of
`NormalSingularCellData.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary`. -/
theorem SingularTwoCell.exists_twoSidedCrossing_of_notMem_boundary
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary)
    (hcross : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    {y : M} (hy : y ∈ doublePointSet D D.domain) (hyBd : y ∉ BdM) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLTwoSidedDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source) (e y) := by
  obtain ⟨e, he, hye, hc⟩ := hcross y hy
  refine ⟨e, he, hye, ?_⟩
  rcases hc with ⟨hmem, -⟩ | ⟨-, hdouble⟩
  · exfalso
    obtain ⟨z, ⟨hzsrc, hzBd⟩, hze⟩ := hmem
    exact hyBd (e.injOn hzsrc hye hze ▸ hzBd)
  · have hEdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    refine hdouble.hasPLTwoSidedDoubleCrossingAt hEdim ?_
    rintro x ⟨⟨hxdom, hxsrc⟩, hxy⟩
    have hxy' : e (D x) = e y := hxy
    have hxDy : D x = y := e.injOn hxsrc hye hxy'
    have hxint : x ∈ interior D.domain :=
      SingularTwoCell.mem_interior_domain_of_image_inter_boundary himage hyBd hxdom hxDy
    have hdomnhds : D.domain ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
    have hcont : ContinuousAt D x := (D.continuousOn x hxdom).continuousAt hdomnhds
    have hpre : D ⁻¹' e.source ∈ 𝓝 x := hcont (e.open_source.mem_nhds hxsrc)
    exact mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hdomnhds hpre)

/-- Properness over the ambient boundary, from the fields instead of from a
`NormalSingularCellData`: the points of the domain that are sent into `BdM` are exactly the
frontier points of the domain.  Only `fiber_le_two`, `image_inter_boundary` and `crossing`
enter the proof. -/
theorem SingularTwoCell.preimage_boundary_eq_frontier_of_crossing
    (hfiber : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2)
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary)
    (hcross : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y)) :
    D.domain ∩ D ⁻¹' BdM = frontier D.domain := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxb⟩
    have hrange : D x ∈ Set.range D.boundary := by
      rw [← himage]
      exact ⟨⟨x, hx, rfl⟩, hxb⟩
    obtain ⟨z, hz⟩ := hrange
    have hzx : D (z : EuclideanSpace ℝ (Fin 2)) = D x := by simpa using hz
    by_cases hxz : x = (z : EuclideanSpace ℝ (Fin 2))
    · rw [hxz]
      exact z.2
    · have hdouble : D x ∈ doublePointSet D D.domain :=
        ⟨x, hx, (z : EuclideanSpace ℝ (Fin 2)),
          D.frontier_subset_domain z.2, hxz, rfl, hzx⟩
      obtain ⟨e, -, hye, hc⟩ := hcross (D x) hdouble
      rcases hc with ⟨-, N, hboundary⟩ | ⟨hnot, -⟩
      · exact hboundary.fiber_subset_frontier_of_comp_openPartialHomeomorph
          D.continuousOn hye (hfiber (D x)) ⟨hx, rfl⟩
      · exact absurd ⟨D x, ⟨hye, hxb⟩, rfl⟩ hnot
  · intro z hz
    have hrange : D z ∈ Set.range D.boundary := ⟨⟨z, hz⟩, rfl⟩
    rw [← himage] at hrange
    exact ⟨D.frontier_subset_domain hz, hrange.2⟩

/-- At a double point on the ambient boundary the crossing datum is a boundary crossing: the
interior branch of `HasPLNormalDoubleCrossingAt` is excluded by `y ∈ BdM`.  This is the
field-level form of `NormalSingularCellData.exists_boundary_crossing_chart`. -/
theorem SingularTwoCell.exists_boundaryCrossing_of_mem_boundary
    (hcross : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    {y : M} (hy : y ∈ doublePointSet D D.domain) (hyBd : y ∈ BdM) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      ∃ N : Set (EuclideanSpace ℝ (Fin 3)),
        HasPLBoundaryDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source) N (e y) := by
  obtain ⟨e, he, hye, hc⟩ := hcross y hy
  refine ⟨e, he, hye, ?_⟩
  rcases hc with ⟨-, N, hb⟩ | ⟨hnot, -⟩
  · exact ⟨N, hb⟩
  · exact (hnot ⟨y, ⟨hye, hyBd⟩, rfl⟩).elim

/-- Local normal form of the double point set of a crossing singular two-cell, read in an
atlas chart of the ambient manifold.  At a double point off `BdM` the germ of the double point
set is a PL-flattened line; at a double point on `BdM` it is a PL-flattened half-line whose
endpoint is the point itself.  In particular the double point set has no isolated point, and a
double arc can only end on `BdM`.  This is the local input for triangulating the double point
set as a one-manifold with boundary `doublePointSet D D.domain ∩ BdM`. -/
theorem SingularTwoCell.exists_chart_germ_doublePointSet
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary)
    (hcross : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      ∃ (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (L : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
        Module.finrank ℝ L = 1 ∧ h (e y) = 0 ∧
          (∃ U V : Set (EuclideanSpace ℝ (Fin 3)),
            IsOpen U ∧ IsOpen V ∧ e y ∈ U ∧ IsPLHomeomorphOn h U V) ∧
            ((y ∉ BdM ∧ ∀ᶠ z in 𝓝 (e y),
                (z ∈ e '' (doublePointSet D D.domain ∩ e.source) ↔ h z ∈ L)) ∨
              (y ∈ BdM ∧ ∃ ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ, (∃ u ∈ L, ℓ u = 1) ∧
                ∀ᶠ z in 𝓝 (e y),
                  (z ∈ e '' (doublePointSet D D.domain ∩ e.source) ↔
                    h z ∈ L ∧ 0 ≤ ℓ (h z)))) := by
  by_cases hyBd : y ∈ BdM
  · obtain ⟨e, he, hye, N, hb⟩ :=
      SingularTwoCell.exists_boundaryCrossing_of_mem_boundary hcross hy hyBd
    obtain ⟨h, L, ℓ, hLdim, hh0, hu, hPL, -, hgerm⟩ :=
      hb.exists_eventually_mem_doublePointSet_iff_mem_halfLine
    have hset := doublePointSet_comp_openPartialHomeomorph
      (D : EuclideanSpace ℝ (Fin 2) → M) D.domain e
    refine ⟨e, he, hye, h, L, hLdim, hh0, hPL, Or.inr ⟨hyBd, ℓ, hu, ?_⟩⟩
    filter_upwards [hgerm] with z hz
    rw [← hset]
    exact hz
  · obtain ⟨e, he, hye, htwo⟩ :=
      SingularTwoCell.exists_twoSidedCrossing_of_notMem_boundary himage hcross hy hyBd
    obtain ⟨h, L, hLdim, hh0, hPL, hgerm⟩ :=
      htwo.exists_eventually_mem_doublePointSet_iff_mem_line
    have hset := doublePointSet_comp_openPartialHomeomorph
      (D : EuclideanSpace ℝ (Fin 2) → M) D.domain e
    refine ⟨e, he, hye, h, L, hLdim, hh0, hPL, Or.inl ⟨hyBd, ?_⟩⟩
    filter_upwards [hgerm] with z hz
    rw [← hset]
    exact hz

open Classical in
/-- The degenerate case of the recognition statement.  A nonsingular singular two-cell has an
empty double point set, and the empty piece together with the empty complex is a
`NormalSingularSetTriangulation` for it. -/
theorem SingularTwoCell.nonempty_normalSingularSetTriangulation_of_isNonsingular
    (D : SingularTwoCell M) (BdM : Set M) (hD : D.IsNonsingular) :
    Nonempty (NormalSingularSetTriangulation D BdM) := by
  have : Nonempty M := ⟨D (0 : EuclideanSpace ℝ (Fin 2))⟩
  have hdouble : doublePointSet D D.domain = ∅ :=
    (doublePointSet_eq_empty_iff_injOn D D.domain).mpr hD
  refine ⟨{
    carrier := (∅ : Set M)
    piece := ⟨0, PLPieceIn.empty (EuclideanSpace ℝ (Fin 0))⟩
    complex := (⊥ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 0)))
    finite_faces := ?_
    faces_subset := ?_
    isManifoldWithBoundary := ?_
    map_space := ?_
    map_boundary := ?_ }⟩
  · rw [Geometry.SimplicialComplex.faces_bot]
    exact Set.finite_empty
  · rw [Geometry.SimplicialComplex.faces_bot]
    exact Set.empty_subset _
  · intro v hv
    rw [Geometry.SimplicialComplex.faces_bot] at hv
    exact absurd hv (Set.notMem_empty _)
  · rw [hdouble]
    apply Set.eq_empty_of_subset_empty
    rintro _ ⟨x, hx, rfl⟩
    rw [space_bot] at hx
    exact hx
  · rw [hdouble, Set.empty_inter]
    apply Set.eq_empty_of_subset_empty
    rintro _ ⟨x, hx, rfl⟩
    have hxbot := boundaryComplex_space_subset 1 _ hx
    rw [space_bot] at hxbot
    exact hxbot

end Cell

/-- The double point set of a locally injective singular two-cell in a closed combinatorial
three-manifold, read in the ambient coordinates of the complex, is a polyhedron.  This is the
polyhedrality step of the singular set recognition, for the ambient that Moise's Lemma 2
actually uses: `K.space` with its vertex-chart charted structure, where the cell is piecewise
affine after composing with the inclusion.  Local injectivity is the only hypothesis needed;
neither the fibre bound nor the crossing models enter. -/
theorem SingularTwoCell.isPolyhedron_image_doublePointSet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ D : SingularTwoCell K.space,
      (∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U) →
        IsPolyhedron (Subtype.val '' doublePointSet D D.domain) := by
  let _ := combinatorialChartedSpace K hK
  intro D hloc
  have hval : IsPiecewiseAffineOn ((Subtype.val : K.space → E) ∘ D.toFun) D.domain :=
    isPiecewiseAffineOn_val_comp_of_isPLOn K hK D.domain D.toFun D.isPLOn
  have hlocval :
      IsLocallyInjective (D.domain.domRestrict ((Subtype.val : K.space → E) ∘ D.toFun)) := by
    refine Covering.isLocallyInjective_domRestrict_iff.mpr ?_
    intro x hx
    obtain ⟨U, hU, hinj⟩ := hloc x hx
    exact ⟨U, hU, fun a ha b hb hab => hinj ha hb (Subtype.ext hab)⟩
  have heq : Subtype.val '' doublePointSet D D.domain
      = doublePointSet ((Subtype.val : K.space → E) ∘ D.toFun) D.domain :=
    (doublePointSet_comp_of_injOn D.toFun Subtype.val D.domain
      Subtype.val_injective.injOn).symm
  rw [heq]
  exact hval.isPolyhedron_doublePointSet D.isPLBall_domain.isPolyhedron hlocval

end DifferentialGeometry.Topology.PiecewiseLinear
