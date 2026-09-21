/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCellProperness
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace

/-!
# Boundary-relative PL tube data

`IsPLBoundarySide D W BdM` says that the singular two cell `D` lies on one side `W` of the
manifold boundary `BdM`: the image lies in the closed set `W`, the image of the open cell lies
in `interior W`, the boundary `BdM` is closed, and at every point of the boundary curve one PL
chart presents `W` as a half space whose face is `BdM`.

The clause `IsClosed BdM` is not decoration.  In `IsPLBoundaryTubeProducer` the set `BdM` is
universally quantified, and the conclusion asks a whole three dimensional tube around a
boundary branch to meet `BdM` in its two end disks only, while every other clause constrains
`BdM` near the boundary curve alone.  Without closedness one may take `BdM` to be the union of
the true boundary with `V \ D '' D.domain` for a small open ball `V` around an interior point
of the branch: properness, the crossing charts, the side condition along the boundary curve and
the buffer all still hold, yet the interior of any tube around that branch has open image and
therefore meets `V \ D '' D.domain`, so `chart '' spliceCylinder ∩ BdM = chart '' spliceEndDisks`
is unsatisfiable.  A closed `BdM` cannot contain such a set, since a point of
`D '' D.domain ∩ V` lies in its closure but not in it.

With that clause, `IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff` converts
properness of `D` over the boundary, `D.domain ∩ D ⁻¹' BdM = frontier D.domain`, which
`NormalSingularCellData.preimage_boundary_eq_frontier` supplies for a normal cell, into
`D '' (D.domain \ frontier D.domain) ⊆ interior (W \ BdM)`: the open cell misses `BdM`
altogether and stays in the open side.  That is the form the surgery consumers use to place an
adapted cap.

At the double of a compact combinatorial three manifold with boundary the clause is free,
because `Bd` is there the frontier of `C`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsPLHalfSpacePairAt {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (W H : Set M) (z : M) : Prop :=
  ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
    e ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ z ∈ e.source ∧
      (∀ y ∈ e.source, y ∈ W ↔ 0 ≤ ℓ (e y)) ∧
      ∀ y ∈ e.source, y ∈ H ↔ ℓ (e y) = 0

def IsPLBoundarySide {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (W BdM : Set M) : Prop :=
  D '' D.domain ⊆ W ∧
    IsClosed W ∧
    IsClosed BdM ∧
    D '' (D.domain \ frontier D.domain) ⊆ interior W ∧
    ∀ z ∈ D '' frontier D.domain, IsPLHalfSpacePairAt W BdM z

theorem IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {W BdM : Set M} (hside : IsPLBoundarySide D W BdM)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain) :
    D '' (D.domain \ frontier D.domain) ⊆ interior (W \ BdM) := by
  obtain ⟨-, -, hBd, hint, -⟩ := hside
  have hsub : interior W ∩ BdMᶜ ⊆ interior (W \ BdM) := by
    rw [Set.sdiff_eq, interior_inter, hBd.isOpen_compl.interior_eq]
  rintro _ ⟨x, hx, rfl⟩
  refine hsub ⟨hint ⟨x, hx, rfl⟩, fun hmem => hx.2 ?_⟩
  rw [← hproper]
  exact ⟨hx.1, hmem⟩

def IsPLBoundaryTubeProducer (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  ∀ (D : SingularTwoCell M) (BdM B W : Set M)
    (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
    IsPLBoundarySide D W BdM →
    (∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) →
    ∃ (U : Set M) (T : CrossSeamTubeData hD c U),
      Nonempty (PLSeamTubeChart M T.chart) ∧
        T.chart '' spliceCylinder ⊆ W ∧
        T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks ∧
        ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z

open Classical in
theorem isPLBoundarySide_double
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (boundaryComplex 3 K).space)
    ∀ {D : SingularTwoCell (double 3 K).space},
      MapsTo D D.domain C →
      D.domain ∩ D ⁻¹' Bd = frontier D.domain →
      IsPLBoundarySide D C Bd := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
    (ι '' (boundaryComplex 3 K).space)
  change ∀ {D : SingularTwoCell (double 3 K).space},
    MapsTo D D.domain C →
    D.domain ∩ D ⁻¹' Bd = frontier D.domain →
    IsPLBoundarySide D C Bd
  intro D hmap hproper
  obtain ⟨x₀, hx₀⟩ := D.isPLBall_domain.nonempty
  have hDx₀ := hmap hx₀
  change (D x₀ : E × E × ℝ) ∈ ι '' K.space at hDx₀
  obtain ⟨y₀, hy₀, -⟩ := hDx₀
  let p : K.space := ⟨y₀, hy₀⟩
  have hC : C = ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (glued₂ K (boundaryComplex 3 K) id).space := by
    rw [glued₂_space]
  let _ : Finite (glued₂ K (boundaryComplex 3 K) id).faces :=
    (glued₂_faces_finite K (boundaryComplex 3 K) id).to_subtype
  have hclosed : IsClosed C := by
    rw [hC]
    exact (isPolyhedron_space (glued₂ K (boundaryComplex 3 K) id)).isClosed.preimage
      continuous_subtype_val
  have hfront : frontier C = Bd := by
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K hK
  have hinterior : interior C = C \ Bd := by
    rw [← self_sdiff_frontier C, hfront]
  have hBdclosed : IsClosed Bd := by
    rw [← hfront]
    exact isClosed_frontier
  refine ⟨image_subset_iff.mpr hmap, hclosed, hBdclosed, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hinterior]
    refine ⟨hmap hx.1, ?_⟩
    intro hyBd
    have hxfront : x ∈ frontier D.domain := by
      rw [← hproper]
      exact ⟨hx.1, hyBd⟩
    exact hx.2 hxfront
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hyBd : D x ∈ Bd := by
      have hpair : x ∈ D.domain ∩ D ⁻¹' Bd := by
        rw [hproper]
        exact hx
      exact hpair.2
    have hyfront : D x ∈ frontier C := by
      rw [hfront]
      exact hyBd
    obtain ⟨e, ℓ, he, hℓ, hye, hCmem, hBdmem⟩ :=
      exists_halfSpace_chart_glued₂_space_in_double K hK p (D x) hyfront
    refine ⟨e, ℓ, he, hℓ, hye, ?_, ?_⟩
    · exact hCmem
    · intro z hz
      have hBdmem' := hBdmem z hz
      change z ∈ frontier C ↔ ℓ (e z) = 0 at hBdmem'
      rw [hfront] at hBdmem'
      exact hBdmem'

open Classical in
theorem isPLBoundarySide_double_of_normal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (boundaryComplex 3 K).space)
    ∀ {D : SingularTwoCell (double 3 K).space} {B : Set (double 3 K).space},
      NormalSingularCellData D Bd B → MapsTo D D.domain C →
      IsPLBoundarySide D C Bd := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
    (ι '' (boundaryComplex 3 K).space)
  change ∀ {D : SingularTwoCell (double 3 K).space} {B : Set (double 3 K).space},
    NormalSingularCellData D Bd B → MapsTo D D.domain C →
    IsPLBoundarySide D C Bd
  intro D B hD hmap
  apply isPLBoundarySide_double K hK hmap
  simpa only using hD.preimage_boundary_eq_frontier

end DifferentialGeometry.Topology.PiecewiseLinear
