/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereFamilyMap
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryHoledChart
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E3 M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E3 M₂]
  [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]

open Classical in
theorem exists_isPLHomeomorphInto_boundary_disk_family
    {ι : Type*} [Finite ι]
    {P PB : Set M₁} {Q QB : Set M₂}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    {D J : ι → Set M₁} {D' J' : ι → Set M₂}
    (hD : ∀ i, IsPLCellOn 2 (D i) (J i))
    (hD' : ∀ i, IsPLCellOn 2 (D' i) (J' i))
    (hDP : ∀ i, D i ⊆ PB) (hD'Q : ∀ i, D' i ⊆ QB)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hdis' : Pairwise fun i j => Disjoint (D' i) (D' j))
    (i₀ : ι) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f PB ∧
      f '' PB = QB ∧ ∀ i, f '' D i = D' i := by
  classical
  obtain ⟨A, r, u, hr, hu, rfl, rfl⟩ := hP
  obtain ⟨B, s, v, hs, hv, rfl, rfl⟩ := hQ
  have hA : IsPLBall 3 A := ⟨r, hr⟩
  have hB : IsPLBall 3 B := ⟨s, hs⟩
  have hAfr : r '' stdSimplexBoundary 3 = frontier A :=
    hr.image_stdSimplexBoundary_eq_frontier
  have hBfr : s '' stdSimplexBoundary 3 = frontier B :=
    hs.image_stdSimplexBoundary_eq_frontier
  have hAfrA : frontier A ⊆ A := hA.isPolyhedron.isClosed.frontier_subset
  have hBfrB : frontier B ⊆ B := hB.isPolyhedron.isClosed.frontier_subset
  let DA : ι → Set E3 := fun i => Function.invFunOn u A '' D i
  let DB : ι → Set E3 := fun i => Function.invFunOn v B '' D' i
  have hDA : ∀ i, D i ⊆ u '' A := fun i =>
    (hDP i).trans (by rw [hAfr]; exact image_mono hAfrA)
  have hDB : ∀ i, D' i ⊆ v '' B := fun i =>
    (hD'Q i).trans (by rw [hBfr]; exact image_mono hBfrB)
  have hDAfr : ∀ i, DA i ⊆ frontier A := by
    intro i
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier A := by
      rw [← hAfr]
      exact hDP i hx
    rw [hu.injOn.leftInvOn_invFunOn (hAfrA hz)]
    exact hz
  have hDBfr : ∀ i, DB i ⊆ frontier B := by
    intro i
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ v '' frontier B := by
      rw [← hBfr]
      exact hD'Q i hx
    rw [hv.injOn.leftInvOn_invFunOn (hBfrB hz)]
    exact hz
  have hDAdis : Pairwise fun i j => Disjoint (DA i) (DA j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hx' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hDA i hx)
    have hy' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hDA j hy)
    have hxy : x = y := by rw [← hx', ← hy', hyx]
    exact disjoint_left.mp (hdis hij) hx (hxy ▸ hy)
  have hDBdis : Pairwise fun i j => Disjoint (DB i) (DB j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hx' := hv.injOn.bijOn_image.invOn_invFunOn.2 (hDB i hx)
    have hy' := hv.injOn.bijOn_image.invOn_invFunOn.2 (hDB j hy)
    have hxy : x = y := by rw [← hx', ← hy', hyx]
    exact disjoint_left.mp (hdis' hij) hx (hxy ▸ hy)
  have hqExists : ∀ i, ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (DA i) ∧
      Function.invFunOn u A '' J i = q '' stdSimplexBoundary 2 :=
    fun i => (hD i).exists_isPLHomeomorphOn_invFunOn hu (hDA i)
  choose q hq hqJ using hqExists
  have hq'Exists : ∀ i, ∃ q' : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (DB i) ∧
      Function.invFunOn v B '' J' i = q' '' stdSimplexBoundary 2 :=
    fun i => (hD' i).exists_isPLHomeomorphOn_invFunOn hv (hDB i)
  choose q' hq' hq'J using hq'Exists
  obtain ⟨g, hg, hgD⟩ :=
    hA.isPLSphere_frontier.exists_isPLHomeomorphOn_disk_family
      hB.isPLSphere_frontier hq hq' hDAfr hDBfr hDAdis hDBdis i₀
  have hAfrPoly : IsPolyhedron (frontier A) := hA.isPLSphere_frontier.isPolyhedron
  have hBfrPoly : IsPolyhedron (frontier B) := hB.isPLSphere_frontier.isPolyhedron
  have huFr : IsPLHomeomorphInto 3 u (frontier A) :=
    IsPLOn.isPLHomeomorphInto
      (hu.isPLOn.mono_of_isPolyhedron hAfrPoly hAfrA)
      hAfrPoly.isCompact (hu.injOn.mono hAfrA)
  have hvFr : IsPLHomeomorphInto 3 v (frontier B) :=
    IsPLOn.isPLHomeomorphInto
      (hv.isPLOn.mono_of_isPolyhedron hBfrPoly hBfrB)
      hBfrPoly.isCompact (hv.injOn.mono hBfrB)
  let f := v ∘ g ∘ Function.invFunOn u (frontier A)
  have ⟨hf, hfimage⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn huFr hvFr hg
  have hDu (i : ι) : u '' DA i = D i := by
    change u '' (Function.invFunOn u A '' D i) = D i
    rw [← image_comp]
    have hleft : EqOn (u ∘ Function.invFunOn u A) id (D i) :=
      fun x hx => hu.injOn.bijOn_image.invOn_invFunOn.2 (hDA i hx)
    exact hleft.image_eq.trans (image_id _)
  have hDv (i : ι) : v '' DB i = D' i := by
    change v '' (Function.invFunOn v B '' D' i) = D' i
    rw [← image_comp]
    have hleft : EqOn (v ∘ Function.invFunOn v B) id (D' i) :=
      fun x hx => hv.injOn.bijOn_image.invOn_invFunOn.2 (hDB i hx)
    exact hleft.image_eq.trans (image_id _)
  have hfi (i : ι) : f '' D i = D' i := by
    have hfu : EqOn (f ∘ u) (v ∘ g) (DA i) := by
      intro z hz
      simp only [f, Function.comp_apply, huFr.injOn.leftInvOn_invFunOn (hDAfr i hz)]
    calc
      f '' D i = f '' (u '' DA i) := by rw [hDu i]
      _ = (f ∘ u) '' DA i := (image_comp f u (DA i)).symm
      _ = (v ∘ g) '' DA i := hfu.image_eq
      _ = v '' (g '' DA i) := image_comp v g (DA i)
      _ = v '' DB i := by rw [hgD i]
      _ = D' i := hDv i
  rw [hAfr, hBfr]
  exact ⟨f, hf, hfimage, hfi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
