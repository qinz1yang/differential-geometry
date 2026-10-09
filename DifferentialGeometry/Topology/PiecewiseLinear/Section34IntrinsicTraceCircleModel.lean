/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U W : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {η : M₁ → ℝ} {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem exists_section34Trace_circle_intrinsic_model
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {J : Set M₂}
    (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v)) :
    ∃ (P C : Set E3) (u : E3 → M₂), IsCombinatorialSolidTorus P ∧
      IsPLHomeomorphInto 3 u P ∧
      u '' P = section34FaceTorus (section34VertexBallImage src f₁) s ∧
      u '' frontier P = frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∧
      IsPLSphere 1 C ∧ C ⊆ frontier P ∧ u '' C = J := by
  obtain ⟨P, u, hP, hu, hUP, hfront⟩ :=
    exists_section34FaceTorus_intrinsic_model hcut hgraph s
  have hJT' : J ⊆ u '' P := by
    rw [hUP]
    exact hJT.trans (section34Trace_subset_faceTorus hcut hgraph.2.2.1 hinv s)
  have hJΘ : J ⊆ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) :=
    fun x hx => ((section34Trace_eq_inter_frontier_faceTorus hcut hgraph.2.2.1 hinv s).subset
      (hJT hx)).2
  let g := Function.invFunOn u P
  let C := g '' J
  have hC : IsPLSphere 1 C := hu.isPLSphere_invFunOn_image hJ hJT'
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hCΘ : C ⊆ frontier P := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hfront.symm.subset (hJΘ hy)
    rw [← hzy, hleft (hP.isPolyhedron.isClosed.frontier_subset hz)]
    exact hz
  have hUC : u '' C = J := by
    rw [image_image]
    exact (image_congr fun y hy => hu.injOn.bijOn_image.invOn_invFunOn.2 (hJT' hy)).trans
      (image_id J)
  exact ⟨P, C, u, hP, hu, hUP, hfront, hC, hCΘ, hUC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
