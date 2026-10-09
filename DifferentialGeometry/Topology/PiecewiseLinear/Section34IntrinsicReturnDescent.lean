/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OperationImages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceRimFiniteness
import DifferentialGeometry.Topology.PiecewiseLinear.SphereReturnDiskDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem exists_section34BigonSlide_of_model_return_disk_crosscuts
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') {P S B₀ R₀ D₀ : Set E3} {u : E3 → M₂}
    {q₀ : (Fin 3 → ℝ) → E3} {β₀ δ₀ : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P) (hS : IsPLSphere 2 S)
    (hβ₀ : IsPLHomeomorphOn β₀ (Icc 0 1) B₀) (hBF₀ : B₀ ⊆ u ⁻¹' fblBd s)
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) R₀)
    (hδ₀0 : δ₀ 0 = β₀ 0) (hδ₀1 : δ₀ 1 = β₀ 1)
    (hR₀ : R₀ ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e)
    (hB₀R₀ : B₀ ∩ R₀ = {β₀ 0, β₀ 1})
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₀B : q₀ '' stdSimplexBoundary 2 = B₀ ∪ R₀) (hD₀S : D₀ ⊆ S) (hD₀P : D₀ ⊆ P)
    (hD₀loc : D₀ ⊆ u ⁻¹' (section34VertexBallImage srcBd f₁ w ∩
      frontier (⋃ v, section34VertexBallImage src f₁ v)))
    (hD₀E : D₀ ∩ u ⁻¹' section34SplitDiskImage src f₁ e = R₀)
    (hother : ∀ d : Section34EdgeIndex 𝒦 𝒦', d ≠ e →
      Disjoint D₀ (u ⁻¹' section34SplitDiskImage src f₁ d))
    (hcross : ∀ (t : Section34SimplexIndex 𝒦 3) (B R D : Set E3)
      (q : (Fin 3 → ℝ) → E3) (β δ : ℝ → E3),
      IsPLHomeomorphOn β (Icc 0 1) B → B ⊆ u ⁻¹' fblBd t →
      IsPLHomeomorphOn δ (Icc 0 1) R → δ 0 = β 0 → δ 1 = β 1 →
      R ⊆ R₀ → B ∩ R = {β 0, β 1} →
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      q '' stdSimplexBoundary 2 = B ∪ R → D ⊆ D₀ → D ∩ R₀ = R →
      ((D \ (B ∪ R)) ∩ ⋃ a : Section34SimplexIndex 𝒦 3, u ⁻¹' fblBd a).Nonempty →
      ∃ (a : Section34SimplexIndex 𝒦 3) (A : Set E3) (α : ℝ → E3),
        IsPLHomeomorphOn α (Icc 0 1) A ∧ A ⊆ u ⁻¹' fblBd a ∧ A ⊆ D ∧
        A ∩ (B ∪ R) = {α 0, α 1} ∧ ({α 0, α 1} : Set E3) ⊆ R \ {β 0, β 1}) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd t := by
  have hR₀D₀ : R₀ ⊆ D₀ := hD₀E.symm.subset.trans inter_subset_left
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hfinite := finite_section34Trace_inter_model_vertex_rim hcut hinv w e hu.injOn
    (hR₀D₀.trans hD₀P)
    (fun x hx => hV.boundary_subset (hD₀loc (hR₀D₀ hx)).1) hR₀
  obtain ⟨t, B, R, D, q, β, δ, hβ, hBF, hδ, hδ0, hδ1, hRR₀, hBR,
    hq, hqB, hDD₀, hDR₀, hclean⟩ :=
    hS.exists_clean_return_subdisk (fun t => u ⁻¹' fblBd t) s hβ₀ hBF₀ hδ₀
      hδ₀0 hδ₀1 hB₀R₀ hq₀ hq₀B hD₀S hfinite hcross
  have hboundaryD : B ∪ R ⊆ D := by
    rw [← hqB, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hBD : B ⊆ D := subset_union_left.trans hboundaryD
  have hRD : R ⊆ D := subset_union_right.trans hboundaryD
  have hDP : D ⊆ P := hDD₀.trans hD₀P
  have hRγ : R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e := hRR₀.trans hR₀
  have hendsR : ({β 0, β 1} : Set E3) ⊆ R := hBR.symm.subset.trans inter_subset_right
  have hBE : B ∩ u ⁻¹' (⋃ d, section34SplitDiskImage src f₁ d) = {β 0, β 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxE⟩
      obtain ⟨d, hxd⟩ := mem_iUnion.mp hxE
      by_cases hde : d = e
      · have hxR₀ := hD₀E.subset ⟨hDD₀ (hBD hxB), hde ▸ hxd⟩
        exact hBR.subset ⟨hxB, hDR₀.subset ⟨hBD hxB, hxR₀⟩⟩
      · exact (disjoint_left.mp (hother d hde) (hDD₀ (hBD hxB)) hxd).elim
    · intro x hx
      exact ⟨(pair_subset (hβ.bijOn.mapsTo (by norm_num))
        (hβ.bijOn.mapsTo (by norm_num))) hx, mem_iUnion.mpr
        ⟨e, (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset (hRγ (hendsR hx))⟩⟩
  have hDcell : IsPLCellOn 2 D (B ∪ R) := by
    rw [← hqB]
    exact isPLCellOn_id_of_isPLBall hq
  have hRcell : IsPLCellOn 1 R {β 0, β 1} := by
    rw [← hδ0, ← hδ1]
    exact isPLCellOn_one_of_isPLHomeomorphOn_Icc hδ
  refine ⟨t, exists_section34BigonSlide_of_pl_model hu t w e
    (isPLCellOn_one_of_isPLHomeomorphOn_Icc hβ) (hBD.trans hDP) hBF
    (fun x hx => (hD₀loc (hDD₀ (hBD hx))).1) (hendsR.trans hRγ) hBE
    hRcell (hRD.trans hDP) hRγ hBR hDcell hDP (hDD₀.trans hD₀loc) rfl hclean⟩

end DifferentialGeometry.Topology.PiecewiseLinear
