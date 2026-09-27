/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualForeignVertex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.inter_subset_frontier_of_disjoint_interior_left
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {R S : Set M} (hR : IsPLCellOn 3 R (frontier R))
    (hdis : Disjoint (interior R) S) : R ∩ S ⊆ frontier S := by
  rintro z ⟨hzR, hzS⟩
  refine ⟨subset_closure hzS, fun hzi => ?_⟩
  obtain ⟨q, hqS, hqR⟩ := mem_closure_iff.mp
    (hR.subset_closure_interior hzR) _ isOpen_interior hzi
  exact Set.disjoint_left.mp hdis hqR (interior_subset hqS)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.residual_inter_splitDiskImage_subset
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    R ∩ section34SplitDiskImage src f₁ e ⊆ section34SplitDiskImage srcBd f₁ e := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  by_cases he : Section34Incident e.1 t.1
  · obtain ⟨c, hc, -, hVc, -⟩ := hdata.exists_chart_tetrahedron t
    have hends : ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
        section34VertexBallImage src f₁ w ⊆ c.source :=
      fun w hw => hVc w (fun x hx => he (hw hx))
    intro y hy
    by_contra hyb
    have hyi := hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc hends ⟨hy.2, hyb⟩
    obtain ⟨q, hqV, hqR⟩ := mem_closure_iff.mp
      (hR.subset_closure_interior hy.1) _ isOpen_interior hyi
    obtain ⟨w, hw, hqw⟩ := mem_iUnion₂.mp (interior_subset hqV)
    exact Set.disjoint_left.mp hint hqR
      (mem_iUnion₂.mpr ⟨w, fun x hx => he (hw hx), hqw⟩)
  · rw [hcut.residual_inter_splitDiskImage_eq_empty hf₁.injOn h7 he]
    exact empty_subset _

end DifferentialGeometry.Topology.PiecewiseLinear
