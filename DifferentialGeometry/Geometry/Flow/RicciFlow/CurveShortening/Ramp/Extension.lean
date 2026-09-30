import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Continuation

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [I.Boundaryless]
  {D : RealTimeInterval} {a b : ℝ}

private theorem extend_solution_Icc
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a T)) :
    ∃ u : ℝ, T < u ∧ u ≤ b ∧ ∃ extended : ProductCurve M,
      extended.IsSolutionOn B.family.metric lambda (Icc a u) ∧
      ∀ z t, t ∈ Icc a T → extended.map z t = c.map z t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc a T) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc haT) hc
  obtain ⟨u, hTu, hub, solution, hsolution, hagree⟩ :=
    c.map.exists_solution_extension Bhat.toSmoothMetricWindow haT hTb hsol
  obtain ⟨extended, hext, heq⟩ := product_solution_lift A B.family.metric lambda hlambda
    solution (haT.trans hTu) (Icc a u) (Or.inr rfl)
    (by rw [← hm]; exact hsolution)
  exact ⟨u, hTu, hub, extended, hext, fun z t ht =>
    (heq z t ⟨ht.1, ht.2.trans hTu.le⟩).trans (hagree z t ht)⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  [I.Boundaryless] in
private theorem smoothOn_singleton (c : ProductCurve M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    c.SmoothOn (I := I) {t} :=
  ⟨hc.1.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht)),
    hc.2.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht))⟩

theorem exists_ramp_extension
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a T))
    (hramp : c.IsRampOn B.family.metric lambda (Icc a T)) :
    ∃ u : ℝ, T < u ∧ u ≤ b ∧ ∃ extended : ProductCurve M,
      extended.IsSolutionOn B.family.metric lambda (Icc a u) ∧
      extended.IsRampOn B.family.metric lambda (Icc a u) ∧
      ∀ z t, t ∈ Icc a T → extended.map z t = c.map z t := by
  obtain ⟨u, hTu, hub, e, he, heq⟩ := extend_solution_Icc B c lambda hlambda haT hTb hc
  have hr : e.IsRampOn B.family.metric lambda (Icc a T) := by
    refine ⟨fun x t ht => he.immersed x t ⟨ht.1, ht.2.trans hTu.le⟩, ?_⟩
    intro x t ht
    rw [e.angle_eq_of_map_eq c B.family.metric lambda t
      (smoothOn_singleton e he.smooth ⟨ht.1, ht.2.trans hTu.le⟩)
      (smoothOn_singleton c hc.smooth ht) (fun z => heq z t ht) x]
    exact hramp.2 x t ht
  have hTsm : e.SmoothOn (I := I) (Icc T u) :=
    ⟨he.smooth.1.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc haT.le le_rfl)),
      he.smooth.2.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc haT.le le_rfl))⟩
  have hrT : e.IsRampOn B.family.metric lambda {T} :=
    hr.mono (singleton_subset_iff.mpr (show T ∈ Icc a T from ⟨haT.le, le_rfl⟩))
  obtain ⟨δ, hδ, hδu, hδr⟩ := e.exists_isRampOn_Icc_of_smoothOn B.family.metric
    hlambda hTu hTsm hrT
  have hTd : T < T + δ := lt_add_of_pos_right T hδ
  refine ⟨T + δ, hTd, hδu.trans hub, e, he.mono_Icc le_rfl hδu (haT.trans hTd), ?_, ?_⟩
  · refine ⟨fun x t ht => he.immersed x t ⟨ht.1, ht.2.trans hδu⟩, ?_⟩
    intro x t ht
    by_cases htT : t ≤ T
    · exact hr.2 x t ⟨ht.1, htT⟩
    · exact hδr.2 x t ⟨(le_of_not_ge htT), ht.2⟩
  · exact heq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
