import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Set Function Bundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

theorem chartGramFamilyJointSmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) :
    chartGramFamilyJointSmoothOn (I := I) (fun t => g_fam t) α D.regular := by
  intro i j s₀ y₀ hs hy
  exact (MetricFamilySmoothOn.chartGramOnE_contDiffOn
    (I := I) hG (J := D.regular) Subset.rfl α i j).contDiffAt
    (prod_mem_nhds (D.regular_isOpen.mem_nhds hs) (isOpen_interior.mem_nhds hy))

variable [I.Boundaryless]

theorem chartInvGramMatrix_jointContMDiffOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) (g_fam p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := chartGramFamilyJointSmoothOn (I := I) g_fam hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_joint_contDiffAt (I := I) (fun t => g_fam t) α hGram i j ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I) (g_fam r.1) α i j r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

theorem chartChristoffel_comp_extChartAt_jointContMDiffOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        chartChristoffel (I := I) (g_fam p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := chartGramFamilyJointSmoothOn (I := I) g_fam hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartChristoffel_joint_contDiffAt (I := I) (fun t => g_fam t) α hGram i j k ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (g_fam r.1) α i j k r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hcomp := hentryM.comp_contMDiffWithinAt p hmoveAt
  change ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
    (fun q : M × ℝ =>
      chartChristoffel (I := I) (g_fam q.2) α i j k (extChartAt I α q.1))
    ((chartAt H α).source ×ˢ D.regular) p at hcomp
  exact hcomp

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature
