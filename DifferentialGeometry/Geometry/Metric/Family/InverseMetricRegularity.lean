import DifferentialGeometry.Geometry.Metric.InverseMetricField


noncomputable section


open Set Function Bundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartBasisVec_jointContMDiffOn (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p.1))
      ((chartAt H α).source ×ˢ (Set.univ : Set ℝ)) := by
  have hbase := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α i
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  rw [hbase_eq] at hbase
  exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)

theorem metricSharpChartCoeff_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  have heq : (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1) =
      (fun p : M × ℝ => ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j *
          cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1)) := by
    funext p; rw [metricSharpChartCoeff_def]
  rw [heq]
  exact contMDiffOn_finsetSum (fun j _ => (hinv i j).mul (hcv j))

theorem metricSharpChartLocal_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (metricSharpChartLocal (I := I) (gfam p.2) α (cv p.2) p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hcoeff : ∀ i, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) :=
    fun i => metricSharpChartCoeff_jointContMDiffOn (I := I) gfam α cv hinv hcv i
  set e := trivializationAt E (TangentSpace I) α with he
  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ S,
      (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2 =
        ∑ i, metricSharpChartCoeff (I := I) (gfam q.2) α (cv q.2) i q.1 •
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    unfold metricSharpChartLocal
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd (I := I) α i hqbase]
  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2)
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finsetSum (fun i _ => ?_)
    exact (hcoeff i).smul contMDiffOn_const
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

theorem metricSharp_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ} (hS : IsOpen S)
    (hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (DifferentialGeometry.Geometry.Operator.metricSharp
          (I := I) (gfam p.2) p.1 (cv p.2 p.1)))
      (Set.univ ×ˢ S) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp
  have hlocal := metricSharpChartLocal_jointContMDiffOn (I := I) gfam p.1 cv
    (hinv p.1) (hcv p.1)
  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ S,
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (DifferentialGeometry.Geometry.Operator.metricSharp
            (I := I) (gfam q.2) q.1 (cv q.2 q.1)) := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    rw [metricSharpChartLocal_eq_metricSharp (I := I) (gfam q.2) p.1 (cv q.2) hqbase]
  have hpmem : p ∈ (chartAt H p.1).source ×ˢ S := ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ S ∈ nhdsWithin p (Set.univ ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ S,
      (chartAt H p.1).open_source.prod hS, hpmem, fun q hq => hq.1⟩
  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1))
      (Set.univ ×ˢ S) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd
  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

end DifferentialGeometry.Geometry.Operator
