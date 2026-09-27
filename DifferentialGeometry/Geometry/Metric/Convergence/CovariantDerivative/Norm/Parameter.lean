import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter

noncomputable section
open Bundle Filter Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem tensor02_norm_continuousOn_in_chart
    (R : SmoothRiemannianMetric I M)
    (A : P → Tensor0SField (I := I) (M := M) ∞ 2) (x : M)
    {S : Set P} {V : Set E} (hV : IsOpen V) (hVt : V ⊆ (extChartAt I x).target)
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => A q.1 ((extChartAt I x).symm q.2)
        (fun j => chartBasisVecFiber (I := I) x (slots j) ((extChartAt I x).symm q.2)))
      (S ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun q : P × E => tensor02CovDerivNormWith r (A q.1) R R
      ((extChartAt I x).symm q.2)) (S ×ˢ V) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_iff_seqContinuous.mpr
  intro q q₀ hq
  have hval := continuous_subtype_val.tendsto q₀ |>.comp hq
  have hp := continuous_fst.tendsto q₀.val |>.comp hval
  have hz := continuous_snd.tendsto q₀.val |>.comp hval
  have hconv (slots : Fin 2 → Fin (Module.finrank ℝ E)) :=
    mapCInfConvergenceOnCompacts_of_tendsto_parameter
      (G := fun p y => A p ((extChartAt I x).symm y)
        (fun j => chartBasisVecFiber (I := I) x (slots j) ((extChartAt I x).symm y)))
      hV (hA slots) (fun n => (q n).val.1) (fun n => (q n).property.1) q₀.property.1 hp
  exact tensor02_covariant_norm_tendsto_of_smooth_chart_convergence (fun _ => R) R
    (fun n => A (q n).val.1) (A q₀.val.1) x hV hVt
    (fun _ _ => mapCInfConvergence_const _) hconv hz.isCompact_insert_range
    (by
      rintro y (rfl | ⟨n, rfl⟩)
      · exact q₀.property.2
      · exact (q n).property.2)
    (fun n => (q n).val.2) (fun n => mem_insert_of_mem _ (mem_range_self n))
    (mem_insert _ _) hz r

theorem tensor02CovDerivNormWith_joint_continuousOn
    (R : SmoothRiemannianMetric I M)
    (A : P → Tensor0SField (I := I) (M := M) ∞ 2) {S : Set P} {U : Set M}
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ extChartAt I x x ∈ V ∧
      V ⊆ (extChartAt I x).target ∧
      ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun q : P × E => A q.1 ((extChartAt I x).symm q.2)
          (fun j => chartBasisVecFiber (I := I) x (slots j) ((extChartAt I x).symm q.2)))
        (S ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun q : P × M => tensor02CovDerivNormWith r (A q.1) R R q.2)
      (S ×ˢ U) := by
  intro q hq
  obtain ⟨V, hV, hxV, hVt, hc⟩ := hlocal q.2 hq.2
  have hchart := tensor02_norm_continuousOn_in_chart R A q.2 hV hVt hc r
  have harg : ContinuousAt (fun w : P × M => (w.1, extChartAt I q.2 w.2)) q :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt q.2).comp continuousAt_snd)
  have hmem : (fun w : P × M => (w.1, extChartAt I q.2 w.2)) ⁻¹' (S ×ˢ V) ∈
      𝓝[S ×ˢ U] q := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (harg.snd.preimage_mem_nhds (hV.mem_nhds hxV))] with w hw hwy
    exact ⟨hw.1, hwy⟩
  have hn := (hchart (q.1, extChartAt I q.2 q.2) ⟨hq.1, hxV⟩).comp_of_preimage_mem_nhdsWithin
    (f := fun w : P × M => (w.1, extChartAt I q.2 w.2)) harg.continuousWithinAt hmem
  apply hn.congr_of_eventuallyEq_of_mem _ hq
  have hs : ∀ᶠ w : P × M in 𝓝[S ×ˢ U] q, w.2 ∈ (extChartAt I q.2).source :=
    nhdsWithin_le_nhds (continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) q.2).mem_nhds (mem_extChartAt_source q.2)))
  filter_upwards [hs] with w hw
  simp only [Function.comp_apply, (extChartAt I q.2).left_inv hw]

end DifferentialGeometry.CheegerGromovCompactness
