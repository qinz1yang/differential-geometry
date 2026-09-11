import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Metric.UniformUpperBound
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic
import DifferentialGeometry.Topology.UniformConvergence

noncomputable section

open Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]

theorem exists_norm_chartGramOp_sub_le
    (R : SmoothRiemannianMetric I M) (alpha : M)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {D D' : RealTimeInterval}
        (G : MetricConnectionFamilyOn (I := I) (M := M) D)
        (G' : MetricConnectionFamilyOn (I := I) (M := M) D')
        (p : Real × E), p.2 ∈ K →
      ‖chartGramOp (I := I) G alpha p - chartGramOp (I := I) G' alpha p‖ ≤
        C * metricDerivNorm (I := I) 0 (G.metric p.1) (G'.metric p.1) R
          ((extChartAt I alpha).symm p.2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hKtgt : K ⊆ (extChartAt I alpha).target := hKchart
  have hKbase : IsCompact ((extChartAt I alpha).symm '' K) :=
    hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) alpha).mono hKtgt)
  have hKsrc : (extChartAt I alpha).symm '' K ⊆ (chartAt H alpha).source := by
    rintro x ⟨z, hz, rfl⟩
    have hx := (extChartAt I alpha).map_target (hKtgt hz)
    simpa only [extChartAt_source] using hx
  obtain ⟨A, hA, hAbound⟩ :=
    g_inner_chartJinv_sqrt_uniform_upper_bound_on_compact
      (I := I) (M := M) R alpha hKbase hKsrc
  refine ⟨A ^ 2, sq_nonneg A, ?_⟩
  intro D D' G G' p hp
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le
  · exact mul_nonneg (sq_nonneg A) (Real.sqrt_nonneg _)
  intro v w hv hw
  simp only [RCLike.re_to_real, sub_apply, inner_sub_left,
    chartGramOp_inner]
  let x := (extChartAt I alpha).symm p.2
  let J := Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
    (I := I) (M := M) alpha x
  have hdiff := metricDifference_abs_le (I := I)
    (G.metric p.1) (G'.metric p.1) R x (J v) (J w)
  have hx : x ∈ (extChartAt I alpha).symm '' K := ⟨p.2, hp, rfl⟩
  have hvR := hAbound x hx v
  have hwR := hAbound x hx w
  change Real.sqrt (R.inner x (J v) (J v)) ≤ A * ‖v‖ at hvR
  change Real.sqrt (R.inner x (J w) (J w)) ≤ A * ‖w‖ at hwR
  have hd0 : 0 ≤ metricDerivNorm (I := I) 0
      (G.metric p.1) (G'.metric p.1) R x := Real.sqrt_nonneg _
  have hw0 : 0 ≤ Real.sqrt (R.inner x (J w) (J w)) := Real.sqrt_nonneg _
  calc
    (G.metric p.1).inner x (J v) (J w) - (G'.metric p.1).inner x (J v) (J w)
        ≤ |(G.metric p.1).inner x (J v) (J w) -
            (G'.metric p.1).inner x (J v) (J w)| := le_abs_self _
    _ ≤ metricDerivNorm (I := I) 0 (G.metric p.1) (G'.metric p.1) R x *
          Real.sqrt (R.inner x (J v) (J v)) *
          Real.sqrt (R.inner x (J w) (J w)) := hdiff
    _ ≤ A ^ 2 * metricDerivNorm (I := I) 0
          (G.metric p.1) (G'.metric p.1) R x := by
      rw [hv, mul_one] at hvR
      rw [hw, mul_one] at hwR
      calc
        _ ≤ metricDerivNorm (I := I) 0 (G.metric p.1) (G'.metric p.1) R x * A * A :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvR hd0) hwR hw0 (mul_nonneg hd0 hA.le)
        _ = _ := by ring

theorem tendstoUniformlyOn_chartGramOp
    {ι : Type*} {l : Filter ι} {D D' : RealTimeInterval}
    (G : ι → MetricConnectionFamilyOn (I := I) (M := M) D)
    (G' : MetricConnectionFamilyOn (I := I) (M := M) D')
    (R : SmoothRiemannianMetric I M) (alpha : M)
    {T : Set ℝ} {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
    (hconv : TendstoUniformlyOn
      (fun i (p : ℝ × E) => metricDerivNorm (I := I) 0
        ((G i).metric p.1) (G'.metric p.1) R ((extChartAt I alpha).symm p.2))
      (fun _ => 0) l (T ×ˢ K)) :
    TendstoUniformlyOn (fun i => chartGramOp (I := I) (G i) alpha)
      (chartGramOp (I := I) G' alpha) l (T ×ˢ K) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_chartGramOp_sub_le R alpha hKc hKchart
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hden
  filter_upwards [hconv (ε / (C + 1)) hδ] with i hi
  intro p hp
  have hnorm : 0 ≤ metricDerivNorm (I := I) 0
      ((G i).metric p.1) (G'.metric p.1) R ((extChartAt I alpha).symm p.2) :=
    Real.sqrt_nonneg _
  have hsmall : metricDerivNorm (I := I) 0
      ((G i).metric p.1) (G'.metric p.1) R ((extChartAt I alpha).symm p.2) <
      ε / (C + 1) := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hnorm]
      using hi p hp
  rw [dist_comm, dist_eq_norm]
  calc
    _ ≤ C * metricDerivNorm (I := I) 0
        ((G i).metric p.1) (G'.metric p.1) R ((extChartAt I alpha).symm p.2) :=
      hbound (G i) G' p hp.2
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hsmall.le hC
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_right (lt_add_one C) hδ
    _ = ε := mul_div_cancel₀ ε hden.ne'

theorem tendstoUniformly_chartGramOp
    {ι Q : Type*} {l : Filter ι} {D D' : RealTimeInterval}
    (G : ι → MetricConnectionFamilyOn (I := I) (M := M) D)
    (G' : MetricConnectionFamilyOn (I := I) (M := M) D')
    (R : SmoothRiemannianMetric I M) (alpha : M)
    {T : Set ℝ} {K : Set E} (hTc : IsCompact T) (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
    (hG' : ContinuousOn (chartGramOp (I := I) G' alpha) (T ×ˢ K))
    (hconv : TendstoUniformlyOn
      (fun i (p : ℝ × E) => metricDerivNorm (I := I) 0
        ((G i).metric p.1) (G'.metric p.1) R ((extChartAt I alpha).symm p.2))
      (fun _ => 0) l (T ×ˢ K))
    {tau : Q → ℝ} {u : ι → Q → E} {v : Q → E}
    (htau : ∀ q, tau q ∈ T) (huK : ∀ᶠ i in l, ∀ q, u i q ∈ K)
    (hvK : ∀ q, v q ∈ K) (hu : TendstoUniformly u v l) :
    TendstoUniformly
      (fun i q => chartGramOp (I := I) (G i) alpha (tau q, u i q))
      (fun q => chartGramOp (I := I) G' alpha (tau q, v q)) l := by
  have htauSelf : TendstoUniformly (fun _ : ι => tau) tau l := by
    rw [tendstoUniformly_iff_tendsto]
    exact tendsto_diag_uniformity (tau ∘ Prod.snd) (l ×ˢ ⊤)
  have hpair : TendstoUniformly
      (fun i q => (tau q, u i q)) (fun q => (tau q, v q)) l :=
    fun U hU => ((htauSelf.prodMk hu) U hU).diag_of_prod
  apply (tendstoUniformlyOn_chartGramOp G G' R alpha hKc hKchart hconv).comp_tendstoUniformly
    ((hTc.prod hKc).uniformContinuousOn_of_continuous hG') hpair
  · filter_upwards [huK] with i hi
    exact fun q => ⟨htau q, hi q⟩
  · exact fun q => ⟨htau q, hvK q⟩

end DifferentialGeometry.Geometry.Curvature
