import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalCompact
import DifferentialGeometry.Analysis.Calculus.Derivative.SuperlevelMonotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_eventually_scalar_bound_of_terminal_convergence_of_deriv_nonneg_above
    {D : ℕ → RealTimeInterval} (S : ∀ n, SolutionOn (I := I) (M := M) (D n))
    (hS : ∀ n, IsSolutionOn (S n)) (R Rref : SmoothRiemannianMetric I M)
    {a b q0 : ℝ} {q : ℕ → ℝ} {K : Set M} (hK : IsCompact K)
    (hslab : ∀ᶠ n in atTop, Icc a b ⊆ (D n).carrier)
    (hterminal : MetricCPConvergenceOn K 2 (fun n => (S n).base.metric b) R Rref)
    (hq : ∀ᶠ n in atTop, q n ≤ q0)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ t ∈ Ioo a b,
      q n < (S n).scalar t x →
      0 ≤ derivWithin (fun r => (S n).scalar r x) (Iic t) t) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ K, (S n).scalar t x ≤ B := by
  obtain ⟨A, hA⟩ := (hK.image (metricScalar_smooth R).continuous).bddAbove
  let B := max 1 (max q0 (A + 1))
  refine ⟨B, le_max_left _ _, ?_⟩
  have hconv := hterminal.tendstoUniformlyOn_metricScalarAt hK
  have hclose := Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one
  filter_upwards [hslab, hq, hbound, hclose] with n hnslab hnq hnbound hnclose
  intro t ht x hx
  have hterminalBound : (S n).scalar b x ≤ A + 1 := by
    have he := hnclose x hx
    rw [Real.dist_eq] at he
    have hA' : metricScalarAt R x ≤ A := hA (mem_image_of_mem _ hx)
    have hd := (abs_lt.mp he).1
    change metricScalarAt R x - (S n).scalar b x > -1 at hd
    linarith
  have hh := DifferentialGeometry.Analysis.le_max_endpoint_of_deriv_nonneg_above
    (q := q n) (fun r hr => ((hS n).scalarTime hr hnslab x).continuousWithinAt) (fun r hr hh => by
      have hd := ((hS n).scalarTime hr (Ioo_subset_Icc_self.trans hnslab) x).differentiableAt
        (Ioo_mem_nhds hr.1 hr.2)
      refine ⟨hd, ?_⟩
      simpa only [hd.derivWithin (uniqueDiffWithinAt_Iic r)] using hnbound x hx r hr hh) ht
  exact hh.trans (max_le (hnq.trans ((le_max_left q0 (A + 1)).trans (le_max_right _ _)))
    (hterminalBound.trans ((le_max_right q0 (A + 1)).trans (le_max_right _ _))))

theorem exists_eventually_riemannNorm_bound_of_terminal_convergence_of_deriv_nonneg_above
    {D : ℕ → RealTimeInterval} (S : ∀ n, SolutionOn (I := I) (M := M) (D n))
    (hS : ∀ n, IsSolutionOn (S n)) (R Rref : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3)
    {a b q0 : ℝ} {q scale : ℕ → ℝ} {K : Set M} (hK : IsCompact K)
    (hslab : ∀ᶠ n in atTop, Icc a b ⊆ (D n).carrier)
    (hterminal : MetricCPConvergenceOn K 2 (fun n => (S n).base.metric b) R Rref)
    (hq : ∀ᶠ n in atTop, q n ≤ q0)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ t ∈ Ioo a b,
      q n < (S n).scalar t x →
      0 ≤ derivWithin (fun r => (S n).scalar r x) (Iic t) t)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscale : Tendsto scale atTop atTop)
    (hpinch : ∀ᶠ n in atTop, PhiAlmostNonnegative (S n) (Icc a b)
      (rescalePinchingFunction (scale n) Phi)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ K,
        Real.sqrt (FlowMetricBall.rmNormSq (S n) t x) ≤ C := by
  obtain ⟨B, hB, hscalar⟩ :=
    exists_eventually_scalar_bound_of_terminal_convergence_of_deriv_nonneg_above
      S hS R Rref hK hslab hterminal hq hbound
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨4 * Real.sqrt 3 * (B + 2), by positivity, ?_⟩
  obtain ⟨Q0, hQ0, hsmall⟩ := exists_forall_rescalePinchingFunction_le hPhi
    (B := 4 * B) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hscalar, hpinch, hscale.eventually (eventually_ge_atTop Q0)] with n hn hnpi hnscale
  intro t ht x hx
  have hscalePos : 0 < scale n := hQ0.trans_le hnscale
  have hbridge : RmNormBoundOn (S n) (2 * Real.sqrt 3) :=
    fun t y basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (S n) t y basis horth ha
  have hsc : (S n).scalar t x ≤ 4 * B := (hn t ht x hx).trans (by linarith)
  have hh := sqrt_rmNormSq_le_of_scalar_le (by positivity : 0 ≤ 2 * Real.sqrt 3)
    hbridge (hPhi.rescale hscalePos) hnpi hdim ht x hBpos hsc
  have hzero := hsmall (scale n) hnscale 0 ⟨le_rfl,by positivity⟩
  have hfour := hsmall (scale n) hnscale (4 * B) ⟨by positivity,le_rfl⟩
  apply hh.trans
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem exists_eventually_curvDerivNorm_bound_of_terminal_convergence_of_deriv_nonneg_above
    {D : ℕ → RealTimeInterval} (S : ∀ n, SolutionOn (I := I) (M := M) (D n))
    (hS : ∀ n, IsSolutionOn (S n)) (R : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3)
    {a b q0 : ℝ} {q scale : ℕ → ℝ} (hab : a < b)
    (hslab : ∀ᶠ n in atTop, Icc a b ⊆ (D n).carrier)
    (hregular : ∀ᶠ n in atTop, Ioo a b ⊆ (D n).regular)
    (hterminal : ∀ K : Set M, IsCompact K →
      MetricCPConvergenceOn K 2 (fun n => (S n).base.metric b) R R)
    (hq : ∀ᶠ n in atTop, q n ≤ q0)
    (hbound : ∀ K : Set M, IsCompact K → ∀ᶠ n in atTop, ∀ x ∈ K, ∀ t ∈ Ioo a b,
      q n < (S n).scalar t x →
      0 ≤ derivWithin (fun r => (S n).scalar r x) (Iic t) t)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscale : Tendsto scale atTop atTop)
    (hpinch : ∀ᶠ n in atTop, PhiAlmostNonnegative (S n) (Icc a b)
      (rescalePinchingFunction (scale n) Phi))
    (K : Set M) (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ n in atTop,
      ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) x ≤ C m := by
  apply exists_eventually_curvDerivNorm_on_compact_of_eventual_interval S hS R hab hslab hregular
    ?_ ?_ K hK
  · intro L hL ε hε
    obtain ⟨n0, hn0⟩ := hterminal L hL (ε / 2) (by positivity)
    refine ⟨n0, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall L 0
      ((S n).base.metric b) R R (ε / 2) (by positivity) ?_) (by linarith)
    intro m hm x hx
    exact ((derivNorm_le_sup hL (by omega : m ≤ 2)
      ((S n).base.metric b) R R hx).trans_lt (hn0 n hn)).le
  · intro L hL
    obtain ⟨C, hC, hbnd⟩ :=
      exists_eventually_riemannNorm_bound_of_terminal_convergence_of_deriv_nonneg_above
        S hS R R hdim hL hslab (hterminal L hL) hq (hbound L hL) hPhi hscale hpinch
    refine ⟨C ^ 2, hbnd.mono fun n hn t ht x hx => ?_⟩
    exact (Real.sqrt_le_iff.mp (hn t ht x hx)).2

theorem exists_eventually_curvDerivNorm_bound_of_terminal_convergence_of_strongNeck
    {M0 : Type*} [TopologicalSpace M0] [ChartedSpace Surgery.Topology.ThreeSpace M0]
    [IsManifold Surgery.Topology.ThreeModel ∞ M0] [T2Space M0] [SigmaCompactSpace M0]
    {D : ℕ → RealTimeInterval}
    (S : ∀ n, SolutionOn (I := Surgery.Topology.ThreeModel) (M := M0) (D n))
    (hS : ∀ n, IsSolutionOn (S n)) (R : SmoothRiemannianMetric Surgery.Topology.ThreeModel M0)
    {a b q0 : ℝ} {q scale : ℕ → ℝ} (hab : a < b)
    (hslab : ∀ᶠ n in atTop, Icc a b ⊆ (D n).carrier)
    (hregular : ∀ᶠ n in atTop, Ioo a b ⊆ (D n).regular)
    (hterminal : ∀ K : Set M0, IsCompact K →
      MetricCPConvergenceOn K 2 (fun n => (S n).base.metric b) R R)
    (hq : ∀ᶠ n in atTop, q n ≤ q0)
    (hneck : ∀ K : Set M0, IsCompact K → ∀ᶠ n in atTop, ∀ x ∈ K, ∀ t ∈ Ioo a b,
      q n < (S n).scalar t x →
        ∃ eps : ℝ, Nonempty (FiniteHorn.StrongNeck (S n) eps x t))
    (hneckRegular : ∀ K : Set M0, IsCompact K → ∀ᶠ n in atTop, ∀ x ∈ K, ∀ t ∈ Ioo a b,
      q n < (S n).scalar t x → ∀ s ∈ Ioo (-1 : ℝ) 0,
        parabolicTime t ((S n).scalar t x) s ∈ (D n).regular)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscale : Tendsto scale atTop atTop)
    (hpinch : ∀ᶠ n in atTop, PhiAlmostNonnegative (S n) (Icc a b)
      (rescalePinchingFunction (scale n) Phi))
    (K : Set M0) (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ n in atTop,
      ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) x ≤ C m := by
  apply exists_eventually_curvDerivNorm_bound_of_terminal_convergence_of_deriv_nonneg_above
    S hS R (by simp [Surgery.Topology.ThreeSpace]) hab hslab hregular hterminal hq ?_
    hPhi hscale hpinch K hK
  intro L hL
  filter_upwards [hneck L hL, hneckRegular L hL] with n hn hnr
  intro x hx t ht hh
  obtain ⟨eps, ⟨nk⟩⟩ := hn x hx t ht hh
  exact (nk.scalar_derivWithin_pos (hS n) (hnr x hx t ht hh)).le

end DifferentialGeometry.CheegerGromovCompactness
