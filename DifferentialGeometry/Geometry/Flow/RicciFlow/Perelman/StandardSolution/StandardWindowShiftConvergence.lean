import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricFamilyRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.Time.CompactBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem tendsto_metricScalarAt_of_metricDerivNormSupOn
    {g : ℕ → SmoothRiemannianMetric I M} {g₀ R : SmoothRiemannianMetric I M}
    (hconv : ∀ K : Set M, IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      metricDerivNormSupOn K 2 (g n) g₀ R < e)
    {x : ℕ → M} {x₀ : M} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n => metricScalarAt (g n) (x n)) atTop (𝓝 (metricScalarAt g₀ x₀)) := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  have hcp : MetricCPConvergenceOn K 2 g g₀ R := fun e he =>
    eventually_atTop.mp (hconv K hK e he)
  exact (hcp.tendstoUniformlyOn_metricScalarAt hK).tendsto_comp
    (metricScalar_smooth g₀).continuous.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hx, hx.eventually_mem hKx⟩)

end Scalar

section Accuracy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem eventually_forall_metricDerivNorm_lt_of_tendsto
    {g h : ℕ → ℝ → SmoothRiemannianMetric I M} {R : SmoothRiemannianMetric I M}
    {A : ℕ → Set ℝ} {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ n, ∀ τ ∈ A n, ∀ i ≤ N n, ∀ v : M,
      metricDerivNorm i (g n τ) (h n τ) R v < ε n) :
    ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ A n, ∀ i ≤ p, ∀ v : M,
      metricDerivNorm i (g n τ) (h n τ) R v < e := by
  intro p e he
  filter_upwards [hN.eventually_ge_atTop p, hε.eventually (gt_mem_nhds he)] with n hNn hεn
  exact fun τ hτ i hi v => (hclose n τ hτ i (hi.trans hNn) v).trans hεn

end Accuracy

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (standardCapWindow)

section SolutionScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]

theorem SolutionOn.tendsto_scalar_of_metricDerivNormSupOn {D : RealTimeInterval}
    {S₀ : SolutionOn (I := I) (M := M) D} {S : ℕ → SolutionOn (I := I) (M := M) D}
    (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      ∀ τ ∈ D.carrier, metricDerivNormSupOn K p ((S n).base.metric τ) (S₀.base.metric τ) R < e)
    {t : ℝ} (ht : t ∈ D.carrier) {x' : ℕ → M} {x : M} (hx' : Tendsto x' atTop (𝓝 x)) :
    Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x)) :=
  tendsto_metricScalarAt_of_metricDerivNormSupOn
    (fun K hK e he => (hconv K hK 2 e he).mono fun _ hn => hn t ht) hx'

end SolutionScalar

private local instance (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) :
    SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)

theorem exists_subseq_tendsto_standardCapWindow {r D : ℝ} (hrD : r < D + 1)
    (z : ℕ → EuclideanSpace ℝ (Fin 3)) (hz : ∀ n, ‖z n‖ < r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z₀ : standardCapWindow D, ‖z₀.val‖ ≤ r ∧
      Tendsto (fun n => (⟨z (φ n), (hz (φ n)).trans hrD⟩ : standardCapWindow D)) atTop
        (𝓝 z₀) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) r).tendsto_subseq
      (x := z) fun n => mem_closedBall_zero_iff.mpr (hz n).le
  have har : ‖a‖ ≤ r := mem_closedBall_zero_iff.mp ha
  exact ⟨φ, hφ, ⟨a, show ‖a‖ < D + 1 from har.trans_lt hrD⟩, har, tendsto_subtype_rng.mpr hlim⟩

theorem StandardSolution.eventually_shifted_window_metricDerivNormSupOn_lt
    {Θ a T₀ D : ℝ} (hΘ : Θ < 1) (ha : 0 < a) {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hTΘ : ∀ n, T n ≤ Θ) (hT : Tendsto T atTop (𝓝 T₀))
    {g : ℕ → ℝ → SmoothRiemannianMetric (𝓡 3) (standardCapWindow D)}
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ Icc 0 (T n), ∀ i ≤ p,
      ∀ v : standardCapWindow D, metricDerivNorm i (g n τ)
        (((Q n).val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    {J : Set ℝ} (hJ : J ⊆ Icc a T₀) :
    ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∀ᶠ n in atTop, ∀ σ ∈ J, metricDerivNormSupOn K p (g n (σ + (T n - T₀)))
        ((Q'.val.metric σ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) < e := by
  intro K hK p e he
  have hT₀Θ : T₀ ≤ Θ := le_of_tendsto' hT hTΘ
  have hreg : Icc (a / 2) Θ ⊆ (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).regular := by
    intro t ht
    rw [mem_lifetimeInterval_regular, Q'.lifetime_eq_one]
    exact ⟨(half_pos ha).trans_le ht.1, ENNReal.ofReal_lt_one.mpr (ht.2.trans_lt hΘ)⟩
  obtain ⟨L, hL, hlip⟩ := exists_metric_time_lipschitz_constant_on_compact_regular
    Q'.val.metric Q'.val.metricFamilySmoothOn hreg StandardCap.metric
    (hK.image continuous_subtype_val) p
  obtain ⟨j, hj⟩ := hQ K hK p (e / 4) (by positivity)
  have hδ : 0 < min (a / 2) (e / (4 * (L + 1))) := lt_min (half_pos ha) (by positivity)
  have hsmall : ∀ᶠ n in atTop, |T n - T₀| < min (a / 2) (e / (4 * (L + 1))) := by
    filter_upwards [Metric.tendsto_nhds.mp hT _ hδ] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hclose p (e / 4) (by positivity), eventually_ge_atTop j, hsmall]
    with n hn hnj hns
  intro σ hσ
  have hσJ := hJ hσ
  have hs1 : |T n - T₀| < a / 2 := hns.trans_le (min_le_left _ _)
  have hs2 : |T n - T₀| < e / (4 * (L + 1)) := hns.trans_le (min_le_right _ _)
  have habs := neg_abs_le (T n - T₀)
  have hτ0 : σ + (T n - T₀) ∈ Icc 0 (T n) := ⟨by linarith [hσJ.1], by linarith [hσJ.2]⟩
  have hτΘ : σ + (T n - T₀) ∈ Icc 0 Θ := ⟨hτ0.1, hτ0.2.trans (hTΘ n)⟩
  have hτreg : σ + (T n - T₀) ∈ Icc (a / 2) Θ := ⟨by linarith [hσJ.1], hτΘ.2⟩
  have hσreg : σ ∈ Icc (a / 2) Θ := ⟨by linarith [hσJ.1], hσJ.2.trans hT₀Θ⟩
  have hLs : L * |σ + (T n - T₀) - σ| ≤ e / 4 := by
    rw [add_sub_cancel_left]
    have hL1 : 0 < L + 1 := by linarith
    have hmul : (L + 1) * |T n - T₀| ≤ (L + 1) * (e / (4 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hs2.le hL1.le
    have heq : (L + 1) * (e / (4 * (L + 1))) = e / 4 := by field_simp
    nlinarith [abs_nonneg (T n - T₀)]
  refine (metricDerivNormSupOn_le_of_forall K p _ _ _ (3 * (e / 4)) (by positivity)
    fun i hi v hv => ?_).trans_lt (by linarith)
  have h1 := (hn _ hτ0 i hi v).le
  have h2 := (derivNorm_le_sup hK hi _ _ _ hv).trans (hj n hnj _ hτΘ).le
  have h3 : metricDerivNorm i ((Q'.val.metric (σ + (T n - T₀))).restrictOpen (standardCapWindow D))
      ((Q'.val.metric σ).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) v ≤ e / 4 := by
    rw [metricDerivNorm_restrictOpen]
    exact (hlip i hi _ hτreg σ hσreg v.val ⟨v, hv, rfl⟩).trans hLs
  have t1 := metricDerivNorm_triangle i (g n (σ + (T n - T₀)))
    (((Q n).val.metric (σ + (T n - T₀))).restrictOpen (standardCapWindow D))
    ((Q'.val.metric σ).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  have t2 := metricDerivNorm_triangle i
    (((Q n).val.metric (σ + (T n - T₀))).restrictOpen (standardCapWindow D))
    ((Q'.val.metric (σ + (T n - T₀))).restrictOpen (standardCapWindow D))
    ((Q'.val.metric σ).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  linarith

end DifferentialGeometry.PDE.RicciFlow
