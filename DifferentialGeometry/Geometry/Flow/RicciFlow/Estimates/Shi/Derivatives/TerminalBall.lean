import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Derivatives

noncomputable section

open Bundle Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem shi_curvDerivNorm_terminal_of_terminal_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K R : ℝ} (hab : a < b) (hK : 0 < K) (hR : 0 < R)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ico a b ⊆ D.regular)
    (p : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric b) p R))
    (hcurv : ∀ t ∈ Icc a b, ∀ y ∈ riemannianClosedBallOf (S.base.metric b) p R,
      curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) (m : ℕ) :
    curvDerivNorm (I := I) m (S.base.metric b) p ≤
      shiLocalUniformBound (Module.finrank ℝ E) m (K * (b - a))
        (R * Real.sqrt K / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (b - a)))) *
          K / Real.sqrt (b - a) ^ m := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hdim : Module.finrank ℝ E ≤ 1
  · rw [curvDerivNorm_eq_zero_of_finrank_le_one (S.base.metric b) hdim m p]
    exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  have hdim' : 2 ≤ Module.finrank ℝ E := by omega
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let L : ℝ := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (b - a))
  have hL : 0 < L := Real.exp_pos _
  have hquad : ∀ y ∈ riemannianClosedBallOf (S.base.metric b) p R,
      ∀ v : TangentSpace I y,
        (S.base.metric b).inner y v v ≤ L ^ 2 * (S.base.metric a).inner y v v := by
    intro y hy v
    have hderiv : ∀ t ∈ Icc a b,
        ∃ d : ℝ, HasDerivWithinAt (fun s => (S.base.metric s).inner y v v) d (Icc a b) t ∧
          |d| ≤ (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * K)) *
            (S.base.metric t).inner y v v := by
      intro t ht
      refine ⟨_, metricPDE_Icc S hS hcarrier
        (fun s hs => hregular ⟨hs.1.le, hs.2⟩) t ht y v v, ?_⟩
      have hr := ricci_quadratic_form_bound_of_solution_curvature_bound S y v (hcurv t ht y hy)
      rw [Real.sqrt_sq hK.le] at hr
      rw [abs_mul, abs_neg, abs_two]
      nlinarith [hr]
    have hb := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric y v hderiv
      (right_mem_Icc.mpr hab.le) (left_mem_Icc.mpr hab.le)
    rw [abs_of_pos (sub_pos.mpr hab)] at hb
    have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * K) * (b - a)) = L ^ 2 := by
      dsimp only [L]
      rw [pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hb
  have hcontain : riemannianClosedBallOf (S.base.metric a) p (R / (4 * L)) ⊆
      riemannianClosedBallOf (S.base.metric b) p R := by
    let F := PartialDiffeomorph.refl (I := I) M
    have hcapture := PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
      (S.base.metric b) (S.base.metric a) F (O := p) (x := p)
      (r := R / 4) (R := R) (A := R / (2 * L)) hL.le
      hcompact (fun _ _ => mem_univ _) (by
        intro y hy v
        change (S.base.metric b).inner y v v ≤ L ^ 2 *
          (S.base.metric a).inner y (mfderiv I I id y v) (mfderiv I I id y v)
        rw [mfderiv_id]
        exact hquad y hy v)
      (by
        change riemannianEDistOf (S.base.metric b) p p < ENNReal.ofReal (R / 4)
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr (by positivity))
      (by
        have heq : L * (R / (2 * L)) = R / 2 := by field_simp
        rw [heq]
        linarith)
    intro y hy
    have hy' : y ∈ riemannianBallOf (S.base.metric a) p (R / (2 * L)) := by
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (div_lt_div_of_pos_left hR (by positivity) (by linarith)))
    obtain ⟨z, hz, hzy⟩ := hcapture hy'
    have hzy' : z = y := hzy
    exact hzy' ▸ hz
  let r : ℝ := R * Real.sqrt K / (4 * L)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrad : r / Real.sqrt K = R / (4 * L) := by
    dsimp only [r]
    field_simp
  have hball : IsCompact {y : M | riemannianEDistOf (S.base.metric a) p y ≤
      ENNReal.ofReal (r / Real.sqrt K)} := by
    rw [hrad]
    apply hcompact.of_isClosed_subset ?_ hcontain
    let g := S.base.metric a
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    change IsClosed {y : M | edist p y ≤ ENNReal.ofReal (R / (4 * L))}
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hb := Perelman.KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets S hS hdim'
    hab hK hr hcarrier hregular p hball (by
      intro t ht y hy
      rw [hrad] at hy
      exact hcurv t ht y (hcontain hy)) m b ⟨hab, le_rfl⟩ p (by
        rw [riemannianEDistOf_self]
        exact zero_le)
  exact hb

end DifferentialGeometry.PDE.RicciFlow
