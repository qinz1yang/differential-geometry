import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Derivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Comparison.LocalDistanceComparison
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback

noncomputable section
open Set
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian (riemannianEDistOf_le_of_metric_lower_on_ball)

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem curvDerivNorm_le_on_terminal_ball_of_curvature_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {T r K : ℝ} (hT : 0 < T) (hr : 0 < r) (hK : 0 < K)
    (hcarrier : Icc (-T) 0 ⊆ D.carrier) (hregular : Ioo (-T) 0 ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric (-(T / 2))))
    (p : M)
    (hcurv : ∀ t ∈ Icc (-T) 0, ∀ y ∈ riemannianClosedBallOf (S.base.metric 0) p r,
      curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2)
    (m : ℕ) (t : ℝ) (ht : t ∈ Icc (-(T / 4)) 0)
    (x : M) (hx : x ∈ riemannianClosedBallOf (S.base.metric 0) p (r / 2)) :
    curvDerivNorm (I := I) m (S.base.metric t) x ≤
      shiLocalUniformBound (Module.finrank ℝ E) m (K * (T / 2))
        (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 * K * T / 2)) * (r / 4) *
          Real.sqrt K) * K / Real.sqrt (T / 4) ^ m := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : BoundarylessManifold I M := inferInstance
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let beta : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 * K * T / 2))
  let rho : ℝ := beta * (r / 4)
  let R : ℝ := rho * Real.sqrt K
  have hbeta : 0 < beta := Real.exp_pos _
  have hrho : 0 < rho := mul_pos hbeta (by positivity)
  have hR : 0 < R := mul_pos hrho (Real.sqrt_pos.mpr hK)
  have hRdiv : R / Real.sqrt K = rho := by
    dsimp only [R]
    exact mul_div_cancel_right₀ rho (Real.sqrt_pos.mpr hK).ne'
  have ha : -(T / 2) ∈ Icc (-T) 0 := ⟨by linarith, by linarith⟩
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
  have hsub : Icc (-(T / 2)) 0 ⊆ Icc (-T) 0 :=
    fun _ hs => ⟨by linarith [hs.1], hs.2⟩
  have hsubreg : Ico (-(T / 2)) 0 ⊆ D.regular := by
    intro s hs
    exact hregular ⟨by linarith [hs.1], hs.2⟩
  have hballx : ∀ y : M,
      riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (r / 2) →
        y ∈ riemannianClosedBallOf (S.base.metric 0) p r := by
    intro y hy
    have hadd : ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) =
        ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ r / 2) (by positivity : 0 ≤ r / 2)]
      congr 1
      ring
    exact (riemannianEDistOf_triangle (S.base.metric 0) p x y).trans
      ((add_le_add hx hy).trans_eq hadd)
  have hmetric : ∀ y : M,
      riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (r / 2) →
      ∀ v : TangentSpace I y,
        beta ^ 2 * (S.base.metric 0).inner y v v ≤
          (S.base.metric (-(T / 2))).inner y v v := by
    intro y hy v
    have hbound : ∀ s ∈ Icc (-T) 0,
        Tensor0SBundle.normSq0S (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K ^ 2 := by
      intro s hs
      exact hcurv s hs y (hballx y hy)
    have h := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular y
      hbound ha hzero v).1
    have habs : |-(T / 2) - (0 : ℝ)| = T / 2 := by
      rw [sub_zero, abs_neg, abs_of_pos (by positivity : 0 < T / 2)]
    have hbetasq : beta ^ 2 =
        Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 2 * K * (T / 2))) := by
      dsimp only [beta]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Real.sqrt_sq hK.le, habs, ← hbetasq] at h
    exact h
  have hcapture : ∀ y : M,
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤ ENNReal.ofReal rho →
        y ∈ riemannianClosedBallOf (S.base.metric 0) p r := by
    intro y hy
    have hsmall : rho < beta * (r / 2) := by dsimp only [rho]; nlinarith
    have hdist : riemannianEDistOf (S.base.metric (-(T / 2))) x y <
        ENNReal.ofReal (beta * (r / 2)) :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hsmall)
    have hle := riemannianEDistOf_le_of_metric_lower_on_ball
      (S.base.metric 0) (S.base.metric (-(T / 2))) x y hbeta hmetric hdist
    have hreal : (riemannianEDistOf (S.base.metric (-(T / 2))) x y).toReal ≤ rho :=
      (ENNReal.toReal_le_of_le_ofReal hrho.le hy)
    apply hballx y
    apply hle.trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hbeta).2
    exact hreal.trans (by dsimp only [rho]; nlinarith)
  have hball : IsCompact {y : M |
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    rw [hRdiv]
    exact hcomplete.closedEBall_isCompact x rho
  have hcurv' : ∀ s ∈ Icc (-(T / 2)) 0, ∀ y : M,
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
      curvDerivNormSq (I := I) 0 (S.base.metric s) y ≤ K ^ 2 := by
    intro s hs y hy
    rw [hRdiv] at hy
    exact hcurv s (hsub hs) y (hcapture y hy)
  have hcenter : riemannianEDistOf (S.base.metric (-(T / 2))) x x ≤
      ENNReal.ofReal (R / (2 * Real.sqrt K)) := by
    rw [riemannianEDistOf_self]
    exact bot_le
  have hshi := Perelman.KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets
    S hS hdim (a := -(T / 2)) (b := 0) (by linarith) hK hR
    (hsub.trans hcarrier) hsubreg x hball hcurv' m t
    ⟨by linarith [ht.1], ht.2⟩ x hcenter
  have hden : Real.sqrt (T / 4) ^ m ≤ Real.sqrt (t - -(T / 2)) ^ m :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith [ht.1])) m
  have hbound := hshi.trans (div_le_div_of_nonneg_left
    (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
    (pow_pos (Real.sqrt_pos.mpr (by positivity : 0 < T / 4)) m) hden)
  simpa only [sub_neg_eq_add, zero_add, R, rho, beta] using hbound

end DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped ENNReal

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem shi_curvDerivNorm_on_terminal_ball_of_innerProductSpace
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K R : ℝ} (hab : a < b) (hK : 0 < K) (hR : 0 < R)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (p : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric b) p R))
    (hcurv : ∀ t ∈ Icc a b, ∀ y ∈ riemannianClosedBallOf (S.base.metric b) p R,
      curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) :
    let tau := (b - a) / 4
    let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (b - a))
    ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b,
      ∀ x ∈ riemannianClosedBallOf (S.base.metric b) p (R / 4),
        curvDerivNorm m (S.base.metric t) x ≤
          shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
            ((R / (4 * L)) * Real.sqrt K /
              (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * tau))) *
            K / Real.sqrt tau ^ m := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  dsimp only
  let tau := (b - a) / 4
  let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (b - a))
  have htau : 0 < tau := by dsimp only [tau]; linarith
  have hL : 0 < L := Real.exp_pos _
  have hquad (t : ℝ) (ht : t ∈ Icc a b)
      (y : M) (hy : y ∈ riemannianClosedBallOf (S.base.metric b) p R)
      (v : TangentSpace I y) :
      (S.base.metric b).inner y v v ≤ L ^ 2 * (S.base.metric t).inner y v v := by
    have hderiv : ∀ s ∈ Icc a b,
        ∃ d : ℝ, HasDerivWithinAt (fun s => (S.base.metric s).inner y v v) d (Icc a b) s ∧
          |d| ≤ (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * K)) *
            (S.base.metric s).inner y v v := by
      intro s hs
      refine ⟨_, metricPDE_Icc S hS hcarrier hregular s hs y v v, ?_⟩
      have hh := ricci_quadratic_form_bound_of_solution_curvature_bound S y v (hcurv s hs y hy)
      rw [Real.sqrt_sq hK.le] at hh
      rw [abs_mul, abs_neg, abs_two]
      nlinarith only [hh]
    have hb := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric y v hderiv
      (right_mem_Icc.mpr hab.le) ht
    have he : Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * K) * |b - t|) ≤ L ^ 2 := by
      dsimp only [L]
      rw [pow_two (Real.exp _), ← Real.exp_add, Real.exp_le_exp, abs_of_nonneg (by linarith [ht.2])]
      nlinarith only [mul_le_mul_of_nonneg_left ht.1
        (by positivity : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * K))]
    have hv : 0 ≤ (S.base.metric t).inner y v v := by
      by_cases hv : v = 0
      · simp only [hv, map_zero, le_refl]
      · exact ((S.base.metric t).pos y v hv).le
    exact hb.trans (mul_le_mul_of_nonneg_right he hv)
  intro m t ht x hx
  have ht' : t ∈ Icc a b := ⟨by linarith [ht.1], ht.2⟩
  have hsmall : 0 < R / (4 * L) := by positivity
  have hcontain : riemannianClosedBallOf (S.base.metric t) x (R / (4 * L)) ⊆
      riemannianClosedBallOf (S.base.metric b) p R := by
    let F := PartialDiffeomorph.refl (I := I) M
    have hcap := PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
      (S.base.metric b) (S.base.metric t) F (O := p) (x := x)
      (r := R / 3) (R := R) (A := R / (2 * L)) hL.le hcompact
      (fun _ _ => mem_univ _) (by
        intro y hy v
        change (S.base.metric b).inner y v v ≤ L ^ 2 *
          (S.base.metric t).inner y (mfderiv I I id y v) (mfderiv I I id y v)
        rw [mfderiv_id]
        exact hquad t ht' y hy v)
      (hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)))
      (by
        have heq : L * (R / (2 * L)) = R / 2 := by field_simp
        rw [heq]
        linarith)
    intro y hy
    have hy' : y ∈ riemannianBallOf (S.base.metric t) x (R / (2 * L)) := by
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (div_lt_div_of_pos_left hR (by positivity) (by linarith)))
    obtain ⟨z, hz, hzy⟩ := hcap hy'
    have hz' : z = y := hzy
    exact hz' ▸ hz
  have hcpt : IsCompact (riemannianClosedBallOf (S.base.metric t) x (R / (4 * L))) := by
    apply hcompact.of_isClosed_subset ?_ hcontain
    let g := S.base.metric t
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    change IsClosed {y : M | edist x y ≤ ENNReal.ofReal (R / (4 * L))}
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsub : Icc (t - tau) t ⊆ Icc a b := by
    intro s hs
    dsimp only [tau] at hs
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hreg : Ico (t - tau) t ⊆ D.regular := by
    intro s hs
    apply hregular
    dsimp only [tau] at hs
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hb := shi_curvDerivNorm_terminal_of_terminal_ball S hS
    (a := t - tau) (b := t) (K := K) (R := R / (4 * L))
    (by linarith) hK hsmall (hsub.trans hcarrier) hreg x hcpt
    (fun s hs y hy => hcurv s (hsub hs) y (hcontain hy)) m
  simpa only [show t - (t - tau) = tau by ring, tau, L] using hb

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem shi_curvDerivNorm_on_terminal_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K R : ℝ} (hab : a < b) (hK : 0 < K) (hR : 0 < R)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (p : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric b) p R))
    (hcurv : ∀ t ∈ Icc a b, ∀ y ∈ riemannianClosedBallOf (S.base.metric b) p R,
      curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) :
    let tau := (b - a) / 4
    let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (b - a))
    ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b,
      ∀ x ∈ riemannianClosedBallOf (S.base.metric b) p (R / 4),
        curvDerivNorm m (S.base.metric t) x ≤
          shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
            ((R / (4 * L)) * Real.sqrt K /
              (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * tau))) *
            K / Real.sqrt tau ^ m := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let f := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback f.symm
  have hU : IsSolutionOn U := hS.pullback S f.symm
  have hballs (r : ℝ) : riemannianClosedBallOf (U.base.metric b) p r =
      riemannianClosedBallOf (S.base.metric b) p r := by
    ext y
    change riemannianEDistOf (Diffeomorph.pullbackMetricCross (S.base.metric b) f.symm) p y
      ≤ ENNReal.ofReal r ↔ _
    rw [riemannianEDistOf_pullbackMetricCross]
    rfl
  have hnorm (m : ℕ) (t : ℝ) (x : M) :
      curvDerivNorm m (U.base.metric t) x = curvDerivNorm m (S.base.metric t) x :=
    Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross (S.base.metric t) f.symm m x
  have hbound : ∀ t ∈ Icc a b, ∀ y ∈ riemannianClosedBallOf (U.base.metric b) p R,
      curvDerivNormSq 0 (U.base.metric t) y ≤ K ^ 2 := by
    intro t ht y hy
    have hh : curvDerivNorm 0 (U.base.metric t) y ≤ K := by
      rw [hnorm]
      exact (Real.sqrt_le_iff.mpr ⟨hK.le, hcurv t ht y ((hballs R) ▸ hy)⟩)
    exact (Real.sqrt_le_iff.mp hh).2
  have hshi := shi_curvDerivNorm_on_terminal_ball_of_innerProductSpace U hU hab hK hR
    hcarrier hregular p ((hballs R).symm ▸ hcompact) hbound
  dsimp only at hshi ⊢
  intro m t ht x hx
  have hh := hshi m t ht x ((hballs (R / 4)).symm ▸ hx)
  rw [hnorm] at hh
  simpa only [finrank_euclideanSpace_fin] using hh

end DifferentialGeometry.PDE.RicciFlow
