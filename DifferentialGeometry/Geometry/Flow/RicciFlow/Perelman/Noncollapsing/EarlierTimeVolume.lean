import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.VolumeDistortion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Comparison.LocalDistanceComparison

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem FlowMetricBall.volume_ge_of_isKappaNoncollapsed_at_earlier_time
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    (hreg : interior D.carrier ⊆ D.regular) {κ δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {T : D.FlowTime} (B : FlowMetricBall S T) (hB : B.IsParabolicallyRmControlled)
    (hlt : ∀ (t : D.FlowTime) (B' : FlowMetricBall S t),
      (t : ℝ) = (T : ℝ) - B.radius ^ 2 * δ ^ 2 → B'.center = B.center →
      B'.radius ≤ B.radius → B'.IsParabolicallyRmControlled → B'.IsKappaNoncollapsed κ) :
    0 < κ ∧ ENNReal.ofReal (κ * (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2 *
        (B.radius ^ 2 * δ ^ 2))) * (B.radius * (1 - δ))) ^ Module.finrank ℝ E *
        Real.exp (-((Module.finrank ℝ E : ℝ) ^ 3 / B.radius ^ 2 * (B.radius ^ 2 * δ ^ 2)))) ≤
      B.volume := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  set t₀ : ℝ := (T : ℝ)
  set r : ℝ := B.radius
  set x : M := B.center
  set n : ℕ := Module.finrank ℝ E
  have hr : 0 < r := B.radius_pos
  obtain ⟨hwin, hcurv⟩ := hB
  have hslabreg : Ioo (t₀ - r ^ 2) t₀ ⊆ D.regular := fun u hu =>
    hreg (interior_mono hwin (by rw [interior_Icc]; exact hu))
  set V : Set M := riemannianBallOf (S.base.metric t₀) x r
  have hVmeas : MeasurableSet V :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric t₀) x)
      continuous_const).measurableSet
  have htI : t₀ ∈ Icc (t₀ - r ^ 2) t₀ := ⟨by nlinarith, le_rfl⟩
  set s : ℝ := t₀ - r ^ 2 * δ ^ 2 with hsdef
  have hrδ : 0 < r ^ 2 * δ ^ 2 := by positivity
  have hδ1 : δ ^ 2 ≤ 1 := by nlinarith
  have hsI : s ∈ Icc (t₀ - r ^ 2) t₀ :=
    ⟨by nlinarith [mul_le_of_le_one_right (sq_nonneg r) hδ1], by linarith⟩
  have hsT : s < t₀ := by linarith
  have habs1 : |t₀ - s| = r ^ 2 * δ ^ 2 := by
    rw [hsdef, sub_sub_cancel, abs_of_pos hrδ]
  have habs2 : |s - t₀| = r ^ 2 * δ ^ 2 := by rw [abs_sub_comm]; exact habs1
  set a : ℝ := (n : ℝ) ^ 2 / r ^ 2 * (r ^ 2 * δ ^ 2)
  set b : ℝ := (n : ℝ) ^ 3 / r ^ 2 * (r ^ 2 * δ ^ 2)
  set c : ℝ := Real.exp (-a) with hcdef
  set R : ℝ := r * (1 - δ)
  set r' : ℝ := c * R
  have ha : 0 ≤ a := by positivity
  have hc : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hR : 0 < R := mul_pos hr (by linarith)
  have hRr : R < r := by nlinarith
  have hr' : 0 < r' := mul_pos hc hR
  have hr'R : r' ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hc1 hR.le]
  have hsub : riemannianBallOf (S.base.metric s) x r' ⊆ V := by
    intro y hy
    have hbound : ∀ z : M, riemannianEDistOf (S.base.metric t₀) x z ≤ ENNReal.ofReal R →
        ∀ v : TangentSpace I z,
          c ^ 2 * (S.base.metric t₀).inner z v v ≤ (S.base.metric s).inner z v v := by
      intro z hz v
      have hzV : z ∈ V := lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)
      have hcmp := inner_le_exp_mul_inner_of_rmNormSq_le hS hr hwin hslabreg
        (fun u hu => hcurv u hu z hzV) htI hsI v
      rw [habs1] at hcmp
      have hc2 : c ^ 2 * Real.exp (2 * a) = 1 := by
        rw [hcdef, sq, ← Real.exp_add, ← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      calc
        c ^ 2 * (S.base.metric t₀).inner z v v ≤
            c ^ 2 * (Real.exp (2 * a) * (S.base.metric s).inner z v v) :=
          mul_le_mul_of_nonneg_left hcmp (by positivity)
        _ = (S.base.metric s).inner z v v := by rw [← mul_assoc, hc2, one_mul]
    have hdist := Geometry.Riemannian.riemannianEDistOf_le_of_metric_lower_on_ball
      (S.base.metric t₀) (S.base.metric s) x y hc hbound hy
    have hlt' : (riemannianEDistOf (S.base.metric s) x y).toReal < c * R :=
      ENNReal.toReal_lt_of_lt_ofReal hy
    have hdiv : (riemannianEDistOf (S.base.metric s) x y).toReal / c < r := by
      rw [div_lt_iff₀ hc]
      nlinarith
    exact lt_of_le_of_lt hdist ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hdiv)
  let s' : D.FlowTime := ⟨s, hwin hsI⟩
  let B' : FlowMetricBall S s' := ⟨x, r', hr'⟩
  have hwin' : Icc (s - r' ^ 2) s ⊆ Icc (t₀ - r ^ 2) t₀ := by
    intro u hu
    refine ⟨?_, hu.2.trans hsI.2⟩
    have h1 : r' ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr'.le hr'R 2
    have h2 : 0 ≤ r ^ 2 * (δ * (1 - δ)) :=
      mul_nonneg (sq_nonneg r) (mul_nonneg hδ.le (by linarith))
    nlinarith [hu.1]
  have hB' : B'.IsParabolicallyRmControlled := by
    refine ⟨hwin'.trans hwin, fun u hu y hy => ?_⟩
    have h1 := hcurv u (hwin' hu) y (hsub hy)
    have hr4 : r' ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hr'.le (hr'R.trans hRr.le) 4
    change r' ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1
    rcases le_or_gt (FlowMetricBall.rmNormSq S u y) 0 with h | h
    · nlinarith [pow_pos hr' 4]
    · nlinarith [mul_le_mul_of_nonneg_right hr4 h.le]
  obtain ⟨hκ, hvol⟩ := hlt s' B' rfl rfl (hr'R.trans hRr.le) hB'
  have hvolcmp := riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le hS hr hwin hslabreg hVmeas
    (fun u hu y hy => hcurv u hu y hy) (subset_refl V) hsI htI
  rw [habs2] at hvolcmp
  have hmono : B'.volume ≤ riemannianVolumeMeasure I M (S.base.metric s) V :=
    measure_mono hsub
  have hchain : ENNReal.ofReal κ * ENNReal.ofReal r' ^ n ≤
      ENNReal.ofReal (Real.exp b) * B.volume :=
    hvol.trans (hmono.trans hvolcmp)
  refine ⟨hκ, ?_⟩
  calc
    ENNReal.ofReal (κ * r' ^ n * Real.exp (-b)) =
        ENNReal.ofReal (Real.exp (-b)) * (ENNReal.ofReal κ * ENNReal.ofReal r' ^ n) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hκ.le,
        ENNReal.ofReal_pow hr'.le, mul_comm]
    _ ≤ ENNReal.ofReal (Real.exp (-b)) * (ENNReal.ofReal (Real.exp b) * B.volume) :=
      mul_le_mul' le_rfl hchain
    _ = B.volume := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

end DifferentialGeometry.PDE.RicciFlow.Perelman
