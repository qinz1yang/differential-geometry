import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistTime_S50
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistBall_S50
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder

set_option autoImplicit false

/-!
# CH12-S50 / P5: `hpersist_S50` (the S38 frozen shape, verbatim)
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

theorem hpersist_S50 : ∀ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (a ε0 : ℝ) (ha : 0 < a),
      0 < ε0 → Q.MetricSmoothUpTo G (Icc a (a + ε0)) → ∀ w : ℝ, 0 < w →
      ∀ (p : Q.Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p r →
        ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (t : ℝ) (ht : a < t), t ≤ a + ε1 →
          ∃ (p' : Q.Carrier) (ρ : ℝ), 0 < ρ ∧
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' =
              ENNReal.ofReal ρ ∧
            ENNReal.ofReal (w / 2 * ρ ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' ρ := by
  intro Q G a ε0 ha hε0 hG w hw p r hr hcr hvol
  let : MeasurableSpace Q.Carrier := borel _
  have : BorelSpace Q.Carrier := ⟨rfl⟩
  set g0 := scaleMetric a⁻¹ (inv_pos.mpr ha) (G a) with hg0
  have hg0' : normFamily_S50 Q G a = g0 := normFamily_S50_of_pos Q G ha
  have hwr : 0 < w * r ^ 3 := mul_pos hw (pow_pos hr 3)
  -- Step 1: a ball slightly smaller than r with ≥ 9/10 of the volume
  have hm : ENNReal.ofReal (9 / 10 * (w * r ^ 3)) <
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure ThreeModel Q.Carrier g0
        (riemannianBallOf g0 p r) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hwr).2 (by linarith)) hvol
  obtain ⟨l, hl0, hl1, hlv⟩ := exists_ball_measure_S50 g0 p hr _ hm
  set mu := (1 + l) / 2 with hmu
  set r1 := (1 + mu) / 2 with hr1
  have hlm : l < mu := by rw [hmu]; linarith
  have hmr1 : mu < r1 := by rw [hr1]; linarith [hlm]
  have hr11 : r1 < 1 := by rw [hr1, hmu]; linarith
  have hmu0 : 0 < mu := hl0.trans hlm
  have hr10 : 0 < r1 := hmu0.trans hmr1
  -- Step 2: curvature data of the base metric
  obtain ⟨K0, hK0, hRm⟩ := exists_riemann_bound_S50 g0 p
  obtain ⟨q, hqb, hqns⟩ := cr_not_prop_S50 g0 p hr hcr (r2 := 21 / 20 * r) (by linarith)
  obtain ⟨epsq, hepsq0, hepsq1, hepsq⟩ := exists_eps_not_sectionalBoundedBelow_S50 g0 q
    (s := ((21 / 20 * r) ^ 2)⁻¹) (by positivity) hqns
  -- Step 3: all smallness requirements are strict inequalities at e = 0
  have hev : ∀ᶠ e : ℝ in 𝓝 0,
      ((((r1 * r) ^ 2)⁻¹ + e * (360 + K0)) / (1 - e) ^ 2 < ((mu * r) ^ 2)⁻¹) ∧
      (Real.sqrt (1 - e)⁻¹ * (mu * r) < r1 * r) ∧
      (Real.sqrt (1 + e) * (l * r) < mu * r) ∧
      (Real.sqrt (1 + e) * (21 / 20 * r) < (21 / 20) ^ 2 * r) ∧
      (Real.sqrt (((1 - e)⁻¹) ^ 3) < 9 / 8) := by
    refine ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const ?_ |>.and ?_
    · norm_num
      rw [inv_lt_inv₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hmu0 hr, mul_pos hr10 hr, mul_pos (sub_pos.2 hmr1) hr]
    refine ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const ?_ |>.and ?_
    · norm_num; nlinarith [mul_pos (sub_pos.2 hmr1) hr]
    refine ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const ?_ |>.and ?_
    · norm_num; nlinarith [mul_pos (sub_pos.2 hlm) hr]
    refine ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const ?_ |>.and ?_
    · norm_num; nlinarith
    refine ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const ?_
    norm_num
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp hev
  set e := min (δ / 2) (min epsq (1 / 2)) with he
  have he0 : 0 < e := lt_min (half_pos hδ) (lt_min hepsq0 (by norm_num))
  have he1 : e ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : e ≤ epsq := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨C1, C2, C3, C4, C5⟩ := hall (y := e) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos he0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ))
  obtain ⟨ε1, hε1, hε1le, hsm⟩ := exists_small_derivNorm_S50 Q G ha hε0 hG he0
  refine ⟨ε1, hε1, fun t ht hta => ?_⟩
  set gt := scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t) with hgt
  have hs : ∀ (x : Q.Carrier) (k : ℕ), k ≤ 2 → metricDerivNorm k gt g0 g0 x ≤ e := by
    intro x k hk
    have := hsm t ht hta x k hk
    rwa [normFamily_S50_of_pos Q G (ha.trans ht), hg0'] at this
  have h1e : 0 < 1 - e := by linarith
  have hup : ∀ (x : Q.Carrier) (v : TangentSpace ThreeModel x),
      gt.inner x v v ≤ (1 + e) * g0.inner x v v := fun x v =>
    (inner_bounds_of_metricDerivNorm_le g0 gt x (hs x 0 (by norm_num)) v).2
  have hdn : ∀ (x : Q.Carrier) (v : TangentSpace ThreeModel x),
      g0.inner x v v ≤ (1 - e)⁻¹ * gt.inner x v v := fun x v => by
    have := (inner_bounds_of_metricDerivNorm_le g0 gt x (hs x 0 (by norm_num)) v).1
    rw [← div_eq_inv_mul, le_div_iff₀ h1e]
    linarith
  have hc1 : 0 < 1 + e := by linarith
  have hc2 : 0 < (1 - e)⁻¹ := inv_pos.2 h1e
  have hR2 : 0 < mu * r := mul_pos hmu0 hr
  have hR1 : 0 < r1 * r := mul_pos hr10 hr
  -- lower bound for the curvature radius of gt at p
  have hprop2 : ∀ q' ∈ riemannianBallOf gt p (mu * r),
      SectionalBoundedBelowAt gt q' (-((mu * r) ^ 2)⁻¹) := by
    intro q' hq'
    have hsub : q' ∈ riemannianBallOf g0 p (r1 * r) :=
      riemannianBallOf_mono_S50 g0 p C2.le
        (riemannianBallOf_subset_of_inner_le_S50 gt g0 hc2 hdn p (mu * r) hq')
    have hsb0 := cr_prop_of_lt_S50 g0 p hcr hR1 (by nlinarith) q' hsub
    have hsb := sectionalBoundedBelow_transfer_S50 gt g0 q' (by linarith) (a := ((r1 * r) ^ 2)⁻¹)
      (K := K0) (by positivity) hK0 (fun k hk => hs q' k hk) hsb0 (hRm q')
    exact sb_mono_S50 gt q' (neg_le_neg C1.le) hsb
  have hlow := cr_lower_S50 gt p hR2 hprop2
  -- upper bound
  have hupper : curvatureRadius gt p ≤ ENNReal.ofReal (Real.sqrt (1 + e) * (21 / 20 * r)) := by
    refine cr_upper_S50 gt p fun R hR hpR => ?_
    by_contra hlt
    push Not at hlt
    have h1 : 21 / 20 * r ≤ Real.sqrt (1 + e) * (21 / 20 * r) := by
      have : 1 ≤ Real.sqrt (1 + e) := Real.one_le_sqrt.2 (by linarith)
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 21 / 20) hr]
    have hqR := hpR q (riemannianBallOf_mono_S50 gt p hlt.le
      (riemannianBallOf_subset_of_inner_le_S50 g0 gt hc1 hup p _ hqb))
    refine hepsq gt (fun k hk => (hs q k hk).trans heq) ?_
    refine sb_mono_S50 gt q ?_ hqR
    exact neg_le_neg (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (h1.trans hlt.le) 2))
  have hne : curvatureRadius gt p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  set ρ := (curvatureRadius gt p).toReal with hρ
  have hcrt : curvatureRadius gt p = ENNReal.ofReal ρ := (ENNReal.ofReal_toReal hne).symm
  have hρlo : mu * r ≤ ρ := by
    have := hlow; rw [hcrt] at this
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 this
  have hρhi : ρ ≤ Real.sqrt (1 + e) * (21 / 20 * r) := by
    have := hupper; rw [hcrt] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hρ0 : 0 < ρ := hR2.trans_le hρlo
  refine ⟨p, ρ, hρ0, hcrt, ?_⟩
  -- volume
  have hSsub : riemannianBallOf g0 p (l * r) ⊆ riemannianBallOf gt p ρ :=
    fun y hy => riemannianBallOf_mono_S50 gt p hρlo
      (riemannianBallOf_mono_S50 gt p C3.le
        (riemannianBallOf_subset_of_inner_le_S50 g0 gt hc1 hup p _ hy))
  have hSmeas : MeasurableSet (riemannianBallOf g0 p (l * r)) :=
    (isOpen_lt (continuous_riemannianEDist g0 p) continuous_const).measurableSet
  have hv := riemannianVolumeMeasure_le_on gt g0 hSmeas hc2 (fun x _ v => hdn x v)
  have hfr : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hfr] at hv
  have hc0 : 0 < Real.sqrt (((1 - e)⁻¹) ^ 3) := Real.sqrt_pos.2 (by positivity)
  have hmain : ENNReal.ofReal (Real.sqrt (((1 - e)⁻¹) ^ 3)) *
      ENNReal.ofReal (w / 2 * ρ ^ 3) ≤ ENNReal.ofReal (Real.sqrt (((1 - e)⁻¹) ^ 3)) *
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure ThreeModel Q.Carrier gt
        (riemannianBallOf gt p ρ) := by
    rw [← ENNReal.ofReal_mul hc0.le]
    refine le_trans ?_ (hv.trans (mul_le_mul' le_rfl (measure_mono hSsub)))
    refine le_trans ?_ hlv.le
    refine ENNReal.ofReal_le_ofReal ?_
    have hρ' : ρ ≤ (21 / 20) ^ 2 * r := hρhi.trans C4.le
    have hρ3 : ρ ^ 3 ≤ ((21 / 20) ^ 2 * r) ^ 3 := pow_le_pow_left₀ hρ0.le hρ' 3
    have h4 : w / 2 * ρ ^ 3 ≤ w / 2 * ((21 / 20) ^ 2 * r) ^ 3 :=
      mul_le_mul_of_nonneg_left hρ3 (by positivity)
    have h5 : Real.sqrt (((1 - e)⁻¹) ^ 3) * (w / 2 * ρ ^ 3) ≤ 9 / 8 * (w / 2 * ((21 / 20) ^ 2 * r) ^ 3) :=
      mul_le_mul C5.le h4 (by positivity) (by norm_num)
    nlinarith
  have h0 : ENNReal.ofReal (Real.sqrt (((1 - e)⁻¹) ^ 3)) ≠ 0 := by simpa using hc0
  exact (ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top).1 hmain

end GC.LongTime.Ch12
