import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.MovingSlope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Family.DistanceRegularity
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ricciFlow_additive_distance_bound_of_ricci_upper [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    (hconnected : ConnectedSpace M) {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ s ∈ Icc a b,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hRic : ∀ s ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      0 ≤ S.ricciAt s x (vec2 v v) ∧
        S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ E : ℝ) - 1) * K * (S.base.metric s).inner x v v)
    (x y : M) :
    0 ≤ (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
      (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
        (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ≤
      (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt K * (b - a) := by
  have hpreconnected : PreconnectedSpace M := hconnected.toPreconnectedSpace
  have hnezero : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hmanifoldOne : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  rcases eq_or_lt_of_le hab with rfl | hablt
  · constructor <;> simp
  have hd0 : 0 ≤ ((Module.finrank ℝ E : ℝ) - 1) := by
    have htwo : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    linarith
  have hinner_nonneg : ∀ (s : ℝ) (z : M) (v : TangentSpace I z),
      0 ≤ (S.base.metric s).inner z v v := fun s z v =>
    metric_inner_self_nonneg (S.base.metric s) z v
  have hric_eq : ∀ (s : ℝ) (z : M) (v : TangentSpace I z),
      S.ricciAt s z (vec2 v v) = ricciTensor (I := I) (S.base.metric s) z v v := by
    intro s z v
    simp [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor]
  have hpde := metricPDE_Icc (I := I) S hS hslab hregular
  have hanti : ∀ z : M, ∀ v : TangentSpace I z,
      AntitoneOn (fun t : ℝ => (S.base.metric t).inner z v v) (Icc a b) := by
    intro z v
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Icc a b)
      (f := fun t : ℝ => (S.base.metric t).inner z v v)
      (f' := fun t : ℝ => -2 * ricciTensor (I := I) (S.base.metric t) z v v)
      (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      exact (hpde t ht z v v).continuousWithinAt
    · intro t ht
      exact (hpde t (interior_subset ht) z v v).mono interior_subset
    · intro t ht
      have h := (hRic t (interior_subset ht) z v).1
      rw [hric_eq t z v] at h
      nlinarith [h]
  have hb_le_a :
      (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ≤
        (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal :=
    ENNReal.toReal_mono (riemannianEDistOf_ne_top (S.base.metric a) x y)
      (edistOf_mono (S.base.metric b) (S.base.metric a)
        (fun z v => hanti z v ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) x y)
  let F : ℝ → ℝ :=
    fun u => (riemannianEDistOf (I := I) (S.base.metric (b - u)) x y).toReal
  have hF_zero : F 0 = (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal := by
    simp [F]
  have hF_delta : F (b - a) =
      (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal := by
    simp [F]
  have hric_abs : ∀ r ∈ Icc a b, ∀ z : M, ∀ v : TangentSpace I z,
      |ricciTensor (I := I) (S.base.metric r) z v v| ≤
        (((Module.finrank ℝ E : ℝ) - 1) * K) * (S.base.metric r).inner z v v := by
    intro r hr z v
    have h := hRic r hr z v
    rw [← hric_eq r z v, abs_of_nonneg h.1]
    exact h.2
  have hcmp : ∀ s ∈ Icc 0 (b - a), ∀ t ∈ Icc 0 (b - a), ∀ p q : M,
      riemannianEDistOf (I := I) (S.base.metric (b - s)) p q ≤
        ENNReal.ofReal (Real.exp ((((Module.finrank ℝ E : ℝ) - 1) * K) * |s - t|)) *
          riemannianEDistOf (I := I) (S.base.metric (b - t)) p q := by
    intro s hs t ht p q
    have hsab : b - s ∈ Icc a b :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have htab : b - t ∈ Icc a b :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := (riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le (I := I)
      (fun u : ℝ => S.base.metric u) (fun q hq z v => hpde q hq z v v)
      hric_abs hsab htab p q).2
    have hsub : (b - s) - (b - t) = t - s := by ring
    rwa [hsub, abs_sub_comm t s] at h
  obtain ⟨L, hL⟩ :=
    exists_lipschitzOnWith_riemannianEDistOf_toReal_of_le_exp_mul_of_contMDiffOn
      (fun u : ℝ => S.base.metric (b - u)) hcmp (fun _ : ℝ => x) (fun _ : ℝ => y)
      contMDiffOn_const contMDiffOn_const
      (by simpa using riemannianEDistOf_ne_top (S.base.metric b) x y)
  have hF_ac : AbsolutelyContinuousOnInterval F 0 (b - a) := by
    have hLu : LipschitzOnWith L F (uIcc 0 (b - a)) := by
      rw [uIcc_of_le (sub_nonneg.mpr hab)]
      exact hL
    exact hLu.absolutelyContinuousOnInterval
  have hdini : ∀ δ > 0, ∀ t ∈ Ioo (0 : ℝ) (b - a), ∀ ε > 0,
      ∀ᶠ s in 𝓝[>] t,
        slope F t s ≤ (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) *
          Real.sqrt (K + δ) + ε := by
    intro δ hδ t ht ε hε
    have ht_ab : b - t ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have htreg : b - t ∈ D.regular := hregular ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hcomp : RiemannianMetricComplete (I := I) (S.base.metric (b - t)) :=
      hcomplete (b - t) ht_ab
    have hKd : 0 < K + δ := by linarith
    have hs_pos : 0 < Real.sqrt (K + δ) := Real.sqrt_pos.2 hKd
    let r : ℝ := 1 / Real.sqrt (K + δ)
    have hr : 0 < r := by
      dsimp only [r]
      positivity
    have hric_slope : ∀ z : M, ∀ w : TangentSpace I z,
        ((riemannianEDistOf (I := I) (S.base.metric (b - t)) x z < ENNReal.ofReal r ∨
          riemannianEDistOf (I := I) (S.base.metric (b - t)) y z < ENNReal.ofReal r) →
        (ricciTensor (I := I) (S.base.metric (b - t)) z w w ≤
          ((Module.finrank ℝ E : ℝ) - 1) * (K + δ) * (S.base.metric (b - t)).inner z w w)) :=
      fun z w _ => by
        have h := (hRic (b - t) ht_ab z w).2
        rw [hric_eq (b - t) z w] at h
        have hinner := hinner_nonneg (b - t) z w
        have hKδ : K ≤ K + δ := by linarith
        exact h.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKδ hd0) hinner)
    have hlong_eq : 2 * ((Module.finrank ℝ E : ℝ) - 1) *
        ((2 / 3 : ℝ) * (K + δ) * r + 1 / r) =
        (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) := by
      have hval : (2 / 3 : ℝ) * (K + δ) * r + 1 / r = (5 / 3 : ℝ) * Real.sqrt (K + δ) := by
        dsimp only [r]
        field_simp
        linarith [Real.sq_sqrt hKd.le]
      rw [hval]
      ring
    by_cases hlong : 2 * r ≤ F t
    · rcases exists_upper_support_riemannianEDistOf_of_two_mul_le (I := I) S hS htreg hcomp hr
          x y (by simpa only [F] using hlong) hric_slope with
        ⟨phi, dd, hcontact, hupper, hphi, hd⟩
      have hmove := eventually_slope_riemannianEDistOf_lt (I := I)
        (fun s : ℝ => S.base.metric (b - s)) (fun _ : ℝ => x) (fun _ : ℝ => y) phi
        hcontact hupper hphi.hasDerivWithinAt (vx := 0) (vy := 0)
        (fun eps heps => by
          filter_upwards with s
          rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_div]
          simpa using heps)
        (fun eps heps => by
          filter_upwards with s
          rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_div]
          simpa using heps)
      filter_upwards [hmove (ε / 2) (by linarith)] with s hs
      have hstep : dd + 0 + 0 + ε / 2 ≤
          (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) + ε := by
        linarith [hlong_eq, hd]
      exact (le_of_lt hs).trans hstep
    · have hshort : F t < 2 * r := not_le.mp hlong
      have hval : (K + δ) * r = Real.sqrt (K + δ) := by
        dsimp only [r]
        field_simp
        linarith [Real.sq_sqrt hKd.le]
      rcases exists_upper_support_riemannianEDistOf_of_lt_two_mul (I := I) S hS htreg hcomp
          hKd.le hr x y (by simpa only [F] using hshort) hric_slope with
        ⟨phi, dd, hcontact, hupper, hphi, hd⟩
      have hmove := eventually_slope_riemannianEDistOf_lt (I := I)
        (fun s : ℝ => S.base.metric (b - s)) (fun _ : ℝ => x) (fun _ : ℝ => y) phi
        hcontact hupper hphi.hasDerivWithinAt (vx := 0) (vy := 0)
        (fun eps heps => by
          filter_upwards with s
          rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_div]
          simpa using heps)
        (fun eps heps => by
          filter_upwards with s
          rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_div]
          simpa using heps)
      filter_upwards [hmove (ε / 2) (by linarith)] with s hs
      have hstep : dd + 0 + 0 + ε / 2 ≤
          (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) + ε := by
        nlinarith [hval, hd, mul_nonneg hd0 (Real.sqrt_nonneg (K + δ))]
      exact (le_of_lt hs).trans hstep
  have hbound : ∀ δ > 0, F (b - a) - F 0 ≤
      (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) * (b - a) := by
    intro δ hδ
    have hg : IntervalIntegrable
        (fun _ : ℝ => (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ))
        MeasureTheory.volume 0 (b - a) := intervalIntegrable_const
    have h := AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le
      (f := F)
      (g := fun _ : ℝ => (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ))
      (a := 0) (b := b - a) (sub_nonneg.mpr hab) hF_ac hg (hdini δ hδ)
    have hint : ∫ t in (0 : ℝ)..(b - a),
        (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) =
        (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt (K + δ) * (b - a) := by
      rw [intervalIntegral.integral_const]
      ring
    rwa [hint] at h
  have hmain : F (b - a) - F 0 ≤
      (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt K * (b - a) := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    let m : ℝ := (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * (b - a)
    have hm : 0 < m := by
      have hdpos : 0 < ((Module.finrank ℝ E : ℝ) - 1) := by
        have htwo : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
        linarith
      have hbpos : 0 < b - a := sub_pos.mpr hablt
      dsimp only [m]
      positivity
    have hεpos : 0 < (δ / m) ^ 2 := by positivity
    have hbd := hbound ((δ / m) ^ 2) hεpos
    have hsqrt : Real.sqrt ((δ / m) ^ 2) = δ / m :=
      Real.sqrt_sq (div_nonneg hδ.le hm.le)
    have hsub : Real.sqrt (K + (δ / m) ^ 2) ≤ Real.sqrt K + Real.sqrt ((δ / m) ^ 2) := by
      have hsq : Real.sqrt ((Real.sqrt K + Real.sqrt ((δ / m) ^ 2)) ^ 2) =
          Real.sqrt K + Real.sqrt ((δ / m) ^ 2) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg K) (Real.sqrt_nonneg _))
      rw [← hsq]
      refine Real.sqrt_le_sqrt ?_
      nlinarith [Real.sq_sqrt hK, Real.sq_sqrt (le_of_lt hεpos), Real.sqrt_nonneg K,
        Real.sqrt_nonneg ((δ / m) ^ 2)]
    calc F (b - a) - F 0
        ≤ (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) *
            Real.sqrt (K + (δ / m) ^ 2) * (b - a) := hbd
      _ = m * Real.sqrt (K + (δ / m) ^ 2) := by dsimp only [m]; ring
      _ ≤ m * (Real.sqrt K + Real.sqrt ((δ / m) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsub hm.le
      _ = m * Real.sqrt K + δ := by
          rw [hsqrt]
          field_simp
      _ = (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt K * (b - a) + δ := by
          dsimp only [m]; ring
  refine ⟨by linarith, ?_⟩
  calc (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
        (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal
      = F (b - a) - F 0 := by rw [← hF_delta, ← hF_zero]
    _ ≤ (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt K * (b - a) := hmain

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
