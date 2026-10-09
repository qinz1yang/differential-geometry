import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TerminalScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarBoundAdditiveDistance
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

private theorem distance_drop_le_sqrt_of_interval_bound
    {a t b C : ℝ} (hat : a < t) (htb : t ≤ b) (hC : 0 ≤ C)
    (d : ℝ → ℝ)
    (hstep : ∀ u ∈ Icc t b, ∀ v ∈ Icc t b, u ≤ v →
      0 ≤ d u - d v ∧ d u - d v ≤ C / Real.sqrt (u - a) * (v - u)) :
    0 ≤ d t - d b ∧
      d t - d b ≤ 2 * C * (Real.sqrt (b - a) - Real.sqrt (t - a)) := by
  have hroot : 0 < Real.sqrt (t - a) := Real.sqrt_pos.mpr (sub_pos.mpr hat)
  have hLip : LipschitzOnWith ⟨C / Real.sqrt (t - a), div_nonneg hC hroot.le⟩ d (Icc t b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have hbound (u : ℝ) (hu : u ∈ Icc t b) (v : ℝ) (hv : v ∈ Icc t b) (huv : u ≤ v) :
        |d u - d v| ≤ C / Real.sqrt (t - a) * |u - v| := by
      have hh := hstep u hu v hv huv
      rw [abs_of_nonneg hh.1, abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
      exact hh.2.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hC hroot
          (Real.sqrt_le_sqrt (sub_le_sub_right hu.1 a))) (sub_nonneg.mpr huv))
    change |d u - d v| ≤ (C / Real.sqrt (t - a)) * |u - v|
    rcases le_total u v with huv | hvu
    · simpa only [Real.dist_eq, NNReal.coe_mk] using hbound u hu v hv huv
    · simpa only [Real.dist_eq, NNReal.coe_mk, abs_sub_comm] using hbound v hv u hu hvu
  let f := fun r => -d r
  let B := fun r => -d t + 2 * C * (Real.sqrt (r - a) - Real.sqrt (t - a))
  let B' := fun r => C / Real.sqrt (r - a)
  have hf : ContinuousOn f (Icc t b) := hLip.continuousOn.neg
  have hB : ContinuousOn B (Icc t b) := by fun_prop
  have hderiv (r : ℝ) (hr : r ∈ Ico t b) : HasDerivWithinAt B (B' r) (Ici r) r := by
    have hpos : 0 < r - a := sub_pos.mpr (hat.trans_le hr.1)
    have h := (((hasDerivAt_id r).sub_const a).sqrt hpos.ne').sub_const (Real.sqrt (t - a))
    have hd := (h.const_mul (2 * C)).const_add (-d t)
    change HasDerivWithinAt (fun r => -d t + 2 * C *
      (Real.sqrt (r - a) - Real.sqrt (t - a))) (C / Real.sqrt (r - a)) (Ici r) r
    convert! hd.hasDerivWithinAt using 1
    simp only [id_eq]
    ring
  have hbound : ∀ r ∈ Ico t b, ∀ z, B' r < z → ∃ᶠ q in 𝓝[>] r, slope f r q < z := by
    intro r hr z hz
    have hnear : ∀ᶠ q in 𝓝[>] r, q ∈ Ioc r b := Ioc_mem_nhdsGT hr.2
    apply Filter.Eventually.frequently
    filter_upwards [hnear] with q hq
    have hh := (hstep r ⟨hr.1, hr.2.le⟩ q ⟨hr.1.trans hq.1.le, hq.2⟩ hq.1.le).2
    have hslope : slope f r q ≤ B' r := by
      rw [slope_def_field]
      dsimp [f, B']
      apply (div_le_iff₀ (sub_pos.mpr hq.1)).mpr
      linarith
    exact hslope.trans_lt hz
  have hb := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (by dsimp [f, B]; simp) hB hderiv hbound (right_mem_Icc.mpr htb)
  refine ⟨(hstep t ⟨le_rfl, htb⟩ b ⟨htb, le_rfl⟩ htb).1, ?_⟩
  dsimp [f, B] at hb
  linarith


open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem ricciFlow_additive_distance_bound_of_finite_left_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) (hconnected : ConnectedSpace M)
    {a b : ℝ} (hcarrier : Ioc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ r ∈ Ioc a b, RiemannianMetricComplete (S.base.metric r))
    (hbound : ∀ c d : ℝ, Icc c d ⊆ Ioc a b →
      ∃ C : ℝ, ∀ r ∈ Icc c d, ∀ x : M,
        normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (hnonnegative : ∀ r ∈ Ioc a b, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (S.base.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone)
    {Q : ℝ} (hQ : 0 ≤ Q) (hterminal : ∀ x : M, S.scalar b x ≤ Q)
    {t : ℝ} (ht : t ∈ Ioc a b) (x y : M) :
    0 ≤ (riemannianEDistOf (S.base.metric t) x y).toReal -
      (riemannianEDistOf (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (S.base.metric t) x y).toReal -
      (riemannianEDistOf (S.base.metric b) x y).toReal ≤
      (20 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q) *
        (Real.sqrt (b - a) - Real.sqrt (t - a)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let D' := RealTimeInterval.openClosed a b b ⟨ht.1.trans_le ht.2, le_rfl⟩
  let T := S.timeRestrict D'
  have hT : IsSolutionOn T := isSolutionOn_timeRestrict hS hcarrier hregular
  have hscalar (r : ℝ) (hr : r ∈ Ioc a b) (z : M) :
      S.scalar r z ≤ (b - a) * Q / (r - a) := by
    apply hamilton_scalar_le_terminal_bound T hT
      (fun q hq => hcomplete q ⟨hq.1, hq.2.le⟩)
      (fun c d hcd => hbound c d (fun q hq =>
        ⟨(hcd hq).1, (hcd hq).2.le⟩))
      (fun q hq => hnonnegative q ⟨hq.1, hq.2.le⟩)
      hr.1 hr.2 (by exact ⟨ht.1.trans_le ht.2, le_rfl⟩) Subset.rfl z
    exact hterminal z
  let C := (10 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hstep : ∀ u ∈ Icc t b, ∀ v ∈ Icc t b, u ≤ v →
      0 ≤ (riemannianEDistOf (S.base.metric u) x y).toReal -
        (riemannianEDistOf (S.base.metric v) x y).toReal ∧
      (riemannianEDistOf (S.base.metric u) x y).toReal -
        (riemannianEDistOf (S.base.metric v) x y).toReal ≤
        C / Real.sqrt (u - a) * (v - u) := by
    intro u hu v hv huv
    have hau : a < u := ht.1.trans_le hu.1
    have hslab : Icc u v ⊆ Ioc a b := fun r hr =>
      ⟨hau.trans_le hr.1, hr.2.trans hv.2⟩
    have hconst : ∀ r ∈ Icc u v, ∀ z : M,
        S.scalar r z ≤ (b - a) * Q / (u - a) := by
      intro r hr z
      exact (hscalar r (hslab hr) z).trans
        (div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr (ht.1.le.trans ht.2)) hQ)
          (sub_pos.mpr hau) (sub_le_sub_right hr.1 a))
    have h := Perelman.KappaSolutions.ricciFlow_additive_distance_bound_of_scalar_upper S hS
      hdim hconnected huv
      (div_nonneg (mul_nonneg (sub_nonneg.mpr (ht.1.le.trans ht.2)) hQ)
        (sub_nonneg.mpr hau.le)) (hslab.trans hcarrier)
      (fun r hr => hregular ⟨hau.trans hr.1, hr.2.trans_le hv.2⟩)
      (fun r hr => hcomplete r (hslab hr))
      (fun r hr => hnonnegative r (hslab hr)) hconst x y
    have hfactor : (10 / 3 : ℝ) * Real.sqrt
        (((Module.finrank ℝ E : ℝ) - 1) * ((b - a) * Q / (u - a))) =
        C / Real.sqrt (u - a) := by
      have hd : 0 ≤ (Module.finrank ℝ E : ℝ) - 1 := by
        have hdim' : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
        linarith
      have hn : 0 ≤ ((Module.finrank ℝ E : ℝ) - 1) * ((b - a) * Q) :=
        mul_nonneg hd (mul_nonneg (sub_nonneg.mpr (ht.1.le.trans ht.2)) hQ)
      rw [← mul_div_assoc, Real.sqrt_div hn]
      dsimp [C]
      rw [← mul_assoc]
      ring
    rwa [hfactor] at h
  have h := distance_drop_le_sqrt_of_interval_bound ht.1 ht.2 hC
    (fun r => (riemannianEDistOf (S.base.metric r) x y).toReal) hstep
  have hconst : (20 / 3 : ℝ) *
      Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q) = 2 * C := by
    dsimp [C]
    ring
  rw [hconst]
  exact h

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem ricciFlow_additive_distance_bound_of_terminal_scalar
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) (hconnected : ConnectedSpace M)
    {a b : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ r ∈ Icc a b, RiemannianMetricComplete (S.base.metric r))
    (hbound : ∃ C : ℝ, ∀ r ∈ Icc a b, ∀ x : M,
      normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (hnonnegative : ∀ r ∈ Icc a b, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (S.base.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone)
    {Q : ℝ} (hQ : 0 ≤ Q) (hterminal : ∀ x : M, S.scalar b x ≤ Q)
    {t : ℝ} (ht : t ∈ Icc a b) (x y : M) :
    0 ≤ (riemannianEDistOf (S.base.metric t) x y).toReal -
      (riemannianEDistOf (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (S.base.metric t) x y).toReal -
      (riemannianEDistOf (S.base.metric b) x y).toReal ≤
      (20 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q) *
        (Real.sqrt (b - a) - Real.sqrt (t - a)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC⟩ := hbound
  let U : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hscalar (r : ℝ) (hr : r ∈ Icc a b) (z : M) : S.scalar r z ≤ U := by
    have hh := (le_abs_self (S.scalar r z)).trans
      (scalar_abs_le_rm (S.base.metric r) z)
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC r hr z))
      (sq_nonneg (Module.finrank ℝ E : ℝ)))
  have hstep (r s : ℝ) (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r ≤ s) :
      0 ≤ (riemannianEDistOf (S.base.metric r) x y).toReal -
        (riemannianEDistOf (S.base.metric s) x y).toReal ∧
      (riemannianEDistOf (S.base.metric r) x y).toReal -
        (riemannianEDistOf (S.base.metric s) x y).toReal ≤
        (10 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * U) * (s - r) := by
    have hsub : Icc r s ⊆ Icc a b := Icc_subset_Icc hr.1 hs.2
    exact Perelman.KappaSolutions.ricciFlow_additive_distance_bound_of_scalar_upper
      S hS hdim hconnected hrs hU (hsub.trans hcarrier)
      ((Ioo_subset_Ioo hr.1 hs.2).trans hregular)
      (fun q hq => hcomplete q (hsub hq))
      (fun q hq => hnonnegative q (hsub hq))
      (fun q hq => hscalar q (hsub hq)) x y
  have hinterior (r : ℝ) (hr : r ∈ Ioc a b) :
      0 ≤ (riemannianEDistOf (S.base.metric r) x y).toReal -
        (riemannianEDistOf (S.base.metric b) x y).toReal ∧
      (riemannianEDistOf (S.base.metric r) x y).toReal -
        (riemannianEDistOf (S.base.metric b) x y).toReal ≤
        (20 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q) *
          (Real.sqrt (b - a) - Real.sqrt (r - a)) :=
    ricciFlow_additive_distance_bound_of_finite_left_endpoint S hS hdim hconnected
      (Ioc_subset_Icc_self.trans hcarrier) hregular
      (fun r hr => hcomplete r ⟨hr.1.le, hr.2⟩)
      (fun c d hcd => ⟨C, fun r hr z => hC r ⟨(hcd hr).1.le, (hcd hr).2⟩ z⟩)
      (fun r hr => hnonnegative r ⟨hr.1.le, hr.2⟩) hQ hterminal hr x y
  rcases eq_or_lt_of_le ht.1 with hta | hat
  · subst t
    refine ⟨(hstep a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le).1, ?_⟩
    let upper : ℝ → ℝ := fun r =>
      (10 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * U) * (r - a) +
        (20 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * (b - a) * Q) *
          (Real.sqrt (b - a) - Real.sqrt (r - a))
    have hu : Continuous upper := by dsimp [upper]; fun_prop
    have hlimit : Tendsto upper (𝓝[>] a) (𝓝 (upper a)) :=
      hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hnear : ∀ᶠ r in 𝓝[>] a, r ∈ Ioc a b := Ioc_mem_nhdsGT hab
    have hmajor : ∀ᶠ r in 𝓝[>] a,
        (riemannianEDistOf (S.base.metric a) x y).toReal -
          (riemannianEDistOf (S.base.metric b) x y).toReal ≤ upper r := by
      filter_upwards [hnear] with r hr
      have hfirst := (hstep a r ⟨le_rfl, hab.le⟩ ⟨hr.1.le, hr.2⟩ hr.1.le).2
      have hsecond := (hinterior r hr).2
      dsimp [upper]
      linarith
    simpa only [upper, sub_self, mul_zero, Real.sqrt_zero, sub_zero, zero_add] using
      (ge_of_tendsto hlimit hmajor)
  · exact hinterior t ⟨hat, ht.2⟩

end DifferentialGeometry.PDE.RicciFlow

end
