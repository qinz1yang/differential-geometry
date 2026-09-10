import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Sequences

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

private theorem two_hinge_inner_lt
    {a b d c z eta : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (heta : 0 < eta) (heta1 : eta ≤ 1 / 2) (hfar : 2 * a < b * eta)
    (hc : 1 - eta < c) (htri : d ≤ a + b)
    (hfirst : d ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * c)
    (hsecond : b ^ 2 ≤ a ^ 2 + d ^ 2 - 2 * a * d * z) :
    z < -1 + 2 * eta := by
  have hcancel : 0 ≤ a - b * c - d * z := by
    by_contra h
    have hneg := mul_neg_of_pos_of_neg ha (lt_of_not_ge h)
    nlinarith only [hfirst, hsecond, hneg]
  by_contra hz
  have hdz := mul_le_mul_of_nonneg_left (le_of_not_gt hz) hd.le
  have hdterm := mul_le_mul_of_nonneg_right htri (by linarith : 0 ≤ 1 - 2 * eta)
  have hbc := mul_lt_mul_of_pos_left hc hb
  have hpos := mul_nonneg ha.le heta.le
  nlinarith only [hcancel, hdz, hdterm, hbc, hfar, hpos]

private theorem growth_of_upper_support {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hsupp : ∀ t ∈ Ioc a b, ∃ φ : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt φ d t ∧ φ t = f t ∧ (∀ᶠ s in 𝓝 t, f s ≤ φ s) ∧ c ≤ d) :
    c * (b - a) ≤ f b - f a := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  by_contra h
  have hquot : (f b - f a) / (b - a) < c :=
    (div_lt_iff₀ (sub_pos.mpr hab)).mpr (lt_of_not_ge h)
  obtain ⟨k, hk, hkc⟩ := exists_between hquot
  let F : ℝ → ℝ := fun t => f t - k * t
  have hFab : F b < F a := by
    have hh := (div_lt_iff₀ (sub_pos.mpr hab)).mp hk
    dsimp only [F]
    nlinarith
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le)
    (hf.sub (continuousOn_const.mul continuousOn_id) : ContinuousOn F (Icc a b))
  have ham : a < m := by
    by_contra hma
    have hma : m = a := le_antisymm (le_of_not_gt hma) hm.1
    have hh := hmin (right_mem_Icc.mpr hab.le)
    rw [hma] at hh
    exact (not_lt_of_ge hh) hFab
  obtain ⟨φ, d, hφ, hcontact, hupper, hcd⟩ := hsupp m ⟨ham, hm.2⟩
  let ψ : ℝ → ℝ := fun s => φ s - k * s
  have hψ : HasDerivAt ψ (d - k) m := by
    convert! hφ.sub ((hasDerivAt_id m).const_mul k) using 1
    simp only [mul_one]
  have hsl : ∀ᶠ s in 𝓝[<] m, 0 < slope ψ m s :=
    (hψ.tendsto_slope.mono_left (nhdsLT_le_nhdsNE m)).eventually
      (lt_mem_nhds (by linarith : 0 < d - k))
  have hfalse : ∀ᶠ s in 𝓝[<] m, False := by
    filter_upwards [hsl, Ioo_mem_nhdsLT ham, nhdsWithin_le_nhds hupper] with s hs hsm hu
    rw [slope_def_field] at hs
    have hlt := (lt_div_iff_of_neg (sub_neg.mpr hsm.2)).mp hs
    have hms := hmin (show s ∈ Icc a b from ⟨hsm.1.le, hsm.2.le.trans hm.2⟩)
    change f m - k * m ≤ f s - k * s at hms
    dsimp only [ψ, F] at hlt hms
    rw [hcontact] at hlt
    nlinarith
  exact hfalse.exists.elim (fun _ h => h)

private theorem escape_of_growth {f : ℝ → ℝ} {R c : ℝ}
    (hf : Continuous f) (hstart : R < f 0) (hc : 0 ≤ c)
    (hg : ∀ a b : ℝ, a ≤ b → (∀ t ∈ Ioc a b, R ≤ f t) →
      c * (b - a) ≤ f b - f a) :
    ∀ t : ℝ, 0 ≤ t → R < f t ∧ c * t ≤ f t - f 0 := by
  have hstay (t : ℝ) (ht : 0 ≤ t) : R < f t := by
    by_contra h
    have hft : f t ≤ R := le_of_not_gt h
    let A : Set ℝ := Icc 0 t ∩ {s | f s = R}
    have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
    have hAne : A.Nonempty := by
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' ht hf.continuousOn ⟨hft, hstart.le⟩
      exact ⟨s, hs, hfs⟩
    obtain ⟨m, hm, hleast⟩ := hAc.exists_isLeast hAne
    have hm0 : 0 ≤ m := hm.1.1
    have hmR : f m = R := hm.2
    have hfar : ∀ s ∈ Ioc 0 m, R ≤ f s := by
      intro s hs
      by_contra hRs
      have hsR : f s < R := lt_of_not_ge hRs
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hs.1.le hf.continuousOn ⟨hsR.le, hstart.le⟩
      have hzs : z < s := lt_of_le_of_ne hz.2 (by intro hzs; rw [hzs] at hfz; linarith)
      have hmz := hleast (show z ∈ A from ⟨⟨hz.1, hz.2.trans (hs.2.trans hm.1.2)⟩, hfz⟩)
      linarith [hs.2]
    have hh := hg 0 m hm0 hfar
    rw [sub_zero, hmR] at hh
    have := mul_nonneg hc hm0
    linarith
  intro t ht
  refine ⟨hstay t ht, ?_⟩
  simpa only [sub_zero] using hg 0 t ht (fun s hs => (hstay s hs.1.le).le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem soul_riemannian_toReal (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] in
theorem soul_unit_minimizing_initial
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hd : 0 < dist p q) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm p u (dist p q) = q := by
  have hfin : riemannianEDist I p q ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q hfin
  rw [soul_riemannian_toReal (I := I)] at hlen
  let d : ℝ := dist p q
  let u : TangentSpace I p := d⁻¹ • v
  have hsq : g.inner p v v = d ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hlen]
  have hu : g.inner p u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g p d⁻¹ v, hsq, ← mul_pow,
      inv_mul_cancel₀ hd.ne', one_pow]
  have hsmul : d • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  refine ⟨u, hu, ?_⟩
  calc
    _ = expMapIntrinsic (I := I) g hEnorm p (d • u) := by
      rw [expMapIntrinsic_def]
      exact (intrinsicGeodesic_smul (I := I) g hEnorm p u d).symm
    _ = q := by rw [hsmul, hv]

private theorem directions_close_of_remote_hinge
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p q r : M) (U V : TangentSpace I p)
    (hU : g.inner p U U = 1) (hV : g.inner p V V = 1)
    (hUq : intrinsicGeodesic (I := I) g hEnorm p U (dist p q) = q)
    (hVr : intrinsicGeodesic (I := I) g hEnorm p V (dist p r) = r)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1 / 2)
    (ha : 0 < dist p q) (hfar : 2 * dist p q < dist p r * eta)
    (hclose : 1 - eta < g.inner p U V)
    (u v : TangentSpace I q) (hu : g.inner q u u = 1) (hv : g.inner q v v = 1)
    (hup : intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p)
    (hvp : intrinsicGeodesic (I := I) g hEnorm q v (dist p q) = p) :
    g.inner q (u - v) (u - v) < 16 * eta := by
  have hb : 0 < dist p r := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) heta.le
    linarith
  have hab : dist p q < dist p r := by
    have := mul_le_mul_of_nonneg_left heta1 hb.le
    linarith
  have hqr : q ≠ r := by
    intro h
    subst r
    exact (lt_irrefl _ hab)
  have hd : 0 < dist q r := dist_pos.mpr hqr
  obtain ⟨w, hw, hwr⟩ := soul_unit_minimizing_initial (I := I) g hEnorm q r hd
  have hminU : (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p U (dist p q))).toReal = dist p q := by
    rw [hUq, soul_riemannian_toReal (I := I)]
  have hfirst := complete_hinge_sq (I := I) g hEnorm hsec p U V
    (dist p q) (dist p r) ha hb hU hV hminU
  rw [hUq, hVr, soul_riemannian_toReal (I := I)] at hfirst
  have htri : dist q r ≤ dist p q + dist p r := by
    simpa only [dist_comm q p] using dist_triangle q p r
  have hinner (z : TangentSpace I q) (hz : g.inner q z z = 1)
      (hzp : intrinsicGeodesic (I := I) g hEnorm q z (dist p q) = p) :
      g.inner q z w < -1 + 2 * eta := by
    have hminz : (riemannianEDist I q
        (intrinsicGeodesic (I := I) g hEnorm q z (dist p q))).toReal = dist p q := by
      rw [hzp, soul_riemannian_toReal (I := I), dist_comm]
    have hsecond := complete_hinge_sq (I := I) g hEnorm hsec q z w
      (dist p q) (dist q r) ha hd hz hw hminz
    rw [hzp, hwr, soul_riemannian_toReal (I := I)] at hsecond
    exact two_hinge_inner_lt ha hb hd heta heta1 hfar hclose htri hfirst hsecond
  have huw := hinner u hu hup
  have hvw := hinner v hv hvp
  have hpos := gInner_self_nonneg (I := I) g q (u + v + (2 : ℝ) • w)
  simp only [map_add, map_smul, add_apply,
    _root_.smul_apply, smul_eq_mul, hu, hv, hw,
    g.symm q v u, g.symm q w u, g.symm q w v] at hpos
  rw [ContinuousLinearMap.map_sub₂, map_sub, map_sub, hu, hv, g.symm q v u]
  nlinarith only [hpos, huw, hvw]

theorem minimizing_directions_close_at_infinity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (eps : ℝ) (heps : 0 < eps) :
    ∃ R : ℝ, 0 < R ∧ ∀ q : M, R < dist p q →
      ∀ u v : TangentSpace I q,
        g.inner q u u = 1 → g.inner q v v = 1 →
        intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p →
        intrinsicGeodesic (I := I) g hEnorm q v (dist p q) = p →
        g.inner q (u - v) (u - v) < eps := by
  classical
  by_contra h
  push Not at h
  choose q hq u v hu hv hup hvp hbad using
    fun n : ℕ => h ((n : ℝ) + 1) (by positivity)
  have hd (n : ℕ) : 0 < dist p (q n) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hq n]
  choose U hU hUq using fun n => soul_unit_minimizing_initial (I := I) g hEnorm p (q n) (hd n)
  obtain ⟨U0, hU0, phi, hphi, hlim⟩ :=
    (gUnitSphere_isCompact (I := I) g p).tendsto_subseq hU
  change g.inner p U0 U0 = 1 at hU0
  let eta : ℝ := min (1 / 4) (eps / 32)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta1 : eta ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hetaE : 16 * eta < eps := by
    have hle : eta ≤ eps / 32 := min_le_right _ _
    linarith
  have hdlim0 : Tendsto (fun n => dist p (q n)) atTop atTop :=
    Filter.tendsto_atTop.2 fun B => by
      obtain ⟨N, hN⟩ := exists_nat_gt B
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith [hq n]
  have hdlim := hdlim0.comp hphi.tendsto_atTop
  have hconv := ((g.inner p U0).continuous.tendsto U0).comp hlim
  rw [hU0] at hconv
  obtain ⟨n, hn⟩ := (hconv.eventually (lt_mem_nhds (by linarith : 1 - eta < 1))).exists
  have hsym : 1 - eta < g.inner p (U (phi n)) U0 := by
    rw [g.symm]
    exact hn
  have hconv2 := ((g.inner p (U (phi n))).continuous.tendsto U0).comp hlim
  have hevent := hconv2.eventually (lt_mem_nhds hsym)
  obtain ⟨k, hk, hfar⟩ :=
    (hevent.and (hdlim (eventually_gt_atTop (2 * dist p (q (phi n)) / eta)))).exists
  have hfar' : 2 * dist p (q (phi n)) < dist p (q (phi k)) * eta :=
    (div_lt_iff₀ heta).mp hfar
  have hresult := directions_close_of_remote_hinge (I := I) g hEnorm hsec
    p (q (phi n)) (q (phi k)) (U (phi n)) (U (phi k))
    (hU (phi n)) (hU (phi k)) (hUq (phi n)) (hUq (phi k))
    eta heta heta1 (hd (phi n)) hfar' hk
    (u (phi n)) (v (phi n)) (hu (phi n)) (hv (phi n)) (hup (phi n)) (hvp (phi n))
  exact (not_lt_of_ge (hbad (phi n))) (hresult.trans hetaE)

theorem exists_outward_direction_at_infinity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ q : M, R < dist p q →
      ∃ X : TangentSpace I q, g.inner q X X = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p →
          g.inner q X u < -(1 / 2 : ℝ) := by
  obtain ⟨R, hR, hclose⟩ := minimizing_directions_close_at_infinity
    (I := I) g hEnorm hsec p 1 (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hdist : 0 < dist q p := by rw [dist_comm]; exact hR.trans hq
  obtain ⟨u0, hu0, hu0p⟩ := soul_unit_minimizing_initial (I := I) g hEnorm q p hdist
  rw [dist_comm q p] at hu0p
  refine ⟨-u0, ?_, ?_⟩
  · simp only [map_neg, neg_apply, hu0, neg_neg]
  · intro u hu hup
    have hsmall := hclose q hq u0 u hu0 hu hu0p hup
    rw [ContinuousLinearMap.map_sub₂, map_sub, map_sub, hu0, hu, g.symm q u u0] at hsmall
    rw [map_neg, neg_apply]
    linarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_soul_scaled_vector
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hf : Continuous f) :
    Continuous (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp (hv.continuousAt (x := x))
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))
  apply (hf.continuousAt.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_soul_inner
    (g : SmoothRiemannianMetric I M)
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v w : (x : P) → TangentSpace I (b x)}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hw : Continuous (fun x => (⟨b x, w x⟩ : TangentBundle I M))) :
    Continuous (fun x => g.inner (b x) (v x) (w x)) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hv.inner_bundle hw

omit [ConnectedSpace M] in
theorem eventually_minimizing_inner_lt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (W : (y : M) → TangentSpace I y)
    (hW : Continuous (fun y => (⟨y, W y⟩ : TangentBundle I M))) (c : ℝ)
    (hneg : ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p → g.inner q (W q) u < c) :
    ∀ᶠ y in 𝓝 q, ∀ u : TangentSpace I y, g.inner y u u = 1 →
      intrinsicGeodesic (I := I) g hEnorm y u (dist p y) = p → g.inner y (W y) u < c := by
  let b : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let v : (z : MetricUnitTangent (I := I) g) → TangentSpace I (b z) :=
    MetricUnitTangent.vec
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : Continuous (fun z => (⟨b z, v z⟩ : TangentBundle I M)) := continuous_subtype_val
  have hscale := continuous_soul_scaled_vector (I := I)
    (f := fun z => dist p (b z)) hv (continuous_const.dist hb)
  have hend : Continuous (fun z => expMapIntrinsic (I := I) g hEnorm (b z)
      (dist p (b z) • v z)) := (intrinsicExp_smooth (I := I) g hEnorm).continuous.comp hscale
  have hinner : Continuous (fun z => g.inner (b z) (W (b z)) (v z)) :=
    continuous_soul_inner (I := I) g (hW.comp hb) hv
  let bad : Set (MetricUnitTangent (I := I) g) :=
    {z | expMapIntrinsic (I := I) g hEnorm (b z) (dist p (b z) • v z) = p ∧
      c ≤ g.inner (b z) (W (b z)) (v z)}
  have hbad : IsClosed bad :=
    (isClosed_eq hend continuous_const).inter (isClosed_le continuous_const hinner)
  have hproper : IsProperMap b := isProperMap_iff_isCompact_preimage.mpr
    ⟨hb, fun _ hK => metricUnitOn_compact (I := I) g hK⟩
  have hq : q ∈ (b '' bad)ᶜ := by
    rintro ⟨⟨⟨y, u⟩, hu⟩, hbad, hy⟩
    change y = q at hy
    subst y
    change expMapIntrinsic (I := I) g hEnorm q (dist p q • u) = p ∧
      c ≤ g.inner q (W q) u at hbad
    have hup : intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p := by
      simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hbad.1
    exact (not_lt_of_ge hbad.2) (hneg u hu hup)
  filter_upwards [(hproper.isClosedMap bad hbad).isOpen_compl.mem_nhds hq] with y hy
  intro u hu hup
  by_contra h
  apply hy
  refine ⟨⟨⟨y, u⟩, hu⟩, ?_, rfl⟩
  change expMapIntrinsic (I := I) g hEnorm y (dist p y • u) = p ∧
    c ≤ g.inner y (W y) u
  exact ⟨by simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hup, le_of_not_gt h⟩

theorem exists_smooth_outward_field_at_infinity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) :
    ∃ R₀ R₁ : ℝ, 0 < R₀ ∧ R₀ < R₁ ∧
      ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
        (∀ q, g.inner q (X q) (X q) < 4) ∧
        (∀ q, dist p q ≤ R₀ → X q = 0) ∧
        ∀ q, R₁ ≤ dist p q → ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p →
          g.inner q (X q) u ≤ -(1 / 4 : ℝ) := by
  classical
  obtain ⟨R₀, hR₀, hout⟩ := exists_outward_direction_at_infinity (I := I) g hEnorm hsec p
  let R₁ : ℝ := R₀ + 1
  have hRR : R₀ < R₁ := by dsimp only [R₁]; linarith
  let t : (q : M) → Set (TangentSpace I q) := fun q =>
    {w | g.inner q w w < 4 ∧ (dist p q ≤ R₀ → w = 0) ∧
      (R₁ ≤ dist p q → ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p →
        g.inner q w u ≤ -(1 / 4 : ℝ))}
  have ht (q : M) : Convex ℝ (t q) := by
    intro x hx y hy a b ha hb hab
    have hid : g.inner q (a • x + b • y) (a • x + b • y) =
        (a + b) * (a * g.inner q x x + b * g.inner q y y) -
          a * b * g.inner q (x - y) (x - y) := by
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul,
        map_sub, sub_apply, g.symm q y x]
      ring
    have hpos := mul_nonneg (mul_nonneg ha hb) (gInner_self_nonneg (I := I) g q (x - y))
    have hbound : a * g.inner q x x + b * g.inner q y y < 4 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.1
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hax := mul_lt_mul_of_pos_left hx.1 hap
        have hby := mul_le_mul_of_nonneg_left hy.1.le hb
        nlinarith only [hax, hby, hab]
    refine ⟨?_, ?_, ?_⟩
    · rw [hid, hab, one_mul]
      linarith
    · intro hq
      rw [hx.2.1 hq, hy.2.1 hq, smul_zero, smul_zero, add_zero]
    · intro hq u hu hup
      have hax := mul_le_mul_of_nonneg_left (hx.2.2 hq u hu hup) ha
      have hby := mul_le_mul_of_nonneg_left (hy.2.2 hq u hu hup) hb
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul]
      nlinarith only [hax, hby, hab]
  have hloc (q : M) : ∃ U ∈ 𝓝 q, ∃ W : (y : M) → TangentSpace I y,
      ContMDiffOn I I.tangent ∞ (fun y => (⟨y, W y⟩ : TangentBundle I M)) U ∧
      ∀ y ∈ U, W y ∈ t y := by
    by_cases hq : dist p q < R₁
    · have hmem : q ∈ Metric.ball p R₁ := by simpa only [Metric.mem_ball, dist_comm] using hq
      refine ⟨Metric.ball p R₁, Metric.isOpen_ball.mem_nhds hmem, fun _ => 0,
        (0 : Cₛ^∞⟮I; E, TangentSpace I⟯).contMDiff.contMDiffOn, ?_⟩
      intro y hy
      have hyd : dist p y < R₁ := by simpa only [Metric.mem_ball, dist_comm] using hy
      refine ⟨by simp, fun _ => rfl, ?_⟩
      intro hfar
      exact ((not_le_of_gt hyd) hfar).elim
    · have hfar : R₀ < dist p q := hRR.trans_le (le_of_not_gt hq)
      obtain ⟨X, hX, hXu⟩ := hout q hfar
      obtain ⟨W, hWq⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (n := ⊤) q X
      have hneg := eventually_minimizing_inner_lt (I := I) g hEnorm p q W
        W.contMDiff.continuous (-(1 / 4 : ℝ)) (by
          intro u hu hup
          rw [hWq]
          exact (hXu u hu hup).trans (by norm_num))
      have hnorm : ∀ᶠ y in 𝓝 q, g.inner y (W y) (W y) < 4 :=
        (continuous_soul_inner (I := I) g W.contMDiff.continuous W.contMDiff.continuous).continuousAt
          (gt_mem_nhds (by rw [hWq, hX]; norm_num))
      have houter : ∀ᶠ y in 𝓝 q, R₀ < dist p y :=
        (continuous_const.dist continuous_id).continuousAt (lt_mem_nhds hfar)
      refine ⟨_, hneg.and (hnorm.and houter), W, W.contMDiff.contMDiffOn, ?_⟩
      intro y hy
      exact ⟨hy.2.1, fun hle => ((not_lt_of_ge hle) hy.2.2).elim,
        fun _ u hu hup => (hy.1 u hu hup).le⟩
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local I
    (TangentSpace I) t ht hloc
  exact ⟨R₀, R₁, hR₀, hRR, X, fun q => (hX q).1,
    fun q => (hX q).2.1, fun q => (hX q).2.2⟩

omit [ConnectedSpace M] in
theorem soul_isCompact_closedBall
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ) : IsCompact (Metric.closedBall p R) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real _
  have hcompact := (isCompact_closedBall (0 : TangentSpace I p) R).image
    (expMapIntrinsic_continuous (I := I) g hEnorm p)
  apply hcompact.of_isClosed_subset Metric.isClosed_closedBall
  intro q hq
  have hfin : riemannianEDist I p q ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q hfin
  refine ⟨v, ?_, hv⟩
  have hn := hEnorm p v
  rw [← ofReal_norm] at hn
  have hn' := (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hn
  rw [Metric.mem_closedBall, dist_zero_right, hn', hlen, soul_riemannian_toReal (I := I)]
  simpa only [Metric.mem_closedBall, dist_comm] using hq

omit [ConnectedSpace M] in
theorem exists_globalIntegralCurve_of_bounded
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, g.inner x (V x) (V x) ≤ C ^ 2) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V := by
  classical
  apply (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo
    (V.contMDiff.of_le (by norm_num)) x).mpr
  intro a
  let r : ℝ := C * |a| + 1
  obtain ⟨f, hf, hf01, hfsupp, hf1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I (n := ⊤)
      (s := Metric.ball x (r + 1)) (t := Metric.closedBall x r)
      Metric.isOpen_ball Metric.isClosed_closedBall
      (Metric.closedBall_subset_ball (by linarith))
  let W : (y : M) → TangentSpace I y := fun y => f y • V y
  have hW : ContMDiff I I.tangent ∞ (fun y => (⟨y, W y⟩ : TangentBundle I M)) :=
    hf.smul_section V.contMDiff
  have hsupp : IsCompact (tsupport W) := by
    apply (soul_isCompact_closedBall (I := I) g hEnorm x (r + 1)).of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro y hy
    have hyf : f y ≠ 0 := by
      intro hzero
      exact hy (by change f y • V y = 0; rw [hzero, zero_smul])
    have hymem : y ∈ Metric.ball x (r + 1) := by
      rw [← hfsupp]
      exact hyf
    exact Metric.ball_subset_closedBall hymem
  let hcomplete := exists_globalIntegralCurve_of_compactSupport W hW hsupp
  let γ : ℝ → M := curveAt W hcomplete x
  have hγ : IsMIntegralCurve γ W := curveAt_integralCurve W hcomplete x
  have hγ0 : γ 0 = x := curveAt_zero W hcomplete x
  have hγsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    (contMDiff_globalFlow_joint_of_compactSupport W hW hsupp).comp
      (contMDiff_id.prodMk contMDiff_const)
  have hspeed (t : ℝ) :
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ ≤ ENNReal.ofReal C := by
    have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = (W (γ t) : E) := by
      have hh := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (γ t) => L 1) (hγ t).mfderiv
      simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hh
      convert! hh using 1
    rw [hvel]
    rw [hEnorm]
    apply ENNReal.ofReal_le_ofReal
    apply (Real.sqrt_le_left hC).mpr
    change g.inner (γ t) (f (γ t) • V (γ t)) (f (γ t) • V (γ t)) ≤ C ^ 2
    rw [gInner_smul_self (I := I)]
    have hfval := hf01 (mem_range_self (γ t))
    have hf_sq : (f (γ t)) ^ 2 ≤ 1 := by nlinarith [hfval.1, hfval.2]
    exact (mul_le_mul_of_nonneg_left (hbound (γ t)) (sq_nonneg _)).trans
      (by nlinarith [sq_nonneg C])
  have hdist (s t : ℝ) (hst : s ≤ t) : dist (γ s) (γ t) ≤ C * (t - s) := by
    have he := curve_edist_le_speed_mul_time (I := I) hC hst
      (hγsm.of_le (by norm_num)).contMDiffOn (fun τ _ => hspeed τ)
    rw [← IsRiemannianManifold.out (I := I), edist_dist] at he
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  have hdt : dist x (γ t) ≤ C * |t| := by
    by_cases h0t : 0 ≤ t
    · simpa only [hγ0, sub_zero, abs_of_nonneg h0t] using hdist 0 t h0t
    · have ht0 := le_of_not_ge h0t
      simpa only [hγ0, zero_sub, abs_of_nonpos ht0, dist_comm] using hdist t 0 ht0
  have hta : |t| ≤ |a| := (abs_lt.mpr ht).le.trans (le_abs_self a)
  have htr : γ t ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_comm]
    exact hdt.trans ((mul_le_mul_of_nonneg_left hta hC).trans (by dsimp [r]; linarith))
  have hWγ : W (γ t) = V (γ t) := by simp only [W, (hf1 _).mp htr, one_smul]
  have hh := (hγ t).hasMFDerivWithinAt (s := Ioo (-a) a)
  rw [hWγ] at hh
  exact hh

omit [ConnectedSpace M] in
private theorem soul_distance_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hpq : 0 < dist p q) :
    ∃ ρ : M → ℝ, ∃ u : TangentSpace I q,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ q ∧ ρ q = dist p q ∧
      (∀ᶠ y in 𝓝 q, dist p y ≤ ρ y) ∧
      g.inner q u u = 1 ∧ intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p ∧
      gradientFun (I := I) g ρ q = -u := by
  have hfin : riemannianEDist I p q ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q hfin
  change intrinsicGeodesic (I := I) g hEnorm p v 1 = q at hv
  have hlen' : Real.sqrt (g.inner p v v) = dist p q := by
    simpa only [soul_riemannian_toReal (I := I)] using hlen
  have hvpos : 0 < g.inner p v v := Real.sqrt_pos.mp (hlen'.symm ▸ hpq)
  have hs := smooth_distance_upper_support_of_minimizing_exp (I := I) g hEnorm p v hvpos
    (by rw [hv]; exact hlen)
  dsimp only at hs
  let w : TangentSpace I q := curveVelocity (I := I)
    (intrinsicGeodesic (I := I) g hEnorm p v) 1
  have hspeed : g.inner q w w = (dist p q) ^ 2 := by
    have hh := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v 1
    rw [hv] at hh
    change g.inner q w w = _ at hh
    rw [hh, ← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hlen']
  rw [hv, hlen'] at hs
  obtain ⟨ρ, hρ, hval, hupper, hgrad⟩ := hs
  let u : TangentSpace I q := -(dist p q)⁻¹ • w
  refine ⟨ρ, u, hρ, hval, ?_, ?_, ?_, ?_⟩
  · simpa only [soul_riemannian_toReal (I := I)] using hupper
  · dsimp only [u]
    rw [gInner_smul_self (I := I), hspeed, neg_sq, ← mul_pow,
      inv_mul_cancel₀ hpq.ne', one_pow]
  · have hcont := congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p v 1) (-1)
    rw [neg_add_cancel, intrinsicGeodesic_zero, hv] at hcont
    have hmul : -(dist p q)⁻¹ * dist p q = -1 := by rw [neg_mul, inv_mul_cancel₀ hpq.ne']
    have hsm := intrinsicGeo_smul_apply (I := I) g hEnorm q w (-(dist p q)⁻¹) (dist p q)
    rw [hmul] at hsm
    convert! hsm.trans hcont.symm using 1
  · change (gradientFun (I := I) g ρ q : E) = (dist p q)⁻¹ • (w : E) at hgrad
    simpa only [u, neg_smul, neg_neg] using hgrad

omit [ConnectedSpace M] in
theorem distance_growth_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (V : (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {a b c : ℝ} (hab : a ≤ b)
    (hpos : ∀ t ∈ Ioc a b, 0 < dist p (γ t))
    (hout : ∀ t ∈ Ioc a b, ∀ u : TangentSpace I (γ t),
      g.inner (γ t) u u = 1 →
      intrinsicGeodesic (I := I) g hEnorm (γ t) u (dist p (γ t)) = p →
      g.inner (γ t) (V (γ t)) u ≤ -c) :
    c * (b - a) ≤ dist p (γ b) - dist p (γ a) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  apply growth_of_upper_support hab (continuous_const.dist hγc).continuousOn
  intro t ht
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hup, hgrad⟩ :=
    soul_distance_upper_support (I := I) g hEnorm p (γ t) (hpos t ht)
  refine ⟨fun s => ρ (γ s), -g.inner (γ t) u (V (γ t)), ?_, hval,
    hγc.continuousAt.eventually hupper, ?_⟩
  · have hd := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
      I ρ γ t (hρ.mdifferentiableAt (by simp)) (hγ t).mdifferentiableAt
    have hvel : (curveVelocity (I := I) γ t : E) = (V (γ t) : E) := by
      have hh := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (γ t) => L 1) (hγ t).mfderiv
      simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hh
      convert! hh using 1
    apply hd.congr_deriv
    change mvfderiv (I := I) ρ (γ t) (curveVelocity (I := I) γ t) = _
    rw [← inner_gradientFun (I := I) g, hgrad, map_neg, neg_apply, hvel]
  · have hh := hout t ht u hu hup
    rw [g.symm (γ t) (V (γ t)) u] at hh
    linarith

omit [ConnectedSpace M] in
theorem escape_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (V : (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hout : ∀ q : M, R ≤ dist p q → ∀ u : TangentSpace I q,
      g.inner q u u = 1 → intrinsicGeodesic (I := I) g hEnorm q u (dist p q) = p →
      g.inner q (V q) u ≤ -c)
    (hstart : R < dist p (γ 0)) :
    ∀ t : ℝ, 0 ≤ t → R < dist p (γ t) ∧ c * t ≤ dist p (γ t) - dist p (γ 0) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  apply escape_of_growth (continuous_const.dist hγc) hstart hc
  intro a b hab hfar
  exact distance_growth_of_outward_integralCurve (I := I) g hEnorm p V hγ hab
    (fun t ht => hR.trans_le (hfar t ht)) (fun t ht => hout (γ t) (hfar t ht))

theorem exists_complete_escape_field
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ q, g.inner q (V q) (V q) < 4) ∧
      (∀ q, ∃ γ : ℝ → M, γ 0 = q ∧ IsMIntegralCurve γ V) ∧
      ∀ q : M, R < dist p q → ∃ γ : ℝ → M,
        γ 0 = q ∧ IsMIntegralCurve γ V ∧
        ∀ t : ℝ, 0 ≤ t → dist p q + t / 4 ≤ dist p (γ t) := by
  obtain ⟨R₀, R, hR₀, hRR, V, hbound, _hzero, hout⟩ :=
    exists_smooth_outward_field_at_infinity (I := I) g hEnorm hsec p
  have hcomplete := exists_globalIntegralCurve_of_bounded (I := I) g hEnorm V 2
    (by norm_num) (fun q => by convert! (hbound q).le using 1; norm_num)
  refine ⟨R, hR₀.trans hRR, V, hbound, hcomplete, ?_⟩
  intro q hq
  obtain ⟨γ, hγ0, hγ⟩ := hcomplete q
  refine ⟨γ, hγ0, hγ, ?_⟩
  have hescape := escape_of_outward_integralCurve (I := I) g hEnorm p V hγ
    (hR₀.trans hRR) (show 0 ≤ (1 / 4 : ℝ) by norm_num) hout (by rwa [hγ0])
  intro t ht
  have hh := (hescape t ht).2
  rw [hγ0] at hh
  linarith

end DifferentialGeometry.Geometry.Topology

end
