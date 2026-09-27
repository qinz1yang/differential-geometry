import DifferentialGeometry.Geometry.Comparison.Soul.DistanceField
import DifferentialGeometry.Geometry.Comparison.Soul.SoulFlow

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Topology

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
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem point_distance_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p q : M) (hpq : 0 < dist p q) :
    ∃ ρ : M → ℝ, ∃ u : TangentSpace I q,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ q ∧ ρ q = dist p q ∧
      (∀ᶠ y in 𝓝 q, dist p y ≤ ρ y) ∧
      g.inner q u u = 1 ∧ intrinsicGeodesic g hEnorm q u (dist p q) = p ∧
      gradientFun g ρ q = -u := by
  have hfin : riemannianEDist I p q ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm p q hfin
  change intrinsicGeodesic g hEnorm p v 1 = q at hv
  have hlen' : Real.sqrt (g.inner p v v) = dist p q := by
    simpa only [riemannian_toReal (I := I)] using hlen
  have hvpos : 0 < g.inner p v v := Real.sqrt_pos.mp (hlen'.symm ▸ hpq)
  have hs := smooth_distance_upper_support_of_minimizing_exp g hEnorm p v hvpos
    (by rw [hv]; exact hlen)
  dsimp only at hs
  let w : TangentSpace I q := curveVelocity (I := I) (intrinsicGeodesic g hEnorm p v) 1
  have hspeed : g.inner q w w = (dist p q) ^ 2 := by
    have hh := intrinsicGeodesic_speedSq_eq g hEnorm p v 1
    rw [hv] at hh
    change g.inner q w w = _ at hh
    rw [hh, ← Real.sq_sqrt (gInner_self_nonneg g p v), hlen']
  rw [hv, hlen'] at hs
  obtain ⟨ρ, hρ, hval, hupper, hgrad⟩ := hs
  let u : TangentSpace I q := -(dist p q)⁻¹ • w
  refine ⟨ρ, u, hρ, hval, ?_, ?_, ?_, ?_⟩
  · simpa only [riemannian_toReal (I := I)] using hupper
  · dsimp only [u]
    rw [gInner_smul_self, hspeed, neg_sq, ← mul_pow,
      inv_mul_cancel₀ hpq.ne', one_pow]
  · have hcont := congrFun (intrinsicGeodesic_continuation g hEnorm p v 1) (-1)
    rw [neg_add_cancel, intrinsicGeodesic_zero, hv] at hcont
    have hmul : -(dist p q)⁻¹ * dist p q = -1 := by rw [neg_mul, inv_mul_cancel₀ hpq.ne']
    have hsm := intrinsicGeo_smul_apply g hEnorm q w (-(dist p q)⁻¹) (dist p q)
    rw [hmul] at hsm
    convert! hsm.trans hcont.symm using 1
  · change (gradientFun g ρ q : E) = (dist p q)⁻¹ • (w : E) at hgrad
    simpa only [u, neg_smul, neg_neg] using hgrad

theorem infDist_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) (q : M)
    (hq : 0 < Metric.infDist q S) :
    ∃ ρ : M → ℝ, ∃ u : TangentSpace I q,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ q ∧ ρ q = Metric.infDist q S ∧
      (∀ᶠ y in 𝓝 q, Metric.infDist y S ≤ ρ y) ∧
      g.inner q u u = 1 ∧ intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S ∧
      gradientFun g ρ q = -u := by
  obtain ⟨p, hp, hd⟩ := hS.exists_infDist_eq_dist hSne q
  have hpd : dist p q = Metric.infDist q S := by simpa only [dist_comm] using hd.symm
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hup, hgrad⟩ :=
    point_distance_upper_support g hEnorm p q (hpd.symm ▸ hq)
  refine ⟨ρ, u, hρ, hval.trans hpd, ?_, hu, ?_, hgrad⟩
  · filter_upwards [hupper] with y hy
    exact (Metric.infDist_le_dist_of_mem hp).trans (by simpa only [dist_comm] using hy)
  · rw [← hpd, hup]
    exact hp

theorem infDist_growth_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {a b c : ℝ} (hab : a ≤ b)
    (hpos : ∀ t ∈ Ioc a b, 0 < Metric.infDist (γ t) S)
    (hout : ∀ t ∈ Ioc a b, ∀ u : TangentSpace I (γ t),
      g.inner (γ t) u u = 1 →
      intrinsicGeodesic g hEnorm (γ t) u (Metric.infDist (γ t) S) ∈ S →
      g.inner (γ t) (V (γ t)) u ≤ -c) :
    c * (b - a) ≤ Metric.infDist (γ b) S - Metric.infDist (γ a) S := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  apply growth_of_upper_support hab ((Metric.continuous_infDist_pt S).comp hγc).continuousOn
  intro t ht
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hup, hgrad⟩ :=
    infDist_upper_support g hEnorm hS hSne (γ t) (hpos t ht)
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
    rw [← inner_gradientFun g, hgrad, map_neg, neg_apply, hvel]
  · have hh := hout t ht u hu hup
    rw [g.symm (γ t) (V (γ t)) u] at hh
    linarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_scaled_vector
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_metric_inner
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

theorem exists_uniform_infDist_outward_margin
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S K : Set M} (hS : IsClosed S) (hK : IsCompact K)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hout : ∀ q ∈ K, ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ K, ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u ≤ -c := by
  classical
  let b : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let v : (z : MetricUnitTangent (I := I) g) → TangentSpace I (b z) := MetricUnitTangent.vec
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : Continuous (fun z => (⟨b z, v z⟩ : TangentBundle I M)) := continuous_subtype_val
  have hscale := continuous_scaled_vector (I := I)
    (f := fun z => Metric.infDist (b z) S) hv ((Metric.continuous_infDist_pt S).comp hb)
  have hend : Continuous (fun z => expMapIntrinsic g hEnorm (b z)
      (Metric.infDist (b z) S • v z)) :=
    (intrinsicExp_smooth g hEnorm).continuous.comp hscale
  let F : MetricUnitTangent (I := I) g → ℝ := fun z => g.inner (b z) (V (b z)) (v z)
  have hF : Continuous F := continuous_metric_inner g (hV.comp hb) hv
  let T : Set (MetricUnitTangent (I := I) g) :=
    {z | b z ∈ K ∧ expMapIntrinsic g hEnorm (b z) (Metric.infDist (b z) S • v z) ∈ S}
  have hT : IsCompact T := (metricUnitOn_compact g hK).inter_right (hS.preimage hend)
  by_cases hTne : T.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hT.exists_isMaxOn hTne hF.continuousOn
    have hneg : F z < 0 := hout (b z) hz.1 (v z) z.2
      (by simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hz.2)
    refine ⟨-F z, neg_pos.mpr hneg, ?_⟩
    intro q hq u hu hup
    have hut : (⟨⟨q, u⟩, hu⟩ : MetricUnitTangent (I := I) g) ∈ T := by
      refine ⟨hq, ?_⟩
      change expMapIntrinsic g hEnorm q (Metric.infDist q S • u) ∈ S
      simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hup
    rw [neg_neg]
    convert! hmax hut using 1
  · refine ⟨1, zero_lt_one, ?_⟩
    intro q hq u hu hup
    apply (hTne ?_).elim
    refine ⟨⟨⟨q, u⟩, hu⟩, hq, ?_⟩
    change expMapIntrinsic g hEnorm q (Metric.infDist q S • u) ∈ S
    simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hup

theorem isCompact_infDist_sublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) (R : ℝ) :
    IsCompact {q : M | Metric.infDist q S ≤ R} := by
  obtain ⟨p, hp⟩ := hSne
  apply (soul_isCompact_closedBall g hEnorm p (R + Metric.diam S)).of_isClosed_subset
    (isClosed_le (Metric.continuous_infDist_pt S) continuous_const)
  intro q hq
  exact (Metric.dist_le_infDist_add_diam hS.isBounded hp).trans (add_le_add hq le_rfl)

theorem exists_infDist_annulus_outward_margin
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {b : ℝ}
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (R : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : M, b ≤ Metric.infDist q S → Metric.infDist q S ≤ R →
      ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u ≤ -c := by
  have hK : IsCompact ({q : M | Metric.infDist q S ≤ R} ∩ {q : M | b ≤ Metric.infDist q S}) :=
    (isCompact_infDist_sublevel g hEnorm hS hSne R).inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt S))
  obtain ⟨c, hc, hmargin⟩ := exists_uniform_infDist_outward_margin g hEnorm hS.isClosed hK V hV
    (fun q hq => hout q hq.2)
  exact ⟨c, hc, fun q hq hqR => hmargin q ⟨hqR, hq⟩⟩

theorem exists_infDist_annulus_growth_rate
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (R : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (γ : ℝ → M), IsMIntegralCurve γ V → ∀ a z : ℝ, a ≤ z →
      (∀ t ∈ Ioc a z, b ≤ Metric.infDist (γ t) S ∧ Metric.infDist (γ t) S ≤ R) →
      c * (z - a) ≤ Metric.infDist (γ z) S - Metric.infDist (γ a) S := by
  obtain ⟨c, hc, hmargin⟩ := exists_infDist_annulus_outward_margin g hEnorm hS hSne V hV hout R
  refine ⟨c, hc, ?_⟩
  intro γ hγ a z haz hann
  exact infDist_growth_of_outward_integralCurve g hEnorm hS hSne V hγ haz
    (fun t ht => hb.trans_le (hann t ht).1)
    (fun t ht => hmargin (γ t) (hann t ht).1 (hann t ht).2)

private theorem local_infDist_growth
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) (hpos : 0 < Metric.infDist (γ 0) S)
    (hout : ∀ u : TangentSpace I (γ 0), g.inner (γ 0) u u = 1 →
      intrinsicGeodesic g hEnorm (γ 0) u (Metric.infDist (γ 0) S) ∈ S →
      g.inner (γ 0) (V (γ 0)) u < 0) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ t ∈ Icc 0 ε,
      c * t ≤ Metric.infDist (γ t) S - Metric.infDist (γ 0) S := by
  obtain ⟨c, hc, hmargin⟩ := exists_uniform_infDist_outward_margin g hEnorm hS.isClosed
    (isCompact_singleton (x := γ 0)) V hV (by
      intro q hq
      rcases mem_singleton_iff.mp hq with rfl
      exact hout)
  have hhalf : -c < -(c / 2) := by linarith
  have hnear := eventually_infDist_minimizing_inner_lt g hEnorm hS.isClosed (γ 0) V hV
    (-(c / 2)) (fun u hu hup => (hmargin (γ 0) (mem_singleton _) u hu hup).trans_lt hhalf)
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < Metric.infDist (γ t) S ∧
      ∀ u : TangentSpace I (γ t), g.inner (γ t) u u = 1 →
        intrinsicGeodesic g hEnorm (γ t) u (Metric.infDist (γ t) S) ∈ S →
        g.inner (γ t) (V (γ t)) u ≤ -(c / 2) := by
    filter_upwards [hγc.continuousAt.eventually hnear,
      ((Metric.continuous_infDist_pt S).comp hγc).continuousAt (lt_mem_nhds hpos)] with t hn hp
    exact ⟨hp, fun u hu hup => (hn u hu hup).le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨c / 2, ε / 2, half_pos hc, half_pos hε, ?_⟩
  intro t ht
  have hgood' (s : ℝ) (hs : s ∈ Ioc 0 t) := hball (show s ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    exact (hs.2.trans ht.2).trans_lt (half_lt_self hε))
  simpa only [sub_zero] using infDist_growth_of_outward_integralCurve g hEnorm hS hSne V hγ ht.1
    (fun s hs => (hgood' s hs).1) (fun s hs => (hgood' s hs).2)

theorem infDist_stays_exterior_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (hstart : b ≤ Metric.infDist (γ 0) S) :
    ∀ t : ℝ, 0 ≤ t → b ≤ Metric.infDist (γ t) S := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  have hstay_shift (δ : ℝ) (hδ : b < Metric.infDist (γ δ) S) :
      ∀ t : ℝ, 0 ≤ t → b < Metric.infDist (γ (t + δ)) S := by
    have hc : Continuous (fun t : ℝ => Metric.infDist (γ (t + δ)) S) :=
      ((Metric.continuous_infDist_pt S).comp hγc).comp (continuous_id.add continuous_const)
    have hh := escape_of_growth (c := 0) hc (by simpa only [zero_add] using hδ) le_rfl
      (by
        intro a z haz hfar
        exact infDist_growth_of_outward_integralCurve g hEnorm hS hSne V (hγ.comp_add δ) haz
          (fun t ht => hb.trans_le (hfar t ht))
          (fun t ht u hu hup => by
            convert! (hout (γ (t + δ)) (hfar t ht) u hu hup).le using 1
            simp only [neg_zero]))
    exact fun t ht => (hh t ht).1
  obtain ⟨c, ε, hc, hε, hlocal⟩ := local_infDist_growth g hEnorm hS hSne V hV hγ
    (hb.trans_le hstart) (hout (γ 0) hstart)
  intro t ht
  by_cases htε : t ≤ ε
  · have hg := hlocal t ⟨ht, htε⟩
    have hct := mul_nonneg hc.le ht
    linarith only [hg, hct, hstart]
  · have hg := hlocal ε ⟨hε.le, le_rfl⟩
    have hcε := mul_pos hc hε
    have hstartε : b < Metric.infDist (γ ε) S := by linarith only [hg, hcε, hstart]
    have hh := hstay_shift ε hstartε (t - ε) (sub_nonneg.mpr (le_of_not_ge htε))
    simpa only [sub_add_cancel] using hh.le

theorem infDist_strictMonoOn_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (hstart : b ≤ Metric.infDist (γ 0) S) :
    StrictMonoOn (fun t => Metric.infDist (γ t) S) (Ici 0) := by
  have hstay := infDist_stays_exterior_of_outward_integralCurve g hEnorm hS hSne V hV hγ hb hout hstart
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  intro a ha z _ haz
  obtain ⟨c, hc, hmargin⟩ := exists_uniform_infDist_outward_margin g hEnorm hS.isClosed
    ((isCompact_Icc : IsCompact (Icc a z)).image hγc) V hV (by
      rintro q ⟨t, ht, rfl⟩
      exact hout (γ t) (hstay t (ha.trans ht.1)))
  have hg := infDist_growth_of_outward_integralCurve g hEnorm hS hSne V hγ haz.le
    (fun t ht => hb.trans_le (hstay t (ha.trans ht.1.le)))
    (fun t ht => hmargin (γ t) ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩)
  have hcz := mul_pos hc (sub_pos.mpr haz)
  linarith only [hg, hcz]

theorem tendsto_infDist_atTop_of_outward_integralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M))) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (hstart : b ≤ Metric.infDist (γ 0) S) :
    Tendsto (fun t => Metric.infDist (γ t) S) atTop atTop := by
  let f : ℝ → ℝ := fun t => Metric.infDist (γ t) S
  have hstay := infDist_stays_exterior_of_outward_integralCurve g hEnorm hS hSne V hV hγ hb hout hstart
  have hmono := (infDist_strictMonoOn_of_outward_integralCurve g hEnorm hS hSne V hV hγ
    hb hout hstart).monotoneOn
  have hunbounded (R : ℝ) : ∃ t : ℝ, 0 ≤ t ∧ R < f t := by
    by_contra h
    push Not at h
    obtain ⟨c, hc, hgrowth⟩ := exists_infDist_annulus_growth_rate g hEnorm hS hSne V hV hb hout R
    have hf0 : f 0 ≤ R := h 0 le_rfl
    have hnum : 0 < R - f 0 + 1 := by linarith only [hf0]
    let T : ℝ := (R - f 0 + 1) / c
    have hT : 0 < T := div_pos hnum hc
    have hprod : c * T = R - f 0 + 1 := by
      dsimp only [T]
      calc
        c * ((R - f 0 + 1) / c) = (R - f 0 + 1) * (c / c) := by ring
        _ = R - f 0 + 1 := by rw [div_self hc.ne', mul_one]
    have hg := hgrowth γ hγ 0 T hT.le
      (fun t ht => ⟨hstay t ht.1.le, h t ht.1.le⟩)
    change c * (T - 0) ≤ f T - f 0 at hg
    rw [sub_zero, hprod] at hg
    have hfT := h T hT.le
    linarith only [hg, hfT]
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨T, hT, hRT⟩ := hunbounded R
  filter_upwards [eventually_ge_atTop T] with t ht
  exact hRT.le.trans (hmono hT (hT.trans ht) ht)

theorem exists_complete_infDist_escape_flow
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q, g.inner q (V q) (V q) ≤ C ^ 2) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0) :
    ∃ ϕ : Flow ℝ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2) ∧
      (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
      ∀ q, b ≤ Metric.infDist q S →
        (∀ t : ℝ, 0 ≤ t → b ≤ Metric.infDist (ϕ t q) S) ∧
        StrictMonoOn (fun t => Metric.infDist (ϕ t q) S) (Ici 0) ∧
        Tendsto (fun t => Metric.infDist (ϕ t q) S) atTop atTop := by
  have hcomplete := exists_globalIntegralCurve_of_bounded g hEnorm V C hC hbound
  refine ⟨completeFieldFlow V hcomplete, contMDiff_curveAt_joint V hcomplete,
    fun q => curveAt_integralCurve V hcomplete q, ?_⟩
  intro q hq
  have hγ := curveAt_integralCurve V hcomplete q
  have hstart : b ≤ Metric.infDist (curveAt V hcomplete q 0) S := by rwa [curveAt_zero]
  exact ⟨infDist_stays_exterior_of_outward_integralCurve g hEnorm hS hSne V
      V.contMDiff.continuous hγ hb hout hstart,
    infDist_strictMonoOn_of_outward_integralCurve g hEnorm hS hSne V
      V.contMDiff.continuous hγ hb hout hstart,
    tendsto_infDist_atTop_of_outward_integralCurve g hEnorm hS hSne V
      V.contMDiff.continuous hγ hb hout hstart⟩

end DifferentialGeometry.Geometry.Topology
