import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]


def rayBusemannSublevel (p : X) (a : ℝ) : Set X :=
  {x | ∀ c : ℝ≥0 → X, Isometry c → c 0 = p → busemann c x ≤ a}


theorem isClosed_rayBusemannSublevel (p : X) (a : ℝ) :
    IsClosed (rayBusemannSublevel p a) := by
  simp only [rayBusemannSublevel, ofPred_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun hc =>
    isClosed_iInter fun _ => isClosed_le (lipschitzWith_busemann hc).continuous continuous_const


theorem rayBusemannSublevel_mono (p : X) : Monotone (rayBusemannSublevel p) := by
  intro a b hab x hx c hc hc0
  exact (hx c hc hc0).trans hab


theorem self_mem_rayBusemannSublevel (p : X) {a : ℝ} (ha : 0 ≤ a) :
    p ∈ rayBusemannSublevel p a := by
  intro c hc hc0
  have h := busemann_ray hc 0
  simpa only [hc0, NNReal.coe_zero] using h.le.trans ha


theorem closedBall_subset_rayBusemannSublevel (p : X) (a : ℝ) :
    Metric.closedBall p a ⊆ rayBusemannSublevel p a := by
  intro x hx c hc hc0
  have h := (le_abs_self (busemann c x)).trans (abs_busemann_le hc x)
  rw [hc0] at h
  exact h.trans hx


theorem iUnion_rayBusemannSublevel (p : X) :
    (⋃ n : ℕ, rayBusemannSublevel p (n : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (dist x p)
  exact mem_iUnion.2 ⟨n, closedBall_subset_rayBusemannSublevel p n hn⟩


theorem rayBusemannSublevel_subset_interior (p : X) {a b : ℝ} (hab : a < b) :
    rayBusemannSublevel p a ⊆ interior (rayBusemannSublevel p b) := by
  intro x hx
  rw [mem_interior_iff_mem_nhds]
  apply Metric.mem_nhds_iff.2 ⟨b - a, sub_pos.2 hab, ?_⟩
  intro y hy c hc hc0
  have h := (lipschitzWith_busemann hc).dist_le_mul y x
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
  have hle := (le_abs_self (busemann c y - busemann c x)).trans h
  have hbase := hx c hc hc0
  change dist y x < b - a at hy
  linarith

end Metric

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
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

theorem convexOn_busemann_intrinsicGeodesic_unit
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) (q : M) (u : TangentSpace I q)
    (hu : g.inner q u u = 1) {D : Set ℝ} (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun s => busemann c (intrinsicGeodesic (I := I) g hEnorm q u s)) := by
  let gamma := intrinsicGeodesic (I := I) g hEnorm q u
  let F : ℝ≥0 → ℝ → ℝ := fun t s =>
    (1 / 2 * (t : ℝ)⁻¹) * (s ^ 2 - dist (c t) (gamma s) ^ 2 + (t : ℝ) ^ 2)
  have hF (t : ℝ≥0) : ConvexOn ℝ D (F t) := by
    have h := convexOn_sq_sub_sq_riemannianEDist_intrinsicGeodesic
      (I := I) g hEnorm hsec (c t) q u hu hD
    simp only [riemannian_toReal_eq_dist (I := I)] at h
    exact (h.add_const ((t : ℝ) ^ 2)).smul (by positivity)
  have hlim (s : ℝ) : Tendsto (fun t => F t s) atTop (𝓝 (busemann c (gamma s))) := by
    have hB := tendsto_busemannApprox hc (gamma s)
    have hinv : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    have hcorr := ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 => s ^ 2) atTop (𝓝 (s ^ 2))).sub (hB.pow 2)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).mul hinv)
    have h := hB.add hcorr
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
    dsimp only [F, busemannApprox]
    rw [dist_comm (c t) (gamma s)]
    field_simp [ht']
    ring
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  exact le_of_tendsto_of_tendsto (hlim (a • x + b • y))
    (((hlim x).const_mul a).add ((hlim y).const_mul b))
    (Eventually.of_forall fun t => (hF t).2 hx hy ha hb hab)

theorem convexOn_busemann_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) (q : M) (v : TangentSpace I q)
    {D : Set ℝ} (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun s => busemann c (intrinsicGeodesic (I := I) g hEnorm q v s)) := by
  by_cases hv : v = 0
  · have hconstant (s : ℝ) : intrinsicGeodesic (I := I) g hEnorm q v s = q := by
      rw [← intrinsicGeodesic_smul, hv, smul_zero, ← expMapIntrinsic_def,
        expMapIntrinsic_zero]
    simp only [hconstant]
    exact convexOn_const _ hD
  let L := Real.sqrt (g.inner q v v)
  have hL : 0 < L := Real.sqrt_pos.2 (g.pos q v hv)
  let u : TangentSpace I q := L⁻¹ • v
  have hu : g.inner q u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self]
    have hsq : g.inner q v v = L ^ 2 := (Real.sq_sqrt (gInner_self_nonneg g q v)).symm
    rw [hsq, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
  have hLu : L • u = v := by simp [u, smul_smul, hL.ne']
  have h := convexOn_busemann_intrinsicGeodesic_unit
    (I := I) g hEnorm hsec hc q u hu convex_univ
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hi := h.2 (mem_univ (L * x)) (mem_univ (L * y)) ha hb hab
  simp only [smul_eq_mul] at hi ⊢
  have hparam (s : ℝ) : intrinsicGeodesic (I := I) g hEnorm q v s =
      intrinsicGeodesic (I := I) g hEnorm q u (L * s) := by
    rw [← hLu]
    exact intrinsicGeo_smul_apply (I := I) g hEnorm q u L s
  simp only [hparam]
  convert hi using 1
  congr 2
  ring

theorem intrinsicGeodesic_mem_rayBusemannSublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p q : M) (v : TangentSpace I q) {a b t k : ℝ}
    (ht : t ∈ Icc a b)
    (ha : intrinsicGeodesic (I := I) g hEnorm q v a ∈ rayBusemannSublevel p k)
    (hb : intrinsicGeodesic (I := I) g hEnorm q v b ∈ rayBusemannSublevel p k) :
    intrinsicGeodesic (I := I) g hEnorm q v t ∈ rayBusemannSublevel p k := by
  intro c hc hc0
  exact ((convexOn_busemann_intrinsicGeodesic (I := I) g hEnorm hsec hc q v
    convex_univ).le_max_of_mem_Icc (mem_univ a) (mem_univ b) ht).trans
      (max_le (ha c hc hc0) (hb c hc hc0))

private theorem isCompact_rayBusemannSublevel_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) {k : ℝ} (hk : 0 ≤ k) : IsCompact (rayBusemannSublevel p k) := by
  by_contra hnc
  have hclosed := isClosed_rayBusemannSublevel p k
  have hex (n : ℕ) : ∃ x ∈ rayBusemannSublevel p k, (n : ℝ) + 1 < dist p x := by
    by_contra h
    push Not at h
    apply hnc
    apply (soul_isCompact_closedBall (I := I) g hEnorm p ((n : ℝ) + 1)).of_isClosed_subset hclosed
    intro x hx
    rw [Metric.mem_closedBall, dist_comm]
    exact h x hx
  choose x hx hfar using hex
  let d : ℕ → ℝ := fun n => dist p (x n)
  have hdpos (n : ℕ) : 0 < d n := by have := hfar n; dsimp [d]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hdiv : Tendsto d atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [d]; have := hfar n; linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  choose v hunit hend using fun n => soul_unit_minimizing_initial (I := I) g hEnorm p (x n) (hdpos n)
  have hmin (n : ℕ) : (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (d n))).toReal = d n := by
    rw [hend n, riemannian_toReal_eq_dist (I := I)]
  obtain ⟨u, hu, phi, hphi, hlim, hray⟩ :=
    exists_minimizing_ray_subsequence (I := I) g hEnorm p v d hunit hdpos hmin hdiv
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hzero : gamma 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hLip : LipschitzWith 1 gamma := lipschitzWith_one_intrinsicGeodesic g hEnorm p u hu
  have hrad (s : ℝ) (hs : 0 ≤ s) : dist (gamma 0) (gamma s) = s := by
    rw [hzero, ← riemannian_toReal_eq_dist (I := I), hray s hs, ENNReal.toReal_ofReal hs]
  have hiso : Isometry (fun s : ℝ≥0 => gamma (s : ℝ)) := by
    apply Isometry.of_dist_eq
    intro s t
    have hord (a b : ℝ≥0) (hab : a ≤ b) :
        dist (gamma (a : ℝ)) (gamma (b : ℝ)) = (b : ℝ) - a :=
      dist_eq_sub_of_lipschitzWith_one_of_endpoints hLip (a := 0)
        a.coe_nonneg hab le_rfl (by simpa only [sub_zero] using hrad b b.coe_nonneg)
    rcases le_total s t with hst | hts
    · have hst' : (s : ℝ) ≤ t := hst
      rw [hord s t hst, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 hst'), neg_sub]
    · have hts' : (t : ℝ) ≤ s := hts
      rw [dist_comm (gamma (s : ℝ)) (gamma (t : ℝ)), hord t s hts,
        NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 hts')]
  have hstay (s : ℝ) (hs : 0 ≤ s) : gamma s ∈ rayBusemannSublevel p k := by
    have hpoint : Tendsto (fun n => intrinsicGeodesic (I := I) g hEnorm p (v (phi n)) s)
        atTop (𝓝 (gamma s)) := by
      have hc := (expMapIntrinsic_continuous (I := I) g hEnorm p).comp
        (continuous_const_smul s : Continuous (fun w : TangentSpace I p => s • w))
      simpa only [Function.comp_def, expMapIntrinsic_def, intrinsicGeodesic_smul] using
        (hc.tendsto u).comp hlim
    apply hclosed.mem_of_tendsto hpoint
    filter_upwards [(hdiv.comp hphi.tendsto_atTop) (eventually_ge_atTop s)] with n hn
    apply intrinsicGeodesic_mem_rayBusemannSublevel (I := I) g hEnorm hsec p p (v (phi n))
      (a := 0) (b := d (phi n)) ⟨hs, hn⟩
    · simpa only [intrinsicGeodesic_zero] using self_mem_rayBusemannSublevel p hk
    · simpa only [d, hend] using hx (phi n)
  let T : ℝ≥0 := ⟨k + 1, by linarith⟩
  have hbound := hstay T T.coe_nonneg (fun s : ℝ≥0 => gamma (s : ℝ)) hiso hzero
  rw [busemann_ray hiso T] at hbound
  change k + 1 ≤ k at hbound
  linarith

theorem isCompact_rayBusemannSublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (k : ℝ) : IsCompact (rayBusemannSublevel p k) := by
  by_cases hk : 0 ≤ k
  · exact isCompact_rayBusemannSublevel_nonneg g hEnorm hsec p hk
  · exact (isCompact_rayBusemannSublevel_nonneg g hEnorm hsec p (le_refl 0)).of_isClosed_subset
      (isClosed_rayBusemannSublevel p k) (rayBusemannSublevel_mono p (le_of_not_ge hk))

omit [ConnectedSpace M] in
private theorem geodesicSegment_eqOn_intrinsic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {gamma : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g gamma (Icc a b))
    (hcont : ContinuousOn gamma (Icc a b)) :
    ∃ (q : M) (v : TangentSpace I q) (r : ℝ),
      EqOn gamma (fun t => intrinsicGeodesic (I := I) g hEnorm q v (t - r)) (Icc a b) := by
  let r : ℝ := (a + b) / 2
  let delta : ℝ → M := fun t => gamma (t + r)
  let q : M := delta 0
  let v : TangentSpace I q := mfderiv 𝓘(ℝ, ℝ) I delta 0 1
  let eta := intrinsicGeodesic (I := I) g hEnorm q v
  have hrleft : a < r := by dsimp [r]; linarith
  have hrright : r < b := by dsimp [r]; linarith
  have hmap : MapsTo (fun t : ℝ => t + r) (Icc (a - r) (b - r)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hdcont : ContinuousOn delta (Icc (a - r) (b - r)) :=
    hcont.comp (continuous_id.add continuous_const).continuousOn hmap
  have hdgeo : Geodesic.IsGeodesicOn (I := I) g delta (Ioo (a - r) (b - r)) := by
    have h := Geodesic.isGeodesicOn_comp_affine (I := I) (c := 1) (d := r) hgeo
    intro t ht
    simpa only [one_mul] using h t (by
      change 1 * t + r ∈ Icc a b
      simpa only [one_mul] using hmap (Ioo_subset_Icc_self ht))
  have heq : EqOn delta eta (Ioo (a - r) (b - r)) := by
    apply geo_eqOn_of_initial (I := I) g isOpen_Ioo isPreconnected_Ioo
      (show (0 : ℝ) ∈ Ioo (a - r) (b - r) by constructor <;> linarith)
      hdgeo ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v).isGeodesicOn _)
      (hdcont.mono Ioo_subset_Icc_self) (intrinsicGeodesic_continuous g hEnorm q v).continuousOn
    · exact (intrinsicGeodesic_zero (I := I) g hEnorm q v).symm
    · exact (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v).symm
  have heqClosed : EqOn delta eta (Icc (a - r) (b - r)) := by
    apply heq.of_subset_closure hdcont (intrinsicGeodesic_continuous g hEnorm q v).continuousOn
      Ioo_subset_Icc_self
    rw [closure_Ioo (by linarith : a - r ≠ b - r)]
  refine ⟨q, v, r, ?_⟩
  intro t ht
  have ht' : t - r ∈ Icc (a - r) (b - r) := by constructor <;> linarith [ht.1, ht.2]
  simpa only [delta, sub_add_cancel] using heqClosed ht'

def IsTotallyConvex (g : SmoothRiemannianMetric I M) (S : Set M) : Prop :=
  ∀ {gamma : ℝ → M} {a b : ℝ}, a ≤ b →
    Geodesic.IsGeodesicOn (I := I) g gamma (Icc a b) → ContinuousOn gamma (Icc a b) →
    gamma a ∈ S → gamma b ∈ S → MapsTo gamma (Icc a b) S

theorem isTotallyConvex_rayBusemannSublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (k : ℝ) : IsTotallyConvex (I := I) g (rayBusemannSublevel p k) := by
  intro gamma a b hab hgeo hcont ha hb t ht
  rcases hab.eq_or_lt with rfl | hab
  · have ht' : t = a := le_antisymm ht.2 ht.1
    simpa only [ht'] using ha
  obtain ⟨q, v, r, heq⟩ := geodesicSegment_eqOn_intrinsic g hEnorm hab hgeo hcont
  rw [heq ht]
  apply intrinsicGeodesic_mem_rayBusemannSublevel (I := I) g hEnorm hsec p q v
    (a := a - r) (b := b - r) ⟨sub_le_sub_right ht.1 r, sub_le_sub_right ht.2 r⟩
  · have he := heq (left_mem_Icc.2 hab.le)
    convert! (congrArg (fun z : M => z ∈ rayBusemannSublevel p k) he).mp ha
  · have he := heq (right_mem_Icc.2 hab.le)
    convert! (congrArg (fun z : M => z ∈ rayBusemannSublevel p k) he).mp hb

omit [ConnectedSpace M] in
theorem IsTotallyConvex.isPathConnected
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {S : Set M} (hS : IsTotallyConvex (I := I) g S) (hne : S.Nonempty) :
    IsPathConnected S := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, hp, ?_⟩
  intro q hq
  obtain ⟨v, hv, _⟩ := minExp_of_ne_top (I := I) g hEnorm p q (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q)
  let gamma := intrinsicGeodesic (I := I) g hEnorm p v
  have hzero : gamma 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hone : gamma 1 = q := hv
  refine ⟨⟨⟨fun t => gamma t, (intrinsicGeodesic_continuous g hEnorm p v).comp
    continuous_subtype_val⟩, hzero, hone⟩, ?_⟩
  intro t
  exact hS (by norm_num : (0 : ℝ) ≤ 1)
    ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn _)
    (intrinsicGeodesic_continuous g hEnorm p v).continuousOn
    (by simpa only [gamma, intrinsicGeodesic_zero] using hp)
    (by change gamma 1 ∈ S; rwa [hone]) t.property

theorem rayBusemannCore_spec
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) : (rayBusemannSublevel p 0).Nonempty ∧ IsCompact (rayBusemannSublevel p 0) ∧
      IsConnected (rayBusemannSublevel p 0) ∧ IsTotallyConvex (I := I) g (rayBusemannSublevel p 0) := by
  have hne : (rayBusemannSublevel p 0).Nonempty := ⟨p, self_mem_rayBusemannSublevel p le_rfl⟩
  have hconv : IsTotallyConvex (I := I) g (rayBusemannSublevel p 0) :=
    isTotallyConvex_rayBusemannSublevel g hEnorm hsec p 0
  exact ⟨hne, isCompact_rayBusemannSublevel g hEnorm hsec p 0,
    (hconv.isPathConnected g hEnorm hne).isConnected, hconv⟩

end DifferentialGeometry.Geometry.Topology
