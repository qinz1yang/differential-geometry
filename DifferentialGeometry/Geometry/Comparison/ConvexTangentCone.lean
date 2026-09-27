import DifferentialGeometry.Geometry.Comparison.ConvexBoundarySupport
import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryConcavity

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

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
  [T2Space (TangentBundle I M)]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_neg_right (g : SmoothRiemannianMetric I M) (p : M)
    (a b : TangentSpace I p) : g.inner p a (-b) = -g.inner p a b := by
  rw [(g.inner p a).map_neg b]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_smul_right (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (a b : TangentSpace I p) : g.inner p a (r • b) = r * g.inner p a b := by
  rw [(g.inner p a).map_smul r b, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_sub_right (g : SmoothRiemannianMetric I M) (p : M)
    (a b d : TangentSpace I p) :
    g.inner p a (b - d) = g.inner p a b - g.inner p a d := by
  rw [(g.inner p a).map_sub]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem dist_intrinsicGeodesic_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (v : TangentSpace I p) {s t : ℝ}
    (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← riemannian_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]


private theorem tendsto_mul_nhdsGT_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s : ℝ => t * s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun s : ℝ => t * s) (𝓝 (0 : ℝ)) (𝓝 (t * 0)) :=
      (continuous_const.mul continuous_id).continuousAt
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos ht hs

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem sdiff_relBoundary {C : Set M} : C \ relBoundary I C = maxSliceLocus I C := by
  ext x
  constructor
  · rintro ⟨hxC, hx⟩
    by_contra hxN
    exact hx ⟨hxC, hxN⟩
  · intro hx
    exact ⟨maxSliceLocus_subset hx, fun h => h.2 hx⟩



theorem isInnerDirection_of_frequently
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M} (hp : p ∈ C)
    {v : TangentSpace I p}
    (hfreq : ∃ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C) :
    IsInnerDirection (I := I) g hEnorm C p v := by
  rw [isInnerDirection_iff]
  have hzero : intrinsicGeodesic (I := I) g hEnorm p v 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hcont : Continuous (intrinsicGeodesic (I := I) g hEnorm p v) :=
    intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hchord := minJoin_intrinsicGeodesic_near (I := I) (g := g) (hEnorm := hEnorm) v 0
    (standardDiagonalInverseBranch (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p v 0))
  have hmapchord : Tendsto (fun s : ℝ => (s, (0 : ℝ))) (𝓝 (0 : ℝ))
      (𝓝 ((0 : ℝ), (0 : ℝ))) := (continuous_id.prodMk continuous_const).continuousAt
  have hchord' : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ t : ℝ,
      minJoin (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p v 0)
          (intrinsicGeodesic (I := I) g hEnorm p v s) t =
        intrinsicGeodesic (I := I) g hEnorm p v (t * (s - 0) + 0) :=
    Eventually.filter_mono nhdsWithin_le_nhds (hmapchord.eventually hchord)
  have hmappair : Tendsto (fun s : ℝ =>
      (intrinsicGeodesic (I := I) g hEnorm p v s, p)) (𝓝 (0 : ℝ)) (𝓝 (p, p)) := by
    have h : Tendsto (fun s : ℝ => (intrinsicGeodesic (I := I) g hEnorm p v s, p))
        (𝓝 (0 : ℝ)) (𝓝 (intrinsicGeodesic (I := I) g hEnorm p v 0, p)) :=
      (hcont.prodMk continuous_const).continuousAt
    rwa [hzero] at h
  have hpair' : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C → p ∈ C →
        ∀ t ∈ Ioc (0 : ℝ) 1,
          minJoin (I := I) g hEnorm p (intrinsicGeodesic (I := I) g hEnorm p v s) t
            ∈ maxSliceLocus I C :=
    Eventually.filter_mono nhdsWithin_le_nhds
      (hmappair.eventually (maxSliceLocus_pair (C := C) hEnorm hC (standardDiagonalInverseBranch (I := I) g hEnorm p)))
  obtain ⟨s₀, hs₀N, hs₀chord, hs₀pair, hs₀pos⟩ :=
    (hfreq.and_eventually (hchord'.and (hpair'.and self_mem_nhdsWithin))).exists
  have hs₀ : (0 : ℝ) < s₀ := hs₀pos
  rw [hzero] at hs₀chord
  filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
  have hts : s / s₀ ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hs.1 hs₀, (div_le_one hs₀).2 hs.2.le⟩
  have hmem := hs₀pair hs₀N hp (s / s₀) hts
  rw [hs₀chord (s / s₀)] at hmem
  have harg : s / s₀ * (s₀ - 0) + 0 = s := by
    field_simp
    ring
  rwa [harg] at hmem

theorem eventually_not_mem_maxSliceLocus_of_not_isInnerDirection
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M} (hp : p ∈ C)
    {v : TangentSpace I p} (hv : ¬ IsInnerDirection (I := I) g hEnorm C p v) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      expMapIntrinsic (I := I) g hEnorm p (s • v) ∉ maxSliceLocus I C := by
  have hfreq : ¬ ∃ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C := fun h =>
    hv (isInnerDirection_of_frequently hEnorm hC hp h)
  rw [not_frequently] at hfreq
  filter_upwards [hfreq] with s hs
  rwa [expMapIntrinsic_smul_eq_intrinsicGeodesic]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem isInnerDirection_smul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} {p : M} {v : TangentSpace I p} {t : ℝ} (ht : 0 < t)
    (hv : IsInnerDirection (I := I) g hEnorm C p v) :
    IsInnerDirection (I := I) g hEnorm C p (t • v) := by
  rw [isInnerDirection_iff] at hv ⊢
  filter_upwards [(tendsto_mul_nhdsGT_zero ht).eventually hv] with s hs
  rwa [intrinsicGeo_smul_apply (I := I) g hEnorm p v t s]

theorem not_isInnerDirection_neg
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} (hp : p ∈ relBoundary I C) {v : TangentSpace I p}
    (hv : IsInnerDirection (I := I) g hEnorm C p v) :
    ¬ IsInnerDirection (I := I) g hEnorm C p (-v) := by
  intro hneg
  rw [isInnerDirection_iff] at hv hneg
  have hback : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v (-s) ∈ maxSliceLocus I C := by
    filter_upwards [hneg] with s hs
    rwa [intrinsicGeodesic_neg] at hs
  obtain ⟨s, hs, hns⟩ :=
    (hv.and (eventually_not_mem_maxSliceLocus_of_back hEnorm hC hp hback)).exists
  exact hns hs



def IsSupportingDirection (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) (p : M) (w : TangentSpace I p) :
    Prop :=
  g.inner p w w = 1 ∧ ∃ l : ℝ, 0 < l ∧
    intrinsicGeodesic (I := I) g hEnorm p w l ∈ maxSliceLocus I C ∧
    Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w l) (relBoundary I C) = l

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem isInnerDirection_of_isSupportingDirection
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M} (hp : p ∈ C)
    {w : TangentSpace I p} (hw : IsSupportingDirection (I := I) g hEnorm C p w) :
    IsInnerDirection (I := I) g hEnorm C p w := by
  obtain ⟨hwu, l, hl, hqN, hqd⟩ := hw
  rw [isInnerDirection_iff]
  have hmaps : MapsTo (intrinsicGeodesic (I := I) g hEnorm p w) (Icc (0 : ℝ) l) C :=
    hC hl.le ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p w).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p w).continuousOn
      (by rw [intrinsicGeodesic_zero]; exact hp) (maxSliceLocus_subset hqN)
  filter_upwards [Ioo_mem_nhdsGT hl] with t ht
  by_contra htN
  have hb : intrinsicGeodesic (I := I) g hEnorm p w t ∈ relBoundary I C :=
    ⟨hmaps ⟨ht.1.le, ht.2.le⟩, htN⟩
  have hdle : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w l) (relBoundary I C)
      ≤ dist (intrinsicGeodesic (I := I) g hEnorm p w l)
          (intrinsicGeodesic (I := I) g hEnorm p w t) :=
    Metric.infDist_le_dist_of_mem hb
  have hspeed := dist_intrinsicGeodesic_le g hEnorm p w ht.2.le
  rw [hwu, Real.sqrt_one, one_mul] at hspeed
  rw [hqd, dist_comm] at hdle
  linarith [ht.1]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem dist_eq_of_isSupportingDirection
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hwu : g.inner p w w = 1) {l : ℝ} (hl : 0 < l)
    (hqd : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w l)
      (relBoundary I C) = l) :
    dist p (intrinsicGeodesic (I := I) g hEnorm p w l) = l := by
  have h1 := dist_intrinsicGeodesic_le g hEnorm p w (s := (0 : ℝ)) (t := l) hl.le
  rw [intrinsicGeodesic_zero, hwu, Real.sqrt_one, one_mul, sub_zero] at h1
  have h2 := Metric.infDist_le_dist_of_mem
    (x := intrinsicGeodesic (I := I) g hEnorm p w l) hp
  rw [hqd, dist_comm] at h2
  linarith

omit [T2Space (TangentBundle I M)] in
theorem isInnerDirection_of_eventually_mem
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hw : IsSupportingDirection (I := I) g hEnorm C p w) {z : TangentSpace I p}
    (hzw : 0 < g.inner p z w)
    (hzC : ∀ᶠ s in 𝓝[>] (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p z s ∈ C) :
    IsInnerDirection (I := I) g hEnorm C p z := by
  obtain ⟨hwu, l, hl, hqN, hqd⟩ := hw
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [ContinuousLinearMap.map_zero, zero_apply] at hzw
    exact lt_irrefl 0 hzw
  have hzz : 0 < g.inner p z z := g.pos p z hzne
  set n : ℝ := Real.sqrt (g.inner p z z) with hndef
  have hn : 0 < n := Real.sqrt_pos.2 hzz
  have hnsq : n ^ 2 = g.inner p z z := Real.sq_sqrt hzz.le
  have hunit : g.inner p (n⁻¹ • z) (n⁻¹ • z) = 1 := by
    rw [gInner_smul_self (I := I) g p n⁻¹ z, ← hnsq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hn))]
  have hwz : 0 < g.inner p w (n⁻¹ • z) := by
    rw [gInner_smul_right, g.symm p w z]
    exact mul_pos (inv_pos.2 hn) hzw
  have hCmem : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p (n⁻¹ • z) s ∈ C := by
    filter_upwards [(tendsto_mul_nhdsGT_zero (inv_pos.2 hn)).eventually hzC] with s hs
    rwa [intrinsicGeo_smul_apply (I := I) g hEnorm p z n⁻¹ s]
  have hkey := eventually_mem_maxSliceLocus_of_inner_pos (C := C) g hEnorm hsec hl hwu hunit
    rfl (dist_eq_of_isSupportingDirection hp hwu hl hqd) hqd.ge hwz hCmem
  have hscaled : IsInnerDirection (I := I) g hEnorm C p (n⁻¹ • z) :=
    isInnerDirection_iff.2 hkey
  have hfinal := isInnerDirection_smul (t := n) hn hscaled
  rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul] at hfinal



def HasOpenTangentCone (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) : Prop :=
  ∀ p ∈ relBoundary I C, ∀ v w : TangentSpace I p,
    IsInnerDirection (I := I) g hEnorm C p v →
      IsInnerDirection (I := I) g hEnorm C p w →
        ∃ᶠ ε in 𝓝[>] (0 : ℝ), IsInnerDirection (I := I) g hEnorm C p (v - ε • w)

def HasAcuteTangentCone (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) : Prop :=
  ∀ p ∈ relBoundary I C, ∀ w : TangentSpace I p,
    IsSupportingDirection (I := I) g hEnorm C p w →
      ∀ v z : TangentSpace I p, IsInnerDirection (I := I) g hEnorm C p v →
        (∃ a b : ℝ, z = a • v + b • w) → 0 < g.inner p z w →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p z s ∈ C



theorem not_isInnerDirection_of_inner_lt_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hacute : HasAcuteTangentCone (I := I) g hEnorm C)
    {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hw : IsSupportingDirection (I := I) g hEnorm C p w)
    {v : TangentSpace I p} (hvw : g.inner p v w < 0) :
    ¬ IsInnerDirection (I := I) g hEnorm C p v := by
  intro hv
  have hspan : -v = (-1 : ℝ) • v + (0 : ℝ) • w := by
    rw [neg_one_smul, zero_smul, add_zero]
  have hzw : 0 < g.inner p (-v) w := by
    rw [g.symm p (-v) w, gInner_neg_right, g.symm p w v]
    linarith
  exact not_isInnerDirection_neg hEnorm hC hp hv
    (isInnerDirection_of_eventually_mem g hEnorm hsec hp hw hzw
      (hacute p hp w hw v (-v) hv ⟨-1, 0, hspan⟩ hzw))

theorem not_isInnerDirection_of_inner_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hopen : HasOpenTangentCone (I := I) g hEnorm C)
    (hacute : HasAcuteTangentCone (I := I) g hEnorm C)
    {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hw : IsSupportingDirection (I := I) g hEnorm C p w)
    {v : TangentSpace I p} (hvw : g.inner p v w ≤ 0) :
    ¬ IsInnerDirection (I := I) g hEnorm C p v := by
  intro hv
  have hwin : IsInnerDirection (I := I) g hEnorm C p w :=
    isInnerDirection_of_isSupportingDirection hC hp.1 hw
  obtain ⟨ε, hεin, hεpos⟩ :=
    ((hopen p hp v w hv hwin).and_eventually self_mem_nhdsWithin).exists
  have hε : (0 : ℝ) < ε := hεpos
  have hspan : -(v - ε • w) = (-1 : ℝ) • (v - ε • w) + (0 : ℝ) • w := by
    rw [neg_one_smul, zero_smul, add_zero]
  have hzw : 0 < g.inner p (-(v - ε • w)) w := by
    have hsymm : g.inner p (-(v - ε • w)) w = g.inner p w (-(v - ε • w)) :=
      g.symm p (-(v - ε • w)) w
    rw [hsymm, gInner_neg_right, gInner_sub_right, gInner_smul_right, hw.1,
      g.symm p w v]
    linarith
  exact not_isInnerDirection_neg hEnorm hC hp hεin
    (isInnerDirection_of_eventually_mem g hEnorm hsec hp hw hzw
      (hacute p hp w hw (v - ε • w) (-(v - ε • w)) hεin ⟨-1, 0, hspan⟩ hzw))

theorem eventually_not_mem_maxSliceLocus_of_inner_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hopen : HasOpenTangentCone (I := I) g hEnorm C)
    (hacute : HasAcuteTangentCone (I := I) g hEnorm C)
    {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hw : IsSupportingDirection (I := I) g hEnorm C p w)
    {v : TangentSpace I p} (hvw : g.inner p v w ≤ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      expMapIntrinsic (I := I) g hEnorm p (s • v) ∉ maxSliceLocus I C :=
  eventually_not_mem_maxSliceLocus_of_not_isInnerDirection hEnorm hC hp.1
    (not_isInnerDirection_of_inner_nonpos g hEnorm hsec hC hopen hacute hp hw hvw)

theorem hasSupportingHalfSpaces_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hopen : HasOpenTangentCone (I := I) g hEnorm C)
    (hacute : HasAcuteTangentCone (I := I) g hEnorm C) :
    HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C) := by
  intro q hq u hu hp v hvel
  have hqN : q ∈ maxSliceLocus I C := by
    rw [← sdiff_relBoundary (I := I) (C := C)]
    exact hq
  have hVeq : curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C))
      = mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
          (Metric.infDist q (relBoundary I C)) 1 := rfl
  rw [hVeq] at hvel
  have hlpos : 0 < Metric.infDist q (relBoundary I C) :=
    infDist_relBoundary_pos hEnorm hC hCclosed ⟨_, hp⟩ hqN
  have hspeed : g.inner (intrinsicGeodesic (I := I) g hEnorm q u
        (Metric.infDist q (relBoundary I C)))
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C)) 1)
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C)) 1) = 1 := by
    rw [intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q u
      (Metric.infDist q (relBoundary I C))]
    exact hu
  have hcontn : intrinsicGeodesic (I := I) g hEnorm q u
        (-Metric.infDist q (relBoundary I C) + Metric.infDist q (relBoundary I C))
      = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q (relBoundary I C)))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
            (Metric.infDist q (relBoundary I C)) 1)
          (-Metric.infDist q (relBoundary I C)) :=
    congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm q u
      (Metric.infDist q (relBoundary I C))) (-Metric.infDist q (relBoundary I C))
  have hback_eq : intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q (relBoundary I C)))
        (-(mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
          (Metric.infDist q (relBoundary I C)) 1))
        (Metric.infDist q (relBoundary I C)) = q := by
    rw [intrinsicGeodesic_neg, ← hcontn, neg_add_cancel, intrinsicGeodesic_zero]
  have hsupp : IsSupportingDirection (I := I) g hEnorm C
      (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q (relBoundary I C)))
      (-(mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C)) 1)) := by
    refine ⟨?_, Metric.infDist q (relBoundary I C), hlpos, ?_, ?_⟩
    · rw [← neg_one_smul ℝ (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C)) 1), gInner_smul_self (I := I) g _ (-1) _,
        hspeed]
      norm_num
    · rw [hback_eq]
      exact hqN
    · rw [hback_eq]
  have hvw : g.inner (intrinsicGeodesic (I := I) g hEnorm q u
        (Metric.infDist q (relBoundary I C))) v
      (-(mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u)
        (Metric.infDist q (relBoundary I C)) 1)) ≤ 0 := by
    rw [gInner_neg_right]
    linarith
  filter_upwards [eventually_not_mem_maxSliceLocus_of_inner_nonpos g hEnorm hsec hC hopen
    hacute hp hsupp hvw] with s hs
  rw [sdiff_relBoundary]
  exact hs

end DifferentialGeometry.Geometry.Topology
