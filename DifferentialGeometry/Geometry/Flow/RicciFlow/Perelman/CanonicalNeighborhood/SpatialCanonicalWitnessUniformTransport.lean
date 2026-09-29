import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessComparisonTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMargins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicNoncollapseLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem MetricComparisonOn.abs_metricScalarAt_sub_le_of_rm_bound
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : TopologicalSpace.Opens P} {order : ℕ}
    {delta K : ℝ} (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order delta)
    (hU : (U : Set P) ⊆ F.source) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 4)
    (horder : 2 ≤ order) {y : P} (hy : y ∈ U)
    (hK : Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ K) :
    |metricScalarAt g' (F y) - metricScalarAt g y| ≤ 243 * (delta + delta * (3 * K)) := by
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hK
  have hB : normSq0S g y 4 (metricRm04At g y) ≤ K ^ 2 := by
    have h0 := normSq0S_nonneg g y 4 (metricRm04At g y)
    have h1 := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (normSq0S g y 4 (metricRm04At g y))]
  have hop : ∀ a b c : TangentSpace I3 y,
      Real.sqrt (g.inner y (riemannOp (cov := LeviCivita g) y a b c)
          (riemannOp (cov := LeviCivita g) y a b c)) ≤
        K * Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) *
          Real.sqrt (g.inner y c c) := by
    intro a b c
    have hh := riemannOp_normSq_le_of_rmNormSq_le g y hB a b c
    refine (Real.sqrt_le_sqrt hh).trans (le_of_eq ?_)
    rw [Real.sqrt_mul' _ (inner_self_nonneg g y c), Real.sqrt_mul' _ (inner_self_nonneg g y b),
      Real.sqrt_mul' _ (inner_self_nonneg g y a), Real.sqrt_sq hK0]
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by
    rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
    norm_num
  have hRic : ∀ v w : TangentSpace I3 y, |ricciTensor g y v w| ≤
      (3 * K) * Real.sqrt (g.inner y v v) * Real.sqrt (g.inner y w w) := by
    intro v w
    have h := abs_ricciTensor_le_of_riemannOp_le g hop v w
    rwa [hdim] at h
  have hcmp := C.scalar_sub_le_of_ricci_bound U hU subset_rfl (mem_singleton 0) hdelta0
    (by linarith) horder hy hRic
  refine hcmp.trans ((scalarComparisonC_le hdelta0 hdelta (by positivity)).trans (le_of_eq ?_))
  norm_num

omit [SigmaCompactSpace N] in
theorem MetricComparisonOn.rmNormSq_image_le_of_mem_opens
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : TopologicalSpace.Opens P} {order : ℕ}
    {delta K : ℝ} (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order delta)
    (hU : (U : Set P) ⊆ F.source) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 10)
    (hK : 40 * delta ≤ K) (horder : 2 ≤ order) {y : P} (hy : y ∈ U)
    (hrm : normSq0S g y 4 (metricRm04At g y) ≤ K ^ 2) :
    normSq0S g' (F y) 4 (metricRm04At g' (F y)) ≤ 324 * K ^ 2 := by
  obtain ⟨g₀, -, hcomplete, -, -, -, -⟩ :=
    DifferentialGeometry.exists_riemannianMetricComplete_eqOn_of_isCompact g (isCompact_singleton (x := y))
  obtain ⟨R, hR, -, hball⟩ :=
    Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds g₀ y
      (U.isOpen.mem_nhds hy)
  have hyball : y ∈ riemannianClosedBallOf g₀ y R := by
    change riemannianEDistOf g₀ y y ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact zero_le
  exact (C.mono hball le_rfl le_rfl).rmNormSq_image_le_of_rmNormSq_le g₀ hcomplete y hR
    hdelta0 hdelta hK horder (mem_singleton 0) (hU hy) hyball hrm

theorem SpatialNeck.exists_scale_invariant_transport_tolerance {alpha Lam : ℝ} (ha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) (hLam : 1 ≤ Lam) {order : ℕ}
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order) :
    ∃ delta0 eta0 : ℝ, 0 < delta0 ∧ 0 < eta0 ∧
      ∀ (g : SmoothRiemannianMetric I3 P) (p : P) (nk : SpatialNeck g (neckModelTolerance alpha) p),
        (metricScalarAt g p)⁻¹ ≤ Lam →
      ∀ U : TopologicalSpace.Opens P,
        (∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ U) →
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
        [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
        (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order delta →
        |metricScalarAt g' (F p) - metricScalarAt g p| ≤ eta0 * metricScalarAt g p →
        ∃ nk' : SpatialNeck g' (2 * alpha) (F p), nk'.map = nk.map.trans F := by
  set target := neckSourceTolerance alpha
  have ht : 0 < target := neckSourceTolerance_pos ha
  set n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  have hLam0 : 0 < Lam := zero_lt_one.trans_le hLam
  have hpow : 1 ≤ Lam ^ order := one_le_pow₀ hLam
  refine ⟨target / (4 * Lam ^ order), min (1 / 2) (target / (2 * (n + 1))), by positivity,
    lt_min (by norm_num) (by positivity), ?_⟩
  intro g p nk hinv U hout N _ _ _ _ _ g' F hUF delta hdelta0 hdelta C hclose
  set q := metricScalarAt g p
  have hq : 0 < q := nk.Q_pos
  set c := metricScalarAt g' (F p)
  set eta := min (1 / 2) (target / (2 * (n + 1)))
  have hetaq : eta * q ≤ q / 2 := by
    have := mul_le_mul_of_nonneg_right (min_le_left (1 / 2 : ℝ) (target / (2 * (n + 1)))) hq.le
    linarith
  have hlow := (abs_le.mp hclose).1
  have hupp := (abs_le.mp hclose).2
  have hc : 0 < c := by linarith
  have hc2 : c ≤ 2 * q := by linarith
  have hratio : |c / q - 1| * n ≤ target / 2 := by
    have he : c / q - 1 = (c - q) / q := by field_simp
    rw [he, abs_div, abs_of_pos hq]
    have h1 : |c - q| / q ≤ target / (2 * (n + 1)) := by
      rw [div_le_iff₀ hq]
      have h2 := hclose.trans (mul_le_mul_of_nonneg_right
        (min_le_right (1 / 2 : ℝ) (target / (2 * (n + 1)))) hq.le)
      linarith
    calc |c - q| / q * n ≤ target / (2 * (n + 1)) * n :=
          mul_le_mul_of_nonneg_right h1 hn
      _ ≤ target / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
  have hcmp := C.staticRescale (t := 0) rfl q c hq hc ht.le (fun a ha' => by
    have hsq : Real.sqrt (q⁻¹ ^ (a + 2)) * c = Real.sqrt (q⁻¹ ^ a) * (q⁻¹ * c) := by
      rw [pow_add, Real.sqrt_mul (pow_nonneg hqinv.le a), Real.sqrt_sq hqinv.le]
      ring
    have hqc : q⁻¹ * c ≤ 2 := by
      rw [inv_mul_le_iff₀ hq]
      linarith
    have hroot : Real.sqrt (q⁻¹ ^ a) ≤ Lam ^ order := by
      have h1 : q⁻¹ ^ a ≤ Lam ^ a := pow_le_pow_left₀ hqinv.le hinv a
      have h2 : Lam ^ a ≤ Lam ^ order := pow_le_pow_right₀ hLam ha'
      calc Real.sqrt (q⁻¹ ^ a) ≤ Real.sqrt (Lam ^ order) := Real.sqrt_le_sqrt (h1.trans h2)
        _ ≤ Lam ^ order := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
    have hw : Real.sqrt (q⁻¹ ^ (a + 2)) * c * delta ≤ target / 2 := by
      rw [hsq]
      calc Real.sqrt (q⁻¹ ^ a) * (q⁻¹ * c) * delta ≤ Lam ^ order * 2 *
            (target / (4 * Lam ^ order)) :=
          mul_le_mul (mul_le_mul hroot hqc (by positivity) (by positivity)) hdelta hdelta0
            (by positivity)
        _ = target / 2 := by field_simp; ring
    linarith)
  exact nk.exists_transport_of_local_comparisons hc F hcmp ha hsmall ht.le le_rfl horder rfl
    hout hUF


omit [T2Space P] [SigmaCompactSpace P] in
private theorem SpatialNeck.map_mem_closedBall_of_mem_window {g : SmoothRiemannianMetric I3 P}
    {eps alpha : ℝ} {v : P} (nk : SpatialNeck g eps v) (heps : eps ≤ alpha)
    {y : Cylinder} (hy : y ∈ (univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ : Set Cylinder)) :
    nk.map y ∈ riemannianClosedBallOf g v
      ((alpha⁻¹ + 6) * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g v)) := by
  have hinv : alpha⁻¹ ≤ eps⁻¹ := inv_anti₀ nk.eps_pos heps
  have habs : |y.2| < alpha⁻¹ := abs_lt.mpr ⟨hy.2.1, hy.2.2⟩
  have hmem : y ∈ (univ ×ˢ Icc (-|y.2|) |y.2| : Set Cylinder) :=
    ⟨trivial, neg_abs_le _, le_abs_self _⟩
  have h := nk.image_slab_subset_closedBall (abs_nonneg _) (habs.trans_le hinv) ⟨y, hmem, rfl⟩
  refine riemannianClosedBallOf_mono g v ?_ h
  have hs : 0 ≤ Real.sqrt (1 + eps) := Real.sqrt_nonneg _
  have hq : 0 ≤ Real.sqrt (metricScalarAt g v) := Real.sqrt_nonneg _
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs) hq

private def SpatialLocalCap.singleNeckChain {g : SmoothRiemannianMetric I3 P}
    {eps eps0 eps' : ℝ} {x : P} {W : Set P} (L : SpatialLocalCap g eps x W)
    {g' : SmoothRiemannianMetric I3 N} (F : PartialDiffeomorph I3 I3 P N ∞)
    {v : P} (nk : SpatialNeck g eps0 v) (hnk : ∀ z, L.tubeMap z = nk.map z)
    (nk' : SpatialNeck g' eps' (F v)) (hmap : nk'.map = nk.map.trans F) :
    SpatialOrderedNeckChain g' eps' (F '' L.tube) where
  count := 1
  count_pos := one_pos
  centers _ := F v
  necks _ := nk'
  lo _ := 0
  hi _ := 1
  lo_lt_hi _ := one_pos
  inside _ := fun z hz => by
    have h11 : (11 : ℝ) < eps'⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk'.eps_pos).mpr (by linarith [nk'.eps_small])
    exact nk'.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  swept_eq := by
    change F '' L.tube = ⋃ _ : Fin 1, nk'.map '' (univ ×ˢ Icc (0 : ℝ) 1)
    rw [iUnion_const, hmap, partialDiffeomorph_image_trans, ← L.tube_eq]
    congr 1
    exact image_congr fun z _ => hnk z
  transition_increasing := by
    intro i j hij
    have := i.isLt
    have := j.isLt
    omega

private theorem sqrt_one_add_le_one_add {δ : ℝ} (hδ : 0 ≤ δ) : Real.sqrt (1 + δ) ≤ 1 + δ := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

private theorem nine_tenths_le_sqrt_one_sub {δ : ℝ} (hδ : δ ≤ 1 / 10) :
    9 / 10 ≤ Real.sqrt (1 - δ) :=
  Real.le_sqrt_of_sq_le (by linarith)

omit [T2Space P] [SigmaCompactSpace P] in
private theorem closedBall_center_mem (g : SmoothRiemannianMetric I3 P) (x : P) (R : ℝ) :
    x ∈ riemannianClosedBallOf (I := I3) g x R := by
  change riemannianEDistOf g x x ≤ ENNReal.ofReal R
  rw [riemannianEDistOf_self]
  exact zero_le

omit [SigmaCompactSpace N] in
private theorem edist_transfer_of_comparison_two_radius
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : Set P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : U ⊆ F.source) {x : P} {r Rb : ℝ} (hr : 0 < r) (hRb : 8 * r < Rb)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x Rb))
    (hball : riemannianClosedBallOf (I := I3) g x Rb ⊆ U) :
    ∀ a ∈ riemannianClosedBallOf (I := I3) g x (2 * r),
      ∀ b ∈ riemannianClosedBallOf (I := I3) g x (2 * r),
      ENNReal.ofReal (Real.sqrt (1 - δ)) * riemannianEDistOf (I := I3) g a b ≤
          riemannianEDistOf (I := I3) g' (F a) (F b) ∧
        riemannianEDistOf (I := I3) g' (F a) (F b) ≤
          ENNReal.ofReal (Real.sqrt (1 + δ)) * riemannianEDistOf (I := I3) g a b := by
  have hsp := sqrt_one_add_le_one_add hδ0
  have hsm := nine_tenths_le_sqrt_one_sub hδ
  have hRb0 : 0 < Rb := by linarith
  have hroom : Real.sqrt (1 + δ) * (3 * (2 * r)) < Real.sqrt (1 - δ) * Rb := by
    have h1 : Real.sqrt (1 + δ) * (3 * (2 * r)) ≤ 11 / 10 * (6 * r) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : 9 / 10 * Rb ≤ Real.sqrt (1 - δ) * Rb := mul_le_mul_of_nonneg_right hsm hRb0.le
    linarith
  exact crossModel_edist_transfer_of_comparison g g' F C x hRb0 hδ0 (by linarith)
    (by linarith : (0 : ℝ) ≤ 2 * r) hcpt hball (hball.trans hUF) hroom

private theorem one_le_margin_factor {m δ : ℝ} (hm : 0 < m) (hm1 : m ≤ 1 / 2)
    (hδ : δ ≤ m / 100000) : 1 ≤ (1 + m / 2) ^ 2 * (1 - δ) := by
  have h1 : 1 + m ≤ (1 + m / 2) ^ 2 := by nlinarith
  have h2 : (1 + m) * (1 - δ) ≤ (1 + m / 2) ^ 2 * (1 - δ) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : δ * (1 + m) ≤ m / 100000 * (1 + m) := mul_le_mul_of_nonneg_right hδ (by linarith)
  have h4 : m / 100000 * (1 + m) ≤ m := by nlinarith
  nlinarith

omit [SigmaCompactSpace N] in
private theorem ball_subset_image_of_comparison
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : Set P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : U ⊆ F.source) {x : P} {r m Rb : ℝ} {D : Set P} (hr : 0 < r) (hm : 0 < m)
    (hδ : δ ≤ m / 100000) (hm1 : m ≤ 1 / 2) (hRb : (1 + m / 2) * r ≤ Rb)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x Rb))
    (hball : riemannianClosedBallOf (I := I3) g x Rb ⊆ U)
    (hin : riemannianBallOf (I := I3) g x ((1 + m) * r) ⊆ D) :
    riemannianBallOf (I := I3) g' (F x) r ⊆ F '' D := by
  have hR0pos : 0 < (1 + m / 2) * r := by positivity
  have hpos : 0 < 1 - δ := by linarith
  have hLsq : 0 < (1 - δ)⁻¹ := inv_pos.mpr hpos
  have hL : 0 < Real.sqrt ((1 - δ)⁻¹) := Real.sqrt_pos.mpr hLsq
  have hsub : riemannianClosedBallOf (I := I3) g x ((1 + m / 2) * r) ⊆
      riemannianClosedBallOf (I := I3) g x Rb := riemannianClosedBallOf_mono g x hRb
  have hcpt0 : IsCompact (riemannianClosedBallOf (I := I3) g x ((1 + m / 2) * r)) :=
    hcpt.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf g x _) hsub
  have hsub0 := hsub.trans hball
  have hlower : ∀ y ∈ riemannianClosedBallOf (I := I3) g x ((1 + m / 2) * r),
      ∀ v : TangentSpace I3 y,
      g.inner y v v ≤ Real.sqrt ((1 - δ)⁻¹) ^ 2 * g'.inner (F y)
        (mfderiv I3 I3 (F : P → N) y v) (mfderiv I3 I3 (F : P → N) y v) := by
    intro y hy v
    have hyU := hsub0 hy
    have heq := C.pullback_eq 0 y hyU (fun _ => v)
    have hcm := (C.equivalence 0 rfl y hyU v).1
    rw [heq] at hcm
    rw [Real.sq_sqrt hLsq.le, ← div_eq_inv_mul, le_div_iff₀ hpos]
    linarith
  have hcap := ball_subset_image_of_metric_lower_crossModel g g' F x hR0pos hL hcpt0
    (hsub0.trans hUF) hlower
  have hrL : r ≤ (1 + m / 2) * r / Real.sqrt ((1 - δ)⁻¹) := by
    rw [le_div_iff₀ hL]
    have hLle : Real.sqrt ((1 - δ)⁻¹) ≤ 1 + m / 2 := by
      rw [Real.sqrt_le_left (by positivity), inv_le_iff_one_le_mul₀ hpos]
      have := one_le_margin_factor hm hm1 hδ
      linarith
    calc r * Real.sqrt ((1 - δ)⁻¹) ≤ r * (1 + m / 2) := mul_le_mul_of_nonneg_left hLle hr.le
      _ = (1 + m / 2) * r := by ring
  intro y' hy'
  obtain ⟨y, hy, rfl⟩ := hcap (riemannianBallOf_mono g' (F x) hrL hy')
  refine ⟨y, hin ?_, rfl⟩
  change riemannianEDistOf g x y < ENNReal.ofReal ((1 + m) * r)
  refine lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
  nlinarith

omit [SigmaCompactSpace N] in
private theorem image_subset_ball_of_comparison
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : Set P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : U ⊆ F.source) {x : P} {r m Rb : ℝ} {D : Set P} (hr : 0 < r) (hm : 0 < m)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ m / 100000) (hm1 : m ≤ 1 / 2) (hRb : 8 * r < Rb)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x Rb))
    (hball : riemannianClosedBallOf (I := I3) g x Rb ⊆ U)
    (hout : D ⊆ riemannianBallOf (I := I3) g x ((2 - m) * r)) :
    F '' D ⊆ riemannianBallOf (I := I3) g' (F x) (2 * r) := by
  have htr := edist_transfer_of_comparison_two_radius C hUF hr hRb hδ0 (by linarith) hcpt hball
  have hsp := sqrt_one_add_le_one_add hδ0
  rintro _ ⟨y, hy, rfl⟩
  have hyb := hout hy
  change riemannianEDistOf g x y < ENNReal.ofReal ((2 - m) * r) at hyb
  have hy2 : y ∈ riemannianClosedBallOf (I := I3) g x (2 * r) := by
    change riemannianEDistOf g x y ≤ ENNReal.ofReal (2 * r)
    exact hyb.le.trans (ENNReal.ofReal_le_ofReal (by have := mul_pos hm hr; linarith))
  have hfin : riemannianEDistOf g x y ≠ ⊤ := ne_top_of_lt hyb
  have hlt : (riemannianEDistOf g x y).toReal < (2 - m) * r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hyb
  have h := (htr x (closedBall_center_mem g x _) y hy2).2
  change riemannianEDistOf g' (F x) (F y) < ENNReal.ofReal (2 * r)
  refine lt_of_le_of_lt h ?_
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have ht0 := ENNReal.toReal_nonneg (a := riemannianEDistOf g x y)
  have h1 : Real.sqrt (1 + δ) * (riemannianEDistOf g x y).toReal ≤
      (1 + δ) * (riemannianEDistOf g x y).toReal := mul_le_mul_of_nonneg_right hsp ht0
  have h2 : (1 + δ) * (riemannianEDistOf g x y).toReal < (1 + δ) * ((2 - m) * r) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have hfac : (1 + δ) * (2 - m) ≤ 2 := by nlinarith [mul_nonneg hδ0 hm.le]
  have h3 : (1 + δ) * ((2 - m) * r) ≤ 2 * r := by
    have h := mul_le_mul_of_nonneg_right hfac hr.le
    linarith [show (1 + δ) * ((2 - m) * r) = (1 + δ) * (2 - m) * r by ring]
  linarith

private theorem depth_margin_real {m δ θ q q' : ℝ} (hm : 0 < m) (hm1 : m ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ m / 100000) (hθ0 : 0 ≤ θ) (hθ : θ ≤ m / 100000) (hq : 0 < q)
    (hq' : (1 - θ) * q ≤ q') :
    10000 / Real.sqrt q' ≤ Real.sqrt (1 - δ) * ((10000 + m) / Real.sqrt q) := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hq'0 : 0 < q' := by nlinarith
  have hsq' : 0 < Real.sqrt q' := Real.sqrt_pos.mpr hq'0
  have hkey : 10000 * Real.sqrt q ≤ Real.sqrt (1 - δ) * (10000 + m) * Real.sqrt q' := by
    have hprod : 100000000 * q ≤ (1 - δ) * (10000 + m) ^ 2 * q' := by
      have h1 : 1 - m / 50000 ≤ (1 - δ) * (1 - θ) := by nlinarith
      have hm2 : m ^ 2 ≤ m := by nlinarith
      have hm3 : m ^ 3 ≤ m ^ 2 := by nlinarith
      have h2 : 100000000 ≤ (1 - m / 50000) * (10000 + m) ^ 2 := by nlinarith
      have h3 : (1 - δ) * (10000 + m) ^ 2 * ((1 - θ) * q) ≤ (1 - δ) * (10000 + m) ^ 2 * q' :=
        mul_le_mul_of_nonneg_left hq' (by nlinarith)
      have h4 : 100000000 * q ≤ (1 - δ) * (1 - θ) * (10000 + m) ^ 2 * q := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (10000 + m) ^ 2 * q)
        nlinarith
      nlinarith
    have hL : 0 ≤ 10000 * Real.sqrt q := by positivity
    have hR : 0 ≤ Real.sqrt (1 - δ) * (10000 + m) * Real.sqrt q' := by positivity
    rw [← pow_le_pow_iff_left₀ hL hR (by norm_num : (2 : ℕ) ≠ 0), mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt hq.le, Real.sq_sqrt hq'0.le, Real.sq_sqrt (by linarith)]
    nlinarith
  rw [div_le_iff₀ hsq', mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hsq]
  linarith

omit [SigmaCompactSpace N] in
private theorem depth_image_of_comparison
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : Set P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : U ⊆ F.source) {x : P} {r m θ Rb : ℝ} {T : Set P} (hr : 0 < r) (hm : 0 < m)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ m / 100000) (hm1 : m ≤ 1 / 2) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ m / 100000) (hRb : 8 * r < Rb)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x Rb))
    (hball : riemannianClosedBallOf (I := I3) g x Rb ⊆ U) (hq : 0 < metricScalarAt g x)
    (hq' : (1 - θ) * metricScalarAt g x ≤ metricScalarAt g' (F x))
    (hT : T ⊆ riemannianBallOf (I := I3) g x (2 * r))
    (hdeep : ∀ y ∈ T,
      (10000 + m) / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y) :
    ∀ y ∈ F '' T, 10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y := by
  have htr := edist_transfer_of_comparison_two_radius C hUF hr hRb hδ0 (by linarith) hcpt hball
  rintro _ ⟨y, hy, rfl⟩
  have hyb : riemannianEDistOf g x y < ENNReal.ofReal (2 * r) := hT hy
  have hfin : riemannianEDistOf g x y ≠ ⊤ := ne_top_of_lt hyb
  have hy2 : y ∈ riemannianClosedBallOf (I := I3) g x (2 * r) := hyb.le
  have h := htr x (closedBall_center_mem g x _) y hy2
  have hfin' : riemannianEDistOf g' (F x) (F y) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h.2
  have hlow : Real.sqrt (1 - δ) * metricDistance g x y ≤ metricDistance g' (F x) (F y) := by
    have := ENNReal.toReal_mono hfin' h.1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  calc 10000 / Real.sqrt (metricScalarAt g' (F x))
      ≤ Real.sqrt (1 - δ) * ((10000 + m) / Real.sqrt (metricScalarAt g x)) :=
        depth_margin_real hm hm1 hδ0 hδ hθ0 hθ hq hq'
    _ ≤ Real.sqrt (1 - δ) * metricDistance g x y :=
        mul_le_mul_of_nonneg_left (hdeep y hy) (Real.sqrt_nonneg _)
    _ ≤ metricDistance g' (F x) (F y) := hlow


omit [SigmaCompactSpace N] in
private theorem rm_image_le_of_comparison
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : TopologicalSpace.Opens P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : (U : Set P) ⊆ F.source) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) (horder : 2 ≤ order)
    {y : P} (hy : y ∈ U) {K : ℝ} (hK : 40 * δ ≤ K)
    (hrm : Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) :
    Real.sqrt (normSq0S g' (F y) 4 (metricRm04 g' (F y))) ≤ 18 * K := by
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hrm
  rw [metricRm04_apply] at hrm ⊢
  have hB : normSq0S g y 4 (metricRm04At g y) ≤ K ^ 2 := by
    have h0 := normSq0S_nonneg g y 4 (metricRm04At g y)
    have h1 := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (normSq0S g y 4 (metricRm04At g y))]
  have h := C.rmNormSq_image_le_of_mem_opens hUF hδ0 hδ hK horder hy hB
  calc Real.sqrt (normSq0S g' (F y) 4 (metricRm04At g' (F y))) ≤ Real.sqrt ((18 * K) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = 18 * K := Real.sqrt_sq (by positivity)

private theorem volume_image_lower_of_comparison
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : TopologicalSpace.Opens P} {order : ℕ} {δ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : (U : Set P) ⊆ F.source) {D : Set P} (hD : IsCompact D) (hDU : D ⊆ U)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) {q q' C2 C2' : ℝ} (hq : 0 < q) (hq' : q / 2 ≤ q')
    (hC2 : 1 ≤ C2) (hC2' : 1000 * C2 ≤ C2')
    (hvol : ENNReal.ofReal (C2⁻¹ / (q * Real.sqrt q)) ≤ riemannianVolumeMeasure I3 P g D) :
    ENNReal.ofReal (C2'⁻¹ / (q' * Real.sqrt q')) ≤
      riemannianVolumeMeasure I3 N g' ((F : P → N) '' D) := by
  have hV := MetricComparisonOn.volume_image_ge F C rfl hδ0 (by linarith) U.isOpen subset_rfl
    hUF hD hDU
  have hdim : Module.finrank ℝ ThreeSpace = 3 := finrank_euclideanSpace_fin
  rw [hdim] at hV
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hZ : 0 < q * Real.sqrt q := mul_pos hq hsq
  have hq'0 : 0 < q' := by linarith
  have hsq' : Real.sqrt q / 2 ≤ Real.sqrt q' := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hq.le]
    linarith
  have hZ' : q * Real.sqrt q / 4 ≤ q' * Real.sqrt q' := by
    have := mul_le_mul hq' hsq' (by positivity) hq'0.le
    linarith
  have hC2pos : 0 < C2 := by linarith
  have hinv : C2'⁻¹ ≤ (1000 * C2)⁻¹ := inv_anti₀ (by positivity) hC2'
  have hL : C2'⁻¹ / (q' * Real.sqrt q') ≤ (1000 * C2)⁻¹ / (q * Real.sqrt q / 4) :=
    div_le_div₀ (by positivity) hinv (by positivity) hZ'
  have he : (1000 * C2)⁻¹ / (q * Real.sqrt q / 4) = 1 / 250 * (C2⁻¹ / (q * Real.sqrt q)) := by
    field_simp
    ring
  have hs : 1 / 2 ≤ Real.sqrt ((1 - δ) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    have h1 : (9 / 10 : ℝ) ^ 3 ≤ (1 - δ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith
  have hX : 0 ≤ C2⁻¹ / (q * Real.sqrt q) := by positivity
  have hreal : C2'⁻¹ / (q' * Real.sqrt q') ≤
      Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (q * Real.sqrt q)) := by
    have h2 : 1 / 2 * (C2⁻¹ / (q * Real.sqrt q)) ≤
        Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (q * Real.sqrt q)) := mul_le_mul_of_nonneg_right hs hX
    rw [he] at hL
    nlinarith
  calc ENNReal.ofReal (C2'⁻¹ / (q' * Real.sqrt q'))
      ≤ ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (q * Real.sqrt q))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3)) * ENNReal.ofReal (C2⁻¹ / (q * Real.sqrt q)) :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ ≤ ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3)) * riemannianVolumeMeasure I3 P g D :=
        mul_le_mul' le_rfl hvol
    _ ≤ _ := hV

private theorem scalar_bounds_real {a a' q q' θ C2 C2' : ℝ} (hq : 0 < q) (hC2 : 1 ≤ C2)
    (hC2' : 1000 * C2 ≤ C2') (hθ : θ ≤ 1 / (2 * C2)) (hlo : C2⁻¹ * q ≤ a)
    (hhi : a ≤ C2 * q) (hclose : |a' - a| ≤ θ * q) (hq'2 : q / 2 ≤ q') (hq'4 : q' ≤ 2 * q) :
    C2'⁻¹ * q' ≤ a' ∧ a' ≤ C2' * q' := by
  have hC2pos : 0 < C2 := by linarith
  have hk : 1 / (2 * C2) = C2⁻¹ / 2 := by field_simp
  rw [hk] at hθ
  have hinv : C2'⁻¹ ≤ C2⁻¹ / 1000 := by
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (by linarith)
  have hq'0 : 0 ≤ q' := by linarith
  have h1 : C2'⁻¹ * q' ≤ C2⁻¹ / 1000 * (2 * q) :=
    mul_le_mul hinv hq'4 hq'0 (by positivity)
  have h2 : θ * q ≤ C2⁻¹ / 2 * q := mul_le_mul_of_nonneg_right hθ hq.le
  have h3 := abs_le.mp hclose
  have hθ1 : θ ≤ C2 := by
    have : C2⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC2
    linarith
  have h4 : θ * q ≤ C2 * q := mul_le_mul_of_nonneg_right hθ1 hq.le
  have h5 : C2 * q ≤ 2 * (C2 * q') := by nlinarith
  have h6 : 4 * (C2 * q') ≤ C2' * q' := by nlinarith
  constructor <;> nlinarith

private theorem radius_bounds_real {m θ q q' r C1 : ℝ} (hm : 0 < m) (hm1 : m ≤ 1 / 2)
    (hθ : θ ≤ m / 100000) (hq : 0 < q) (hq'lo : (1 - θ) * q ≤ q')
    (hq'4 : q' ≤ 2 * q) (hrad : (1 + m) / Real.sqrt q ≤ r) (hrC : r ≤ C1 / Real.sqrt q) :
    (Real.sqrt q')⁻¹ ≤ r ∧ r ≤ 2 * C1 / Real.sqrt q' := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hfac := one_le_margin_factor hm hm1 hθ
  have hq' : 0 < q' := by nlinarith
  have hsq' : 0 < Real.sqrt q' := Real.sqrt_pos.mpr hq'
  constructor
  · have h1 : q ≤ ((1 + m) * Real.sqrt q') ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq'.le]
      have h2 : (1 + m / 2) ^ 2 ≤ (1 + m) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h3 : q ≤ (1 + m / 2) ^ 2 * (1 - θ) * q := le_mul_of_one_le_left hq.le hfac
      have h4 : (1 + m / 2) ^ 2 * (1 - θ) * q ≤ (1 + m / 2) ^ 2 * q' := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hq'lo (by positivity)
      have h5 : (1 + m / 2) ^ 2 * q' ≤ (1 + m) ^ 2 * q' := mul_le_mul_of_nonneg_right h2 hq'.le
      linarith
    have h6 : Real.sqrt q ≤ (1 + m) * Real.sqrt q' := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (1 + m) * Real.sqrt q')]
      exact Real.sqrt_le_sqrt h1
    refine le_trans ?_ hrad
    rw [inv_eq_one_div, div_le_div_iff₀ hsq' hsq]
    linarith
  · have hC1 : 0 ≤ C1 := by
      have hr : 0 ≤ r := (div_nonneg (by linarith) hsq.le).trans hrad
      have := hr.trans hrC
      rwa [le_div_iff₀ hsq, zero_mul] at this
    have h7 : Real.sqrt q' ≤ 2 * Real.sqrt q := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt q), mul_pow,
        Real.sq_sqrt hq.le]
      exact Real.sqrt_le_sqrt (by linarith)
    refine hrC.trans ?_
    rw [div_le_div_iff₀ hsq hsq']
    nlinarith

omit [T2Space P] [SigmaCompactSpace P] in
private theorem neck_window_subset_closedBall {g : SmoothRiemannianMetric I3 P}
    {eps alpha : ℝ} {x v : P} (nk : SpatialNeck g eps v) (heps : eps ≤ alpha) {d s : ℝ}
    (hv : riemannianEDistOf (I := I3) g x v ≤ ENNReal.ofReal d) (hd : 0 ≤ d)
    (hs : d + (alpha⁻¹ + 6) * (3 / 2) / Real.sqrt (metricScalarAt g v) ≤ s) :
    ∀ y ∈ (univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ : Set Cylinder),
      nk.map y ∈ riemannianClosedBallOf (I := I3) g x s := by
  intro y hy
  have h := nk.map_mem_closedBall_of_mem_window heps hy
  have hai : 0 < alpha⁻¹ := inv_pos.mpr (nk.eps_pos.trans_le heps)
  have hsqv : 0 ≤ Real.sqrt (metricScalarAt g v) := Real.sqrt_nonneg _
  have h32 : Real.sqrt (1 + eps) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [nk.eps_small]
  have hw : (alpha⁻¹ + 6) * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g v) ≤
      (alpha⁻¹ + 6) * (3 / 2) / Real.sqrt (metricScalarAt g v) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h32 (by linarith)) hsqv
  have hw0 : 0 ≤ (alpha⁻¹ + 6) * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g v) := by
    positivity
  change riemannianEDistOf g x (nk.map y) ≤ ENNReal.ofReal s
  refine (riemannianEDistOf_triangle g x v (nk.map y)).trans ?_
  refine (add_le_add hv h).trans ?_
  rw [← ENNReal.ofReal_add hd hw0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem exists_spatialCanonicalWitness_of_bounds {g' : SmoothRiemannianMetric I3 N}
    {eps C1 C2 : ℝ} {x : N} (heps : 0 < eps) (heps1 : eps < 1)
    (hQ : 0 < metricScalarAt g' x) (K : CompactDomain N) (hx : x ∈ interior K.carrier)
    {r : ℝ} (hr1 : (Real.sqrt (metricScalarAt g' x))⁻¹ ≤ r)
    (hr2 : r ≤ C1 / Real.sqrt (metricScalarAt g' x))
    (hin : riemannianBallOf (I := I3) g' x r ⊆ K.carrier)
    (hout : K.carrier ⊆ riemannianBallOf (I := I3) g' x (2 * r))
    (hsc : ∀ y ∈ K.carrier, C2⁻¹ * metricScalarAt g' x ≤ metricScalarAt g' y ∧
      metricScalarAt g' y ≤ C2 * metricScalarAt g' x)
    (hrm : ∀ y ∈ K.carrier,
      Real.sqrt (normSq0S (I := I3) g' y 4 (metricRm04 g' y)) ≤ C2 * metricScalarAt g' x)
    (hvol : ENNReal.ofReal (C2⁻¹ / (metricScalarAt g' x * Real.sqrt (metricScalarAt g' x))) ≤
      riemannianVolumeMeasure I3 N g' K.carrier)
    (hgrad : ∀ v : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') x v)| ≤
        C2 * metricScalarAt g' x * Real.sqrt (metricScalarAt g' x) * Real.sqrt (g'.inner x v v))
    (A : SpatialCanonicalAlternative g' eps C2 x K.carrier)
    (hA : ∀ (cap : SpatialLocalCap g' eps x K.carrier)
      (depth : ∀ y ∈ cap.tube, 10000 / Real.sqrt (metricScalarAt g' x) ≤ metricDistance g' x y),
      A = .cap cap depth → ∃ (v : N) (nk : SpatialNeck g' eps v), ∀ z, cap.tubeMap z = nk.map z) :
    ∃ W : SpatialCanonicalWitness g' eps C1 C2 x, W.capTubeHasNeckChart eps ∧ W.domain = K :=
  ⟨{ Q_pos := hQ
     eps_pos := heps
     eps_lt_one := heps1
     domain := K
     center_inside := hx
     radius := r
     radius_lower := hr1
     radius_upper := hr2
     ball_inside := hin
     inside_ball := hout
     scalar_bounds := hsc
     rm_bound := hrm
     alternative := A
     volume := fun _ => hvol
     gradient := hgrad }, hA, rfl⟩


private theorem window_radius_real {r C1 C2 ai q qv : ℝ} (hq : 0 < q) (hqv : q ≤ C2 * qv)
    (hC2 : 1 ≤ C2) (hC1 : 0 ≤ C1) (hai : 0 < ai) (hr : r ≤ C1 / Real.sqrt q) :
    2 * r + (ai + 6) * (3 / 2) / Real.sqrt qv ≤
      (8 * C1 + 3 * (ai + 7) * Real.sqrt C2) / Real.sqrt q := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hqv0 : 0 < qv := by
    by_contra hneg
    have h0 : C2 * qv ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hneg)
    linarith
  have hsqv : 0 < Real.sqrt qv := Real.sqrt_pos.mpr hqv0
  have hsC2 : 1 ≤ Real.sqrt C2 := Real.one_le_sqrt.mpr hC2
  have hroot : Real.sqrt q ≤ Real.sqrt C2 * Real.sqrt qv := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hqv
  have h1 : (ai + 6) * (3 / 2) / Real.sqrt qv ≤ (ai + 6) * (3 / 2) * Real.sqrt C2 / Real.sqrt q := by
    rw [div_le_div_iff₀ hsqv hsq]
    have h := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ (ai + 6) * (3 / 2))
    linarith [show (ai + 6) * (3 / 2) * Real.sqrt C2 * Real.sqrt qv =
      (ai + 6) * (3 / 2) * (Real.sqrt C2 * Real.sqrt qv) by ring]
  have h2 : 2 * r ≤ 2 * C1 / Real.sqrt q := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hr (by norm_num)
  have h3 : 2 * C1 / Real.sqrt q + (ai + 6) * (3 / 2) * Real.sqrt C2 / Real.sqrt q ≤
      (8 * C1 + 3 * (ai + 7) * Real.sqrt C2) / Real.sqrt q := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hsq.le
    nlinarith
  linarith

private theorem exists_transported_witness_of_alternative
    {g : SmoothRiemannianMetric I3 P} {g' : SmoothRiemannianMetric I3 N}
    {F : PartialDiffeomorph I3 I3 P N ∞} {U : TopologicalSpace.Opens P} {order : ℕ} {δ θ : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} order δ)
    (hUF : (U : Set P) ⊆ F.source) (horder2 : 2 ≤ order)
    {alpha m C1 C2 C2' : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (hm : 0 < m)
    (hm1 : m ≤ 1 / 2) (hC2 : 1 ≤ C2) (hC2' : 1000 * C2 ≤ C2') {x : P}
    (W : SpatialCanonicalWitness g (neckModelTolerance alpha) C1 C2 x) (hM : W.HasMargins m)
    {Rb : ℝ} (hRbr : 8 * W.radius < Rb)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x Rb))
    (hball : riemannianClosedBallOf (I := I3) g x Rb ⊆ U)
    (hdomF : W.domain.carrier ⊆ F.source) (hdomU : W.domain.carrier ⊆ U)
    (hδ0 : 0 < δ) (hδ10 : δ ≤ 1 / 10) (hδm : δ ≤ m / 100000)
    (hK : 40 * δ ≤ C2 * metricScalarAt g x) (hθm : θ ≤ m / 100000)
    (hθC : θ ≤ 1 / (2 * C2))
    (hscal : ∀ y ∈ W.domain.carrier,
      |metricScalarAt g' (F y) - metricScalarAt g y| ≤ θ * metricScalarAt g x)
    (hgrad : ∀ v : TangentSpace I3 (F x),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') (F x) v)| ≤
        C2' * metricScalarAt g' (F x) * Real.sqrt (metricScalarAt g' (F x)) *
          Real.sqrt (g'.inner (F x) v v))
    (A' : SpatialCanonicalAlternative g' (2 * alpha) C2' (F x) (F '' W.domain.carrier))
    (hA' : ∀ (cap : SpatialLocalCap g' (2 * alpha) (F x) (F '' W.domain.carrier))
      (depth : ∀ y ∈ cap.tube,
        10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y),
      A' = .cap cap depth →
        ∃ (v : N) (nk : SpatialNeck g' (2 * alpha) v), ∀ z, cap.tubeMap z = nk.map z) :
    ∃ W' : SpatialCanonicalWitness g' (2 * alpha) (2 * C1) C2' (F x),
      W'.capTubeHasNeckChart (2 * alpha) ∧ W'.domain.carrier = F '' W.domain.carrier := by
  obtain ⟨hshape, hrad, hin, hout, -⟩ := hM
  have hq : 0 < metricScalarAt g x := W.Q_pos
  have hsq : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hq
  have hr0 : 0 < W.radius := lt_of_lt_of_le (inv_pos.mpr hsq) W.radius_lower
  have hxdom : x ∈ W.domain.carrier := interior_subset W.center_inside
  have hqq := abs_le.mp (hscal x hxdom)
  have hθq : θ * metricScalarAt g x ≤ 1 / 2 * metricScalarAt g x :=
    mul_le_mul_of_nonneg_right (by linarith) hq.le
  have hq'lo : (1 - θ) * metricScalarAt g x ≤ metricScalarAt g' (F x) := by
    linarith [hqq.1]
  have hq'2 : metricScalarAt g x / 2 ≤ metricScalarAt g' (F x) := by linarith
  have hq'4 : metricScalarAt g' (F x) ≤ 2 * metricScalarAt g x := by linarith [hqq.2]
  have hq' : 0 < metricScalarAt g' (F x) := by linarith
  have hradii := radius_bounds_real hm hm1 hθm hq hq'lo hq'4 hrad W.radius_upper
  have hballin := ball_subset_image_of_comparison C hUF hr0 hm hδm hm1
    (by nlinarith) hcpt hball hin
  have hinside := image_subset_ball_of_comparison C hUF hr0 hm hδ0.le hδm hm1 hRbr hcpt hball
    hout
  have hvolW : ENNReal.ofReal (C2⁻¹ / (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 P g W.domain.carrier := by
    apply W.volume
    rcases hshape with ⟨n, hn⟩ | ⟨c, d, hcd⟩
    · rw [hn]
      trivial
    · rw [hcd]
      trivial
  have hvol := volume_image_lower_of_comparison C hUF W.domain.compact hdomU hδ0.le hδ10 hq hq'2
    hC2 hC2' hvolW
  have hsc : ∀ y ∈ F '' W.domain.carrier,
      C2'⁻¹ * metricScalarAt g' (F x) ≤ metricScalarAt g' y ∧
        metricScalarAt g' y ≤ C2' * metricScalarAt g' (F x) := by
    rintro _ ⟨y, hy, rfl⟩
    exact scalar_bounds_real hq hC2 hC2' hθC (W.scalar_bounds y hy).1
      (W.scalar_bounds y hy).2 (hscal y hy) hq'2 hq'4
  have hrmW : ∀ y ∈ F '' W.domain.carrier,
      Real.sqrt (normSq0S (I := I3) g' y 4 (metricRm04 g' y)) ≤
        C2' * metricScalarAt g' (F x) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := rm_image_le_of_comparison C hUF hδ0.le hδ10 horder2 (hdomU hy) hK
      (W.rm_bound y hy)
    have h3 : 36 * C2 * metricScalarAt g' (F x) ≤ C2' * metricScalarAt g' (F x) :=
      mul_le_mul_of_nonneg_right (by linarith) hq'.le
    have h4 : C2 * metricScalarAt g x ≤ C2 * (2 * metricScalarAt g' (F x)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hxint : F x ∈ interior (W.domain.map F hdomF).carrier := by
    rw [CompactDomain.map_carrier, ← partialDiffeomorph_image_interior_of_subset_source F hdomF]
    exact ⟨x, W.center_inside, rfl⟩
  obtain ⟨W', hW', hdom⟩ := exists_spatialCanonicalWitness_of_bounds (N := N)
    (by linarith : (0 : ℝ) < 2 * alpha) (by linarith) hq' (W.domain.map F hdomF) hxint
    hradii.1 hradii.2 hballin hinside hsc hrmW hvol hgrad A' hA'
  exact ⟨W', hW', by rw [hdom]; rfl⟩

omit [SigmaCompactSpace P] [SigmaCompactSpace N] in
private theorem transport_neck_alternative {g : SmoothRiemannianMetric I3 P}
    {g' : SmoothRiemannianMetric I3 N} {F : PartialDiffeomorph I3 I3 P N ∞} {x : P}
    {D : Set P} {eps alpha C2' : ℝ} (hD : IsCompact D) (hDF : D ⊆ F.source)
    (n : SpatialLocalNeck g eps x D) (nk' : SpatialNeck g' (2 * alpha) (F x))
    (hmap : nk'.map = n.neck.map.trans F) :
    ∃ A' : SpatialCanonicalAlternative g' (2 * alpha) C2' (F x) (F '' D),
      ∀ (cap : SpatialLocalCap g' (2 * alpha) (F x) (F '' D))
        (depth : ∀ y ∈ cap.tube,
          10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y),
        A' ≠ .cap cap depth := by
  have hc : IsCompact (F '' D) :=
    hD.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hDF)
  refine ⟨.neck { neck := nk', region_eq := ?_, boundary_eq := ?_ }, fun _ _ h => by cases h⟩
  · rw [hmap, partialDiffeomorph_image_trans]
    exact congrArg (fun s => F '' s) n.region_eq
  · rw [← partialDiffeomorph_image_frontier_of_subset_source F hDF hD.isClosed hc.isClosed, hmap,
      partialDiffeomorph_image_trans]
    exact congrArg (fun s => F '' s) n.boundary_eq

omit [SigmaCompactSpace P] [SigmaCompactSpace N] in
private theorem transport_cap_alternative {g : SmoothRiemannianMetric I3 P}
    {g' : SmoothRiemannianMetric I3 N} {F : PartialDiffeomorph I3 I3 P N ∞} {x : P}
    {D : Set P} {eps alpha C2' : ℝ} (hD : IsCompact D) (hDF : D ⊆ F.source)
    (c : SpatialLocalCap g eps x D)
    (hnk : ∃ (v : P) (nk : SpatialNeck g eps v), ∀ z, c.tubeMap z = nk.map z)
    (hnecktr : ∀ v ∈ D, ∀ nk : SpatialNeck g eps v,
      ∃ nk' : SpatialNeck g' (2 * alpha) (F v), nk'.map = nk.map.trans F)
    (hdepth : ∀ y ∈ F '' c.tube,
      10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y) :
    ∃ A' : SpatialCanonicalAlternative g' (2 * alpha) C2' (F x) (F '' D),
      ∀ (cap : SpatialLocalCap g' (2 * alpha) (F x) (F '' D))
        (depth : ∀ y ∈ cap.tube,
          10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y),
        A' = .cap cap depth →
          ∃ (v : N) (nk : SpatialNeck g' (2 * alpha) v), ∀ z, cap.tubeMap z = nk.map z := by
  obtain ⟨v, nk, hz⟩ := hnk
  have hvtube : v ∈ c.tube := by
    rw [← c.tube_eq, ← nk.center_eq, ← hz]
    exact ⟨(nk.center, 0), ⟨trivial, le_rfl, zero_le_one⟩, rfl⟩
  have hvD : v ∈ D := by
    rw [c.union_eq]
    exact Or.inr hvtube
  obtain ⟨nk', hmap⟩ := hnecktr v hvD nk
  let chain := c.singleNeckChain F nk hz nk' hmap
  let L' := c.pushforward F hDF hD chain
  refine ⟨.cap L' hdepth, ?_⟩
  intro cap depth h
  cases h
  refine ⟨F v, nk', fun z => ?_⟩
  change (c.tubeMap.trans F) z = nk'.map z
  rw [hmap, partialDiffeomorph_trans_apply, partialDiffeomorph_trans_apply, hz]

theorem SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance
    {alpha m C1 C2 Rlow : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hm : 0 < m) (hm1 : m ≤ 1 / 2) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (g : SmoothRiemannianMetric I3 P) (x : P)
      (W : SpatialCanonicalWitness g (neckModelTolerance alpha) C1 C2 x),
      W.capTubeHasNeckChart (neckModelTolerance alpha) → W.HasMargins m →
      Rlow ≤ metricScalarAt g x →
    ∀ U : TopologicalSpace.Opens P,
      IsCompact (riemannianClosedBallOf (I := I3) g x
        ((8 * C1 + 3 * (alpha⁻¹ + 7) * Real.sqrt C2) / Real.sqrt (metricScalarAt g x))) →
      riemannianClosedBallOf (I := I3) g x
        ((8 * C1 + 3 * (alpha⁻¹ + 7) * Real.sqrt C2) / Real.sqrt (metricScalarAt g x)) ⊆ U →
    ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
      [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
      (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
      MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} (max 2 ⌈(2 * alpha)⁻¹⌉₊) δ →
    ∀ C2' : ℝ, 1000 * C2 ≤ C2' →
      (∀ v : TangentSpace I3 (F x),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') (F x) v)| ≤
          C2' * metricScalarAt g' (F x) * Real.sqrt (metricScalarAt g' (F x)) *
            Real.sqrt (g'.inner (F x) v v)) →
      ∃ W' : SpatialCanonicalWitness g' (2 * alpha) (2 * C1) C2' (F x),
        W'.capTubeHasNeckChart (2 * alpha) ∧ W'.domain.carrier = F '' W.domain.carrier := by
  have horder2 : 2 ≤ max 2 ⌈(2 * alpha)⁻¹⌉₊ := le_max_left _ _
  have hordern : ⌈(2 * alpha)⁻¹⌉₊ ≤ max 2 ⌈(2 * alpha)⁻¹⌉₊ := le_max_right _ _
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  obtain ⟨dN, eN, hdN, heN, hneckT⟩ :=
    SpatialNeck.exists_scale_invariant_transport_tolerance (P := P) ha hsmall (le_max_left 1 (C2 / Rlow))
      hordern
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 243 * (Rlow⁻¹ + 3 * C2) := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  obtain ⟨θ0, hθ0def⟩ : ∃ θ0 : ℝ, θ0 = min (m / 100000) (min (1 / (2 * C2)) (eN / C2)) :=
    ⟨_, rfl⟩
  have hθ0 : 0 < θ0 := by
    rw [hθ0def]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨min (min dN (1 / 10)) (min (Rlow / 40) (min (m / 100000) (θ0 / A))),
    lt_min (lt_min hdN (by norm_num))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))), ?_⟩
  intro g x W hW hM hRx U hcpt hball N _ _ _ _ _ g' F hUF C C2' hC2' hgrad
  generalize hδdef : min (min dN (1 / 10)) (min (Rlow / 40) (min (m / 100000) (θ0 / A))) = δ
    at C
  have hδ0 : 0 < δ := by
    rw [← hδdef]
    exact lt_min (lt_min hdN (by norm_num))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hδN : δ ≤ dN := hδdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hδ10 : δ ≤ 1 / 10 := hδdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hδR : δ ≤ Rlow / 40 := hδdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδm : δ ≤ m / 100000 :=
    hδdef ▸ ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδA : δ ≤ θ0 / A :=
    hδdef ▸ ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hθ0le : A * δ ≤ θ0 := by
    have := mul_le_mul_of_nonneg_left hδA hA.le
    rwa [mul_div_cancel₀ _ hA.ne'] at this
  have hθpos : 0 < A * δ := mul_pos hA hδ0
  have hθm : A * δ ≤ m / 100000 := hθ0le.trans (hθ0def ▸ min_le_left _ _)
  have hθC : A * δ ≤ 1 / (2 * C2) :=
    hθ0le.trans (hθ0def ▸ (min_le_right _ _).trans (min_le_left _ _))
  have hAeN : A * δ * C2 ≤ eN := by
    have hθN : A * δ ≤ eN / C2 :=
      hθ0le.trans (hθ0def ▸ (min_le_right _ _).trans (min_le_right _ _))
    have := mul_le_mul_of_nonneg_right hθN hC2pos.le
    rwa [div_mul_cancel₀ _ hC2pos.ne'] at this
  have hq : 0 < metricScalarAt g x := W.Q_pos
  have hsq : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hq
  have hr0 : 0 < W.radius := lt_of_lt_of_le (inv_pos.mpr hsq) W.radius_lower
  have hC1' : 0 ≤ C1 := by linarith
  have hai : 0 < alpha⁻¹ := inv_pos.mpr ha
  obtain ⟨Rb, hRbdef⟩ : ∃ Rb : ℝ,
      Rb = (8 * C1 + 3 * (alpha⁻¹ + 7) * Real.sqrt C2) / Real.sqrt (metricScalarAt g x) :=
    ⟨_, rfl⟩
  rw [← hRbdef] at hcpt hball
  have hRbr : 8 * W.radius < Rb := by
    have h1 : 8 * W.radius ≤ 8 * C1 / Real.sqrt (metricScalarAt g x) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left W.radius_upper (by norm_num)
    have hsC2 : 1 ≤ Real.sqrt C2 := Real.one_le_sqrt.mpr hC2
    have h2 : 8 * C1 / Real.sqrt (metricScalarAt g x) < Rb := by
      rw [hRbdef]
      exact div_lt_div_of_pos_right (by nlinarith) hsq
    linarith
  have hdom2 : ∀ y ∈ W.domain.carrier,
      riemannianEDistOf (I := I3) g x y ≤ ENNReal.ofReal (2 * W.radius) := fun y hy =>
    le_of_lt (show riemannianEDistOf g x y < _ from W.inside_ball hy)
  have hdomU : W.domain.carrier ⊆ U := fun y hy =>
    hball (riemannianClosedBallOf_mono g x (by linarith) (hdom2 y hy :
      y ∈ riemannianClosedBallOf (I := I3) g x (2 * W.radius)))
  have hdomF : W.domain.carrier ⊆ F.source := hdomU.trans hUF
  have hRq : 1 ≤ Rlow⁻¹ * metricScalarAt g x := by
    rw [inv_mul_eq_div, one_le_div hRlow]
    exact hRx
  have hscal : ∀ y ∈ W.domain.carrier,
      |metricScalarAt g' (F y) - metricScalarAt g y| ≤ A * δ * metricScalarAt g x := by
    intro y hy
    have hrm := W.rm_bound y hy
    rw [metricRm04_apply] at hrm
    have h := C.abs_metricScalarAt_sub_le_of_rm_bound hUF hδ0.le (by linarith) horder2
      (hdomU hy) hrm
    have e : A * δ * metricScalarAt g x = 243 * (δ * (Rlow⁻¹ * metricScalarAt g x) +
        δ * (3 * (C2 * metricScalarAt g x))) := by
      rw [hAdef]
      ring
    have h1 : δ ≤ δ * (Rlow⁻¹ * metricScalarAt g x) := le_mul_of_one_le_right hδ0.le hRq
    rw [e]
    linarith
  have hK : 40 * δ ≤ C2 * metricScalarAt g x := by
    have h1 : Rlow ≤ C2 * metricScalarAt g x := hRx.trans (le_mul_of_one_le_left hq.le hC2)
    linarith
  have hnecktr : ∀ v ∈ W.domain.carrier, ∀ nk : SpatialNeck g (neckModelTolerance alpha) v,
      ∃ nk' : SpatialNeck g' (2 * alpha) (F v), nk'.map = nk.map.trans F := by
    intro v hv nk
    have hqv : metricScalarAt g x ≤ C2 * metricScalarAt g v := by
      have h := (W.scalar_bounds v hv).1
      rw [inv_mul_le_iff₀ hC2pos] at h
      exact h
    have hqv0 : 0 < metricScalarAt g v := by
      by_contra hneg
      have h0 : C2 * metricScalarAt g v ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hC2pos.le (not_lt.mp hneg)
      linarith
    have hLam : (metricScalarAt g v)⁻¹ ≤ max 1 (C2 / Rlow) := by
      refine le_trans ?_ (le_max_right _ _)
      rw [inv_le_comm₀ hqv0 (by positivity), inv_div, div_le_iff₀ hC2pos]
      linarith
    have hwin := neck_window_subset_closedBall nk (neckModelTolerance_le alpha) (s := Rb)
      (hdom2 v hv) (by linarith)
      (by rw [hRbdef]; exact window_radius_real hq hqv hC2 hC1' hai W.radius_upper)
    have hclose : |metricScalarAt g' (F v) - metricScalarAt g v| ≤ eN * metricScalarAt g v := by
      have h1 : A * δ * metricScalarAt g x ≤ A * δ * (C2 * metricScalarAt g v) :=
        mul_le_mul_of_nonneg_left hqv hθpos.le
      have h2 : A * δ * C2 * metricScalarAt g v ≤ eN * metricScalarAt g v :=
        mul_le_mul_of_nonneg_right hAeN hqv0.le
      linarith [hscal v hv, show A * δ * (C2 * metricScalarAt g v) =
        A * δ * C2 * metricScalarAt g v by ring]
    exact hneckT g v nk hLam U (fun y hy => hball (hwin y hy)) N g' F hUF δ hδ0.le hδN C hclose
  have hbuild := exists_transported_witness_of_alternative C hUF horder2 ha hsmall hm hm1 hC2
    hC2' W hM hRbr hcpt hball hdomF hdomU hδ0 hδ10 hδm hK hθm hθC hscal hgrad
  obtain ⟨hshape, -, -, -, hdeep⟩ := hM
  rcases hshape with ⟨n, hn⟩ | ⟨c, d, hcd⟩
  · obtain ⟨nk', hmap⟩ := hnecktr x (interior_subset W.center_inside) n.neck
    obtain ⟨A', hA'⟩ := transport_neck_alternative (C2' := C2') W.domain.compact hdomF n nk' hmap
    exact hbuild A' fun cap depth h => absurd h (hA' cap depth)
  · have hdepth := depth_image_of_comparison C hUF hr0 hm hδ0.le hδm hm1 hθpos.le hθm hRbr
      hcpt hball hq (by linarith [(abs_le.mp (hscal x (interior_subset W.center_inside))).1])
      (fun y hy => W.inside_ball (by rw [c.union_eq]; exact Or.inr hy)) (hdeep c d hcd)
    obtain ⟨A', hA'⟩ := transport_cap_alternative (C2' := C2') W.domain.compact hdomF c
      (hW c d hcd) hnecktr hdepth
    exact hbuild A' hA'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
