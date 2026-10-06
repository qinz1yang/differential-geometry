import DifferentialGeometry.Geometry.Neck.BallVolume
import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Measure.RoundCylinderVolume
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

/-!
# CH12-O10, Group V: canonical neighbourhoods are not almost Euclidean

Input (V) of KL Sublemma 86.3 (frozen in DELIVERIES CH12-O10).  A point `x` with a spatial
canonical neighbourhood witness (constants `C1 C2`, neck accuracy `eps < 1/100`, cap tubes carried
by a neck chart, as supplied by `AnalyticSurgeryProfile.canonical`) has, within distance
`L / √R(x)`, a ball of radius `ρ ≤ L / √R(x)` whose volume is `< ρ³`; here `L` depends only on
`C1, C2`.  Since `(1 - ε) ω₃ ≥ 1` for `ε ≤ 3/4`, such a ball is not `(1 - ε)`-Euclidean.

* `spatialNeck_ball_volume_lt_O10`: on an `eps`-neck centred at `p`, the ball of radius
  `30 / √R(p)` has volume `< (30 / √R(p))³` (the normalised ball of radius 30 lies in the image of
  `S² × [-60, 60]`, of volume `≤ (1 + eps)^{3/2} · 8π · 120`).
* neck alternative: the neck at `x`; cap alternative: the tube neck chart centred at a tube point
  `v` with `R(v) ≥ C2⁻¹ R(x)`; positive / round alternatives: the domain is the whole component,
  so every ball about `x` lies in `B(x, 2C1/√R)`, whose volume is bounded by Bishop–Gromov with
  `sec ≥ -C2 R(x)` from the curvature bound of the witness.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

private theorem cylinder_metric_zero_eq_round_O10 (C : CylinderReference) :
    C.metric 0 = Geometry.Metric.roundCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := C.inner_eq 0 le_rfl z v w
  apply hC.trans
  rw [Geometry.Metric.roundCylinderMetric_inner]
  simp only [sub_zero, mul_one]
  rfl

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **V1.** Volume deficit on a neck: `vol B(p, 30/√R(p)) < (30/√R(p))³`. -/
theorem spatialNeck_ball_volume_lt_O10 {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (heps : eps < 1 / 100) :
    ballVolume g p (30 / Real.sqrt (metricScalarAt g p)) <
      ENNReal.ofReal ((30 / Real.sqrt (metricScalarAt g p)) ^ 3) := by
  set Q := metricScalarAt g p with hQdef
  have hQ : 0 < Q := nk.Q_pos
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  set gn := scaleMetric Q nk.Q_pos g with hgn
  set ρ := 30 / Real.sqrt Q with hρ
  have hρpos : 0 < ρ := by positivity
  have hsρ : Real.sqrt Q * ρ = 30 := by rw [hρ]; field_simp
  have hdimM : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscale := ballVolume_scaleMetric hdimM Q nk.Q_pos g p ρ
  rw [hsρ] at hscale
  -- the normalised ball lies in the image of a compact slab
  have hepspos := nk.eps_pos
  have hinv : (100 : ℝ) < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hepspos]; linarith
  have hball : riemannianBallOf gn p 30 ⊆ nk.map '' (univ ×ˢ Icc (-60) 60) := by
    have h := nk.ball_subset_closed_slab (r := 60) (by norm_num) (by linarith)
    have h30 : (60 : ℝ) / 2 = 30 := by norm_num
    rw [h30] at h
    exact h
  let K : Set Cylinder := univ ×ˢ Icc (-60 : ℝ) 60
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hKV : K ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    rintro z ⟨-, hz1, hz2⟩
    exact ⟨mem_univ _, by linarith, by linarith⟩
  have hle := MetricComparisonOn.volume_image_le nk.map nk.comparison
    (by simp : (0 : ℝ) ∈ ({0} : Set ℝ)) hepspos.le (by linarith)
    (isOpen_univ.prod isOpen_Ioo) Subset.rfl nk.domain hK hKV
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at hle
  have hcyl : riemannianVolumeMeasure IC Cylinder (nk.cylinder.metric 0) K =
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (60 - (-60)) := by
    rw [cylinder_metric_zero_eq_round_O10 nk.cylinder]
    exact Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval (-60) 60
  rw [hcyl] at hle
  have hfac : Real.sqrt ((1 + eps) ^ 3) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have h1 : 1 + eps ≤ 101 / 100 := by linarith
    have h0 : 0 ≤ 1 + eps := by linarith
    have := pow_le_pow_left₀ h0 h1 3
    nlinarith
  have hpi : Real.pi < 4 := by linarith [Real.pi_lt_d2]
  have hupper : ENNReal.ofReal (Real.sqrt Q) ^ 3 * ballVolume g p ρ ≤ ENNReal.ofReal 7680 := by
    rw [← hscale]
    calc ballVolume gn p 30
        ≤ riemannianVolumeMeasure I3 M gn (nk.map '' K) := measure_mono hball
      _ ≤ _ := hle
      _ = ENNReal.ofReal (Real.sqrt ((1 + eps) ^ 3) * (8 * Real.pi) * (60 - (-60))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal 7680 := by
        apply ENNReal.ofReal_le_ofReal
        have h8 : 8 * Real.pi ≤ 32 := by linarith
        calc Real.sqrt ((1 + eps) ^ 3) * (8 * Real.pi) * (60 - (-60))
            ≤ 2 * 32 * 120 := by
              have := Real.sqrt_nonneg ((1 + eps) ^ 3)
              have hp := Real.pi_pos
              nlinarith
          _ = 7680 := by norm_num
  have htarget : ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal (ρ ^ 3) =
      ENNReal.ofReal 27000 := by
    rw [← ENNReal.ofReal_pow hsQ.le, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, hsρ]
    norm_num
  have hlt : ENNReal.ofReal (Real.sqrt Q) ^ 3 * ballVolume g p ρ <
      ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal (ρ ^ 3) := by
    rw [htarget]
    exact hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))
  have h0 : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hsQ))
  have htop : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_lt_mul_iff_right h0 htop).1 hlt

/-- Neck / cap case: a neck centred at a point `v` of the witness domain. -/
private theorem neck_case_O10 {g : SmoothRiemannianMetric I3 M} {eps C1 C2 L : ℝ} {x v : M}
    (heps : eps < 1 / 100) (nk : SpatialNeck g eps v) (hR : 0 < metricScalarAt g x)
    (hC2 : 0 < C2) (hRv : C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g v)
    (hdist : riemannianEDistOf g x v ≤ ENNReal.ofReal (2 * C1 / Real.sqrt (metricScalarAt g x)))
    (hL1 : 30 * Real.sqrt C2 ≤ L) (hL2 : 2 * C1 ≤ L) :
    ∃ z : M, ∃ ρ : ℝ, riemannianEDistOf g x z ≤
        ENNReal.ofReal (L / Real.sqrt (metricScalarAt g x)) ∧
      0 < ρ ∧ ρ ≤ L / Real.sqrt (metricScalarAt g x) ∧
      ballVolume g z ρ < ENNReal.ofReal (ρ ^ 3) := by
  have hsR : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hR
  have hRv0 : 0 < metricScalarAt g v := nk.Q_pos
  have hsRv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr hRv0
  refine ⟨v, 30 / Real.sqrt (metricScalarAt g v), ?_, div_pos (by norm_num) hsRv, ?_,
    spatialNeck_ball_volume_lt_O10 nk heps⟩
  · exact hdist.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hL2 hsR.le))
  · have hRR : metricScalarAt g x ≤ C2 * metricScalarAt g v := by
      have := mul_le_mul_of_nonneg_left hRv hC2.le
      rwa [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at this
    have hsq : Real.sqrt (metricScalarAt g x) ≤
        Real.sqrt C2 * Real.sqrt (metricScalarAt g v) := by
      rw [← Real.sqrt_mul hC2.le]
      exact Real.sqrt_le_sqrt hRR
    rw [div_le_div_iff₀ hsRv hsR]
    calc 30 * Real.sqrt (metricScalarAt g x)
        ≤ 30 * (Real.sqrt C2 * Real.sqrt (metricScalarAt g v)) := by linarith
      _ = (30 * Real.sqrt C2) * Real.sqrt (metricScalarAt g v) := by ring
      _ ≤ L * Real.sqrt (metricScalarAt g v) := mul_le_mul_of_nonneg_right hL1 hsRv.le

omit [T2Space M] [SigmaCompactSpace M] in
private theorem mem_ball_mono_O10 {g : SmoothRiemannianMetric I3 M} {x y : M} {r s : ℝ}
    (hy : y ∈ riemannianBallOf g x r) (hrs : r ≤ s) : y ∈ riemannianBallOf g x s :=
  lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hrs)

/-- Local Bishop–Gromov upper bound without `ConnectedSpace`: pass to the component of `x`. -/
theorem ballVolume_le_modelVolume_component_O10 (g : SmoothRiemannianMetric I3 M)
    (hg : RiemannianMetricComplete (I := I3) g) (x : M) {κ s : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s)
    (hsec : ∀ q ∈ riemannianBallOf g x s, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g x s ≤ ENNReal.ofReal (VolumeComparison.modelVolume (-κ) 3 s) := by
  let C := connectedComponentOpen (I := I3) x
  have : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := I3) x
  have : SigmaCompactSpace C :=
    (show IsClosed (C : Set M) from isClosed_connectedComponent).sigmaCompactSpace
  let xC : C := ⟨x, mem_connectedComponent⟩
  have hgC := Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen g x hg
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hballC : (Subtype.val : C → M) ⁻¹' riemannianBallOf g x s =
      riemannianBallOf (g.restrictOpen C) xC s := by
    ext q
    change riemannianEDistOf g x q < _ ↔ riemannianEDistOf (g.restrictOpen C) xC q < _
    rw [Geometry.Metric.edistOf_restrictOpen_connCompOpen]
  have hsecC : ∀ q ∈ riemannianBallOf (g.restrictOpen C) xC s,
      SectionalBoundedBelowAt (g.restrictOpen C) q (-κ) := by
    intro q hq
    rw [sectionalBoundedBelowAt_restrictOpen_iff_T2]
    rw [← hballC] at hq
    exact hsec q hq
  have hBG := ballVolume_le_modelVolume_of_sectional_three (g.restrictOpen C) hgC hdim xC
    hκ hs hsecC
  have hsub : riemannianBallOf g x s ⊆ (C : Set M) :=
    Geometry.Metric.edistOf_ball_subset_connCompOpen g x s
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have hmeas : MeasurableSet (riemannianBallOf g x s) :=
    (isOpen_riemannianBallOf g x s).measurableSet
  have hvol := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset g C
    hmeas hsub
  unfold ballVolume at hBG ⊢
  rw [← hvol, hballC]
  exact hBG

/-- Positive / round case: the domain is the whole component. -/
private theorem component_case_O10 {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete (I := I3) g) {eps C1 C2 L : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hwhole : W.domain.carrier = connectedComponent x) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hL : 8 * C1 * Real.exp (4 * C1 * Real.sqrt C2) ≤ L) :
    ∃ z : M, ∃ ρ : ℝ, riemannianEDistOf g x z ≤
        ENNReal.ofReal (L / Real.sqrt (metricScalarAt g x)) ∧
      0 < ρ ∧ ρ ≤ L / Real.sqrt (metricScalarAt g x) ∧
      ballVolume g z ρ < ENNReal.ofReal (ρ ^ 3) := by
  set R := metricScalarAt g x with hRdef
  have hR : 0 < R := W.Q_pos
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  set E := Real.exp (4 * C1 * Real.sqrt C2) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  set s := 2 * C1 / Real.sqrt R with hs
  have hspos : 0 < s := by positivity
  have hball_dom : ∀ r : ℝ, 0 < r → riemannianBallOf g x r ⊆ W.domain.carrier := by
    intro r hr
    rw [hwhole]
    exact (isPathConnected_riemannianBallOf g x hr).isConnected.isPreconnected.subset_connectedComponent
      (by
        change riemannianEDistOf g x x < ENNReal.ofReal r
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr hr)
  have hdom_s : W.domain.carrier ⊆ riemannianBallOf g x s := by
    intro y hy
    refine mem_ball_mono_O10 (W.inside_ball hy) ?_
    have := W.radius_upper
    rw [hs, mul_div_assoc]
    linarith
  refine ⟨x, L / Real.sqrt R, by rw [riemannianEDistOf_self]; exact zero_le,
    div_pos hLpos hsR, le_rfl, ?_⟩
  have hsub : riemannianBallOf g x (L / Real.sqrt R) ⊆ riemannianBallOf g x s :=
    (hball_dom _ (by positivity)).trans hdom_s
  have hC2R : 0 ≤ C2 * R := by positivity
  have hsec : ∀ q ∈ riemannianBallOf g x s,
      SectionalBoundedBelowAt g q (-(Real.sqrt (C2 * R)) ^ 2) := by
    intro q hq
    have hqd := hball_dom s hspos hq
    rw [Real.sq_sqrt hC2R]
    exact sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le g q (W.rm_bound q hqd)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hBG := ballVolume_le_modelVolume_component_O10 g hg x
    (κ := Real.sqrt (C2 * R) ^ 2) (by positivity) hspos hsec
  have hmodel := modelVolume_neg_sq_three_le (Real.sqrt_nonneg (C2 * R)) hspos.le
  have hqs : 2 * Real.sqrt (C2 * R) * s = 4 * C1 * Real.sqrt C2 := by
    rw [hs, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ C2)]
    field_simp
    ring
  rw [hqs, euclideanUnitBallVolume_three_eq] at hmodel
  have hpi : Real.pi < 4 := by linarith [Real.pi_lt_d2]
  have hs3 : s ^ 3 = (2 * C1) ^ 3 / Real.sqrt R ^ 3 := by rw [hs, div_pow]
  have hρ3 : (L / Real.sqrt R) ^ 3 = L ^ 3 / Real.sqrt R ^ 3 := div_pow _ _ _
  have hkey : 4 * Real.pi / 3 * s ^ 3 * E < (L / Real.sqrt R) ^ 3 := by
    rw [hs3, hρ3]
    have hR3 : 0 < Real.sqrt R ^ 3 := by positivity
    rw [show 4 * Real.pi / 3 * ((2 * C1) ^ 3 / Real.sqrt R ^ 3) * E =
      (4 * Real.pi / 3 * (2 * C1) ^ 3 * E) / Real.sqrt R ^ 3 by ring]
    apply div_lt_div_of_pos_right _ hR3
    have h8 : (8 * C1 * E) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
    have hC13 : 1 ≤ C1 ^ 3 := one_le_pow₀ hC1
    have hE3 : E ≤ E ^ 3 := by
      have h1 : 1 ≤ E ^ 2 := one_le_pow₀ hE1
      calc E = E * 1 := by ring
        _ ≤ E * E ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = E ^ 3 := by ring
    have hpos : 0 < C1 ^ 3 * E := by positivity
    nlinarith [Real.pi_pos]
  calc ballVolume g x (L / Real.sqrt R)
      ≤ ballVolume g x s := measure_mono hsub
    _ ≤ ENNReal.ofReal (VolumeComparison.modelVolume (-(Real.sqrt (C2 * R) ^ 2)) 3 s) := hBG
    _ ≤ ENNReal.ofReal (4 * Real.pi / 3 * s ^ 3 * E) := ENNReal.ofReal_le_ofReal hmodel
    _ < ENNReal.ofReal ((L / Real.sqrt R) ^ 3) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hkey

/-- **V.** Canonical-neighbourhood volume deficit (input (V) of KL Sublemma 86.3). -/
theorem canonical_volume_deficit_O10 (C1 C2 : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete (I := I3) g → ∀ {eps : ℝ}, eps < 1 / 100 →
        ∀ {x : M} (W : SpatialCanonicalWitness g eps C1 C2 x), W.capTubeHasNeckChart eps →
        ∃ z : M, ∃ ρ : ℝ, riemannianEDistOf g x z ≤
            ENNReal.ofReal (L / Real.sqrt (metricScalarAt g x)) ∧
          0 < ρ ∧ ρ ≤ L / Real.sqrt (metricScalarAt g x) ∧
          ballVolume g z ρ < ENNReal.ofReal (ρ ^ 3) := by
  set C1' := max C1 1
  set C2' := max C2 1
  set L := 8 * C1' * Real.exp (4 * C1' * Real.sqrt C2') + 30 * Real.sqrt C2' + 2 * C1'
  have hC1' : 1 ≤ C1' := le_max_right _ _
  have hC2' : 1 ≤ C2' := le_max_right _ _
  have hE := Real.exp_pos (4 * C1' * Real.sqrt C2')
  have hsC2 := Real.sqrt_nonneg C2'
  refine ⟨L, by positivity, ?_⟩
  intro M _ _ _ _ _ g hg eps heps x W hW
  have hR : 0 < metricScalarAt g x := W.Q_pos
  have hsR : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hR
  have hxdom : x ∈ W.domain.carrier := interior_subset W.center_inside
  have hC2 : 1 ≤ C2 := by
    have h := (W.scalar_bounds x hxdom).2
    by_contra hc
    push Not at hc
    have : C2 * metricScalarAt g x < 1 * metricScalarAt g x := mul_lt_mul_of_pos_right hc hR
    linarith
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    rw [div_eq_mul_inv] at h
    have hi : 0 < (Real.sqrt (metricScalarAt g x))⁻¹ := inv_pos.mpr hsR
    nlinarith
  have hC1e : C1' = C1 := max_eq_left hC1
  have hC2e : C2' = C2 := max_eq_left hC2
  have hL1 : 30 * Real.sqrt C2 ≤ L := by rw [← hC2e]; nlinarith
  have hL2 : 2 * C1 ≤ L := by rw [← hC1e]; nlinarith
  have hL3 : 8 * C1 * Real.exp (4 * C1 * Real.sqrt C2) ≤ L := by
    rw [← hC1e, ← hC2e]; nlinarith
  have hdist : ∀ v ∈ W.domain.carrier, riemannianEDistOf g x v ≤
      ENNReal.ofReal (2 * C1 / Real.sqrt (metricScalarAt g x)) := by
    intro v hv
    refine (W.inside_ball hv).le.trans (ENNReal.ofReal_le_ofReal ?_)
    have := W.radius_upper
    rw [mul_div_assoc]
    linarith
  have hneck : ∀ v ∈ W.domain.carrier, SpatialNeck g eps v →
      ∃ z : M, ∃ ρ : ℝ, riemannianEDistOf g x z ≤
          ENNReal.ofReal (L / Real.sqrt (metricScalarAt g x)) ∧
        0 < ρ ∧ ρ ≤ L / Real.sqrt (metricScalarAt g x) ∧
        ballVolume g z ρ < ENNReal.ofReal (ρ ^ 3) := fun v hv nk =>
    neck_case_O10 heps nk hR (by linarith) (W.scalar_bounds v hv).1 (hdist v hv) hL1 hL2
  cases hA : W.alternative with
  | neck data => exact hneck x hxdom data.neck
  | cap data deep =>
    obtain ⟨v, nk, hmap⟩ := hW data deep hA
    have hvt : v ∈ data.tube := by
      rw [← data.tube_eq, ← nk.center_eq, ← hmap]
      exact mem_image_of_mem _ ⟨mem_univ _, by norm_num, by norm_num⟩
    have hvd : v ∈ W.domain.carrier := by
      rw [data.union_eq]
      exact Or.inr hvt
    exact hneck v hvd nk
  | positive whole data sec => exact component_case_O10 hg W whole hC1 hC2 hL3
  | round whole data => exact component_case_O10 hg W whole hC1 hC2 hL3

end GC.LongTime.Ch12
