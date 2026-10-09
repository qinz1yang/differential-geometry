import DifferentialGeometry.Geometry.Collapse.RescaledLimits.LowDimensionalLimit
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Count

/-!
# LC02: the slowly varying modified volume scale (envelope and Lipschitz tier)

Blueprint 207A, LC02 (`prop:collapse-modified-scale`, A:20013). Fix `Λ > 0`, `0 < w < c₃`,
`S = 1 + 2Λ⁻¹` and `w' = w / (2 S³)`. Along a standing closed sequence (`R_p ≥ α r_p(1/α)`,
`α → ∞`), for all sufficiently large `α` and uniformly in the points:

* `firstVolumeScale_sub_le_of_buffer` / `eventually_modifiedScale_envelope`: the envelope
  inequality `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` (the blueprint's first paragraph: local
  Bishop–Gromov at `q` with a curvature constant that is small at the scale `r_p(w)`);
* `eventually_exists_lipschitz_modifiedScale`: a positive `(Λ/2)`-Lipschitz function `ρ` with
  `r_p(w) ≤ ρ(p) ≤ r_p(w')` (MC19, by the explicit McShane envelope
  `ρ(p) = sup_q (r_q(w) - (Λ/2) d(p, q))`), hence `r_p(w)/2 ≤ ρ(p) ≤ 2 r_p(w')`.

Not proved here: the SMOOTH replacement of the blueprint's last paragraph, which cites
compact-manifold Lipschitz smoothing (KL Corollary 3.15); no such theorem is in this tree. The
envelope uses the crude model-volume bounds `c₃ t³ ≤ V_{-q²}(t) ≤ c₃ t³ e^{2qt}`
(`modelVolume_neg_sq_three_le`) instead of the blueprint's `sinh(v)/v` monotonicity; with the
curvature constant `(4S r_p(w))⁻²` the contradiction is `2 ≤ e^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The three-dimensional hyperbolic model volume is at most the Euclidean one times
`e^{2qR}`. -/
theorem modelVolume_neg_sq_three_le {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R) :
    modelVolume (-(q ^ 2)) 3 R ≤ euclideanUnitBallVolume 3 * R ^ 3 * Real.exp (2 * q * R) := by
  rw [modelVolume_neg_sq q 3 R hq, hyperbolicRadialVolume]
  have hc := euclideanUnitBallVolume_pos 3
  have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) R,
      hyperbolicDensity q (3 - 1) t ≤ t ^ 2 * Real.exp (2 * q * R) := by
    intro t ht
    have h := hyperbolicDen_le 2 hq ht.1.le
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    push_cast
    nlinarith [ht.2]
  have hint : ∫ t in (0 : ℝ)..R, hyperbolicDensity q (3 - 1) t ≤
      ∫ t in (0 : ℝ)..R, t ^ 2 * Real.exp (2 * q * R) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hR
    · exact ((hyperbolicSn_continuous q).pow _).intervalIntegrable 0 R
    · exact ((continuous_pow 2).mul continuous_const).intervalIntegrable 0 R
    · exact hbound
  rw [intervalIntegral.integral_mul_const, integral_pow] at hint
  calc ((3 : ℕ) : ℝ) * euclideanUnitBallVolume 3 *
        ∫ t in (0 : ℝ)..R, hyperbolicDensity q (3 - 1) t
      ≤ ((3 : ℕ) : ℝ) * euclideanUnitBallVolume 3 *
          ((R ^ (2 + 1) - 0 ^ (2 + 1)) / (2 + 1) * Real.exp (2 * q * R)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = euclideanUnitBallVolume 3 * R ^ 3 * Real.exp (2 * q * R) := by
        push_cast
        ring

/-- `e^{1/2} < 2`. -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2)]

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
private theorem riemannianBallOf_eq_ball_of_riemannian (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M) (r : ℝ) :
    riemannianBallOf g p r = Metric.ball p r := by
  refine Set.ext fun y => ?_
  change riemannianEDistOf g p y < ENNReal.ofReal r ↔ _
  rw [hmetric, Metric.mem_ball, dist_comm]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg

/-- **LC02 envelope** at one pair of points of a closed manifold. With `S = 1 + 2Λ⁻¹` and
`w' = w / (2 S³)`, if `sec ≥ -(4 S r_p(w))⁻²` on `B(p, 4 S r_p(w))`, then
`r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')`. -/
theorem firstVolumeScale_sub_le_of_buffer (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) (p q : M)
    (hsec : ∀ y ∈ riemannianBallOf g p (4 * (1 + 2 * Λ⁻¹) * firstVolumeScale g p w),
      SectionalBoundedBelowAt g y
        (-((4 * (1 + 2 * Λ⁻¹) * firstVolumeScale g p w) ^ 2)⁻¹)) :
    firstVolumeScale g p w - Λ / 2 * dist p q ≤
      firstVolumeScale g q (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
  set S := 1 + 2 * Λ⁻¹ with hSdef
  set l := firstVolumeScale g p w with hldef
  set w' := w / (2 * S ^ 3) with hw'def
  set u := firstVolumeScale g q w' with hudef
  have hΛi : 0 < Λ⁻¹ := inv_pos.mpr hΛ
  have hS1 : 1 < S := by linarith
  have hS3 : 1 < 2 * S ^ 3 := by nlinarith [one_le_pow₀ (n := 3) hS1.le]
  have hw' : 0 < w' := div_pos hw (by linarith)
  have hw'c : w' < 4 * Real.pi / 3 := (div_lt_self hw hS3).trans hwc
  have hl : 0 < l := (firstVolumeScale_spec g hdim p hw hwc).1
  have hu : 0 < u := (firstVolumeScale_spec g hdim q hw' hw'c).1
  by_contra hfail
  push Not at hfail
  have hd0 := dist_nonneg (x := p) (y := q)
  have hul : u < l := by nlinarith
  have hd : dist p q < 2 * Λ⁻¹ * l := by
    have h1 : Λ / 2 * dist p q < l := by nlinarith
    have h2 : dist p q = (Λ / 2 * dist p q) * (2 * Λ⁻¹) := by field_simp
    rw [h2]
    nlinarith
  have hball := riemannianBallOf_eq_ball_of_riemannian g hmetric
  have hincl1 : riemannianBallOf g p l ⊆ riemannianBallOf g q (S * l) := by
    rw [hball, hball]
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have := dist_triangle y p q
    rw [hSdef]
    linarith
  have hincl2 : riemannianBallOf g q (S * l) ⊆ riemannianBallOf g p (4 * S * l) := by
    rw [hball, hball]
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have := dist_triangle y q p
    rw [dist_comm q p] at this
    nlinarith
  set κ := ((4 * S * l) ^ 2)⁻¹ with hκdef
  have hκ : 0 ≤ κ := inv_nonneg.mpr (sq_nonneg _)
  have hsecq : ∀ y ∈ riemannianBallOf g q (S * l), SectionalBoundedBelowAt g y (-κ) :=
    fun y hy => hsec y (hincl2 hy)
  have : ConnectedSpace M := connectedSpace_of_aligned_metric g hmetric p
  have hg : RiemannianMetricComplete (I := I) g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  have huSl : u ≤ S * l := hul.le.trans (le_mul_of_one_le_left hl.le hS1.le)
  have hBG := ballVolume_cross_endpoint_of_sectional_three g hg hdim q hκ hu huSl hsecq
  have hmono : ballVolume g p l ≤ ballVolume g q (S * l) := measure_mono hincl1
  rw [hldef, ballVolume_firstVolumeScale g hdim p hw hwc, ← hldef] at hmono
  rw [hudef, ballVolume_firstVolumeScale g hdim q hw' hw'c, ← hudef] at hBG
  have hVu : euclideanUnitBallVolume 3 * u ^ 3 ≤ modelVolume (-κ) 3 u :=
    sectionalThree_euclidean_le_model hκ hu.le
  have hVSl : modelVolume (-κ) 3 (S * l) ≤
      euclideanUnitBallVolume 3 * (S * l) ^ 3 * Real.exp (1 / 2) := by
    have hq : 0 ≤ (4 * S * l)⁻¹ := inv_nonneg.mpr (by positivity)
    have h := modelVolume_neg_sq_three_le hq (by positivity : 0 ≤ S * l)
    have hκq : κ = (4 * S * l)⁻¹ ^ 2 := by rw [hκdef, inv_pow]
    have hexp : 2 * (4 * S * l)⁻¹ * (S * l) = 1 / 2 := by
      field_simp
      ring
    rwa [hκq, ← hexp]
  have hc := euclideanUnitBallVolume_pos 3
  have hVSl0 : 0 ≤ modelVolume (-κ) 3 (S * l) :=
    (mul_nonneg hc.le (by positivity)).trans
      (sectionalThree_euclidean_le_model hκ (by positivity : 0 ≤ S * l))
  have hcomb := (mul_le_mul_left hmono (ENNReal.ofReal (modelVolume (-κ) 3 u))).trans hBG
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hVSl0,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hVSl0 (by positivity))] at hcomb
  have hw2 : w = 2 * S ^ 3 * w' := by
    rw [hw'def]
    field_simp
  have hE := exp_half_lt_two
  have hP : 0 < euclideanUnitBallVolume 3 * S ^ 3 * l ^ 3 * u ^ 3 * w' := by positivity
  have key : 2 * (euclideanUnitBallVolume 3 * S ^ 3 * l ^ 3 * u ^ 3 * w') ≤
      Real.exp (1 / 2) * (euclideanUnitBallVolume 3 * S ^ 3 * l ^ 3 * u ^ 3 * w') := by
    calc 2 * (euclideanUnitBallVolume 3 * S ^ 3 * l ^ 3 * u ^ 3 * w')
        = (w * l ^ 3) * (euclideanUnitBallVolume 3 * u ^ 3) := by rw [hw2]; ring
      _ ≤ (w * l ^ 3) * modelVolume (-κ) 3 u :=
          mul_le_mul_of_nonneg_left hVu (by positivity)
      _ ≤ modelVolume (-κ) 3 (S * l) * (w' * u ^ 3) := hcomb
      _ ≤ (euclideanUnitBallVolume 3 * (S * l) ^ 3 * Real.exp (1 / 2)) * (w' * u ^ 3) :=
          mul_le_mul_of_nonneg_right hVSl (by positivity)
      _ = Real.exp (1 / 2) * (euclideanUnitBallVolume 3 * S ^ 3 * l ^ 3 * u ^ 3 * w') := by
          ring
  have := le_of_mul_le_mul_right key hP
  linarith

end Single

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]

/-- **LC02 envelope** along a standing closed sequence (`R_p ≥ α r_p(1/α)`, `α → ∞`): on a tail
independent of the points, `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` for all `p, q`. -/
theorem eventually_modifiedScale_envelope (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∀ᶠ i in atTop, ∀ p q : X i,
      firstVolumeScale (g i) p w - Λ / 2 * dist p q ≤
        firstVolumeScale (g i) q (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
  filter_upwards [hα.eventually (eventually_ge_atTop (4 * (1 + 2 * Λ⁻¹))),
    hα.eventually (eventually_ge_atTop w⁻¹)] with i h1 h2 p q
  have hαpos : 0 < α i := (inv_pos.mpr hw).trans_le h2
  have hαinv : (α i)⁻¹ ≤ w := by
    rw [inv_le_comm₀ hαpos hw]
    exact h2
  have hl := (firstVolumeScale_spec (g i) hdim p hw hwc).1
  have hanti : firstVolumeScale (g i) p w ≤ firstVolumeScale (g i) p (α i)⁻¹ :=
    (firstVolumeScale_strictAntiOn (g i) hdim p).antitoneOn
      ⟨inv_pos.mpr hαpos, hαinv.trans_lt hwc⟩ ⟨hw, hwc⟩ hαinv
  have hA : 0 < 4 * (1 + 2 * Λ⁻¹) := by have := inv_pos.mpr hΛ; positivity
  have hle : 4 * (1 + 2 * Λ⁻¹) * firstVolumeScale (g i) p w ≤
      α i * firstVolumeScale (g i) p (α i)⁻¹ :=
    mul_le_mul h1 hanti hl.le hαpos.le
  exact firstVolumeScale_sub_le_of_buffer hdim (g i) (hmetric i) hΛ hw hwc p q
    (sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius (g i) (mul_pos hA hl)
      ((ENNReal.ofReal_le_ofReal hle).trans (hstand i p)))

/-- **LC02, Lipschitz tier** (MC19 by the McShane envelope): along a standing closed sequence,
on a tail independent of the points, there is a `(Λ/2)`-Lipschitz function `ρ` with
`0 < r_p(w) ≤ ρ(p) ≤ r_p(w')`, `w' = w / (2 (1 + 2Λ⁻¹)³)`. -/
theorem eventually_exists_lipschitz_modifiedScale (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, LipschitzWith (Real.toNNReal (Λ / 2)) ρ ∧
      ∀ p : X i, 0 < firstVolumeScale (g i) p w ∧ firstVolumeScale (g i) p w ≤ ρ p ∧
        ρ p ≤ firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
  filter_upwards [eventually_modifiedScale_envelope hdim g hmetric hα hstand hΛ hw hwc]
    with i hi
  set w' := w / (2 * (1 + 2 * Λ⁻¹) ^ 3)
  have hK : ((Real.toNNReal (Λ / 2) : ℝ≥0) : ℝ) = Λ / 2 := Real.coe_toNNReal _ (by positivity)
  have hbdd : ∀ p : X i,
      BddAbove (Set.range fun q => firstVolumeScale (g i) q w - Λ / 2 * dist p q) := by
    intro p
    refine ⟨firstVolumeScale (g i) p w', ?_⟩
    rintro _ ⟨q, rfl⟩
    have h := hi q p
    rwa [dist_comm] at h
  refine ⟨fun p => ⨆ q, (firstVolumeScale (g i) q w - Λ / 2 * dist p q), ?_, fun p => ?_⟩
  · apply LipschitzWith.of_le_add_mul
    intro x y
    have : Nonempty (X i) := ⟨x⟩
    rw [hK]
    apply ciSup_le
    intro q
    have h1 := le_ciSup (hbdd y) q
    have h2 := dist_triangle y x q
    rw [dist_comm y x] at h2
    nlinarith
  · have : Nonempty (X i) := ⟨p⟩
    refine ⟨(firstVolumeScale_spec (g i) hdim p hw hwc).1, ?_, ?_⟩
    · have h := le_ciSup (hbdd p) p
      simpa only [dist_self, mul_zero, sub_zero] using h
    · apply ciSup_le
      intro q
      have h := hi q p
      rwa [dist_comm] at h

end Sequence

end DifferentialGeometry.Geometry.Collapse
