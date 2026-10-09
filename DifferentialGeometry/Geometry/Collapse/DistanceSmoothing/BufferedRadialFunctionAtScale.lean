import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunctionAtScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessConeRadial

/-!
# LC67 and LC31 at a prescribed scale `R` (LC80 item 2, obligations (i), (iv))

Master207A, LC67 (A:23899), LC80 (A:24719), LCP04 (A:30123). LCP04 asks for the selected radial
function `η_i` smooth on the BUFFERED shell `C⁺ = {3/40 ≤ r_i⁻¹ d(·, i) ≤ 11}`, while LC30 (and the
LC58 binding `exists_uniform_scale_interval_joint_witnesses`, item (2)) only gives an open set
containing `{1/10 ≤ r⁻¹ d ≤ 10}`. The two windows cannot be matched by changing the scale (band
ratios `100` and `146.7`). LC67 is the blueprint's answer: the LC30 function is CHOSEN at the
smoothing step smooth near `C⁺`, with every LC30 conclusion retained ("an arbitrary already selected
LC30 witness is not silently assumed to have this larger smooth neighborhood").

* `exists_coneError_below_thresholds` (iv): after `ε` and LCP04's `δ'` one cone error
  `δ < min{1, δ', radialSmoothingConeError (ε / 4)}`.
* `exists_buffered_radial_cutoff_at_scale` (i): LC67 + LC31 at the scale `R`: from a Kleiner–Lott
  `δ`-map of `(M, R⁻¹ d, p)` to a radial cone and the original buffer, the normalized manifold
  carries an LC30 function with ALL of LC30's clauses, smooth near `C⁺`, and LC31's cutoff (the
  clause list of item (2) of the LC58 binding, with the window `C⁺`).
* `radial_original_clauses_of_rescaled`: LCP04's two radial hypotheses (smoothness on `C⁺` and the
  difference-Lipschitz bound) in the ORIGINAL metric from the rescaled clauses.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The cone error after the thresholds (obligation (iv)).** For `ε > 0` and a threshold `δ' > 0`
(LCP04's, fixed before every manifold) there is one `δ` below `1`, below `δ'` and below LC30's cone
error `radialSmoothingConeError (ε / 4)`. -/
theorem exists_coneError_below_thresholds {ε δ' : ℝ} (hε : 0 < ε) (hδ' : 0 < δ') :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < δ' ∧ δ < radialSmoothingConeError (ε / 4) := by
  have hrs : 0 < radialSmoothingConeError (ε / 4) := radialSmoothingConeError_pos (by positivity)
  refine ⟨min (min δ' (radialSmoothingConeError (ε / 4))) 1 / 2, by positivity, ?_, ?_, ?_⟩
  · have := min_le_right (min δ' (radialSmoothingConeError (ε / 4))) 1
    linarith
  · have := (min_le_left (min δ' (radialSmoothingConeError (ε / 4))) 1).trans (min_le_left _ _)
    linarith
  · have := (min_le_left (min δ' (radialSmoothingConeError (ε / 4))) 1).trans (min_le_right _ _)
    linarith

variable {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [hM : CompleteSpace M]

/-- **LC67 and LC31 at scale `R` (obligation (i)).** From a Kleiner–Lott `δ`-map of `(M, R⁻¹ d, p)`
to a radial cone and the original buffer `sec_g ≥ -(1/60)² R⁻²` on `B(p, 400 R)`, the normalized
manifold `(M, R⁻¹ d, R⁻² g)` carries an LC30 radial function with all of LC30's clauses, smooth on
an open set containing the buffered shell `{3/40 ≤ d_p ≤ 11}`, together with LC31's cutoff
`Φ ∘ F` and its bounds. -/
theorem exists_buffered_radial_cutoff_at_scale (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {p : M} {R : ℝ} (hR : 0 < R) {C : Type*} [MetricSpace C] {o : C} {δ ε e : ℝ}
    (φ : @KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p o δ)
    (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p (400 * R),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)))
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e)
    (he1 : e < 1 / 40) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ∧
          Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ≤ 1 + ε) ∧
      (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun gR F q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
        (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
          {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε) := by
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  have hMR : @CompleteSpace M (m.rescale R⁻¹ hRinv).toUniformSpace :=
    (m.rescale_completeSpace_iff R⁻¹ hRinv).mpr hM
  have hsecR : ∀ y ∈ @Metric.ball M (m.rescale R⁻¹ hRinv).toPseudoMetricSpace p 400,
      SectionalBoundedBelowAt (scaleMetric (R⁻¹ ^ 2) (pow_pos hRinv 2) g) y
        (-(1 / 60) ^ 2) := by
    intro y hy
    have hy' : R⁻¹ * dist y p < 400 := hy
    have hyR : y ∈ Metric.ball p (400 * R) := by
      rw [Metric.mem_ball]
      have := (inv_mul_lt_iff₀ hR).mp hy'
      linarith
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    simpa only [neg_mul] using hsec y hyR
  let := m.rescale R⁻¹ hRinv
  let := radialScaledBundle g R⁻¹ hRinv
  let := radialScaledContinuous g R⁻¹ hRinv
  let := radialScaledManifold (m := m) g hmetric R⁻¹ hRinv
  let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos hRinv 2) g
  have hEnorm : IsMetricNorm gR := isMetricNorm_of_riemannianBundle gR
  obtain ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub, O', hO', hband, hFO',
      hne⟩ :=
    exists_buffered_radialFunction_of_kleinerLottApprox gR hEnorm φ H hsecR hε hε1 hδ he he1
  obtain ⟨L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩ :=
    exists_radial_cutoff_of_band gR p hε.le hFlip.continuous hclose (fun q hq => (hgrad q hq).2)
      hsub hO' hband hFO'
  exact ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub,
    ⟨O', hO', hband, hFO', hne⟩, L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] hM in
/-- **LCP04's radial hypotheses in the original metric.** Smoothness near the rescaled shell
`{3/40 ≤ d_p ≤ 11}` of `(M, R⁻¹ d)` and the rescaled difference-Lipschitz bound give LCP04's
form: `F` smooth on `{3/40 ≤ R⁻¹ d(x, p) ≤ 11}` and
`|(F x - R⁻¹ d(p, x)) - (F y - R⁻¹ d(p, y))| ≤ ε R⁻¹ d(x, y)`. -/
theorem radial_original_clauses_of_rescaled {p : M} {R : ℝ} (hR : 0 < R) {F : M → ℝ} {ε : ℝ}
    (hO : letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      ∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hdiff : letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      ∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F {x | 3 / 40 ≤ R⁻¹ * dist x p ∧ R⁻¹ * dist x p ≤ 11} ∧
      ∀ x y, |(F x - R⁻¹ * dist p x) - (F y - R⁻¹ * dist p y)| ≤ ε * (R⁻¹ * dist x y) := by
  obtain ⟨O, -, hCO, hFO⟩ := hO
  refine ⟨hFO.mono hCO, fun x y => ?_⟩
  have h := hdiff x y
  simp only [Metric.infDist_singleton] at h
  rw [dist_comm p x, dist_comm p y]
  exact h

end DifferentialGeometry.Geometry.Collapse
