import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LipschitzSmoothing

/-!
# LC02: the smooth modified volume scale

Blueprint 207A, LC02 (`prop:collapse-modified-scale`, A:20013), last paragraph: the
`(Λ/2)`-Lipschitz function `f` with `r_p(w) ≤ f ≤ r_p(w')`
(`eventually_exists_lipschitz_modifiedScale`) has positive minimum `m` on the closed manifold;
smoothing with `0 < η < min {m/2, Λ/2}` (`exists_contMDiff_lipschitz_approx`, lane W3-LC28, the
KL Corollary 3.15 input) gives a smooth `ρ` with `|ρ - f| < η` and Lipschitz constant at most
`Λ/2 + η < Λ`; then `r_p(w)/2 < ρ(p) < 2 r_p(w')`.

* `eventually_exists_smooth_modifiedScale`: LC02 as stated in the blueprint.
* `exists_kl618_metric_model_at_smooth_modifiedScale` (consumer, LC02 + LC09): eventually every
  point has LC08's metric model at the smooth modified scale.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]

/-- **LC02.** Along a standing closed sequence, for all sufficiently large indices and
uniformly over the points, there is a smooth positive `Λ`-Lipschitz function `ρ` with
`r_p(w)/2 < ρ(p) < 2 r_p(w')`, `w' = w / (2 (1 + 2Λ⁻¹)³)`. -/
theorem eventually_exists_smooth_modifiedScale (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
      LipschitzWith (Real.toNNReal Λ) ρ ∧ ∀ p : X i, 0 < ρ p ∧
        firstVolumeScale (g i) p w / 2 < ρ p ∧
        ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
  filter_upwards [eventually_exists_lipschitz_modifiedScale hdim g hmetric hα hstand hΛ hw hwc]
    with i hi
  obtain ⟨f, hf, hbounds⟩ := hi
  rcases isEmpty_or_nonempty (X i) with hX | hX
  · exact ⟨f, fun p => (hX.false p).elim, fun p => (hX.false p).elim,
      fun p => (hX.false p).elim⟩
  obtain ⟨p₀, -, hp₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  have hm : 0 < f p₀ := (hbounds p₀).1.trans_le (hbounds p₀).2.1
  set η := min (f p₀ / 2) (Λ / 2) / 2 with hηdef
  have hη : 0 < η := by positivity
  have hηm : η < f p₀ / 2 := by
    have := min_le_left (f p₀ / 2) (Λ / 2)
    linarith
  have hηΛ : η < Λ / 2 := by
    have := min_le_right (f p₀ / 2) (Λ / 2)
    linarith
  obtain ⟨ρ, hsmooth, hclose, hlip⟩ :=
    exists_contMDiff_lipschitz_approx (g i) (hmetric i) hf hη
  refine ⟨ρ, hsmooth, hlip.weaken ?_, fun p => ?_⟩
  · have key : Real.toNNReal (Λ / 2) + Real.toNNReal η ≤ Real.toNNReal Λ := by
      rw [← Real.toNNReal_add (by positivity) hη.le]
      exact Real.toNNReal_le_toNNReal (by linarith)
    refine le_trans (le_of_eq ?_) key
    rw [Real.toNNReal_of_nonneg hη.le]
    rfl
  · obtain ⟨hl, hlo, hup⟩ := hbounds p
    have hmin : f p₀ ≤ f p := hp₀ (mem_univ p)
    have hc := abs_lt.mp (hclose p)
    refine ⟨by linarith, by linarith, by linarith⟩

end Sequence

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC02 + LC09 consumer**: along a standing closed sequence, for every small fixed `w`,
eventually there is a smooth `Λ`-Lipschitz modified scale `ρ` (LC02) at which every point has
LC08's two-dimensional metric model (LC09). -/
theorem exists_kl618_metric_model_at_smooth_modifiedScale (hdim : Module.finrank ℝ E = 3)
    {σ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
          LipschitzWith (Real.toNNReal Λ) ρ ∧
          ∀ p : X i, ∃ hρ : 0 < ρ p, ∃ (Y : Type) (mY : MetricSpace Y),
            letI := mY
            ∃ q : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
              fourPointComparison 0 (univ : Set Y) ∧
              Nonempty (@KleinerLottApprox (X i) Y ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr hρ))
                mY p q σ) := by
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := I) hdim hσ hσ1 hΛ
  refine ⟨w₀, hw₀, fun w hw hww hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand,
    eventually_exists_smooth_modifiedScale hdim g hmetric hα hstand hΛ hw hwc]
    with i hmodel hscale
  obtain ⟨ρ, hsmooth, hlip, hbounds⟩ := hscale
  refine ⟨ρ, hsmooth, hlip, fun p => ?_⟩
  obtain ⟨hρ, hlo, hup⟩ := hbounds p
  obtain ⟨Y, mY, q, hc, hp, hd, hcomp, -, hKL⟩ := hmodel p (ρ p) hρ hlo.le hup.le
  exact ⟨hρ, Y, mY, q, hc, hp, hd, hcomp, hKL⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
