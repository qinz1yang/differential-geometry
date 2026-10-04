import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale

/-!
# Consumers of the F1 rows (LC02, LC05–LC09) on closed manifolds

* `curvatureRadius_lt_top_of_not_sectionalBoundedBelowAt_zero`: on a manifold whose metric
  realizes `g`, a point where the sectional curvature is somewhere negative makes every curvature
  scale finite.
* `exists_pointed_limit_rescaled_below_curvatureScale` (LC05 consumer): closed three-manifolds
  whose sectional curvature is somewhere negative, rescaled at `ρ i = R_{p i} / (i + 1)` (the
  curvature scale divided by a buffer tending to infinity): a subsequence has a complete proper
  pointed limit with nonnegative four-point comparison and Hausdorff dimension at most three.
* `exists_kl618_metric_model_at_lipschitz_modifiedScale` (LC02 + LC09 consumer): along a
  standing closed sequence, eventually there is an actual `Λ`-Lipschitz modified scale `ρ`
  (LC02) at which every point has LC08's metric model (LC09).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Finite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A point with some negative sectional curvature makes the curvature scale finite at every
point of a manifold whose metric realizes `g`. -/
theorem curvatureRadius_lt_top_of_not_sectionalBoundedBelowAt_zero
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p y : M)
    (hy : ¬ SectionalBoundedBelowAt g y 0) : curvatureRadius g p < ⊤ := by
  unfold SectionalBoundedBelowAt at hy
  push Not at hy
  obtain ⟨v, w, hvw⟩ := hy
  rw [zero_mul] at hvw
  set G := g.inner y v v * g.inner y w w - g.inner y v w ^ 2 with hG
  set K := Curvature.metricRm04StandardAt g y v w w v with hK
  have hG0 : 0 ≤ G := sub_nonneg.mpr (gInner_sq_le_mul g y v w)
  set R := dist p y + 1 + (G + 1) / (-K) with hR
  have hKpos : 0 < -K := neg_pos.mpr hvw
  have hR1 : 1 ≤ R := by
    have : 0 ≤ (G + 1) / (-K) := div_nonneg (by linarith) hKpos.le
    have := dist_nonneg (x := p) (y := y)
    linarith
  have hRpos : 0 < R := by linarith
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hGR : (G + 1) / (-K) ≤ R := by
    have := dist_nonneg (x := p) (y := y)
    linarith
  have hfail : ¬ SectionalBoundedBelowAt g y (-(R ^ 2)⁻¹) := by
    intro h
    have h1 := h v w
    rw [← hG, ← hK] at h1
    have h2 : G + 1 ≤ -K * R ^ 2 := by
      rw [div_le_iff₀ hKpos] at hGR
      nlinarith
    have h3 : (R ^ 2)⁻¹ * G < -K := by
      rw [inv_mul_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hdR : dist p y ≤ R := by
    have : 0 ≤ (G + 1) / (-K) := div_nonneg (by linarith) hKpos.le
    linarith
  have hle := curvatureRadius_le_of_not_sectionalBoundedBelowAt g (p := p) hRpos
    (by rw [hmetric]; exact ENNReal.ofReal_le_ofReal hdR) hfail
  exact hle.trans_lt ENNReal.ofReal_lt_top

end Finite

section Closed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]

/-- **LC05 consumer.** Closed three-manifolds `(X i, g i)` with base points `p i`, each with some
negative sectional curvature, rescaled at `ρ i = R_{p i} / (i + 1)`: a subsequence converges in
the pointed Gromov–Hausdorff sense to a complete proper geodesic space with nonnegative
four-point comparison and Hausdorff dimension at most three. -/
theorem exists_pointed_limit_rescaled_below_curvatureScale (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) (p : ∀ i, X i)
    (hneg : ∀ i, ∃ y : X i, ¬ SectionalBoundedBelowAt (g i) y 0) :
    ∃ hρ : ∀ i, 0 < (curvatureRadius (g i) (p i)).toReal / ((i : ℝ) + 1),
      ∃ (Y : Type) (m : MetricSpace Y),
        letI := m
        ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
          @PointedGHConverges (fun i => X (φ i))
            (fun i => (mX (φ i)).rescale
              ((curvatureRadius (g (φ i)) (p (φ i))).toReal / ((φ i : ℝ) + 1))⁻¹
              (inv_pos.mpr (hρ (φ i)))) Y m (fun i => p (φ i)) q ∧
          dimH (univ : Set Y) ≤ 3 ∧ fourPointComparison 0 (univ : Set Y) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hfin : ∀ i, curvatureRadius (g i) (p i) ≠ ⊤ := fun i =>
    (curvatureRadius_lt_top_of_not_sectionalBoundedBelowAt_zero (g i) (hmetric i) (p i)
      (hneg i).choose (hneg i).choose_spec).ne
  have hR : ∀ i, 0 < (curvatureRadius (g i) (p i)).toReal := fun i =>
    ENNReal.toReal_pos (curvatureRadius_pos (g i) (p i)).ne' (hfin i)
  have hρ : ∀ i, 0 < (curvatureRadius (g i) (p i)).toReal / ((i : ℝ) + 1) := fun i =>
    div_pos (hR i) (by positivity)
  have hL : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i)
      (((i : ℝ) + 1) * ((curvatureRadius (g i) (p i)).toReal / ((i : ℝ) + 1))),
      SectionalBoundedBelowAt (g i) y
        (-((((i : ℝ) + 1) * ((curvatureRadius (g i) (p i)).toReal / ((i : ℝ) + 1))) ^ 2)⁻¹) := by
    intro i
    have heq : ((i : ℝ) + 1) * ((curvatureRadius (g i) (p i)).toReal / ((i : ℝ) + 1)) =
        (curvatureRadius (g i) (p i)).toReal := by
      field_simp
    rw [heq]
    exact sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius (g i) (hR i)
      (ENNReal.ofReal_toReal_le)
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, -, -, -⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer g hmetric p hρ hL hsec
  refine ⟨hρ, Y, m, q, φ, hφ, hcomplete, hproper, hconv, ?_, hcomp⟩
  rw [hdim] at hdimY
  exact_mod_cast hdimY

end Closed

section Standing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC02 + LC09 consumer.** Along a standing closed sequence, for every small fixed `w`,
eventually there is an actual `Λ`-Lipschitz modified scale `ρ` (LC02) such that every point `p`
has LC08's two-dimensional metric model at the scale `ρ p` (LC09). -/
theorem exists_kl618_metric_model_at_lipschitz_modifiedScale (hdim : Module.finrank ℝ E = 3)
    {σ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, LipschitzWith (Real.toNNReal Λ) ρ ∧
          ∀ p : X i, ∃ hρ : 0 < ρ p, ∃ (Y : Type) (mY : MetricSpace Y),
            letI := mY
            ∃ q : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
              fourPointComparison 0 (univ : Set Y) ∧
              Nonempty (@KleinerLottApprox (X i) Y ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr hρ))
                mY p q σ) := by
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := I) hdim hσ hσ1 hΛ
  refine ⟨w₀, hw₀, fun w hw hww hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand,
    eventually_exists_lipschitz_modifiedScale hdim g hmetric hα hstand hΛ hw hwc]
    with i hmodel hscale
  obtain ⟨ρ, hlip, hbounds⟩ := hscale
  refine ⟨ρ, hlip.weaken (Real.toNNReal_le_toNNReal (by linarith)), fun p => ?_⟩
  obtain ⟨hl, hlo, hup⟩ := hbounds p
  have hρ : 0 < ρ p := hl.trans_le hlo
  have hw' : 0 < firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := hl.trans_le
    (hlo.trans hup)
  obtain ⟨Y, mY, q, hc, hp, hd, hcomp, -, hKL⟩ :=
    hmodel p (ρ p) hρ (by linarith) (by linarith)
  exact ⟨hρ, Y, mY, q, hc, hp, hd, hcomp, hKL⟩

end Standing

end DifferentialGeometry.Geometry.Collapse
