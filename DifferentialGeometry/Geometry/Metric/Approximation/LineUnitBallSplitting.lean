import DifferentialGeometry.Geometry.Metric.Approximation.AnnularExactStrainer
import DifferentialGeometry.Geometry.Metric.Approximation.OppositeLineLifts
import DifferentialGeometry.Geometry.Metric.Approximation.UniformLongStrainerSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Comparison.FourPointMonotone

/-!
# A line approximation excludes rank zero on the unit ball (LC76, metric kernel)

Blueprint `master207A.tex`, LC76 (`lem:collapse-line-cone-unit-splitting`, lines 24480–24529).
For every `0 < β < 1` and dimension bound `n ≥ 1` there are `δℓ, Λℓ > 0` such that a complete
geodesic space `X` with `dimH B(p, 2) ≤ n`, four-point comparison at curvature `-(1/60)²` on
`B(p, 7)`, and a pointed Kleiner–Lott `δ`-map from `(X, p)` to the real line
with `δ < δℓ` has, at EVERY `q ∈ B(p, 1)` and for EVERY factor `λ ≥ Λℓ`, a normalized
`(1, β)`-splitting of `(X, λ d, q)`.

The proof is the blueprint's: opposite lifts of `F(q) ± 4` shortened to equal legs
(`exists_equal_radius_line_lifts`), the equal-leg angle defect at curvature `-(1/60)²`, AC64
shortening of both legs to `L / λ` with `L = σ⁻¹`, the resulting chord forces the comparison
angle above `π - σ` at curvature `-σ` for `λ d`, and AC55 (`exists_prescribed_splitting_parameter`)
gives the splitting. AC55 consumes comparison at curvature `-σ λ²` for the original distance;
it follows from the single level `-(1/60)²` by monotonicity of four-point comparison in the
curvature (`fourPointComparison.forall_ge`, lane MON).
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- Four-point comparison is invariant under rescaling the distance by `c` and the curvature by
`c⁻²`. -/
theorem fourPointComparison_rescale_iff {X : Type*} {m : MetricSpace X} {c κ : ℝ} (hc : 0 < c)
    (hκ : 0 ≤ κ) {Ω : Set X} :
    @fourPointComparison X (m.rescale c hc) κ Ω ↔ @fourPointComparison X m (κ * c ^ 2) Ω := by
  have hscale (a b d : ℝ) : comparisonAngleNegCurvature κ (c * a) (c * b) (c * d) =
      comparisonAngleNegCurvature (κ * c ^ 2) a b d := by
    rw [mul_comm c a, mul_comm c b, comparisonAngleNegCurvature_mul_scale hκ hc a b (c * d)]
    congr 1
    field_simp
  constructor <;> intro h x hx a ha b hb d hd hax hbx hdx
  · have ht := @h x hx a ha b hb d hd hax hbx hdx
    simpa only [MetricSpace.rescale_dist, hscale] using ht
  · have ht := @h x hx a ha b hb d hd hax hbx hdx
    simp only [MetricSpace.rescale_dist, hscale]
    exact ht

/-- AC64 shortening of an equal-leg triangle with a comparison angle above `π - θ` to legs of
length `s`: the chord of the shortened triangle exceeds `2 s cos (θ/2)`. -/
theorem exists_shortened_equal_leg_chord {X : Type*} [MetricSpace X]
    (hsegments : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    {K : ℝ} (hK : 0 ≤ K) {Ω : Set X} (hcomp : fourPointComparison K Ω) {q x y : X} {D θ s : ℝ}
    (hqx : dist q x = D) (hqy : dist q y = D) (hθ : 0 ≤ θ) (hθpi : θ ≤ π)
    (hangle : π - θ < comparisonAngleNegCurvature K D D (dist x y))
    (hs : 0 < s) (hsD : s ≤ D) (hΩ : closedBall q D ⊆ Ω) :
    ∃ x' y' : X, dist q x' = s ∧ dist q y' = s ∧
      dist q x' + dist x' x = dist q x ∧ dist q y' + dist y' y = dist q y ∧
      2 * s * cos (θ / 2) < dist x' y' ∧ dist x' y' ≤ 2 * s := by
  obtain ⟨x', y', hqx', hqy', hx'x, hy'y, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hsegments q x y hs.le (hqx ▸ hsD) (hqy ▸ hsD)
  have hmem (w : X) (hw : dist w q ≤ D) : w ∈ Ω := hΩ hw
  have hqΩ : q ∈ Ω := hmem q (by rw [dist_self]; linarith)
  have hxΩ : x ∈ Ω := hmem x (by rw [dist_comm, hqx])
  have hyΩ : y ∈ Ω := hmem y (by rw [dist_comm, hqy])
  have hx'Ω : x' ∈ Ω := hmem x' (by rw [dist_comm, hqx']; exact hsD)
  have hy'Ω : y' ∈ Ω := hmem y' (by rw [dist_comm, hqy']; exact hsD)
  have hyq : y ≠ q := by
    intro h
    rw [h, dist_self] at hqy
    linarith
  have hx'q : x' ≠ q := by
    intro h
    rw [h, dist_self] at hqx'
    linarith
  have hsh1 := comparisonAngleNegCurvature_le_of_shortening_left hK hcomp hqΩ hx'Ω hxΩ hyΩ
    (by rw [hqx']; exact hs) hyq (by rw [hqx', hx'x]; ring)
  have hsh2 := comparisonAngleNegCurvature_le_of_shortening_right hK hcomp hqΩ hy'Ω hyΩ hx'Ω
    (by rw [hqy']; exact hs) hx'q (by rw [hqy', hy'y]; ring)
  have h0 : π - θ < comparisonAngleNegCurvature K (dist q x) (dist q y) (dist x y) := by
    rw [hqx, hqy]; exact hangle
  have h := (h0.trans_le hsh1).trans_le hsh2
  rw [hqx', hqy'] at h
  have hup : dist x' y' ≤ 2 * s := by
    have ht := dist_triangle x' q y'
    rw [dist_comm x' q, hqx', hqy'] at ht
    linarith
  refine ⟨x', y', hqx', hqy', by rw [hqx', hx'x]; ring, by rw [hqy', hy'y]; ring, ?_, hup⟩
  exact two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature hK hs dist_nonneg hup hθ
    hθpi h

/-- The chord of a shortened triangle, rescaled to legs `σ⁻¹`, forces the comparison angle
above `π - σ` at curvature `-σ`, for the auxiliary angle of `exists_annular_strainer_angle`. -/
theorem pi_sub_lt_comparisonAngle_of_scaled_chord {σ θ s c lam : ℝ} (hσ : 0 < σ)
    (hθbudget : 4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2)) < 1 - cos σ)
    (hs : 0 < s) (hlam : 0 < lam) (hlams : lam * s = σ⁻¹)
    (hchord : 2 * s * cos (θ / 2) < c) (hc0 : 0 ≤ c) (hcs : c ≤ 2 * s) :
    π - σ < comparisonAngleNegCurvature σ (lam * s) (lam * s) (lam * c) := by
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  rw [hlams]
  have hc_up : lam * c ≤ L + L := by nlinarith
  have hc_low : 2 * L * cos (θ / 2) < lam * c := by nlinarith
  have hfinal : π - σ < comparisonAngleNegCurvature (sqrt σ ^ 2) L L (lam * c) := by
    apply pi_sub_lt_comparisonAngleNegCurvature_of_excess (sqrt_nonneg σ) hLpos hLpos
      (by rw [sub_self, abs_zero]; nlinarith) hc_up hσ.le
    have hK : 0 < cosh (sqrt σ * (L + L)) := cosh_pos _
    rw [div_lt_iff₀ (by positivity)]
    have hexcess : L + L - lam * c < 2 * L * (1 - cos (θ / 2)) := by linarith
    have h1 : cosh (sqrt σ * (L + L)) * (L + L - lam * c) * (L + L) <
        cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_left hexcess hK
    have h2 : cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) =
        (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) := by
      rw [hL]
      ring
    have h3 : (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) <
        (1 - cos σ) * (L * L) := mul_lt_mul_of_pos_right hθbudget (by positivity)
    linarith
  rwa [sq_sqrt hσ.le] at hfinal

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u

/-- AC55 applied to a one-strainer at exact scale `σ⁻¹` of the rescaled distance `λ d` at `q`:
the conclusion is a normalized `(1, β)`-splitting of `(X, λ d, q)`. The geometric inputs are
read off in the original distance: dimension of the `σ⁻¹ / λ`-ball, comparison at curvature
`-σ λ²` on an open set containing it, and the two anchors at exact distance `σ⁻¹ / λ`. -/
theorem hasEuclideanSplitting_one_of_rescaled_strainer {n : ℕ} {β σ : ℝ}
    (hσ : 0 < σ)
    (hAC55 : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (o : X)
        (aPlus aMinus : Fin k → X),
      (∀ a b : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
          eVariationOn c univ < ENNReal.ofReal (dist a b + η)) →
      dimH (ball o σ⁻¹) ≤ n →
      (∀ z ∈ ball o σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) →
      (∀ j, dist o (aPlus j) = σ⁻¹) → (∀ j, dist o (aMinus j) = σ⁻¹) →
      (∀ j, Real.pi - σ ≤ comparisonAngleNegCurvature σ
        (dist o (aPlus j)) (dist o (aMinus j)) (dist (aPlus j) (aMinus j))) →
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aPlus l))) →
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aMinus l))) →
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ (z : Z) (F : KleinerLottApprox o
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z)) β),
          ∀ x : X, (F.toFun x).fst =
            WithLp.toLp 2 (fun j => dist o (aPlus j) - dist x (aPlus j)))
    (hn : 1 ≤ n) {X : Type u} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    {q : X} {lam : ℝ} (hlam : 0 < lam) (hdim : dimH (ball q (σ⁻¹ / lam)) ≤ n)
    {Ω : Set X} (hΩ : IsOpen Ω) (hqΩ : ball q (σ⁻¹ / lam) ⊆ Ω)
    (hcomp : fourPointComparison (σ * lam ^ 2) Ω) {a b : X}
    (ha : lam * dist q a = σ⁻¹) (hb : lam * dist q b = σ⁻¹)
    (hangle : π - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
      (lam * dist a b)) :
    @HasEuclideanSplitting.{u, 0} X (m.rescale lam hlam) q 1 β := by
  have hball := MetricSpace.rescale_ball m lam hlam q (σ⁻¹ / lam)
  have hc : lam * (σ⁻¹ / lam) = σ⁻¹ := by field_simp
  rw [hc] at hball
  have hcomplete : @CompleteSpace X (m.rescale lam hlam).toUniformSpace :=
    (MetricSpace.rescale_completeSpace_iff m lam hlam).mpr inferInstance
  have hdim' : @dimH X (m.rescale lam hlam).toEMetricSpace
      (@ball X (m.rescale lam hlam).toPseudoMetricSpace q σ⁻¹) ≤ n := by
    rw [hball, MetricSpace.rescale_dimH]; exact hdim
  have hcomp' := (fourPointComparison_rescale_iff (m := m) (Ω := Ω) hlam hσ.le).mpr hcomp
  obtain ⟨Z, mZ, z, F, -⟩ := @hAC55 1 le_rfl hn X (m.rescale lam hlam) hcomplete q
    (fun _ => a) (fun _ => b)
    (fun x y η hη => MetricSpace.rescale_arbitrarily_short_curves hcurves lam hlam x y hη)
    hdim'
    (fun w hw => ⟨Ω, hΩ, hcomp', by rw [hball] at hw; exact hqΩ hw⟩)
    (fun _ => ha) (fun _ => hb) (fun _ => hangle.le)
    (fun j l hjl => absurd (Subsingleton.elim j l) hjl)
    (fun j l hjl => absurd (Subsingleton.elim j l) hjl)
  exact ⟨Z, mZ, z, ⟨F⟩⟩

/-- **LC76 (metric kernel).** A line approximation excludes rank zero on the unit ball at
every sufficiently large scale. -/
theorem exists_line_unit_ball_splitting_parameter {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : 0 < β)
    (hβone : β < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompleteSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ p : X, dimH (ball p 2) ≤ n →
      fourPointComparison ((1 / 60) ^ 2) (ball p 7) →
      ∀ {δ o : ℝ}, KleinerLottApprox p o δ → δ < δℓ →
      ∀ q ∈ ball p 1, ∀ (lam : ℝ) (hlam : 0 < lam), Λℓ ≤ lam →
        @HasEuclideanSplitting.{u, 0} X (m.rescale lam hlam) q 1 β := by
  obtain ⟨σ, hσ, hσone, hAC55⟩ := exists_prescribed_splitting_parameter.{u} hn hβ hβone
  obtain ⟨θ, hθ, hθone, hθbudget⟩ := exists_annular_strainer_angle hσ hσone
  have hcosθ : 0 < 1 - cos θ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hθ
    rw [cos_zero] at h
    linarith
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  refine ⟨min (1 / 100) ((1 - cos θ) / 12), L, lt_min (by norm_num) (by positivity), hLpos, ?_⟩
  intro X m _ hsegments p hdim hcomp1 δ o F hδ q hq lam hlam hΛ
  have hcomp := hcomp1.forall_ge (by positivity)
  have hseg' : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
    intro x y
    obtain ⟨f, _, h0, h1, hd⟩ := hsegments x y
    exact ⟨f, h0, h1, hd⟩
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hδpos := F.error_pos
  have hδ1 : δ < 1 / 100 := hδ.trans_le (min_le_left _ _)
  have hδ2 : δ < (1 - cos θ) / 12 := hδ.trans_le (min_le_right _ _)
  have hqp : dist q p < 1 := hq
  have hδinv : 100 < δ⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hδpos]
    linarith
  -- Opposite lifts of `F(q) ± 4`, shortened to equal legs.
  have hqball : q ∈ ball p δ⁻¹ := by
    change dist q p < δ⁻¹
    linarith
  have hrad := abs_le.mp (F.radial_error q hqball)
  obtain ⟨D, x, y, hD1, hD2, hqx, hqy, hex0, hex⟩ :=
    F.exists_equal_radius_line_lifts hseg' hqball (r := 4) (by norm_num) (by linarith)
  have hDpos : 0 < D := by linarith
  have hxy_up : dist x y ≤ 2 * D := by linarith
  have hangle0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist x y) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hDpos dist_nonneg hxy_up
      (by nlinarith) hθ.le
    rw [div_lt_iff₀ hDpos]
    nlinarith
  -- Shorten both legs to `s = L / λ ≤ 1 < D`.
  set s : ℝ := L / lam with hs
  have hspos : 0 < s := div_pos hLpos hlam
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hlam]
    exact hΛ
  have hballD : closedBall q D ⊆ ball p 7 := by
    intro w hw
    have hw' : dist w q ≤ D := hw
    change dist w p < 7
    linarith [dist_triangle w q p]
  obtain ⟨x', y', hqx', hqy', -, -, hchord, hcs⟩ :=
    exists_shortened_equal_leg_chord hseg' (by positivity)
      (hcomp _ le_rfl) hqx hqy hθ.le (by linarith [two_le_pi]) hangle0 hspos (by linarith) hballD
  have hlams : lam * s = L := by rw [hs]; field_simp
  have hangle := pi_sub_lt_comparisonAngle_of_scaled_chord hσ hθbudget hspos hlam hlams
    hchord dist_nonneg hcs
  have hangle' : π - σ < comparisonAngleNegCurvature σ (lam * dist q x') (lam * dist q y')
      (lam * dist x' y') := by rw [hqx', hqy']; exact hangle
  -- AC55 in the rescaled distance.
  have hσlam : (1 / 60) ^ 2 ≤ σ * lam ^ 2 := by
    have h1 : 1 ≤ σ * lam := by
      have := mul_le_mul_of_nonneg_left hΛ hσ.le
      rwa [hL, mul_inv_cancel₀ hσ.ne'] at this
    nlinarith
  apply hasEuclideanSplitting_one_of_rescaled_strainer hσ hAC55 hn hcurves hlam
    (hdim := (dimH_mono (fun w hw => ?_)).trans hdim) isOpen_ball (fun w hw => ?_)
    (hcomp _ hσlam) (by rw [hqx', hlams]) (by rw [hqy', hlams]) hangle'
  · have hw' : dist w q < L / lam := hw
    change dist w p < 2
    linarith [dist_triangle w q p]
  · have hw' : dist w q < L / lam := hw
    change dist w p < 7
    linarith [dist_triangle w q p]

end GC.MetricGeometry
