import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopRechart
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The Kleiner-Lott approximation of the long sphere loop (S-FIXTURE-C2b, K2, G2 file 4)

At the constant scale `R` the rescaled sphere loop `(S² × S¹_ℓ, R⁻¹ d)` of length `ℓ ≥ 4 R / δ` is
`δ`-approximated by `ℝ ×₂ (S², R⁻¹ d_{S²})` at EVERY point, with distortion exactly zero:
the window lift `winLift_FXC2` (the unique lift in the cylinder window `-ℓ/2 < t ≤ ℓ/2` of the
shifted covering) is an isometry from the ball of radius `R / δ` onto the corresponding ball of the
product (`cyl_sq_dist_FXC2` and `loopDist_eq_cylS_of_close_FXC2`).

* `loopKL_exists_FXC2`: the factor `Z = S²` has diameter at most `D₀ / R` and
  `Nonempty (KleinerLottApprox p (0, z) δ)` for every `p`.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open GC.MetricGeometry
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS2" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

/-- The intrinsic metric space of the round unit sphere (not an instance). -/
@[reducible] def sphereMS_FXC2 : MetricSpace S2 := inducedMetricSpace gS2

/-- The intrinsic metric space of the sphere of radius `R` (distance `R⁻¹ d`, not an instance). -/
@[reducible] def sphereMSR_FXC2 {R : ℝ} (hR : 0 < R) : MetricSpace S2 :=
  sphereMS_FXC2.rescale R⁻¹ (inv_pos.mpr hR)

theorem sphereMS_dist_FXC2 (s s' : S2) :
    @dist S2 sphereMS_FXC2.toDist s s' = sphereDist_FXC2 s s' := rfl

theorem sphereMSR_dist_FXC2 {R : ℝ} (hR : 0 < R) (s s' : S2) :
    @dist S2 (sphereMSR_FXC2 hR).toDist s s' = R⁻¹ * sphereDist_FXC2 s s' := rfl

theorem exists_sphereDiam_FXC2 : ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : S2, sphereDist_FXC2 a b ≤ D := by
  let mS : MetricSpace S2 := sphereMS_FXC2
  let mP : PseudoMetricSpace S2 := mS.toPseudoMetricSpace
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (isCompact_univ : IsCompact (univ : Set S2)).isBounded
  refine ⟨max D 0, le_max_right D 0, fun a b => ?_⟩
  rw [← sphereMS_dist_FXC2]
  exact (hD (mem_univ a) (mem_univ b)).trans (le_max_left D 0)

theorem sphereDist_nonneg_FXC2 (s s' : S2) : 0 ≤ sphereDist_FXC2 s s' := ENNReal.toReal_nonneg

/-! ### The window lift -/

theorem exists_window_lift_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) (x : SphereLoop_FXC2) :
    ∃ x' : sphereCylinder, loopCoverS_FXC2 ℓ a x' = x ∧ x'.2 ∈ Ioc (-(ℓ / 2)) (ℓ / 2) := by
  obtain ⟨x0, hx0⟩ := (loopCoverS_isCoveringMap_FXC2 ℓ a hℓ).2 x
  refine ⟨((x0.1, toIocMod hℓ (-(ℓ / 2)) x0.2) : sphereCylinder), ?_, ?_⟩
  · rw [← hx0, loopCoverS_eq_iff_FXC2 a hℓ]
    refine ⟨rfl, toIocDiv hℓ (-(ℓ / 2)) x0.2, ?_⟩
    have h := self_sub_toIocMod hℓ (-(ℓ / 2)) x0.2
    simp only [zsmul_eq_mul] at h ⊢
    linarith
  · have h := toIocMod_mem_Ioc hℓ (-(ℓ / 2)) x0.2
    convert h using 2
    ring

theorem window_lift_unique_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) {x y : sphereCylinder}
    (hxy : loopCoverS_FXC2 ℓ a x = loopCoverS_FXC2 ℓ a y) (hx : x.2 ∈ Ioc (-(ℓ / 2)) (ℓ / 2))
    (hy : y.2 ∈ Ioc (-(ℓ / 2)) (ℓ / 2)) : x = y := by
  obtain ⟨h1, n, hn⟩ := (loopCoverS_eq_iff_FXC2 a hℓ).mp hxy
  have hnl : |(n : ℝ) * ℓ| < ℓ := by
    have : (n : ℝ) * ℓ = y.2 - x.2 := by linarith
    rw [this, abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      exact_mod_cast this
    rw [abs_mul, abs_of_pos hℓ] at hnl
    nlinarith
  subst hn0
  exact Prod.ext h1 (by simpa using hn.symm)

/-- The window lift of the shifted covering. -/
def winLift_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) (x : SphereLoop_FXC2) : sphereCylinder :=
  Classical.choose (exists_window_lift_FXC2 hℓ a x)

theorem winLift_cover_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) (x : SphereLoop_FXC2) :
    loopCoverS_FXC2 ℓ a (winLift_FXC2 hℓ a x) = x :=
  (Classical.choose_spec (exists_window_lift_FXC2 hℓ a x)).1

theorem winLift_mem_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) (x : SphereLoop_FXC2) :
    (winLift_FXC2 hℓ a x).2 ∈ Ioc (-(ℓ / 2)) (ℓ / 2) :=
  (Classical.choose_spec (exists_window_lift_FXC2 hℓ a x)).2

theorem winLift_eq_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) {x : SphereLoop_FXC2} {x' : sphereCylinder}
    (h : loopCoverS_FXC2 ℓ a x' = x) (hx' : x'.2 ∈ Ioc (-(ℓ / 2)) (ℓ / 2)) :
    winLift_FXC2 hℓ a x = x' :=
  window_lift_unique_FXC2 hℓ a ((winLift_cover_FXC2 hℓ a x).trans h.symm)
    (winLift_mem_FXC2 hℓ a x) hx'

/-- Exact distance of two points whose window lifts are at most `ℓ / 2` apart. -/
theorem loopDist_eq_window_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) (x y : SphereLoop_FXC2)
    (h : |(winLift_FXC2 hℓ a x).2 - (winLift_FXC2 hℓ a y).2| ≤ ℓ / 2) :
    loopDist_FXC2 ℓ hℓ x y = dist (winLift_FXC2 hℓ a x) (winLift_FXC2 hℓ a y) := by
  have := loopDist_eq_cylS_of_close_FXC2 ℓ a hℓ (winLift_FXC2 hℓ a x) (winLift_FXC2 hℓ a y) h
  rwa [winLift_cover_FXC2, winLift_cover_FXC2] at this

theorem exists_shift_base_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (p0 : SphereLoop_FXC2) :
    ∃ a : ℝ, loopCoverS_FXC2 ℓ a (p0.1, 0) = p0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p0.2
  refine ⟨ℓ * s, Prod.ext rfl ?_⟩
  change (((0 + ℓ * s) / ℓ : ℝ) : AddCircle (1 : ℝ)) = p0.2
  rw [zero_add, mul_div_cancel_left₀ _ hℓ.ne']
  exact hs

/-- Distance of the rescaled carrier. -/
theorem distR_loopMS3_FXC2 (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) (x y : LoopC_FXC2 ℓ) :
    @dist _ ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x y =
      R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x) ((loopDiffeo_FXC2 ℓ).symm y) := by
  change R⁻¹ * (riemannianEDistOf (loopMetric3_FXC2 ℓ) x y).toReal = _
  rw [loopMetric3_edist_FXC2]
  rfl

theorem inv_mul_cancel_left_FXC2 {R : ℝ} (hR : 0 < R) (r : ℝ) : R⁻¹ * (R * r) = r := by
  field_simp

theorem prod_dist_sq_real_FXC2 {Z : Type} [MetricSpace Z] (a b : WithLp 2 (ℝ × Z)) :
    dist a b ^ 2 = (a.fst - b.fst) ^ 2 + dist a.snd b.snd ^ 2 := by
  rw [WithLp.prod_dist_sq_eq_add_sq, Real.dist_eq, sq_abs]

theorem abs_fst_le_dist_FXC2 {Z : Type} [MetricSpace Z] (a b : WithLp 2 (ℝ × Z)) :
    |a.fst - b.fst| ≤ dist a b := by
  have h := prod_dist_sq_real_FXC2 a b
  have h2 : |a.fst - b.fst| ^ 2 ≤ dist a b ^ 2 := by
    rw [sq_abs, h]
    nlinarith [sq_nonneg (dist a.snd b.snd)]
  exact (sq_le_sq₀ (abs_nonneg _) dist_nonneg).1 h2

/-- **The Kleiner-Lott approximation of the long sphere loop by `ℝ ×₂ Z`**, `Z` the sphere of
radius `R`, at every point (core form: `Z` is any metric space identified with the sphere with the
distance `R⁻¹ d`). -/
theorem loopKL_core_FXC2 (ℓ : LoopLen_FXC2) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hℓ : 4 * R / δ ≤ ℓ.1) {Z : Type} [mZ : MetricSpace Z] (φ : Z ≃ S2)
    (hφ : ∀ s s' : Z, dist s s' = R⁻¹ * sphereDist_FXC2 (φ s) (φ s')) (p : LoopC_FXC2 ℓ) :
    Nonempty (@KleinerLottApprox (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × Z))
      ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _ p
      (WithLp.toLp 2 ((0 : ℝ), φ.symm ((loopDiffeo_FXC2 ℓ).symm p).1)) δ) := by
  have hℓ0 : 0 < ℓ.1 := ℓ.2
  have hRδ : R / δ ≤ ℓ.1 / 4 := by
    have : 4 * R / δ = 4 * (R / δ) := by ring
    linarith
  have hδinv : R * δ⁻¹ ≤ ℓ.1 / 4 := by
    have : R / δ = R * δ⁻¹ := div_eq_mul_inv R δ
    linarith
  obtain ⟨a, hbase⟩ := exists_shift_base_FXC2 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm p)
  have hcover := winLift_cover_FXC2 ℓ.2 a
  have hmem := winLift_mem_FXC2 ℓ.2 a
  have huniq : ∀ {x : SphereLoop_FXC2} {x' : sphereCylinder}, loopCoverS_FXC2 ℓ.1 a x' = x →
      x'.2 ∈ Ioc (-(ℓ.1 / 2)) (ℓ.1 / 2) → winLift_FXC2 ℓ.2 a x = x' :=
    fun h hx' => winLift_eq_FXC2 ℓ.2 a h hx'
  have hdist := loopDist_eq_window_FXC2 ℓ.2 a
  generalize winLift_FXC2 ℓ.2 a = W at hcover hmem huniq hdist
  generalize hp0 : (loopDiffeo_FXC2 ℓ).symm p = p0 at hbase
  have hWp : W p0 = (p0.1, 0) := huniq hbase ⟨by linarith, by simp; linarith⟩
  -- the height of a window lift is bounded by the distance to the base point
  have hheight : ∀ x0 : SphereLoop_FXC2, |(W x0).2| ≤ loopDist_FXC2 ℓ.1 ℓ.2 x0 p0 := by
    intro x0
    have hw := hmem x0
    have h1 : |(W x0).2 - (W p0).2| ≤ ℓ.1 / 2 := by
      rw [hWp]
      simp only [sub_zero]
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2]
    rw [hdist x0 p0 h1]
    have := cyl_snd_le_dist_FXC2 (W x0) (W p0)
    rw [hWp] at this
    rw [hWp]
    simpa using this
  have hsmall : ∀ x : LoopC_FXC2 ℓ, R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x) p0 <
      δ⁻¹ → |(W ((loopDiffeo_FXC2 ℓ).symm x)).2| < R * δ⁻¹ := by
    intro x hx
    have h1 := hheight ((loopDiffeo_FXC2 ℓ).symm x)
    have h2 : loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x) p0 < R * δ⁻¹ := by
      have := mul_lt_mul_of_pos_left hx hR
      rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at this
    linarith
  refine ⟨@KleinerLottApprox.mk (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × Z))
    ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _ p _ δ hδ hδ1
    (fun x => WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x)).2,
      φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x)).1)) ?_ ?_ ?_⟩
  · show WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm p)).2,
      φ.symm (W ((loopDiffeo_FXC2 ℓ).symm p)).1) = _
    rw [hp0, hWp]
    simp
  · let mR : MetricSpace (LoopC_FXC2 ℓ) := (loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)
    intro x hx x' hx'
    have hx1 : R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x) p0 < δ⁻¹ := by
      have := Metric.mem_ball.mp hx
      rwa [distR_loopMS3_FXC2 ℓ hR x p, hp0] at this
    have hx1' : R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x') p0 < δ⁻¹ := by
      have := Metric.mem_ball.mp hx'
      rwa [distR_loopMS3_FXC2 ℓ hR x' p, hp0] at this
    have ht := hsmall x hx1
    have ht' := hsmall x' hx1'
    have hclose : |(W ((loopDiffeo_FXC2 ℓ).symm x)).2 - (W ((loopDiffeo_FXC2 ℓ).symm x')).2| ≤
        ℓ.1 / 2 := by
      rw [abs_lt] at ht ht'
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    have hL := hdist ((loopDiffeo_FXC2 ℓ).symm x) ((loopDiffeo_FXC2 ℓ).symm x') hclose
    have hsq := cyl_sq_dist_FXC2 (W ((loopDiffeo_FXC2 ℓ).symm x))
      (W ((loopDiffeo_FXC2 ℓ).symm x'))
    have hdx : dist x x' = R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm x)
        ((loopDiffeo_FXC2 ℓ).symm x') := distR_loopMS3_FXC2 ℓ hR x x'
    have hF := prod_dist_sq_real_FXC2 (Z := Z)
      (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x)).2,
        φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x)).1))
      (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x')).2,
        φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x')).1))
    have hZ : dist (φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x)).1)
        (φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x')).1) =
        R⁻¹ * sphereDist_FXC2 (W ((loopDiffeo_FXC2 ℓ).symm x)).1
          (W ((loopDiffeo_FXC2 ℓ).symm x')).1 := by
      rw [hφ]
      simp
    have heq : dist (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x)).2,
          φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x)).1))
        (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x')).2,
          φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x')).1)) = dist x x' := by
      refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
      rw [hF, hdx, hL, mul_pow, hsq]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, hZ]
      ring
    change |dist (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x)).2,
          φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x)).1))
        (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm x')).2,
          φ.symm (W ((loopDiffeo_FXC2 ℓ).symm x')).1)) - dist x x'| ≤ δ
    rw [heq, sub_self, abs_zero]
    exact hδ.le
  · let mR : MetricSpace (LoopC_FXC2 ℓ) := (loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)
    intro y hy
    have hq : dist y (WithLp.toLp 2 ((0 : ℝ), φ.symm p0.1)) < δ⁻¹ - δ := hy
    have hsq := prod_dist_sq_real_FXC2 y (WithLp.toLp 2 ((0 : ℝ), φ.symm p0.1))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, sub_zero] at hsq
    have hrabs : |y.fst| ≤ dist y (WithLp.toLp 2 ((0 : ℝ), φ.symm p0.1)) := by
      have := abs_fst_le_dist_FXC2 y (WithLp.toLp 2 ((0 : ℝ), φ.symm p0.1))
      simpa using this
    set dq := dist y (WithLp.toLp 2 ((0 : ℝ), φ.symm p0.1)) with hdq
    have hdq0 : 0 ≤ dq := dist_nonneg
    have hRr : R * |y.fst| < ℓ.1 / 4 := by
      have h1 : R * |y.fst| ≤ R * dq := mul_le_mul_of_nonneg_left hrabs hR.le
      have h2 : R * dq < R * δ⁻¹ := by
        apply mul_lt_mul_of_pos_left _ hR
        linarith
      linarith
    let xt : sphereCylinder := (φ y.snd, R * y.fst)
    have hwin : xt.2 ∈ Ioc (-(ℓ.1 / 2)) (ℓ.1 / 2) := by
      have : |R * y.fst| = R * |y.fst| := by rw [abs_mul, abs_of_pos hR]
      have h3 : |xt.2| < ℓ.1 / 4 := by
        change |R * y.fst| < ℓ.1 / 4
        linarith
      rw [abs_lt] at h3
      constructor <;> linarith [h3.1, h3.2]
    have hWx : W (loopCoverS_FXC2 ℓ.1 a xt) = xt := huniq rfl hwin
    have hFx : (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm
        (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a xt)))).2,
        φ.symm (W ((loopDiffeo_FXC2 ℓ).symm (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a xt)))).1) :
        WithLp 2 (ℝ × Z)) = y := by
      rw [Diffeomorph.symm_apply_apply, hWx]
      change WithLp.toLp 2 (R⁻¹ * (R * y.fst), φ.symm (φ y.snd)) = y
      rw [inv_mul_cancel_left_FXC2 hR, Equiv.symm_apply_apply]
      rfl
    -- the preimage lies in the ball
    have hcyl : dist xt (p0.1, 0) = R * dq := by
      have h1 := cyl_sq_dist_FXC2 xt (p0.1, 0)
      have h2 : dist y.snd (φ.symm p0.1) = R⁻¹ * sphereDist_FXC2 (φ y.snd) p0.1 := by
        rw [hφ]
        simp
      have h3 : dq ^ 2 = y.fst ^ 2 + (R⁻¹ * sphereDist_FXC2 (φ y.snd) p0.1) ^ 2 := by
        rw [hdq, hsq, h2]
      refine (sq_eq_sq₀ dist_nonneg (mul_nonneg hR.le hdq0)).mp ?_
      rw [h1, mul_pow, h3]
      change (R * y.fst - 0) ^ 2 + sphereDist_FXC2 (φ y.snd) p0.1 ^ 2 =
        R ^ 2 * (y.fst ^ 2 + (R⁻¹ * sphereDist_FXC2 (φ y.snd) p0.1) ^ 2)
      field_simp
      ring
    have hball : loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a xt) ∈ Metric.ball p δ⁻¹ := by
      rw [Metric.mem_ball, distR_loopMS3_FXC2 ℓ hR, Diffeomorph.symm_apply_apply, hp0]
      have h4 := loopDist_le_cylS_FXC2 ℓ.1 a ℓ.2 xt (p0.1, 0)
      rw [hbase] at h4
      rw [hcyl] at h4
      have h5 : R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 (loopCoverS_FXC2 ℓ.1 a xt) p0 ≤ dq := by
        calc R⁻¹ * loopDist_FXC2 ℓ.1 ℓ.2 (loopCoverS_FXC2 ℓ.1 a xt) p0 ≤ R⁻¹ * (R * dq) :=
            mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hR.le)
          _ = dq := by field_simp
      linarith
    refine le_trans (Metric.infDist_le_dist_of_mem
      (Set.mem_image_of_mem _ hball)) ?_
    change dist y (WithLp.toLp 2 (R⁻¹ * (W ((loopDiffeo_FXC2 ℓ).symm
        (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a xt)))).2,
        φ.symm (W ((loopDiffeo_FXC2 ℓ).symm (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a xt)))).1)) ≤ δ
    rw [hFx, dist_self]
    exact hδ.le

/-- **The Kleiner-Lott approximation of the long sphere loop by `ℝ ×₂ S²_R`** at every point. -/
theorem loopKL_exists_FXC2 (ℓ : LoopLen_FXC2) {R δ D0 : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hℓ : 4 * R / δ ≤ ℓ.1) (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0)
    (p : LoopC_FXC2 ℓ) :
    ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      (∀ y y' : Z, dist y y' ≤ D0 / R) ∧
      Nonempty (@KleinerLottApprox (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × Z))
        ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _ p (WithLp.toLp 2 ((0 : ℝ), z)) δ) := by
  refine ⟨S2, sphereMSR_FXC2 hR, ((loopDiffeo_FXC2 ℓ).symm p).1, ?_⟩
  refine ⟨fun y y' => ?_, ?_⟩
  · change R⁻¹ * sphereDist_FXC2 y y' ≤ D0 / R
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hD0 _ _) (inv_nonneg.mpr hR.le)
  · exact loopKL_core_FXC2 ℓ hR hδ hδ1 hℓ (mZ := sphereMSR_FXC2 hR) (Equiv.refl S2)
      (fun _ _ => rfl) p

end DifferentialGeometry.Geometry.Collapse
