import DifferentialGeometry.Geometry.Collapse.MetricRank.ThinOnlyRank
import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxDistortionExamples

/-!
# Explicit consumers of the thin-only rank theorems (S-X144c, group G10)

Scale `ρ ≡ 2` (the rescaled metric is `dist / 2`), register `β = (1/20, 1/10, 3/20)` of
`RankAdaptersExamples` (`betaRegister_SMR`). The space is `M = A ×₂ [0, 1/400]` and the
approximation of the rescaled metric `(M, dist / 2)` is the half-scaling
`(a, t) ↦ (a / 2, t / 2) : M → A ×₂ [0, 1/800]` (surjective, multiplies distances by `1/2`), a
Kleiner-Lott approximation of every tolerance `δ ∈ (0, 1)`; the thin factor `[0, 1/800]` has
`D = 1/800` and `δ = 1/200` gives `δ + D = 5/800 ≤ 1/100`.

* `thin_halfscale_approx_SMR` : the half-scaling approximation, for any `A`, `A'` and a
  surjective `g : A → A'` with `d(g x, g y) = d(x, y) / 2`;
* `thin_line_only_scaledSplittingRank_one_SMR` : `ℝ ×₂ [0, 1/400]` at `(0, 0)`: rank exactly `1`
  (no explicit one-splitting: it is derived from `δ = 1/200` and `β 1 = 1/20`);
* `thin_plane_only_scaledSplittingRank_two_SMR` : `ℝ² ×₂ [0, 1/400]` at `(0, 0)`: rank exactly
  `2` (two-splitting derived from `δ = 1/200`, `β 2 = 1/10`).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

local notation "ZT" => {t : ℝ // t ∈ Set.Icc (0 : ℝ) (1 / 400)}
local notation "ZH" => {t : ℝ // t ∈ Set.Icc (0 : ℝ) (1 / 800)}

/-- The half-scaling `[0, 1/400] → [0, 1/800]`, `t ↦ t / 2`. -/
noncomputable def halfThin_SMR (t : ZT) : ZH :=
  ⟨2⁻¹ * t.1, by
    have h := t.2
    constructor <;> nlinarith [h.1, h.2]⟩

/-- The base point `0` of the scaled thin factor. -/
def thinBaseH_SMR : ZH := ⟨0, by norm_num⟩

theorem halfThin_dist_SMR (s t : ZT) : dist (halfThin_SMR s) (halfThin_SMR t) = 2⁻¹ * dist s t := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  change |2⁻¹ * s.1 - 2⁻¹ * t.1| = 2⁻¹ * |s.1 - t.1|
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]

theorem halfThin_surjective_SMR : Function.Surjective halfThin_SMR := by
  intro s
  refine ⟨⟨2 * s.1, ?_⟩, ?_⟩
  · have h := s.2
    constructor <;> nlinarith [h.1, h.2]
  · apply Subtype.ext
    change 2⁻¹ * (2 * s.1) = s.1
    ring

theorem halfThin_base_SMR : halfThin_SMR thinBase_SMR = thinBaseH_SMR := by
  apply Subtype.ext
  change 2⁻¹ * (0 : ℝ) = 0
  ring

/-- All distances of the scaled thin factor `[0, 1/800]` are `≤ 1/800`. -/
theorem thin_factorH_dist_SMR (z₁ z₂ : ZH) : dist z₁ z₂ ≤ 1 / 800 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  have h1 := z₁.2
  have h2 := z₂.2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The half-scaling approximation.** For `g : A → A'` surjective with `d(g x, g y) = d(x, y)/2`,
the map `(a, t) ↦ (g a, t/2)` is a Kleiner-Lott `δ`-approximation of the rescaled metric
`(A ×₂ [0, 1/400], dist / 2)` into `A' ×₂ [0, 1/800]` for every `δ ∈ (0, 1)`. -/
theorem thin_halfscale_approx_SMR {A A' : Type*} [MetricSpace A] [MetricSpace A'] (g : A → A')
    (hg : ∀ x y, dist (g x) (g y) = 2⁻¹ * dist x y) (hs : Function.Surjective g) (a : A)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Nonempty (@KleinerLottApprox (WithLp 2 (A × ZT)) (WithLp 2 (A' × ZH))
      (MetricSpace.rescale (inferInstance : MetricSpace (WithLp 2 (A × ZT))) (2 : ℝ)⁻¹
        (inv_pos.mpr two_pos)) _
      (WithLp.toLp 2 (a, thinBase_SMR)) (WithLp.toLp 2 (g a, thinBaseH_SMR)) δ) := by
  refine kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr two_pos)
    (fun w : WithLp 2 (A × ZT) => (WithLp.toLp 2 (g w.fst, halfThin_SMR w.snd) :
      WithLp 2 (A' × ZH))) ?_ ?_ ?_ hδ hδ1
  · intro v w
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    have h1 := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 (g v.fst, halfThin_SMR v.snd) : WithLp 2 (A' × ZH))
      (WithLp.toLp 2 (g w.fst, halfThin_SMR w.snd))
    have h2 := WithLp.prod_dist_sq_eq_add_sq v w
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h1
    rw [h1, mul_pow, h2, hg, halfThin_dist_SMR]
    ring
  · rintro ⟨a', t'⟩
    obtain ⟨a₀, rfl⟩ := hs a'
    obtain ⟨t₀, rfl⟩ := halfThin_surjective_SMR t'
    exact ⟨WithLp.toLp 2 (a₀, t₀), rfl⟩
  · change WithLp.toLp 2 (g a, halfThin_SMR thinBase_SMR) = _
    rw [halfThin_base_SMR]

/-- The half-scaling of `ℝ`, `x ↦ x / 2`. -/
theorem real_half_dist_SMR (x y : ℝ) : dist (2⁻¹ * x) (2⁻¹ * y) = 2⁻¹ * dist x y := by
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]

/-- The half-scaling of `ℝ²`, `v ↦ v / 2`. -/
theorem plane_half_dist_SMR (x y : EuclideanSpace ℝ (Fin 2)) :
    dist ((2 : ℝ)⁻¹ • x) ((2 : ℝ)⁻¹ • y) = 2⁻¹ * dist x y := by
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]

/-- **Thin line, rank exactly one from the approximation alone.** `M = ℝ ×₂ [0, 1/400]` at
`(0, 0)`, scale `ρ ≡ 2`, register `β = (1/20, 1/10, 3/20)`: the one-splitting at `β 1 = 1/20` is
produced by `exists_splitting_of_thin_product_line_SMR` from `δ = 1/200`. -/
theorem thin_line_only_scaledSplittingRank_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (ℝ × ZT) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR)) = 1 :=
  scaledSplittingRank_eq_one_of_thin_line_only_SMR (D := 1 / 800)
    (thin_halfscale_approx_SMR (fun x : ℝ => 2⁻¹ * x) real_half_dist_SMR
      (fun y => ⟨2 * y, by ring⟩) 0 (δ := 1 / 200) (by norm_num) (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_one_SMR]; norm_num)
    (by rw [betaRegister_one_SMR]; norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR])

/-- **Thin plane, rank exactly two from the approximation alone.** `M = ℝ² ×₂ [0, 1/400]` at
`(0, 0)`, scale `ρ ≡ 2`, register `β = (1/20, 1/10, 3/20)`: the two-splitting at `β 2 = 1/10`
is produced by `exists_splitting_of_thin_product_plane_SMR` from `δ = 1/200`. -/
theorem thin_plane_only_scaledSplittingRank_two_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT) => (2 : ℝ))
      (fun _ => two_pos) betaRegister_SMR
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), thinBase_SMR)) = 2 :=
  scaledSplittingRank_eq_two_of_thin_plane_only_SMR (D := 1 / 800)
    (thin_halfscale_approx_SMR (fun v : EuclideanSpace ℝ (Fin 2) => (2 : ℝ)⁻¹ • v)
      plane_half_dist_SMR
      (fun y => ⟨(2 : ℝ) • y, by simp [smul_smul]⟩) 0 (δ := 1 / 200) (by norm_num)
      (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_two_SMR]; norm_num) (by rw [betaRegister_three_SMR])

/-- The same two ranks in the register form (`1/50 ≤ β k < 1`), line. -/
theorem thin_line_only_scaledSplittingRank_one_hundredth_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (ℝ × ZT) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR)) = 1 :=
  scaledSplittingRank_eq_one_of_thin_line_only_of_hundredth_SMR (D := 1 / 800)
    (thin_halfscale_approx_SMR (fun x : ℝ => 2⁻¹ * x) real_half_dist_SMR
      (fun y => ⟨2 * y, by ring⟩) 0 (δ := 1 / 300) (by norm_num) (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_one_SMR]; norm_num)
    (by rw [betaRegister_one_SMR]; norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR])

/-- The same two ranks in the register form (`1/50 ≤ β k < 1`), plane. -/
theorem thin_plane_only_scaledSplittingRank_two_hundredth_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT) => (2 : ℝ))
      (fun _ => two_pos) betaRegister_SMR
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), thinBase_SMR)) = 2 :=
  scaledSplittingRank_eq_two_of_thin_plane_only_of_hundredth_SMR (D := 1 / 800)
    (thin_halfscale_approx_SMR (fun v : EuclideanSpace ℝ (Fin 2) => (2 : ℝ)⁻¹ • v)
      plane_half_dist_SMR
      (fun y => ⟨(2 : ℝ) • y, by simp [smul_smul]⟩) 0 (δ := 1 / 300) (by norm_num)
      (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_two_SMR]; norm_num) (by rw [betaRegister_three_SMR])

end GC.MetricGeometry
