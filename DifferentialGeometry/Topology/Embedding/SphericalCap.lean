import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped ContDiff Manifold

namespace EuclideanGeometry

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def sphericalCapHeight (a : ℝ) (x : E) : ℝ :=
  a * (1 - ‖x‖ ^ 2) / (1 + a ^ 2 * ‖x‖ ^ 2)

noncomputable def sphericalCap (a : ℝ) (x : E) : E × ℝ :=
  ((1 + a * sphericalCapHeight a x) • x, sphericalCapHeight a x)

omit [NormedSpace ℝ E] in
theorem sphericalCap_denominator_pos (a : ℝ) (x : E) :
    0 < 1 + a ^ 2 * ‖x‖ ^ 2 := by positivity

omit [NormedSpace ℝ E] in
theorem one_add_mul_sphericalCapHeight (a : ℝ) (x : E) :
    1 + a * sphericalCapHeight a x = (1 + a ^ 2) / (1 + a ^ 2 * ‖x‖ ^ 2) := by
  unfold sphericalCapHeight
  field_simp [(sphericalCap_denominator_pos a x).ne']
  ring

omit [NormedSpace ℝ E] in
theorem one_add_mul_sphericalCapHeight_pos (a : ℝ) (x : E) :
    0 < 1 + a * sphericalCapHeight a x := by
  rw [one_add_mul_sphericalCapHeight]
  exact div_pos (by positivity) (sphericalCap_denominator_pos a x)

@[simp] theorem sphericalCap_zero (x : E) : sphericalCap 0 x = (x, 0) := by
  simp [sphericalCap, sphericalCapHeight]

theorem sphericalCap_of_norm_eq_one (a : ℝ) {x : E} (hx : ‖x‖ = 1) :
    sphericalCap a x = (x, 0) := by simp [sphericalCap, sphericalCapHeight, hx]

theorem sphericalCap_neg (a : ℝ) (x : E) :
    sphericalCap (-a) x = ((sphericalCap a x).1, -(sphericalCap a x).2) := by
  have h : sphericalCapHeight (-a) x = -sphericalCapHeight a x := by
    simp [sphericalCapHeight, neg_div]
  simp [sphericalCap, h]

theorem sphericalCap_norm_sq_add_sq (a : ℝ) (x : E) :
    ‖(sphericalCap a x).1‖ ^ 2 + (sphericalCap a x).2 ^ 2 =
      (a ^ 2 + ‖x‖ ^ 2) / (1 + a ^ 2 * ‖x‖ ^ 2) := by
  change ‖(1 + a * sphericalCapHeight a x) • x‖ ^ 2 + sphericalCapHeight a x ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_add_mul_sphericalCapHeight_pos a x),
    one_add_mul_sphericalCapHeight]
  unfold sphericalCapHeight
  field_simp [(sphericalCap_denominator_pos a x).ne']
  ring

theorem sphericalCap_norm_sq_add_sq_le_one {a : ℝ} (ha : |a| ≤ 1)
    {x : E} (hx : ‖x‖ ≤ 1) :
    ‖(sphericalCap a x).1‖ ^ 2 + (sphericalCap a x).2 ^ 2 ≤ 1 := by
  rw [sphericalCap_norm_sq_add_sq, div_le_one (sphericalCap_denominator_pos a x)]
  have ha' : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).mpr ha
  have hx' : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hx')]


theorem sphericalCap_one_image_closedBall_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    sphericalCap (E := E) 1 '' Metric.closedBall 0 r =
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 ∧ (1 - r ^ 2) / (1 + r ^ 2) ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
    constructor
    · rw [sphericalCap_norm_sq_add_sq]
      simp only [one_pow, one_mul]
      exact div_self (by positivity)
    · change (1 - r ^ 2) / (1 + r ^ 2) ≤ sphericalCapHeight 1 x
      simp only [sphericalCapHeight, one_pow, one_mul]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg x]
  · intro hp
    have hc : -1 < (1 - r ^ 2) / (1 + r ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have hz : 0 < 1 + p.2 := by linarith [hp.2]
    let x : E := (1 + p.2)⁻¹ • p.1
    have hxnorm : ‖x‖ = ‖p.1‖ / (1 + p.2) := by
      simp only [x, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
      ring
    have hxn : ‖x‖ ≤ r := by
      rw [hxnorm, div_le_iff₀ hz]
      have hb := (div_le_iff₀ (show 0 < 1 + r ^ 2 by positivity)).mp hp.2
      have hd : 0 ≤ r ^ 2 * (1 + p.2) - (1 - p.2) := by nlinarith
      have hm := mul_nonneg hz.le hd
      nlinarith [hp.1, norm_nonneg p.1, mul_nonneg hr hz.le]
    have hq : sphericalCapHeight 1 x = p.2 := by
      unfold sphericalCapHeight
      rw [hxnorm]
      field_simp [hz.ne']
      nlinarith [hp.1]
    refine ⟨x, mem_closedBall_zero_iff.mpr hxn, ?_⟩
    simp only [sphericalCap, hq, one_mul, x, smul_smul, mul_inv_cancel₀ hz.ne', one_smul]


theorem sphericalCap_one_image_closedBall :
    sphericalCap (E := E) 1 '' Metric.closedBall 0 1 =
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 ∧ 0 ≤ p.2} := by
  simpa using sphericalCap_one_image_closedBall_of_nonneg (E := E) (r := 1) (by norm_num)


theorem sphericalCap_neg_one_image_closedBall :
    sphericalCap (E := E) (-1) '' Metric.closedBall 0 1 =
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≤ 0} := by
  have heq : sphericalCap (E := E) (-1) =
      (fun p : E × ℝ => (p.1, -p.2)) ∘ sphericalCap 1 := by
    funext x
    exact sphericalCap_neg 1 x
  rw [heq, Set.image_comp,
    sphericalCap_one_image_closedBall]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨by simpa using hq.1, neg_nonpos.mpr hq.2⟩
  · intro hp
    refine ⟨(p.1, -p.2), ⟨?_, neg_nonneg.mpr hp.2⟩, ?_⟩
    · simpa using hp.1
    · simp

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_sphericalCapHeight {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : ℝ × E => sphericalCapHeight p.1 p.2) := by
  exact (contDiff_fst.mul (contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_snd))).div
    (contDiff_const.add ((contDiff_fst.pow 2).mul ((contDiff_norm_sq ℝ).comp contDiff_snd)))
    (fun p => (sphericalCap_denominator_pos p.1 p.2).ne')

theorem contDiff_sphericalCap {n : ℕ∞ω} : ContDiff ℝ n (fun p : ℝ × E => sphericalCap p.1 p.2) :=
  (((contDiff_const.add (contDiff_fst.mul contDiff_sphericalCapHeight)).smul contDiff_snd).prodMk
    contDiff_sphericalCapHeight)

end

end EuclideanGeometry

namespace Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} {f : M → F}

theorem IsSmoothEmbedding.sphericalCap (hf : IsSmoothEmbedding I 𝓘(ℝ, F) n f) (a : ℝ) :
    IsSmoothEmbedding I 𝓘(ℝ, F × ℝ) n (EuclideanGeometry.sphericalCap a ∘ f) := by
  let g := fun x : M => (f x, EuclideanGeometry.sphericalCapHeight a (f x))
  have hg : IsSmoothEmbedding I 𝓘(ℝ, F × ℝ) n g :=
    hf.graph (EuclideanGeometry.contDiff_sphericalCapHeight.comp
      (contDiff_const.prodMk contDiff_id))
  let T := PartialDiffeomorph.fiberwiseSmul (E := F)
    (contDiff_const.add (contDiff_const.mul contDiff_id) :
      ContDiff ℝ n (fun z : ℝ => 1 + a * z))
  have hs (x : M) : g x ∈ T.source :=
    (EuclideanGeometry.one_add_mul_sphericalCapHeight_pos a (f x)).ne'
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, F × ℝ) 𝓘(ℝ, F × ℝ) n T (Set.range g) := by
    rintro ⟨_, x, rfl⟩
    exact T.isLocalDiffeomorphAt _ _ _ (hs x)
  exact ⟨hg.isImmersion.isLocalDiffeomorphOn_comp hloc,
    T.toOpenPartialHomeomorph.isEmbedding_restrict.comp
      (hg.isEmbedding.codRestrict T.source hs)⟩

end Manifold
