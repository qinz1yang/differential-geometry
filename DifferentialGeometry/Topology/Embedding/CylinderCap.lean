import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Metric
open scoped ContDiff Manifold

namespace EuclideanGeometry

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cylinderCap (a : ℝ) (x : E) : E × ℝ :=
  ((Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (‖x‖ ^ 2)))⁻¹ • x,
    a * (‖x‖ ^ 2 - 1))

private theorem cylinder_cap_profile_pos (s : ℝ) :
    0 < Real.smoothMax (1 / 4) (1 / 2) s := by
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    ((le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _))

@[simp] theorem cylinderCap_snd (a : ℝ) (x : E) :
    (cylinderCap a x).2 = a * (‖x‖ ^ 2 - 1) := rfl

@[simp] theorem cylinderCap_zero (a : ℝ) : cylinderCap a (0 : E) = (0, -a) := by
  simp [cylinderCap]

theorem cylinderCap_of_norm_sq_ge (a : ℝ) {x : E} (hx : 3 / 4 ≤ ‖x‖ ^ 2) :
    cylinderCap a x = (‖x‖⁻¹ • x, a * (‖x‖ ^ 2 - 1)) := by
  have hmax : Real.smoothMax (1 / 4) (1 / 2) (‖x‖ ^ 2) = ‖x‖ ^ 2 := by
    rw [Real.smoothMax.eq_max_of_le (by norm_num), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp only [cylinderCap, hmax, Real.sqrt_sq (norm_nonneg x)]

theorem cylinderCap_of_norm_eq_one (a : ℝ) {x : E} (hx : ‖x‖ = 1) :
    cylinderCap a x = (x, 0) := by
  rw [cylinderCap_of_norm_sq_ge a (by rw [hx]; norm_num)]
  simp [hx]

theorem norm_cylinderCap_fst_le_one (a : ℝ) (x : E) : ‖(cylinderCap a x).1‖ ≤ 1 := by
  have hg := cylinder_cap_profile_pos (‖x‖ ^ 2)
  have hs := Real.sqrt_pos.mpr hg
  change ‖(Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (‖x‖ ^ 2)))⁻¹ • x‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_le_iff₀ hs, mul_one]
  apply (Real.le_sqrt (norm_nonneg x) hg.le).mpr
  exact (le_max_right _ _).trans (Real.smoothMax.max_le (by norm_num) _ _)

theorem cylinderCap_snd_mem_Icc {a : ℝ} (ha : 0 ≤ a) {x : E} (hx : ‖x‖ ≤ 1) :
    (cylinderCap a x).2 ∈ Icc (-a) 0 := by
  rw [cylinderCap_snd]
  constructor
  · nlinarith [sq_nonneg ‖x‖, mul_nonneg ha (sq_nonneg ‖x‖)]
  · exact mul_nonpos_of_nonneg_of_nonpos ha (by nlinarith [norm_nonneg x])

theorem cylinderCap_snd_eq_neg_iff {a : ℝ} (ha : a ≠ 0) (x : E) :
    (cylinderCap a x).2 = -a ↔ x = 0 := by
  rw [cylinderCap_snd]
  constructor
  · intro h
    have hh : a * ‖x‖ ^ 2 = 0 := by nlinarith [h]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left ha))
  · rintro rfl
    simp

theorem cylinderCap_neg (a : ℝ) (x : E) :
    cylinderCap (-a) x = ((cylinderCap a x).1, -(cylinderCap a x).2) := by
  simp [cylinderCap]

theorem cylinderCap_sqrt_smul {a t : ℝ} (ha : a ≠ 0) (ht : -(1 / 4) ≤ t / a)
    {θ : E} (hθ : ‖θ‖ = 1) :
    cylinderCap a (Real.sqrt (1 + t / a) • θ) = (θ, t) := by
  have hp : 0 < 1 + t / a := by linarith
  have hs : 0 < Real.sqrt (1 + t / a) := Real.sqrt_pos.mpr hp
  have hn : ‖Real.sqrt (1 + t / a) • θ‖ = Real.sqrt (1 + t / a) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hθ, mul_one]
  have hn2 : ‖Real.sqrt (1 + t / a) • θ‖ ^ 2 = 1 + t / a := by
    rw [hn, Real.sq_sqrt hp.le]
  rw [cylinderCap_of_norm_sq_ge a (by rw [hn2]; linarith), hn2, hn,
    smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  congr 1
  field_simp
  ring

theorem cylinderCap_of_norm_sq_le (a : ℝ) {x : E} (hx : ‖x‖ ^ 2 ≤ 1 / 4) :
    cylinderCap a x = ((Real.sqrt (1 / 2))⁻¹ • x, a * (‖x‖ ^ 2 - 1)) := by
  have hmax : Real.smoothMax (1 / 4) (1 / 2) (‖x‖ ^ 2) = 1 / 2 := by
    rw [Real.smoothMax.eq_max_of_le (by norm_num), max_eq_left (by linarith)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  simp only [cylinderCap, hmax]

theorem cylinderCap_image_sphere (a : ℝ) :
    cylinderCap (E := E) a '' sphere 0 1 = sphere 0 1 ×ˢ {0} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [cylinderCap_of_norm_eq_one a (mem_sphere_zero_iff_norm.mp hx)]
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, ht⟩
    refine ⟨p.1, hx, ?_⟩
    rw [cylinderCap_of_norm_eq_one a (mem_sphere_zero_iff_norm.mp hx)]
    exact Prod.ext rfl ht.symm

theorem cylinderCap_image_closedBall_subset {a : ℝ} (ha : 0 ≤ a) :
    cylinderCap (E := E) a '' closedBall 0 1 ⊆ closedBall 0 1 ×ˢ Icc (-a) 0 := by
  rintro p ⟨x, hx, rfl⟩
  exact ⟨mem_closedBall_zero_iff.mpr (norm_cylinderCap_fst_le_one a x),
    cylinderCap_snd_mem_Icc ha (mem_closedBall_zero_iff.mp hx)⟩

theorem cylinderCap_image_annulus {a : ℝ} (ha : 0 < a) :
    cylinderCap (E := E) a '' {x | 3 / 4 ≤ ‖x‖ ^ 2 ∧ ‖x‖ ≤ 1} =
      sphere 0 1 ×ˢ Icc (-a / 4) 0 := by
  ext p
  constructor
  · rintro ⟨x, ⟨hxl, hxu⟩, rfl⟩
    have hxpos : 0 < ‖x‖ := by nlinarith [norm_nonneg x]
    rw [cylinderCap_of_norm_sq_ge a hxl]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxl)]
    · exact mul_nonpos_of_nonneg_of_nonpos ha.le (by nlinarith [norm_nonneg x])
  · rintro ⟨hθ, ht⟩
    have hratio : -(1 / 4) ≤ p.2 / a := by
      rw [le_div_iff₀ ha]
      linarith [ht.1]
    have hp : 0 < 1 + p.2 / a := by linarith
    have hn : ‖Real.sqrt (1 + p.2 / a) • p.1‖ = Real.sqrt (1 + p.2 / a) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mem_sphere_zero_iff_norm.mp hθ, mul_one]
    refine ⟨Real.sqrt (1 + p.2 / a) • p.1, ⟨?_, ?_⟩,
      cylinderCap_sqrt_smul ha.ne' hratio (mem_sphere_zero_iff_norm.mp hθ)⟩
    · rw [hn, Real.sq_sqrt hp.le]
      linarith
    · rw [hn, Real.sqrt_le_one]
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht.2 ha.le)

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem contDiff_cylinder_cap_profile :
    ContDiff ℝ ∞ (fun s : ℝ => (Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) s))⁻¹) := by
  exact (((Real.smoothMax.contDiff (1 / 4)).comp (contDiff_const.prodMk contDiff_id)).sqrt
    (fun s => (cylinder_cap_profile_pos s).ne')).inv
    (fun s => (Real.sqrt_pos.mpr (cylinder_cap_profile_pos s)).ne')

theorem contDiff_cylinderCap : ContDiff ℝ ∞ (fun p : ℝ × E => cylinderCap p.1 p.2) := by
  exact (((contDiff_cylinder_cap_profile.comp ((contDiff_norm_sq ℝ).comp contDiff_snd)).smul
    contDiff_snd).prodMk (contDiff_fst.mul
      (((contDiff_norm_sq ℝ).comp contDiff_snd).sub contDiff_const)))

theorem fderiv_cylinderCap_snd (a : ℝ) (x : E) :
    fderiv ℝ (fun y : E => (cylinderCap a y).2) x = (2 * a) • innerSL ℝ x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).const_mul a
  change fderiv ℝ (fun y : E => a * (‖y‖ ^ 2 - 1)) x = _
  rw [h.fderiv]
  ext v
  simp only [smul_apply, smul_eq_mul]
  ring

theorem fderiv_cylinderCap_snd_eq_zero_iff {a : ℝ} (ha : a ≠ 0) (x : E) :
    fderiv ℝ (fun y : E => (cylinderCap a y).2) x = 0 ↔ x = 0 := by
  rw [fderiv_cylinderCap_snd]
  constructor
  · intro h
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L x) h
    simp only [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul,
      zero_apply] at hh
    have hn : ‖x‖ ^ 2 = 0 := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) ha)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · rintro rfl
    simp

theorem fderiv_fderiv_cylinderCap_snd (a : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => (cylinderCap a y).2)) x =
      (2 * a) • innerSL ℝ := by
  rw [show fderiv ℝ (fun y : E => (cylinderCap a y).2) =
    (fun y => (2 * a) • innerSL ℝ y) from funext (fderiv_cylinderCap_snd a)]
  exact ((innerSL ℝ).hasFDerivAt.const_smul (2 * a)).fderiv

end

end EuclideanGeometry

namespace Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f : M → F}

theorem IsSmoothEmbedding.cylinderCap (hf : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ f)
    {a : ℝ} (ha : a ≠ 0) :
    IsSmoothEmbedding I 𝓘(ℝ, F × ℝ) ∞ (EuclideanGeometry.cylinderCap a ∘ f) := by
  let g : F → ℝ := fun x => a * (‖x‖ ^ 2 - 1)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  let k : ℝ → ℝ := fun z =>
    (Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (1 + z / a)))⁻¹
  have hk : ContDiff ℝ ∞ k := EuclideanGeometry.contDiff_cylinder_cap_profile.comp
    (contDiff_const.add (contDiff_id.div_const a))
  have hk0 : ∀ z, k z ≠ 0 := fun z => inv_ne_zero
    (Real.sqrt_pos.mpr (EuclideanGeometry.cylinder_cap_profile_pos (1 + z / a))).ne'
  have h := (hf.graph hg).diffeomorph_comp (Diffeomorph.fiberwiseSmul hk hk0)
  have heq : (Diffeomorph.fiberwiseSmul (E := F) hk hk0) ∘ (fun x => (f x, g (f x))) =
      EuclideanGeometry.cylinderCap a ∘ f := by
    funext x
    have hz : 1 + g (f x) / a = ‖f x‖ ^ 2 := by dsimp [g]; field_simp; ring
    simp only [Function.comp_def, Diffeomorph.fiberwiseSmul_apply, k, hz,
      EuclideanGeometry.cylinderCap, g]
  exact heq ▸ h

end Manifold
