import DifferentialGeometry.Geometry.Curvature.Surface.DevelopingCoframe
import DifferentialGeometry.Analysis.Calculus.Potential
import DifferentialGeometry.Analysis.Calculus.Inverse.UniformCovering
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The developing map of a doubly periodic coefficient field with closed connection form

Let `b` be a `C²` positive symmetric coefficient field on a two-dimensional space `E`,
periodic along a basis `(v₁, v₂)`, whose connection form `ω = P dx + Q dy`
(`ConnectionPotential.lean`) is closed: `∂₂ P = ∂₁ Q` (this is flatness, by the divergence
identity of `DivergenceForm.lean`). Then:

1. `ω` has a potential `α` (the tree's radial Poincaré lemma, `radialPotential_hasFDerivAt`);
2. the rotated coframe `η¹ + i η² = e^{iα} (θ¹ + i θ²)` is closed (structure equations of
   `DevelopingCoframe.lean`), so it has a potential `φ : E → ℂ` with `φ*⟨·,·⟩ = b`;
3. `φ (y + vⱼ) = e^{i aⱼ} φ y + dⱼ` (`α (y + vⱼ) − α y` is constant);
4. the uniform inverse function theorem (`UniformCovering.lean`: derivative bounded below by
   periodicity and compactness, uniformly continuous by equivariance) makes `φ` a covering map,
   hence a homeomorphism `E ≃ₜ ℂ`;
5. `e^{i aⱼ} = 1`, since an affine rotation of `ℂ` with nontrivial linear part has a fixed point.

Result: `exists_developing_of_closed_connection`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Linear

private theorem exists_coords (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) (x : E) : ∃ a c : ℝ, x = a • v₁ + c • v₂ := by
  have htop : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hE])
  rw [Matrix.range_cons_cons_empty] at htop
  have hx : x ∈ Submodule.span ℝ ({v₁, v₂} : Set E) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, c, h⟩ := Submodule.mem_span_pair.mp hx
  exact ⟨a, c, h.symm⟩

/-- Coordinate functionals of a basis pair. -/
private theorem exists_coordinate_functionals (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ∃ c₁ c₂ : E →L[ℝ] ℝ, c₁ v₁ = 1 ∧ c₁ v₂ = 0 ∧ c₂ v₁ = 0 ∧ c₂ v₂ = 1 := by
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hE])
  have h0 : B 0 = v₁ := by simp [B]
  have h1 : B 1 = v₂ := by simp [B]
  refine ⟨LinearMap.toContinuousLinearMap (B.coord 0),
    LinearMap.toContinuousLinearMap (B.coord 1), ?_, ?_, ?_, ?_⟩ <;>
    simp only [LinearMap.coe_toContinuousLinearMap']
  · rw [← h0, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  · rw [← h1, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  · rw [← h0, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  · rw [← h1, Module.Basis.coord_apply, Module.Basis.repr_self]; simp

/-- A bilinear form on a two-dimensional space is symmetric as soon as it is symmetric on a basis
pair. -/
private theorem bilinear_symm_of_pair (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) (β : E →L[ℝ] E →L[ℝ] ℝ) (h : β v₁ v₂ = β v₂ v₁)
    (u w : E) : β u w = β w u := by
  obtain ⟨a₁, a₂, rfl⟩ := exists_coords hE hli u
  obtain ⟨c₁, c₂, rfl⟩ := exists_coords hE hli w
  simp only [map_add, map_smul, add_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (a₁ * c₂ - a₂ * c₁) * h

omit [FiniteDimensional ℝ E] in
private theorem fderiv_apply_eq {L : E → E →L[ℝ] ℝ} {y : E} (hL : DifferentiableAt ℝ L y)
    (u w : E) : fderiv ℝ (fun z => L z u) y w = fderiv ℝ L y w u := by
  rw [fderiv_clm_apply hL (differentiableAt_const u)]
  simp

end Linear

section Regularity

variable {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

omit [FiniteDimensional ℝ E] in
private theorem contDiff_apply_apply' (hb : ContDiff ℝ 2 b) (u v : E) :
    ContDiff ℝ 2 (fun z => b z u v) :=
  (hb.clm_apply contDiff_const).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
theorem contDiff_surfaceCoframeA (hb : ContDiff ℝ 2 b) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) : ContDiff ℝ 2 (surfaceCoframeA b v₁) :=
  (contDiff_apply_apply' hb v₁ v₁).sqrt fun y => (surfaceE_pos hpos hli y).ne'

omit [FiniteDimensional ℝ E] in
theorem contDiff_surfaceCoframeC (hb : ContDiff ℝ 2 b) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) : ContDiff ℝ 2 (surfaceCoframeC b v₁ v₂) :=
  (contDiff_apply_apply' hb v₁ v₂).div (contDiff_surfaceCoframeA hb hpos hli)
    fun y => (Real.sqrt_pos.mpr (surfaceE_pos hpos hli y)).ne'

omit [FiniteDimensional ℝ E] in
theorem contDiff_surfaceGramDet (hb : ContDiff ℝ 2 b) : ContDiff ℝ 2 (surfaceGramDet b v₁ v₂) :=
  ((contDiff_apply_apply' hb v₁ v₁).mul (contDiff_apply_apply' hb v₂ v₂)).sub
    ((contDiff_apply_apply' hb v₁ v₂).pow 2)

theorem contDiff_surfaceCoframeW (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ContDiff ℝ 2 (surfaceCoframeW b v₁ v₂) :=
  ((contDiff_surfaceGramDet hb).sqrt fun y => (surfaceGramDet_pos hsymm hpos hli y).ne').div
    (contDiff_surfaceCoframeA hb hpos hli)
    fun y => (Real.sqrt_pos.mpr (surfaceE_pos hpos hli y)).ne'

omit [FiniteDimensional ℝ E] in
theorem contDiff_surfaceCoframe₁ (hb : ContDiff ℝ 2 b) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) : ContDiff ℝ 2 (surfaceCoframe₁ b v₁) :=
  ((contDiff_surfaceCoframeA hb hpos hli).inv
    fun y => (Real.sqrt_pos.mpr (surfaceE_pos hpos hli y)).ne').smul
    (hb.clm_apply contDiff_const)

theorem contDiff_surfaceCoframe₂ (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ContDiff ℝ 2 (surfaceCoframe₂ b v₁ v₂) := by
  have hW : ContDiff ℝ 2 (fun y => √(surfaceGramDet b v₁ v₂ y) * √(b y v₁ v₁)) :=
    ((contDiff_surfaceGramDet hb).sqrt fun y => (surfaceGramDet_pos hsymm hpos hli y).ne').mul
      (contDiff_surfaceCoframeA hb hpos hli)
  exact (hW.inv fun y => (mul_pos (Real.sqrt_pos.mpr (surfaceGramDet_pos hsymm hpos hli y))
    (Real.sqrt_pos.mpr (surfaceE_pos hpos hli y))).ne').smul
    (((contDiff_apply_apply' hb v₁ v₁).smul (hb.clm_apply contDiff_const)).sub
      ((contDiff_apply_apply' hb v₁ v₂).smul (hb.clm_apply contDiff_const)))

end Regularity

section Rotated

variable {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

/-- The rotated coframe, real part: `cos α θ¹ − sin α θ²`. -/
def surfaceRotatedCoframe₁ (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (α : E → ℝ) (y : E) :
    E →L[ℝ] ℝ :=
  Real.cos (α y) • surfaceCoframe₁ b v₁ y - Real.sin (α y) • surfaceCoframe₂ b v₁ v₂ y

/-- The rotated coframe, imaginary part: `sin α θ¹ + cos α θ²`. -/
def surfaceRotatedCoframe₂ (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (α : E → ℝ) (y : E) :
    E →L[ℝ] ℝ :=
  Real.sin (α y) • surfaceCoframe₁ b v₁ y + Real.cos (α y) • surfaceCoframe₂ b v₁ v₂ y

theorem contDiff_surfaceRotatedCoframe₁ (hb : ContDiff ℝ 2 b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) {α : E → ℝ} (hα : ContDiff ℝ 1 α) :
    ContDiff ℝ 1 (surfaceRotatedCoframe₁ b v₁ v₂ α) :=
  ((Real.contDiff_cos.comp hα).smul ((contDiff_surfaceCoframe₁ hb hpos hli).of_le
    (by norm_num))).sub ((Real.contDiff_sin.comp hα).smul
    ((contDiff_surfaceCoframe₂ hb hsymm hpos hli).of_le (by norm_num)))

theorem contDiff_surfaceRotatedCoframe₂ (hb : ContDiff ℝ 2 b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) {α : E → ℝ} (hα : ContDiff ℝ 1 α) :
    ContDiff ℝ 1 (surfaceRotatedCoframe₂ b v₁ v₂ α) :=
  ((Real.contDiff_sin.comp hα).smul ((contDiff_surfaceCoframe₁ hb hpos hli).of_le
    (by norm_num))).add ((Real.contDiff_cos.comp hα).smul
    ((contDiff_surfaceCoframe₂ hb hsymm hpos hli).of_le (by norm_num)))

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_trig_mul {f g : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (w : E) :
    fderiv ℝ (fun z => Real.cos (f z) * g z) y w =
        Real.cos (f y) * fderiv ℝ g y w - g y * Real.sin (f y) * fderiv ℝ f y w ∧
      fderiv ℝ (fun z => Real.sin (f z) * g z) y w =
        Real.sin (f y) * fderiv ℝ g y w + g y * Real.cos (f y) * fderiv ℝ f y w := by
  constructor
  · rw [show (fun z => Real.cos (f z) * g z) = (fun x => Real.cos (f x)) * g from rfl,
      (hf.hasFDerivAt.cos.mul hg.hasFDerivAt).fderiv]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  · rw [show (fun z => Real.sin (f z) * g z) = (fun x => Real.sin (f x)) * g from rfl,
      (hf.hasFDerivAt.sin.mul hg.hasFDerivAt).fderiv]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- **Closedness of the rotated coframe.** If `∂₁ α = P` and `∂₂ α = Q`, the two rotated
coframe forms have symmetric derivatives. -/
theorem surfaceRotatedCoframe_closed (hE : Module.finrank ℝ E = 2) (hb : ContDiff ℝ 2 b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) {α : E → ℝ} (hα : ContDiff ℝ 1 α)
    (hα₁ : ∀ y, fderiv ℝ α y v₁ = surfaceConnectionP b v₁ v₂ y)
    (hα₂ : ∀ y, fderiv ℝ α y v₂ = surfaceConnectionQ b v₁ v₂ y) (y : E) :
    (∀ u w, fderiv ℝ (surfaceRotatedCoframe₁ b v₁ v₂ α) y u w =
      fderiv ℝ (surfaceRotatedCoframe₁ b v₁ v₂ α) y w u) ∧
    ∀ u w, fderiv ℝ (surfaceRotatedCoframe₂ b v₁ v₂ α) y u w =
      fderiv ℝ (surfaceRotatedCoframe₂ b v₁ v₂ α) y w u := by
  have hd₁ := (contDiff_surfaceRotatedCoframe₁ hb hsymm hpos hli hα).differentiable
    (by norm_num) y
  have hd₂ := (contDiff_surfaceRotatedCoframe₂ hb hsymm hpos hli hα).differentiable
    (by norm_num) y
  have hαd := hα.differentiable (by norm_num) y
  have hA := (contDiff_surfaceCoframeA hb hpos hli).differentiable (by norm_num) y
  have hC := (contDiff_surfaceCoframeC hb hpos hli).differentiable (by norm_num) y
  have hW := (contDiff_surfaceCoframeW hb hsymm hpos hli).differentiable (by norm_num) y
  obtain ⟨hS1, hS2⟩ := surfaceCoframe_structure (hb.differentiable (by norm_num)) hsymm hpos
    hli y
  have e11 : (fun z => surfaceRotatedCoframe₁ b v₁ v₂ α z v₁) =
      fun z => Real.cos (α z) * surfaceCoframeA b v₁ z := by
    funext z
    simp [surfaceRotatedCoframe₁, surfaceCoframe₁_apply_left hpos hli,
      surfaceCoframe₂_apply_left hsymm]
  have e12 : (fun z => surfaceRotatedCoframe₁ b v₁ v₂ α z v₂) =
      fun z => Real.cos (α z) * surfaceCoframeC b v₁ v₂ z -
        Real.sin (α z) * surfaceCoframeW b v₁ v₂ z := by
    funext z
    simp [surfaceRotatedCoframe₁, surfaceCoframe₁_apply_right,
      surfaceCoframe₂_apply_right hsymm hpos hli]
  have e21 : (fun z => surfaceRotatedCoframe₂ b v₁ v₂ α z v₁) =
      fun z => Real.sin (α z) * surfaceCoframeA b v₁ z := by
    funext z
    simp [surfaceRotatedCoframe₂, surfaceCoframe₁_apply_left hpos hli,
      surfaceCoframe₂_apply_left hsymm]
  have e22 : (fun z => surfaceRotatedCoframe₂ b v₁ v₂ α z v₂) =
      fun z => Real.sin (α z) * surfaceCoframeC b v₁ v₂ z +
        Real.cos (α z) * surfaceCoframeW b v₁ v₂ z := by
    funext z
    simp [surfaceRotatedCoframe₂, surfaceCoframe₁_apply_right,
      surfaceCoframe₂_apply_right hsymm hpos hli]
  constructor
  · refine bilinear_symm_of_pair hE hli _ ?_
    rw [← fderiv_apply_eq hd₁, ← fderiv_apply_eq hd₁, e11, e12,
      fderiv_fun_sub (f := fun z => Real.cos (α z) * surfaceCoframeC b v₁ v₂ z)
        (g := fun z => Real.sin (α z) * surfaceCoframeW b v₁ v₂ z)
        ((hαd.cos).mul hC) ((hαd.sin).mul hW)]
    rw [sub_apply, (hasFDerivAt_trig_mul hαd hC v₁).1,
      (hasFDerivAt_trig_mul hαd hW v₁).2, (hasFDerivAt_trig_mul hαd hA v₂).1, hα₁, hα₂]
    linear_combination Real.cos (α y) * hS1 - Real.sin (α y) * hS2
  · refine bilinear_symm_of_pair hE hli _ ?_
    rw [← fderiv_apply_eq hd₂, ← fderiv_apply_eq hd₂, e21, e22,
      fderiv_fun_add (f := fun z => Real.sin (α z) * surfaceCoframeC b v₁ v₂ z)
        (g := fun z => Real.cos (α z) * surfaceCoframeW b v₁ v₂ z)
        ((hαd.sin).mul hC) ((hαd.cos).mul hW)]
    rw [add_apply, (hasFDerivAt_trig_mul hαd hC v₁).2,
      (hasFDerivAt_trig_mul hαd hW v₁).1, (hasFDerivAt_trig_mul hαd hA v₂).2, hα₁, hα₂]
    linear_combination Real.sin (α y) * hS1 + Real.cos (α y) * hS2

end Rotated

section Periodic

variable {v₁ v₂ : E}

/-- Every point is within `‖v₁‖ + ‖v₂‖` of the lattice `ℤ v₁ + ℤ v₂`. -/
private theorem exists_lattice_near (hE : Module.finrank ℝ E = 2)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) :
    ∃ n₁ n₂ : ℤ, ‖y - (n₁ • v₁ + n₂ • v₂)‖ ≤ ‖v₁‖ + ‖v₂‖ := by
  obtain ⟨a, c, rfl⟩ := exists_coords hE hli y
  refine ⟨⌊a⌋, ⌊c⌋, ?_⟩
  have h : a • v₁ + c • v₂ - (⌊a⌋ • v₁ + ⌊c⌋ • v₂) = Int.fract a • v₁ + Int.fract c • v₂ := by
    rw [Int.fract, Int.fract, sub_smul, sub_smul, Int.cast_smul_eq_zsmul ℝ,
      Int.cast_smul_eq_zsmul ℝ]
    abel
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
  · rw [norm_smul, Real.norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

/-- A doubly periodic continuous positive coefficient field is uniformly positive. -/
theorem exists_pos_mul_sq_le_of_periodic (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : Continuous b) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂])
    (hper₁ : ∀ y, b (y + v₁) = b y) (hper₂ : ∀ y, b (y + v₂) = b y) :
    ∃ m : ℝ, 0 < m ∧ ∀ y u, m * ‖u‖ ^ 2 ≤ b y u u := by
  have hlat : ∀ n₁ n₂ : ℤ, ∀ y, b (y + (n₁ • v₁ + n₂ • v₂)) = b y := fun n₁ n₂ =>
    ((show Function.Periodic b v₁ from hper₁).zsmul n₁).add_period
      ((show Function.Periodic b v₂ from hper₂).zsmul n₂)
  set R := ‖v₁‖ + ‖v₂‖
  have hv₁ : v₁ ≠ 0 := by simpa using hli.ne_zero 0
  have hS : IsCompact (closedBall (0 : E) R ×ˢ sphere (0 : E) 1) :=
    (isCompact_closedBall 0 R).prod (isCompact_sphere 0 1)
  have hne : (closedBall (0 : E) R ×ˢ sphere (0 : E) 1).Nonempty :=
    ⟨(0, ‖v₁‖⁻¹ • v₁), by simp [R, add_nonneg], by
      simp [norm_smul, norm_ne_zero_iff.mpr hv₁]⟩
  have hg : Continuous fun p : E × E => b p.1 p.2 p.2 :=
    ((hb.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
  have hp₀ne : p₀.2 ≠ 0 := by
    intro h
    have := hp₀.2
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  refine ⟨b p₀.1 p₀.2 p₀.2, hpos _ _ hp₀ne, fun y u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨n₁, n₂, hn⟩ := exists_lattice_near hE hli y
  set y' := y - (n₁ • v₁ + n₂ • v₂)
  have hby : b y = b y' := by
    have := hlat n₁ n₂ y'
    rwa [sub_add_cancel] at this
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hmem : (y', ‖u‖⁻¹ • u) ∈ closedBall (0 : E) R ×ˢ sphere (0 : E) 1 :=
    ⟨by simpa [y'] using hn, by simp [norm_smul, hu0]⟩
  have hle : b p₀.1 p₀.2 p₀.2 ≤ b y' (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) := hmin hmem
  have hscale : b y u u = ‖u‖ ^ 2 * b y' (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) := by
    rw [hby]
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hscale]
  nlinarith [sq_nonneg ‖u‖]

/-- A continuous map whose oscillation is invariant under a set of translations reaching every
point within distance `R` is uniformly continuous. -/
private theorem uniform_of_translation_invariant {X : Type*} [NormedAddCommGroup X] {D : E → X}
    (hD : Continuous D) {R : ℝ} {Λ : Set E} (hred : ∀ y, ∃ w ∈ Λ, ‖y - w‖ ≤ R)
    (hinv : ∀ w ∈ Λ, ∀ z z', ‖D (z + w) - D (z' + w)‖ = ‖D z - D z'‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ z z', dist z z' < δ → ‖D z - D z'‖ < ε := by
  intro ε hε
  have hK : IsCompact (closedBall (0 : E) (R + 1)) := isCompact_closedBall 0 _
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hD.continuousOn) ε hε
  refine ⟨min δ 1, by positivity, fun z z' hzz' => ?_⟩
  obtain ⟨w, hw, hzw⟩ := hred z
  have heq := hinv w hw (z - w) (z' - w)
  simp only [sub_add_cancel] at heq
  rw [heq, ← dist_eq_norm]
  have hd : dist (z - w) (z' - w) = dist z z' := dist_sub_right _ _ _
  refine h _ ?_ _ ?_ (by rw [hd]; exact lt_of_lt_of_le hzz' (min_le_left _ _))
  · rw [mem_closedBall_zero_iff]; linarith
  · rw [mem_closedBall_zero_iff]
    have h1 : ‖z' - w‖ ≤ ‖z - w‖ + dist z z' := by
      rw [dist_comm, dist_eq_norm]
      calc ‖z' - w‖ = ‖(z - w) + (z' - z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : dist z z' < 1 := lt_of_lt_of_le hzz' (min_le_right _ _)
    linarith

omit [FiniteDimensional ℝ E] in
/-- An equivariant developing map with an invertible differential: a translation of the domain
by `v ≠ 0` becomes a translation of `ℂ` (an affine rotation with nontrivial linear part has a
fixed point, which a bijection cannot have). -/
private theorem exists_translation_of_equivariant {φ : E → ℂ} {D : E → E →L[ℝ] ℂ}
    (hφ : ∀ y, HasFDerivAt φ (D y) y) (hbij : Bijective φ) {v : E} (hv : v ≠ 0) {c : ℂ}
    (hc : ∀ y, D (y + v) = c • D y) : ∃ l : ℂ, ∀ y, φ (y + v) = φ y + l := by
  have hg : ∀ z, HasFDerivAt (fun z => φ (z + v) - c * φ z) (0 : E →L[ℝ] ℂ) z := by
    intro z
    have h1 : HasFDerivAt (fun z => φ (z + v)) (D (z + v)) z := by
      have := (hφ (z + v)).comp z ((hasFDerivAt_id z).add_const v)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have h2 : HasFDerivAt (fun z => c * φ z) (c • D z) z := (hφ z).const_mul c
    have h3 := h1.sub h2
    rwa [hc z, sub_self] at h3
  have hconst : ∀ y, φ (y + v) - c * φ y = φ (0 + v) - c * φ 0 := fun y =>
    is_const_of_fderiv_eq_zero (fun z => (hg z).differentiableAt) (fun z => (hg z).fderiv) y 0
  set d := φ (0 + v) - c * φ 0
  by_cases hc1 : c = 1
  · refine ⟨d, fun y => ?_⟩
    have := hconst y
    rw [hc1, one_mul] at this
    rw [← this]
    ring
  · exfalso
    have hc1' : (1 : ℂ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
    obtain ⟨z, hz⟩ := hbij.2 (d / (1 - c))
    have h := hconst z
    rw [hz] at h
    have hfix : φ (z + v) = φ z := by
      have h' : φ (z + v) = c * (d / (1 - c)) + d := by linear_combination h
      rw [h', hz]
      field_simp
      ring
    exact hv (by simpa using hbij.1 hfix)

end Periodic

section Assembly

variable {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

/-- A potential `α` of the connection form `ω = P dx + Q dy` when `∂₂ P = ∂₁ Q`. -/
theorem exists_surfaceConnection_potential (hE : Module.finrank ℝ E = 2) (hb : ContDiff ℝ 2 b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂])
    (hclosed : ∀ y, fderiv ℝ (surfaceConnectionP b v₁ v₂) y v₂ =
      fderiv ℝ (surfaceConnectionQ b v₁ v₂) y v₁) :
    ∃ α : E → ℝ, ContDiff ℝ 1 α ∧ (∀ y, fderiv ℝ α y v₁ = surfaceConnectionP b v₁ v₂ y) ∧
      (∀ y, fderiv ℝ α y v₂ = surfaceConnectionQ b v₁ v₂ y) ∧
      ∀ w, (∀ y, b (y + w) = b y) → ∀ y, fderiv ℝ α (y + w) = fderiv ℝ α y := by
  obtain ⟨c₁, c₂, h11, h12, h21, h22⟩ := exists_coordinate_functionals hE hli
  have hP := contDiff_surfaceConnectionP hb hsymm hpos hli
  have hQ := contDiff_surfaceConnectionQ hb hsymm hpos hli
  set P := surfaceConnectionP b v₁ v₂
  set Q := surfaceConnectionQ b v₁ v₂
  let κ : E → E →L[ℝ] ℝ := fun y => P y • c₁ + Q y • c₂
  have hκ : ContDiff ℝ 1 κ := (hP.smul contDiff_const).add (hQ.smul contDiff_const)
  have hκd : ∀ y, HasFDerivAt κ
      ((fderiv ℝ P y).smulRight c₁ + (fderiv ℝ Q y).smulRight c₂) y := fun y =>
    ((hP.differentiable (by norm_num) y).hasFDerivAt.smul_const c₁).add
      ((hQ.differentiable (by norm_num) y).hasFDerivAt.smul_const c₂)
  have hsym : ∀ y u w, fderiv ℝ κ y u w = fderiv ℝ κ y w u := by
    intro y
    refine bilinear_symm_of_pair hE hli _ ?_
    rw [(hκd y).fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, h11, h12, h21, h22]
    rw [hclosed y]
    ring
  have hα : ∀ x, HasFDerivAt (Calculus.radialPotential κ 0) (κ x) x := fun x =>
    Calculus.radialPotential_hasFDerivAt isOpen_univ hκ.contDiffOn (fun _ _ => mem_univ _)
      (fun _ _ u w => hsym _ u w)
  refine ⟨Calculus.radialPotential κ 0, ?_, fun y => ?_, fun y => ?_, fun w hper y => ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hα x).differentiableAt, ?_⟩
    have : fderiv ℝ (Calculus.radialPotential κ 0) = κ := funext fun x => (hα x).fderiv
    rw [this]
    exact hκ.continuous
  · rw [(hα y).fderiv]
    simp [κ, h11, h21]
  · rw [(hα y).fderiv]
    simp [κ, h12, h22]
  · rw [(hα _).fderiv, (hα y).fderiv]
    simp only [κ, P, Q, surfaceConnectionP_add_period hper, surfaceConnectionQ_add_period hper]

/-- **Developing map of a doubly periodic field with closed connection form.** There is a
homeomorphism `φ : E ≃ₜ ℂ` with invertible derivative `φ' y`, isometric from `b y` to the
Euclidean plane, with a uniform bound on `(φ' y)⁻¹`, translating the periods `v₁, v₂` into
translations of `ℂ`. -/
theorem exists_developing_of_closed_connection (hE : Module.finrank ℝ E = 2)
    (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) (hli : LinearIndependent ℝ ![v₁, v₂])
    (hper₁ : ∀ y, b (y + v₁) = b y) (hper₂ : ∀ y, b (y + v₂) = b y)
    (hclosed : ∀ y, fderiv ℝ (surfaceConnectionP b v₁ v₂) y v₂ =
      fderiv ℝ (surfaceConnectionQ b v₁ v₂) y v₁) :
    ∃ (φ : E ≃ₜ ℂ) (φ' : E → E ≃L[ℝ] ℂ) (l₁ l₂ : ℂ) (K : ℝ),
      (∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] ℂ) y) ∧ Continuous (fun y => (φ' y : E →L[ℝ] ℂ)) ∧
      (∀ y u w, inner ℝ (φ' y u) (φ' y w) = b y u w) ∧
      (∀ y, ‖((φ' y).symm : ℂ →L[ℝ] E)‖ ≤ K) ∧
      (∀ y, φ (y + v₁) = φ y + l₁) ∧ ∀ y, φ (y + v₂) = φ y + l₂ := by
  obtain ⟨α, hα, hα₁, hα₂, hαper⟩ :=
    exists_surfaceConnection_potential hE hb hsymm hpos hli hclosed
  set η₁ := surfaceRotatedCoframe₁ b v₁ v₂ α
  set η₂ := surfaceRotatedCoframe₂ b v₁ v₂ α
  have hη₁ : ContDiff ℝ 1 η₁ := contDiff_surfaceRotatedCoframe₁ hb hsymm hpos hli hα
  have hη₂ : ContDiff ℝ 1 η₂ := contDiff_surfaceRotatedCoframe₂ hb hsymm hpos hli hα
  have hcl := surfaceRotatedCoframe_closed hE hb hsymm hpos hli hα hα₁ hα₂
  have hφ₁ : ∀ x, HasFDerivAt (Calculus.radialPotential η₁ 0) (η₁ x) x := fun x =>
    Calculus.radialPotential_hasFDerivAt isOpen_univ hη₁.contDiffOn (fun _ _ => mem_univ _)
      (fun _ _ u w => (hcl _).1 u w)
  have hφ₂ : ∀ x, HasFDerivAt (Calculus.radialPotential η₂ 0) (η₂ x) x := fun x =>
    Calculus.radialPotential_hasFDerivAt isOpen_univ hη₂.contDiffOn (fun _ _ => mem_univ _)
      (fun _ _ u w => (hcl _).2 u w)
  let ι₁ : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  let ι₂ : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  let φ₀ : E → ℂ := fun z =>
    ι₁ (Calculus.radialPotential η₁ 0 z) + ι₂ (Calculus.radialPotential η₂ 0 z)
  let D : E → E →L[ℝ] ℂ := fun y => ι₁.comp (η₁ y) + ι₂.comp (η₂ y)
  have hφ₀ : ∀ y, HasFDerivAt φ₀ (D y) y := fun y =>
    (ι₁.hasFDerivAt.comp y (hφ₁ y)).add (ι₂.hasFDerivAt.comp y (hφ₂ y))
  have hDc : Continuous D :=
    (continuous_const.clm_comp hη₁.continuous).add (continuous_const.clm_comp hη₂.continuous)
  have hDη : ∀ y u, D y u = (η₁ y u : ℂ) + Complex.I * (η₂ y u : ℂ) := fun y u => by
    simp [D, ι₁, ι₂]
  have hDexp : ∀ y u, D y u = Complex.exp ((α y : ℂ) * Complex.I) *
      ((surfaceCoframe₁ b v₁ y u : ℂ) + Complex.I * (surfaceCoframe₂ b v₁ v₂ y u : ℂ)) := by
    intro y u
    rw [hDη]
    apply Complex.ext <;>
      simp [η₁, η₂, surfaceRotatedCoframe₁, surfaceRotatedCoframe₂, Complex.mul_re,
        Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_im]
    ring
  have hgram : ∀ y u w, surfaceCoframe₁ b v₁ y u * surfaceCoframe₁ b v₁ y w +
      surfaceCoframe₂ b v₁ v₂ y u * surfaceCoframe₂ b v₁ v₂ y w = b y u w := by
    intro y u w
    obtain ⟨a₁, a₂, rfl⟩ := exists_coords hE hli u
    obtain ⟨c₁, c₂, rfl⟩ := exists_coords hE hli w
    exact surfaceCoframe_gram hsymm hpos hli y
  have hinner : ∀ y u w, inner ℝ (D y u) (D y w) = b y u w := by
    intro y u w
    rw [hDη, hDη, Complex.inner, ← hgram y u w]
    simp only [η₁, η₂, surfaceRotatedCoframe₁, surfaceRotatedCoframe₂,
      sub_apply, add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.neg_re, Complex.neg_im]
    linear_combination (surfaceCoframe₁ b v₁ y u * surfaceCoframe₁ b v₁ y w +
      surfaceCoframe₂ b v₁ v₂ y u * surfaceCoframe₂ b v₁ v₂ y w) * Real.cos_sq_add_sin_sq (α y)
  have hnormsq : ∀ y u, ‖D y u‖ ^ 2 = b y u u := fun y u => by
    rw [← real_inner_self_eq_norm_sq, hinner]
  obtain ⟨m, hm, hmle⟩ := exists_pos_mul_sq_le_of_periodic hE hb.continuous hpos hli hper₁ hper₂
  have hinj : ∀ y, Injective (D y) := by
    intro y
    refine (injective_iff_map_eq_zero (D y)).mpr fun u hu => ?_
    by_contra hne
    have h1 := hpos y u hne
    rw [← hnormsq, hu, norm_zero] at h1
    simp at h1
  have hequiv : ∀ y, ∃ e : E ≃L[ℝ] ℂ, (e : E →L[ℝ] ℂ) = D y := fun y =>
    ⟨(LinearEquiv.ofBijective (D y : E →ₗ[ℝ] ℂ) ⟨hinj y,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [hE, Complex.finrank_real_complex])).mp (hinj y)⟩).toContinuousLinearEquiv,
      by ext; rfl⟩
  choose φ' hφ' using hequiv
  have hK : ∀ y, ‖((φ' y).symm : ℂ →L[ℝ] E)‖ ≤ (√m)⁻¹ := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    set u := (φ' y).symm w
    have hw : w = D y u := by rw [← hφ' y]; simp [u]
    have h1 : m * ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [hw, hnormsq]; exact hmle y u
    have hsm := Real.sqrt_pos.mpr hm
    have h2 : √m * ‖u‖ ≤ ‖w‖ := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_mul hm.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
        at this
    change ‖u‖ ≤ (√m)⁻¹ * ‖w‖
    rw [inv_mul_eq_div, le_div_iff₀ hsm]
    linarith
  -- lattice of periods along which `α` shifts by constants
  have hαshift : ∀ w, (∀ y, b (y + w) = b y) → ∃ a : ℝ, ∀ y, α (y + w) = α y + a := by
    intro w hw
    refine ⟨α (0 + w) - α 0, fun y => ?_⟩
    have hd : ∀ z, HasFDerivAt (fun z => α (z + w) - α z) (0 : E →L[ℝ] ℝ) z := by
      intro z
      have h1 : HasFDerivAt (fun z => α (z + w)) (fderiv ℝ α (z + w)) z := by
        have := ((hα.differentiable (by norm_num)) (z + w)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).add_const w)
        rw [ContinuousLinearMap.comp_id] at this
        exact this
      have h3 := h1.sub ((hα.differentiable (by norm_num)) z).hasFDerivAt
      rwa [hαper w hw z, sub_self] at h3
    have := is_const_of_fderiv_eq_zero (fun z => (hd z).differentiableAt)
      (fun z => (hd z).fderiv) y 0
    linarith
  let S : AddSubgroup E :=
    { carrier := {w | (∀ y, b (y + w) = b y) ∧ ∃ a : ℝ, ∀ y, α (y + w) = α y + a}
      add_mem' := by
        rintro w₁ w₂ ⟨hb₁, a₁, ha₁⟩ ⟨hb₂, a₂, ha₂⟩
        refine ⟨fun y => by rw [← add_assoc, hb₂, hb₁], a₁ + a₂, fun y => ?_⟩
        rw [← add_assoc, ha₂, ha₁]
        ring
      zero_mem' := ⟨fun y => by rw [add_zero], 0, fun y => by rw [add_zero, add_zero]⟩
      neg_mem' := by
        rintro w ⟨hbw, a, ha⟩
        refine ⟨fun y => ?_, -a, fun y => ?_⟩
        · have := hbw (y + -w)
          rwa [neg_add_cancel_right, eq_comm] at this
        · have := ha (y + -w)
          rw [neg_add_cancel_right] at this
          linarith }
  have hv₁S : v₁ ∈ S := ⟨hper₁, hαshift v₁ hper₁⟩
  have hv₂S : v₂ ∈ S := ⟨hper₂, hαshift v₂ hper₂⟩
  have hDS : ∀ w ∈ S, ∃ a : ℝ, ∀ y, D (y + w) = Complex.exp ((a : ℂ) * Complex.I) • D y := by
    rintro w ⟨hbw, a, ha⟩
    refine ⟨a, fun y => ?_⟩
    ext u
    rw [smul_apply, smul_eq_mul, hDexp, hDexp, ha,
      surfaceCoframe₁_add_period hbw, surfaceCoframe₂_add_period hbw]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  have hunif : ∀ ε > 0, ∃ δ > 0, ∀ z z', dist z z' < δ →
      ‖(φ' z : E →L[ℝ] ℂ) - φ' z'‖ < ε := by
    simp only [hφ']
    refine uniform_of_translation_invariant hDc (Λ := S) (R := ‖v₁‖ + ‖v₂‖) (fun y => ?_) ?_
    · obtain ⟨n₁, n₂, hn⟩ := exists_lattice_near hE hli y
      exact ⟨_, S.add_mem (S.zsmul_mem hv₁S n₁) (S.zsmul_mem hv₂S n₂), hn⟩
    · intro w hw z z'
      obtain ⟨a, ha⟩ := hDS w hw
      rw [ha, ha, ← smul_sub, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcov : IsCoveringMap φ₀ :=
    isCoveringMap_of_uniform_fderiv (φ' := φ') (fun y => by rw [hφ']; exact hφ₀ y) hK
      (by positivity) hunif
  have hbij : Bijective φ₀ := hcov.bijective_sc
  have hv₁ : v₁ ≠ 0 := by simpa using hli.ne_zero 0
  have hv₂ : v₂ ≠ 0 := by simpa using hli.ne_zero 1
  obtain ⟨a₁, ha₁⟩ := hDS v₁ hv₁S
  obtain ⟨a₂, ha₂⟩ := hDS v₂ hv₂S
  obtain ⟨l₁, hl₁⟩ := exists_translation_of_equivariant hφ₀ hbij hv₁ ha₁
  obtain ⟨l₂, hl₂⟩ := exists_translation_of_equivariant hφ₀ hbij hv₂ ha₂
  refine ⟨hcov.homeomorphSc, φ', l₁, l₂, (√m)⁻¹, fun y => ?_, ?_, fun y u w => ?_, hK,
    hl₁, hl₂⟩
  · rw [hφ']
    exact hφ₀ y
  · simp only [hφ']
    exact hDc
  · rw [← ContinuousLinearEquiv.coe_coe, hφ']
    exact hinner y u w

end Assembly

end DifferentialGeometry.Analysis
