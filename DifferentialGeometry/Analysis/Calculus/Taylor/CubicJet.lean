import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Smooth maps with a prescribed third-order jet

A map of class `C³` near a point agrees to third order (value and three iterated Fréchet
derivatives) with its cubic Taylor polynomial, which is smooth. Used for jet replacement.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem cubicJet_symm3 {φ : E → F} {y₀ : E} (hφ : ContDiffAt ℝ 3 φ y₀) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ u w v := by
  let Fl : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E F).toLinearIsometry.toContinuousLinearMap
  have hFl : ∀ (B : E →L[ℝ] E →L[ℝ] F) (a b : E), Fl B a b = B b a := fun _ _ _ => rfl
  have hev : ∀ᶠ y in 𝓝 y₀, ContDiffAt ℝ 3 φ y := hφ.eventually (by simp)
  have heq : fderiv ℝ (fderiv ℝ φ) =ᶠ[𝓝 y₀] fun y => Fl (fderiv ℝ (fderiv ℝ φ) y) := by
    filter_upwards [hev] with y hy
    have hs := hy.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
    ext a b
    rw [hFl]
    exact hs a b
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ :=
    ((hφ.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : HasFDerivAt (fun y => Fl (fderiv ℝ (fderiv ℝ φ) y))
      (Fl.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀)) y₀ :=
    Fl.hasFDerivAt.comp y₀ hd.hasFDerivAt
  have h2 := (h1.congr_of_eventuallyEq heq).fderiv
  have := congrArg (fun L => L u v w) h2
  simpa [hFl] using this

private theorem cubicJet_symm3' {φ : E → F} {y₀ : E} (hφ : ContDiffAt ℝ 3 φ y₀) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ v u w := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) y₀ := hφ.fderiv_right (by norm_num)
  have hs := h2.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  exact congrArg (fun L : E →L[ℝ] F => L w) (hs u v)

/-- **Cubic jet replacement.** A map of class `C³` at `y₀` has a smooth companion with the same
value and the same first three iterated Fréchet derivatives at `y₀`. -/
theorem exists_contDiff_eq_jet3 {φ : E → F} {y₀ : E} (hφ : ContDiffAt ℝ 3 φ y₀) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ ψ y₀ = φ y₀ ∧ fderiv ℝ ψ y₀ = fderiv ℝ φ y₀ ∧
      fderiv ℝ (fderiv ℝ ψ) y₀ = fderiv ℝ (fderiv ℝ φ) y₀ ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) y₀ = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀ := by
  set D1 := fderiv ℝ φ y₀
  set D2 := fderiv ℝ (fderiv ℝ φ) y₀
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y₀
  have hS2 : ∀ v w, D2 v w = D2 w v := hφ.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  have hS3 : ∀ u v w, D3 u v w = D3 u w v := cubicJet_symm3 hφ
  have hS3' : ∀ u v w, D3 u v w = D3 v u w := cubicJet_symm3' hφ
  let ψ : E → F := fun y => φ y₀ + D1 (y - y₀) + (1 / 2 : ℝ) • D2 (y - y₀) (y - y₀) +
    (1 / 6 : ℝ) • D3 (y - y₀) (y - y₀) (y - y₀)
  let L : E → E →L[ℝ] F := fun y => D1 + D2 (y - y₀) + (1 / 2 : ℝ) • D3 (y - y₀) (y - y₀)
  let Mf : E → E →L[ℝ] E →L[ℝ] F := fun y => D2 + D3 (y - y₀)
  have hh : ∀ y : E, HasFDerivAt (fun z : E => z - y₀) (ContinuousLinearMap.id ℝ E) y :=
    fun y => (hasFDerivAt_id y).sub_const y₀
  have hψ : ∀ y, HasFDerivAt ψ (L y) y := by
    intro y
    have h1 : HasFDerivAt (fun z : E => D1 (z - y₀)) D1 y := by
      simpa [map_sub] using (D1.hasFDerivAt (x := y)).sub_const (D1 y₀)
    have h2 := D2.hasFDerivAt_of_bilinear (hh y) (hh y)
    have hc : HasFDerivAt (fun z : E => D3 (z - y₀)) D3 y := by
      simpa [map_sub] using (D3.hasFDerivAt (x := y)).sub_const (D3 y₀)
    have h3 := hc.clm_apply (hh y)
    have h3' := h3.clm_apply (hh y)
    have hsum := (((hasFDerivAt_const (φ y₀) y).add h1).add (h2.const_smul (1 / 2 : ℝ))).add
      (h3'.const_smul (1 / 6 : ℝ))
    refine (show HasFDerivAt ψ _ y from hsum).congr_fderiv ?_
    ext v
    simp only [L, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_id, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.flip_apply, zero_add]
    rw [hS2 v (y - y₀), hS3' v (y - y₀) (y - y₀), hS3 (y - y₀) v (y - y₀)]
    module
  have hL : ∀ y, HasFDerivAt L (Mf y) y := by
    intro y
    have h2 : HasFDerivAt (fun z : E => D2 (z - y₀)) D2 y := by
      simpa [map_sub] using (D2.hasFDerivAt (x := y)).sub_const (D2 y₀)
    have h3 := D3.hasFDerivAt_of_bilinear (hh y) (hh y)
    have hsum := ((hasFDerivAt_const D1 y).add h2).add (h3.const_smul (1 / 2 : ℝ))
    refine (show HasFDerivAt L _ y from hsum).congr_fderiv ?_
    ext u v
    simp only [Mf, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_id, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, zero_add]
    rw [hS3' u (y - y₀) v]
    module
  have hM : ∀ y, HasFDerivAt Mf D3 y := by
    intro y
    have h3 : HasFDerivAt (fun z : E => D3 (z - y₀)) D3 y := by
      simpa [map_sub] using (D3.hasFDerivAt (x := y)).sub_const (D3 y₀)
    refine (show HasFDerivAt Mf _ y from (hasFDerivAt_const D2 y).add h3).congr_fderiv ?_
    simp
  have hfψ : fderiv ℝ ψ = L := funext fun y => (hψ y).fderiv
  have hfL : fderiv ℝ L = Mf := funext fun y => (hL y).fderiv
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ψ]
    fun_prop
  · simp [ψ]
  · rw [hfψ]; simp [L]
  · rw [hfψ, hfL]; simp [Mf]
  · rw [hfψ, hfL, (hM y₀).fderiv]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Second-order jets of a composition.** If two maps have the same second-order jet at `x₀`,
so do their compositions with a map of class `C²` at the common value. -/
theorem jet2_comp_eq (Θ : F → G) {J₁ J₂ : E → F} {x₀ : E} (hΘ : ContDiffAt ℝ 2 Θ (J₁ x₀))
    (hJ₁ : ContDiffAt ℝ 2 J₁ x₀) (hJ₂ : ContDiffAt ℝ 2 J₂ x₀) (h0 : J₁ x₀ = J₂ x₀)
    (h1 : fderiv ℝ J₁ x₀ = fderiv ℝ J₂ x₀)
    (h2 : fderiv ℝ (fderiv ℝ J₁) x₀ = fderiv ℝ (fderiv ℝ J₂) x₀) :
    fderiv ℝ (Θ ∘ J₁) x₀ = fderiv ℝ (Θ ∘ J₂) x₀ ∧
      fderiv ℝ (fderiv ℝ (Θ ∘ J₁)) x₀ = fderiv ℝ (fderiv ℝ (Θ ∘ J₂)) x₀ := by
  have key : ∀ J : E → F, ContDiffAt ℝ 2 J x₀ → ContDiffAt ℝ 2 Θ (J x₀) →
      fderiv ℝ (Θ ∘ J) x₀ = (fderiv ℝ Θ (J x₀)).comp (fderiv ℝ J x₀) ∧
      fderiv ℝ (fderiv ℝ (Θ ∘ J)) x₀ =
        (ContinuousLinearMap.compL ℝ E F G (fderiv ℝ Θ (J x₀))).comp (fderiv ℝ (fderiv ℝ J) x₀) +
          ((ContinuousLinearMap.compL ℝ E F G).flip (fderiv ℝ J x₀)).comp
            ((fderiv ℝ (fderiv ℝ Θ) (J x₀)).comp (fderiv ℝ J x₀)) := by
    intro J hJ hΘJ
    have hJd : DifferentiableAt ℝ J x₀ := hJ.differentiableAt (by norm_num)
    have hΘd : DifferentiableAt ℝ Θ (J x₀) := hΘJ.differentiableAt (by norm_num)
    refine ⟨fderiv_comp x₀ hΘd hJd, ?_⟩
    have hΘev : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ Θ (J x) := by
      have h := (hΘJ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
      exact hJd.continuousAt.eventually h
    have hJev : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ J x :=
      (hJ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have heq : fderiv ℝ (Θ ∘ J) =ᶠ[𝓝 x₀] fun x => (fderiv ℝ Θ (J x)).comp (fderiv ℝ J x) := by
      filter_upwards [hΘev, hJev] with x hx hx'
      exact fderiv_comp x hx hx'
    have hc : HasFDerivAt (fun x => fderiv ℝ Θ (J x))
        ((fderiv ℝ (fderiv ℝ Θ) (J x₀)).comp (fderiv ℝ J x₀)) x₀ :=
      ((hΘJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp
        x₀ hJd.hasFDerivAt
    have hd : HasFDerivAt (fun x => fderiv ℝ J x) (fderiv ℝ (fderiv ℝ J) x₀) x₀ :=
      ((hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    rw [heq.fderiv_eq, (hc.clm_comp hd).fderiv]
  obtain ⟨a1, a2⟩ := key J₁ hJ₁ hΘ
  obtain ⟨b1, b2⟩ := key J₂ hJ₂ (h0 ▸ hΘ)
  refine ⟨?_, ?_⟩
  · rw [a1, b1, h0, h1]
  · rw [a2, b2, h0, h1, h2]

end DifferentialGeometry.Analysis
