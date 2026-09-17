import DifferentialGeometry.Analysis.ODE.SaddleBandCurve
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis.ODE (saddleBandCurve)

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def saddleFiberVectorField (B : (ℝ × ℝ) ≃ₘ[ℝ] E) (x : E) : E :=
  fderiv ℝ (B : ℝ × ℝ → E) (B.symm x)
    (DifferentialGeometry.Analysis.ODE.saddleBandVectorField (B.symm x))

theorem contDiffOn_saddleFiberVectorField (B : (ℝ × ℝ) ≃ₘ[ℝ] E) :
    ContDiffOn ℝ ∞ B.saddleFiberVectorField
      {x | (1 - (B.symm x).1 ^ 2) * (B.symm x).2 ≠ 0} := by
  have hB : ContDiff ℝ ∞ (B : ℝ × ℝ → E) := B.contMDiff.contDiff
  have hBi : ContDiff ℝ ∞ (B.symm : E → ℝ × ℝ) := B.symm.contMDiff.contDiff
  have hD := (hB.fderiv_right (by simp)).comp hBi
  have hW := DifferentialGeometry.Analysis.ODE.contDiffOn_saddleBandVectorField.comp
    hBi.contDiffOn (fun _ hx => hx)
  exact hD.contDiffOn.clm_apply hW

theorem hasDerivAt_comp_saddleBandCurve (B : (ℝ × ℝ) ≃ₘ[ℝ] E)
    {z : ℝ × ℝ} (hv : z.2 ≠ 0) {t : ℝ}
    (ht : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) :
    HasDerivAt (fun s => B (saddleBandCurve z s))
      (B.saddleFiberVectorField (B (saddleBandCurve z t))) t := by
  have hd := (B.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (DifferentialGeometry.Analysis.ODE.hasDerivAt_saddleBandCurve hv ht)
  simpa only [saddleFiberVectorField, B.symm_apply_apply, Function.comp_def] using hd

theorem contDiffOn_comp_saddleBandCurve (B : (ℝ × ℝ) ≃ₘ[ℝ] E) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B (saddleBandCurve p.2 p.1))
      {p | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * p.1 / p.2.2 ^ 2} :=
  B.contMDiff.contDiff.comp_contDiffOn
    DifferentialGeometry.Analysis.ODE.contDiffOn_saddleBandCurve

end Diffeomorph

namespace PartialDiffeomorph

open DifferentialGeometry.Analysis.ODE

theorem exists_saddleBandCurve_time_change_on
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {ψ : A × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {U : Set (A × (ℝ × ℝ))} (hU : IsOpen U)
    (hUdom : ∀ p ∈ U, (p.1, p.2.1) ∉ tsupport ψ ∨ (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2)) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, A × (ℝ × ℝ)) 𝓘(ℝ, A × (ℝ × ℝ))
        (A × (ℝ × ℝ)) (A × (ℝ × ℝ)) ∞,
      χ.source = U ∧
      χ.target = (fun p => (p.1, saddleBandCurve p.2 (ψ (p.1, p.2.1)))) '' U ∧
      (χ : (A × (ℝ × ℝ)) → A × (ℝ × ℝ)) =
        (fun p => (p.1, saddleBandCurve p.2 (ψ (p.1, p.2.1)))) ∧
      (χ.symm : (A × (ℝ × ℝ)) → A × (ℝ × ℝ)) =
        (fun p => (p.1, saddleBandCurve p.2 (-ψ (p.1, p.2.1)))) := by
  let D (v : A × ℝ → ℝ) := {p : A × (ℝ × ℝ) | (p.1, p.2.1) ∉ tsupport v ∨
    (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * v (p.1, p.2.1) / p.2.2 ^ 2)}
  let f (v : A × ℝ → ℝ) : A × (ℝ × ℝ) → A × (ℝ × ℝ) := fun p =>
    (p.1, saddleBandCurve p.2 (v (p.1, p.2.1)))
  have hmap (v : A × ℝ → ℝ) : MapsTo (f v) (D v) (D (-v)) := by
    intro p hp
    rcases hp with hp | hp
    · apply Or.inl
      change (p.1, p.2.1) ∉ tsupport (-v)
      simpa only [tsupport_neg] using hp
    · refine Or.inr ⟨hp.1, ?_, ?_⟩
      · exact quadraticRadialCurve_ne_zero (1 - p.2.1 ^ 2)⁻¹ hp.2.1
          (by simpa only [Real.norm_eq_abs, sq_abs] using hp.2.2)
      · change 0 < 1 + 2 * (1 - (saddleBandCurve p.2 (v (p.1, p.2.1))).1 ^ 2)⁻¹ *
          (-v (p.1, p.2.1)) / (saddleBandCurve p.2 (v (p.1, p.2.1))).2 ^ 2
        rw [saddleBandCurve_reverse_radicand hp.2.2]
        exact inv_pos.mpr hp.2.2
  have hinv (v : A × ℝ → ℝ) : LeftInvOn (f (-v)) (f v) (D v) := by
    intro p hp
    apply Prod.ext
    · rfl
    rcases hp with hp | hp
    · have hzero := image_eq_zero_of_notMem_tsupport hp
      simp only [f, Pi.neg_apply, hzero, neg_zero, saddleBandCurve_zero]
    · exact saddleBandCurve_reverse hp.2.2
  have hdiff (v : A × ℝ → ℝ) (hv : ContDiff ℝ ∞ v) : ContDiffOn ℝ ∞ (f v) (D v) := by
    intro p hp
    exact (contDiffAt_fst.prodMk
      (contDiffAt_saddleBandCurve_time_change hv.contDiffAt hp)).contDiffWithinAt
  have htarget : (f ψ) '' U = D (-ψ) ∩ (f (-ψ)) ⁻¹' U := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨hmap ψ (hUdom q hq), ?_⟩
      change f (-ψ) (f ψ q) ∈ U
      rw [hinv ψ (hUdom q hq)]
      exact hq
    · rintro ⟨hp, hq⟩
      refine ⟨f (-ψ) p, hq, ?_⟩
      simpa only [neg_neg] using hinv (-ψ) hp
  have hopen : IsOpen ((f ψ) '' U) := by
    rw [htarget]
    exact (hdiff (-ψ) hψ.neg).continuousOn.isOpen_inter_preimage
      (isOpen_saddleBandCurve_time_change_domain hψ.neg.continuous) hU
  refine ⟨{
    toFun := f ψ
    invFun := f (-ψ)
    source := U
    target := (f ψ) '' U
    map_source' := fun p hp => mem_image_of_mem (f ψ) hp
    map_target' := ?_
    left_inv' := fun p hp => hinv ψ (hUdom p hp)
    right_inv' := ?_
    open_source := hU
    open_target := hopen
    contMDiffOn_toFun := ((hdiff ψ hψ).mono hUdom).contMDiffOn
    contMDiffOn_invFun := ?_ }, rfl, rfl, rfl, rfl⟩
  · rintro p ⟨q, hq, rfl⟩
    rw [hinv ψ (hUdom q hq)]
    exact hq
  · rintro p ⟨q, hq, rfl⟩
    rw [hinv ψ (hUdom q hq)]
  · apply ((hdiff (-ψ) hψ.neg).mono _).contMDiffOn
    rintro p ⟨q, hq, rfl⟩
    exact hmap ψ (hUdom q hq)

end PartialDiffeomorph
