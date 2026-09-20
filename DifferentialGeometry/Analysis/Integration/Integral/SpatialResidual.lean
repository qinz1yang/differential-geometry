import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

theorem integrable_spatial_residual_iff_and_integral_eq_joint
    (μ : Measure E) [SFinite μ]
    (f : E × ℝ → ℝ) (test : ℝ × E → ℝ) (c : ℝ)
    (density r : ℝ × E → ℝ)
    (B : ℝ × E → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    {K : Set E} {T : Set ℝ} (hK : MeasurableSet K) (hT : MeasurableSet T)
    (htest : Differentiable ℝ test) (hsupport : tsupport test ⊆ T ×ˢ K)
    (hf : ∀ᵐ z ∂μ.prod (volume : Measure ℝ), z ∈ K ×ˢ T →
      DifferentiableAt ℝ f z) :
    let ds := fun p : ℝ × E => fderiv ℝ (fun y : E => f (y, p.1)) p.2
    let es := fun p : ℝ × E => fderiv ℝ (fun y : E => test (p.1, y)) p.2
    let d := fun z : E × ℝ => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let e := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let S := fun p => density p *
      ((c * B p (ds p) (ds p) + r p) * test p + B p (ds p) (es p))
    let Q := fun z => density z.swap *
      ((c * B z.swap (d z) (d z) + r z.swap) * test z.swap + B z.swap (d z) (e z))
    (Integrable S (volume.prod μ) ↔ IntegrableOn Q (K ×ˢ T) (μ.prod volume)) ∧
      (∫ p, S p ∂volume.prod μ) = ∫ z in K ×ˢ T, Q z ∂μ.prod volume := by
  dsimp only
  let S : ℝ × E → ℝ := fun p => density p *
    ((c * B p (fderiv ℝ (fun y : E => f (y, p.1)) p.2)
        (fderiv ℝ (fun y : E => f (y, p.1)) p.2) + r p) * test p +
      B p (fderiv ℝ (fun y : E => f (y, p.1)) p.2)
        (fderiv ℝ (fun y : E => test (p.1, y)) p.2))
  have hzero : ∀ p, p ∉ T ×ˢ K → S p = 0 := by
    intro p hp
    have hnot : p ∉ tsupport test := fun h => hp (hsupport h)
    have hval : test p = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hder : fderiv ℝ test p = 0 := fderiv_of_notMem_tsupport ℝ hnot
    have hslice := (htest p).hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
    have hspatial : fderiv ℝ (fun y : E => test (p.1, y)) p.2 = 0 := by
      have hsd := hslice.fderiv
      simp only [Function.comp_def] at hsd
      rw [hsd, hder]
      rfl
    simp only [S, hval, hspatial, map_zero, mul_zero, add_zero]
  let Q : E × ℝ → ℝ := fun z => density z.swap *
    ((c * B z.swap ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ))
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)) + r z.swap) * test z.swap +
      B z.swap ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ))
        ((fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)))
  have hident : (S ∘ Prod.swap) =ᵐ[(μ.prod volume).restrict (K ×ˢ T)] Q := by
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem (hK.prod hT)] with z hz hmem
    have hd := ((hz hmem).hasFDerivAt.comp z.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv
    have hswap : DifferentiableAt ℝ (fun v : E × ℝ => test v.swap) z :=
      (htest z.swap).comp z (differentiableAt_snd.prodMk differentiableAt_fst)
    have he := (hswap.hasFDerivAt.comp z.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv
    change density z.swap *
      ((c * B z.swap (fderiv ℝ (fun y : E => f (y, z.2)) z.1)
          (fderiv ℝ (fun y : E => f (y, z.2)) z.1) + r z.swap) * test z.swap +
        B z.swap (fderiv ℝ (fun y : E => f (y, z.2)) z.1)
          (fderiv ℝ (fun y : E => test (z.2, y)) z.1)) = Q z
    dsimp only [Q]
    simp only [Function.comp_def, Prod.swap_prod_mk] at hd he
    rw [hd, he]
  change (Integrable S (volume.prod μ) ↔ IntegrableOn Q (K ×ˢ T) (μ.prod volume)) ∧ _
  constructor
  · constructor
    · intro h
      exact h.swap.integrableOn.congr_fun_ae hident
    · intro h
      have hswap : IntegrableOn (S ∘ Prod.swap) (K ×ˢ T) (μ.prod volume) :=
        h.congr_fun_ae hident.symm
      have horiginal : IntegrableOn S (T ×ˢ K) (volume.prod μ) := by
        simpa only [Function.comp_def, Prod.swap_swap] using hswap.swap
      exact horiginal.integrable_of_forall_notMem_eq_zero hzero
  · calc
      (∫ p, S p ∂volume.prod μ) = ∫ p in T ×ˢ K, S p ∂volume.prod μ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ z in K ×ˢ T, S z.swap ∂μ.prod volume :=
        (setIntegral_prod_swap T K S).symm
      _ = ∫ z in K ×ˢ T, Q z ∂μ.prod volume := integral_congr_ae hident

end DifferentialGeometry.Analysis
