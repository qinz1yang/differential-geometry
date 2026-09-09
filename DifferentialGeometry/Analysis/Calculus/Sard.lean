import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos

open Set MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem dense_regular_values_endomorphism {f : E → E} (hf : Differentiable ℝ f) :
    Dense {y : E | ∀ x, f x = y → Function.Bijective (fderiv ℝ f x)} := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let s : Set E := {x | (fderiv ℝ f x).det = 0}
  have hnull : Measure.addHaar (f '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero Measure.addHaar
      (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)
  have hdense : Dense ((f '' s)ᶜ) := Measure.dense_of_ae (μ := Measure.addHaar) (by
    rw [ae_iff]
    have hset : {a | ¬a ∉ f '' s} = f '' s := by
      ext z
      simp only [Set.mem_ofPred_eq, not_not]
    rw [hset]
    exact hnull)
  apply hdense.mono
  intro y hy x hxy
  have hdet : (fderiv ℝ f x).det ≠ 0 := by
    intro hx
    exact hy ⟨x, hx, hxy⟩
  have hker : (fderiv ℝ f x).ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hinj : Function.Injective (fderiv ℝ f x) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem Differentiable.dense_regular_values_of_finrank_eq {f : E → F}
    (hf : Differentiable ℝ f) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    Dense {y : F | ∀ x, f x = y → Function.Bijective (fderiv ℝ f x)} := by
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  have h := dense_regular_values_endomorphism (e.differentiable.comp hf)
  have hpre := h.preimage e.toHomeomorph.isOpenMap
  apply hpre.mono
  intro y hy x hxy
  have hbij := hy x (congrArg e hxy)
  have heq : fderiv ℝ (e ∘ f) x = e.toContinuousLinearMap.comp (fderiv ℝ f x) := by
    rw [fderiv_comp x e.differentiableAt (hf x), e.fderiv]
  rw [heq] at hbij
  constructor
  · intro v w hvw
    apply hbij.1
    exact congrArg e hvw
  · intro v
    obtain ⟨w, hw⟩ := hbij.2 (e v)
    exact ⟨w, e.injective hw⟩
