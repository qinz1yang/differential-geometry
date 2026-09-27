import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem exists_equiv_of_transverse (L : E →L[ℝ] F)
    (hinj : Function.Injective L)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ F)
    {v : F} (htransverse : v ∉ Set.range L) :
    ∃ B : (E × ℝ) ≃L[ℝ] F, ∀ z, B z = L z.1 + z.2 • v := by
  let A : E × ℝ →L[ℝ] F := L.coprod (ContinuousLinearMap.toSpanSingleton ℝ v)
  have hker : ∀ z, A z = 0 → z = 0 := by
    intro z hz
    have hz' : L z.1 + z.2 • v = 0 := hz
    have hr : z.2 = 0 := by
      by_contra hr
      apply htransverse
      refine ⟨(-z.2⁻¹) • z.1, ?_⟩
      rw [map_smul, eq_neg_of_add_eq_zero_left hz', smul_neg, smul_smul]
      simp [hr]
    have hx : z.1 = 0 := hinj (by simpa only [hr, zero_smul, add_zero, map_zero] using hz')
    exact Prod.ext hx hr
  have hA : Function.Injective A := by
    intro z w hzw
    exact sub_eq_zero.mp (hker (z - w) (by rw [map_sub, hzw, sub_self]))
  have hdim' : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, Module.finrank_self] using hdim
  let B : (E × ℝ) ≃L[ℝ] F := (A.toLinearMap.linearEquivOfInjective hA hdim').toContinuousLinearEquiv
  exact ⟨B, fun _ ↦ rfl⟩

theorem exists_localInverse_of_transverse_immersion
    {ι : E → F} {V : Set E} {p : E} {v : F}
    (hι : ContDiffOn ℝ ∞ ι V) (hV : IsOpen V) (hp : p ∈ V)
    (hinj : Function.Injective (fderiv ℝ ι p))
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ F)
    (htransverse : v ∉ Set.range (fderiv ℝ ι p)) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) F,
      (p, 0) ∈ e.source ∧ e.source ⊆ V ×ˢ univ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z, e z = ι z.1 + z.2 • v := by
  let L := fderiv ℝ ι p
  obtain ⟨B, hBval⟩ := exists_equiv_of_transverse L hinj hdim htransverse
  let A : E × ℝ →L[ℝ] F := L.coprod (ContinuousLinearMap.toSpanSingleton ℝ v)
  have hB : (B : E × ℝ →L[ℝ] F) = A := ContinuousLinearMap.ext hBval
  have hL : HasFDerivAt ι L p :=
    ((hι.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun z : E × ℝ ↦ ι z.1 + z.2 • v)
      (B : E × ℝ →L[ℝ] F) (p, 0) := by
    rw [hB]
    have hsnd : HasFDerivAt (fun z : E × ℝ ↦ z.2) (ContinuousLinearMap.snd ℝ E ℝ) (p, 0) :=
      hasFDerivAt_snd
    convert! (hL.comp (p, 0) hasFDerivAt_fst).add (hsnd.smul_const v) using 1
  exact exists_localInverse_of_hasFDerivAt_equiv
    ((hι.comp contDiffOn_fst (fun z hz ↦ hz.1)).add (contDiffOn_snd.smul contDiffOn_const))
    (hV.prod isOpen_univ) ⟨hp, mem_univ _⟩ hd

theorem exists_localInverse_of_transverse_family
    {f : E × ℝ → F} {ι : E → F} {U : Set (E × ℝ)} {p : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hp : (p, 0) ∈ U)
    (hzero : ∀ x, (x, 0) ∈ U → f (x, 0) = ι x)
    (hinj : Function.Injective (fderiv ℝ ι p))
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ F)
    (htransverse : deriv (fun t ↦ f (p, t)) 0 ∉ Set.range (fderiv ℝ ι p)) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) F,
      (p, 0) ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z, e z = f z := by
  let L := fderiv ℝ f (p, 0)
  have hdf : HasFDerivAt f L (p, 0) :=
    ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have heq : (fun x ↦ f (x, 0)) =ᶠ[𝓝 p] ι := by
    have hnear : ∀ᶠ x in 𝓝 p, (x, (0 : ℝ)) ∈ U :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds hp)
    exact hnear.mono hzero
  have hparam : L.comp (ContinuousLinearMap.inl ℝ E ℝ) = fderiv ℝ ι p :=
    ((hdf.comp p (hasFDerivAt_prodMk_left p (0 : ℝ))).congr_of_eventuallyEq heq.symm).fderiv.symm
  have htime : HasDerivAt (fun t ↦ f (p, t)) (L (0, 1)) 0 :=
    hdf.comp_hasDerivAt 0 ((hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0))
  obtain ⟨B, hBval⟩ := exists_equiv_of_transverse (fderiv ℝ ι p) hinj hdim
    (show L (0, 1) ∉ range (fderiv ℝ ι p) by rwa [htime.deriv] at htransverse)
  have hB : (B : E × ℝ →L[ℝ] F) = L := by
    apply ContinuousLinearMap.ext
    intro z
    change B z = L z
    rw [hBval]
    have hz : z = (z.1, (0 : ℝ)) + z.2 • ((0 : E), (1 : ℝ)) := by ext <;> simp
    conv_rhs => rw [hz]
    rw [map_add, map_smul]
    have hh := congrArg (fun A : E →L[ℝ] F ↦ A z.1) hparam
    exact congrArg (fun w ↦ w + z.2 • L (0, 1)) hh.symm
  apply exists_localInverse_of_hasFDerivAt_equiv hf hU hp
  rwa [hB]

end DifferentialGeometry.Analysis
