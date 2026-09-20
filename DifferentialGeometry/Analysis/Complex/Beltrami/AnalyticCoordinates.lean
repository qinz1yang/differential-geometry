import DifferentialGeometry.Analysis.Complex.Beltrami.LinearParts
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.ContDiff.Operations

section

noncomputable section

namespace DifferentialGeometry.Analysis

theorem differentiableAt_comp_symm_of_same_beltrami
    {f : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ) {z : ℂ} (hz : z ∈ e.target)
    {K : ℂ ≃L[ℝ] ℂ} (he : HasFDerivAt e K.toContinuousLinearMap (e.symm z))
    (hf : DifferentiableAt ℝ f (e.symm z)) {μ : ℂ}
    (hfBel : complexAntilinearPart (fderiv ℝ f (e.symm z)) =
      μ * complexLinearPart (fderiv ℝ f (e.symm z)))
    (heBel : complexAntilinearPart K.toContinuousLinearMap =
      μ * complexLinearPart K.toContinuousLinearMap) :
    DifferentiableAt ℂ (fun w => f (e.symm w)) z := by
  have hcomp := hf.hasFDerivAt.comp z (e.hasFDerivAt_symm hz he)
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hcomp.differentiableAt, ?_⟩
  have hh := hcomp.fderiv
  change fderiv ℝ (fun w => f (e.symm w)) z = _ at hh
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply]
  change fderiv ℝ f (e.symm z) (K.symm Complex.I) =
    Complex.I • fderiv ℝ f (e.symm z) (K.symm 1)
  rw [comp_inverse_apply_eq_mul_of_same_beltrami (fderiv ℝ f (e.symm z)) K hfBel heBel,
    comp_inverse_apply_eq_mul_of_same_beltrami (fderiv ℝ f (e.symm z)) K hfBel heBel]
  simp only [smul_eq_mul, mul_one]
  exact mul_comm _ _

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem analyticOnNhd_comp_symm_of_same_beltrami
    {Ω : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℝ f Ω)
    {μ : ℂ → ℂ}
    (hfBel : ∀ z ∈ Ω, complexAntilinearPart (fderiv ℝ f z) =
      μ z * complexLinearPart (fderiv ℝ f z))
    (e : OpenPartialHomeomorph ℂ ℂ) (heΩ : e.source ⊆ Ω)
    (he : DifferentiableOn ℝ e e.source)
    (hedet : ∀ z ∈ e.source, (fderiv ℝ e z).toLinearMap.det ≠ 0)
    (heBel : ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
      μ z * complexLinearPart (fderiv ℝ e z)) :
    AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target := by
  apply DifferentiableOn.analyticOnNhd _ e.open_target
  intro z hz
  have hx := e.map_target hz
  let K : ℂ ≃L[ℝ] ℂ :=
    ((fderiv ℝ e (e.symm z)).toLinearMap.equivOfIsUnitDet
      (isUnit_iff_ne_zero.mpr (hedet _ hx))).toContinuousLinearEquiv
  have hK : K.toContinuousLinearMap = fderiv ℝ e (e.symm z) := by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply _ v
  have heD : HasFDerivAt e K.toContinuousLinearMap (e.symm z) := by
    rw [hK]
    exact (he.differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt
  apply (differentiableAt_comp_symm_of_same_beltrami e hz heD
    ((hf.mono heΩ).differentiableAt (e.open_source.mem_nhds hx))
    (hfBel _ (heΩ hx)) ?_).differentiableWithinAt
  rw [hK]
  exact heBel _ hx

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_normalized_translate_beltrami
    (e : OpenPartialHomeomorph ℂ ℂ) (p : ℂ) {U : Set ℂ} {n : ℕ∞ω} {μ : ℂ → ℂ}
    (he0 : 0 ∈ e.source) (heU : e.source ⊆ (fun z => p + z) ⁻¹' U)
    (he : ContDiffOn ℝ n e e.source) (hei : ContDiffOn ℝ n e.symm e.target)
    (hbeltrami : ∀ z ∈ e.source,
      complexAntilinearPart (fderiv ℝ e z) = μ (p + z) * complexLinearPart (fderiv ℝ e z))
    (hdet : 0 < (fderiv ℝ e 0).toLinearMap.det) :
    ∃ f : OpenPartialHomeomorph ℂ ℂ,
      p ∈ f.source ∧ f.source ⊆ U ∧ f p = 0 ∧
      ContDiffOn ℝ n f f.source ∧ ContDiffOn ℝ n f.symm f.target ∧
      (∀ z, f z = e (z - p) - e 0) ∧
      (∀ y, f.symm y = e.symm (y + e 0) + p) ∧
      (∀ z ∈ f.source,
        complexAntilinearPart (fderiv ℝ f z) = μ z * complexLinearPart (fderiv ℝ f z)) ∧
      0 < (fderiv ℝ f p).toLinearMap.det := by
  let s := (Homeomorph.subRight p).toOpenPartialHomeomorph
  let t := (Homeomorph.subRight (e 0)).toOpenPartialHomeomorph
  let f := (s.trans e).trans t
  have hf (z : ℂ) : f z = e (z - p) - e 0 := rfl
  have hfi (y : ℂ) : f.symm y = e.symm (y + e 0) + p := rfl
  have hsource : f.source = (fun z : ℂ => z - p) ⁻¹' e.source := by
    simp [f, s, t]
  have htarget : f.target = (fun y : ℂ => y + e 0) ⁻¹' e.target := by
    simp only [f, s, t, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ,
      Set.univ_inter]
    rfl
  have hp : p ∈ f.source := by rw [hsource]; simpa using he0
  have hsourceU : f.source ⊆ U := by
    intro z hz
    rw [hsource] at hz
    have hzU := heU hz
    change p + (z - p) ∈ U at hzU
    simpa only [show p + (z - p) = z by ring] using hzU
  have hforward : ContDiffOn ℝ n f f.source := by
    change ContDiffOn ℝ n (fun z => e (z - p) - e 0) f.source
    apply (he.comp (contDiff_id.sub contDiff_const).contDiffOn _).sub contDiffOn_const
    intro z hz
    simpa only [hsource, Set.mem_preimage, id_eq] using hz
  have hinverse : ContDiffOn ℝ n f.symm f.target := by
    change ContDiffOn ℝ n (fun y => e.symm (y + e 0) + p) f.target
    apply (hei.comp (contDiff_id.add contDiff_const).contDiffOn _).add contDiffOn_const
    intro y hy
    simpa only [htarget, Set.mem_preimage, id_eq] using hy
  have hder (z : ℂ) : fderiv ℝ f z = fderiv ℝ e (z - p) := by
    change fderiv ℝ (fun z => e (z - p) - e 0) z = _
    rw [fderiv_sub_const, fderiv_comp_sub]
  refine ⟨f, hp, hsourceU, ?_, hforward, hinverse, hf, hfi, ?_, ?_⟩
  · rw [hf, sub_self, sub_self]
  · intro z hz
    rw [hder]
    have hz' : z - p ∈ e.source := by simpa only [hsource, Set.mem_preimage] using hz
    have hb := hbeltrami (z - p) hz'
    simpa only [show p + (z - p) = z by ring] using hb
  · rw [hder, sub_self]
    exact hdet

end DifferentialGeometry.Analysis

end

end
