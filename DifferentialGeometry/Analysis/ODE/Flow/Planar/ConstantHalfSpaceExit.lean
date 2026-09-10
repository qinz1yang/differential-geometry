import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHalfSpaceFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.TransverseHittingTime

noncomputable section
open Set Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_smooth_exitTime_of_constant_halfSpace
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : P × E → E} {γ : P × ℝ → E} {S : Set P}
    (hv : ContDiff ℝ ∞ v) (hγ : ContDiff ℝ ∞ γ)
    (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ} (hc : 0 < ℓ c)
    (hfixed : ∀ p ∈ S, ∀ x, b ≤ ℓ x → v (p, x) = c)
    (hderiv : ∀ p ∈ S, ∀ t, HasDerivAt (fun t ↦ γ (p, t)) (v (p, γ (p, t))) t)
    (hzero : ∀ p ∈ S, ℓ (γ (p, 0)) < b)
    (hcross : ∀ p ∈ S, ∃ t : ℝ, ℓ (γ (p, t)) = b) :
    ∃ τ : P → ℝ, ContDiffOn ℝ ∞ τ S ∧
      (∀ p ∈ S, 0 < τ p) ∧
      (∀ p ∈ S, ℓ (γ (p, τ p)) = b) ∧
      (∀ p ∈ S, ∀ t, ℓ (γ (p, t)) = b → t = τ p) ∧
      ∀ p ∈ S, ∀ s : ℝ, 0 ≤ s → γ (p, τ p + s) = γ (p, τ p) + s • c := by
  have hvs (p : P) : ContDiff ℝ ∞ (fun x ↦ v (p, x)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  let H : P × ℝ → ℝ := fun q ↦ ℓ (γ q)
  have hH : ContDiff ℝ ∞ H := ℓ.contDiff.comp hγ
  have hunique (p : P) (hp : p ∈ S) : ∃! t : ℝ, H (p, t) = b := by
    obtain ⟨t, ht⟩ := hcross p hp
    exact ⟨t, ht, fun s hs ↦ eq_of_integralCurve_constant_halfSpace_crossings
      (hvs p) ℓ c hc (hfixed p hp) (hderiv p hp) hs ht⟩
  have htrans (p : P) (hp : p ∈ S) (t : ℝ) (ht : H (p, t) = b) :
      fderiv ℝ H (p, t) (0, 1) ≠ 0 := by
    have hd : HasDerivAt (fun t ↦ H (p, t)) (ℓ c) t := by
      have hd' := ℓ.hasFDerivAt.comp_hasDerivAt t (hderiv p hp t)
      simpa only [hfixed p hp _ ht.ge, Function.comp_def, H] using hd'
    have hdf : HasDerivAt (fun t ↦ H (p, t)) (fderiv ℝ H (p, t) (0, 1)) t :=
      (hH.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t p).prodMk (hasDerivAt_id t))
    exact (hdf.unique hd).trans_ne hc.ne'
  obtain ⟨τ, hτ, hroot, huniq⟩ := exists_contDiffOn_transverse_hittingTime
    (V := univ) isOpen_univ (subset_univ S) hH.contDiffOn contDiffOn_const hunique htrans
  refine ⟨τ, hτ, ?_, hroot, huniq, ?_⟩
  · intro p hp
    exact pos_of_integralCurve_constant_halfSpace_crossing (hvs p) ℓ c hc.le (hfixed p hp)
      (hderiv p hp) (hzero p hp) (hroot p hp)
  · intro p hp s hs
    exact integralCurve_eq_translation_in_constant_halfSpace (hvs p) ℓ c hc.le (hfixed p hp)
      (hderiv p hp) (hroot p hp).ge hs

end DifferentialGeometry.Analysis
