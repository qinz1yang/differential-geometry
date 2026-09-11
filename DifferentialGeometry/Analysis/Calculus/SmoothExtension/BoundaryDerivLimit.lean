import Mathlib.Analysis.Calculus.FDeriv.Extend

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus.SmoothExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivWithinAt_Ici_of_tendsto_nhdsGT
    {f f' : ℝ → F} {L : F} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hlim : Tendsto f' (𝓝[>] a) (𝓝 L)) :
    HasDerivWithinAt f L (Ici a) a := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    ((hcont a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) ?_
  exact hlim.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab)
    (fun x hx => (hderiv x hx).deriv.symm))

theorem hasDerivWithinAt_Iic_of_tendsto_nhdsLT
    {f f' : ℝ → F} {L : F} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hlim : Tendsto f' (𝓝[<] b) (𝓝 L)) :
    HasDerivWithinAt f L (Iic b) b := by
  refine hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    ((hcont b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) ?_
  exact hlim.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
    (fun x hx => (hderiv x hx).deriv.symm))

theorem hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
    {f f' : ℝ → F} {a b t : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (ht : t ∈ Icc a b) :
    HasDerivWithinAt f (f' t) (Icc a b) t := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · by_cases hta : t = a
    · subst t
      have hlim : Tendsto f' (𝓝[>] a) (𝓝 (f' a)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
        exact (hf' a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
      exact (hasDerivWithinAt_Ici_of_tendsto_nhdsGT hab hf hderiv hlim).mono
        Icc_subset_Ici_self
    by_cases htb : t = b
    · subst t
      have hlim : Tendsto f' (𝓝[<] b) (𝓝 (f' b)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
        exact (hf' b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
      exact (hasDerivWithinAt_Iic_of_tendsto_nhdsLT hab hf hderiv hlim).mono
        Icc_subset_Iic_self
    exact (hderiv t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
      lt_of_le_of_ne ht.2 htb⟩).hasDerivWithinAt
  · rw [Icc_self, hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.singleton
  · exact (not_le_of_gt hab (ht.1.trans ht.2)).elim

end DifferentialGeometry.Analysis.Calculus.SmoothExtension
