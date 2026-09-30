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

theorem hasDerivAt_ite_of_one_sided_derivatives
    {fL fR : ℝ → F} {s : ℝ} {L : F}
    (hval : fL s = fR s)
    (hL : HasDerivWithinAt fL L (Iic s) s)
    (hR : HasDerivWithinAt fR L (Ici s) s) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) L s := by
  have hL' : HasDerivWithinAt (fun t => if t ≤ s then fL t else fR t) L (Iic s) s :=
    hL.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
  have hR' : HasDerivWithinAt (fun t => if t ≤ s then fL t else fR t) L (Ici s) s := by
    apply hR.congr
    · intro t ht
      rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | hst
      · exact (ite_eq_left le_rfl).trans hval
      · exact ite_eq_right (not_le.mpr hst)
    · exact (ite_eq_left le_rfl).trans hval
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hL'.union hR'

theorem hasDerivAt_ite_of_tendsto_derivatives
    {fL fR FL FR : ℝ → F} {a s b : ℝ} {L : F} (ha : a < s) (hb : s < b)
    (hL : ContinuousWithinAt fL (Icc a s) s)
    (hR : ContinuousWithinAt fR (Icc s b) s)
    (hderivL : ∀ t ∈ Ioo a s, HasDerivAt fL (FL t) t)
    (hderivR : ∀ t ∈ Ioo s b, HasDerivAt fR (FR t) t)
    (hval : fL s = fR s)
    (hlimL : Tendsto FL (𝓝[<] s) (𝓝 L))
    (hlimR : Tendsto FR (𝓝[>] s) (𝓝 L)) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) L s := by
  apply hasDerivAt_ite_of_one_sided_derivatives hval
  · refine hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hderivL t ht).differentiableAt.differentiableWithinAt)
      (hL.mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT ha) ?_
    exact hlimL.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT ha)
      (fun t ht => (hderivL t ht).deriv.symm))
  · refine hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hderivR t ht).differentiableAt.differentiableWithinAt)
      (hR.mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hb) ?_
    exact hlimR.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hb)
      (fun t ht => (hderivR t ht).deriv.symm))

theorem hasDerivAt_ite_of_continuous_derivatives
    {fL fR FL FR : ℝ → F} {a s b : ℝ} (ha : a < s) (hb : s < b)
    (hL : ContinuousWithinAt fL (Icc a s) s)
    (hR : ContinuousWithinAt fR (Icc s b) s)
    (hderivL : ∀ t ∈ Ioo a s, HasDerivAt fL (FL t) t)
    (hderivR : ∀ t ∈ Ioo s b, HasDerivAt fR (FR t) t)
    (hval : fL s = fR s)
    (hFL : ContinuousWithinAt FL (Icc a s) s)
    (hFR : ContinuousWithinAt FR (Icc s b) s) (hmatch : FL s = FR s) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) (FL s) s := by
  apply hasDerivAt_ite_of_tendsto_derivatives ha hb hL hR hderivL hderivR hval
  · rw [← nhdsWithin_Ioo_eq_nhdsLT ha]
    exact hFL.mono Ioo_subset_Icc_self
  · rw [hmatch, ← nhdsWithin_Ioo_eq_nhdsGT hb]
    exact hFR.mono Ioo_subset_Icc_self

end DifferentialGeometry.Analysis.Calculus.SmoothExtension
