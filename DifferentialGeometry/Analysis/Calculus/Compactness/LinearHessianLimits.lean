import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.LinearSystemBounds
import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothLimits

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private local instance derivativeNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) :=
  inferInstance

private local instance derivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) :=
  inferInstance

private local instance hessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

private local instance hessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

theorem contDiffOn_and_continuousOn_spatial_iteratedFDeriv_Icc_of_hessian_eq
    {a b : ℝ} (hab : a < b) {U : Set E} (hU : IsOpen U)
    (f : ℝ → E → F)
    (A : ℝ → E → (E →L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (B : ℝ → E → E →L[ℝ] E →L[ℝ] F)
    (hf : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (Icc a b ×ˢ U))
    (hfs : ∀ t ∈ Ico a b, ContDiffOn ℝ ∞ (f t) U)
    (hAs : ∀ t ∈ Ico a b, ContDiffOn ℝ ∞ (A t) U)
    (hBs : ∀ t ∈ Ico a b, ContDiffOn ℝ ∞ (B t) U)
    (heq : ∀ t ∈ Ico a b, EqOn (fderiv ℝ (fderiv ℝ (f t)))
      (fun x => A t x (fderiv ℝ (f t) x) + B t x) U)
    (hdf : ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ Ico a b, ∀ x ∈ K, ‖fderiv ℝ (f t) x‖ ≤ C)
    (hAbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ Ico a b, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (A t) x‖ ≤ C)
    (hBbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ Ico a b, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (B t) x‖ ≤ C) :
    (∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (f t) U) ∧
      ∀ r : ℕ, ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ r (f p.1) p.2) (Icc a b ×ˢ U) := by
  have hfTime (x : E) (hx : x ∈ U) : ContinuousOn (fun t => f t x) (Icc a b) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, hx⟩)
  apply CheegerGromovCompactness.contDiffOn_and_continuousOn_spatial_iteratedFDeriv_Icc
    hab hU f (fun x hx => (hfTime x hx).mono Ico_subset_Icc_self)
    (fun x hx => (hfTime x hx b ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self) hfs
  intro r K hK hKU
  cases r with
  | zero =>
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (hf.mono (Set.prod_mono Set.Subset.rfl hKU))
    refine ⟨C, fun t ht x hx => ?_⟩
    simpa only [norm_iteratedFDeriv_zero] using hC (t, x) ⟨Ico_subset_Icc_self ht, hx⟩
  | succ r =>
    have hu : ∀ t : Ico a b, ContDiffOn ℝ ∞ (fderiv ℝ (f t)) U :=
      fun t => (hfs t t.property).fderiv_of_isOpen hU (by simp)
    obtain ⟨C, hC⟩ := exists_iteratedFDeriv_bound_of_fderiv_eq_clm_apply_add hU hKU
      (fun t : Ico a b => fderiv ℝ (f t))
      (fun t : Ico a b => A t) (fun t : Ico a b => B t) hu
      (fun t => hAs t t.property) (fun t => hBs t t.property)
      (fun t => heq t t.property)
      (by
        obtain ⟨C, hC⟩ := hdf K hK hKU
        exact ⟨C, fun t x hx => hC t t.property x hx⟩)
      (by
        intro q
        obtain ⟨C, hC⟩ := hAbdd q K hK hKU
        exact ⟨C, fun t x hx => hC t t.property x hx⟩)
      (by
        intro q
        obtain ⟨C, hC⟩ := hBbdd q K hK hKU
        exact ⟨C, fun t x hx => hC t t.property x hx⟩) r
    refine ⟨C, fun t ht x hx => ?_⟩
    simpa only [norm_iteratedFDeriv_fderiv] using hC ⟨t, ht⟩ x hx

end DifferentialGeometry.Analysis.Calculus
