import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {A : ℕ → E → F} {Ainf : E → F}
    {B : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ} {Binf : F → F →L[ℝ] F →L[ℝ] ℝ}
    (hA : MapCInfConvergenceOnCompacts U A Ainf)
    (hB : MapCInfConvergenceOnCompacts V B Binf)
    (hAc : ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W ∧ MapsTo (A k) W V)
    (hAinfC : ContDiffOn ℝ ∞ Ainf U)
    (hBc : ∀ k, ContDiffOn ℝ ∞ (B k) V)
    (hBinfC : ContDiffOn ℝ ∞ Binf V)
    (hmap : MapsTo Ainf U V) :
    MapCInfConvergenceOnCompacts U
      (fun k z => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B k (A k z), fderiv ℝ (A k) z))
      (fun z => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (Binf (Ainf z), fderiv ℝ Ainf z)) := by
  classical
  let : ProperSpace F := FiniteDimensional.proper ℝ F
  let : ProperSpace ((F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F)) :=
    FiniteDimensional.proper ℝ _
  intro K hK hKU p
  obtain ⟨W, hW, hKW, hWU, hev⟩ := hAc K hK hKU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let A' : ℕ → E → F := fun k => if N ≤ k then A k else Ainf
  have hAeq : ∀ᶠ k in atTop, EqOn (A' k) (A k) W := by
    filter_upwards [eventually_ge_atTop N] with k hk
    intro z _
    simp only [A', if_pos hk]
  have hAW : MapCInfConvergenceOnCompacts W A Ainf :=
    fun L hL hLW => hA L hL (hLW.trans hWU)
  have hA' : MapCInfConvergenceOnCompacts W A' Ainf :=
    hAW.congr_eventually hW hAeq (fun _ _ => rfl)
  have hA'c : ∀ k, ContDiffOn ℝ ∞ (A' k) W := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [A', if_pos hk] using (hN k hk).1
    · simpa only [A', if_neg hk] using hAinfC.mono hWU
  have hA'map : ∀ k, MapsTo (A' k) W V := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [A', if_pos hk] using (hN k hk).2
    · simpa only [A', if_neg hk] using hmap.mono_left hWU
  have hP := hA'.pullbackForm_comp_fderiv hW hV hB hA'c
    (hAinfC.mono hWU) hBc hBinfC (hmap.mono_left hWU) hA'map
  have hPeq : ∀ᶠ k in atTop,
      EqOn (fun z => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B k (A k z), fderiv ℝ (A k) z))
        (fun z => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
          (B k (A' k z), fderiv ℝ (A' k) z)) W := by
    filter_upwards [eventually_ge_atTop N] with k hk
    intro z _
    simp only [A', if_pos hk]
  exact (hP.congr_eventually hW hPeq (fun _ _ => rfl)) K hK hKW p

end DifferentialGeometry.CheegerGromovCompactness

end

end
