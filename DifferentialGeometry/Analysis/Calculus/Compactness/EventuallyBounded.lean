import DifferentialGeometry.Analysis.Calculus.Compactness.BilinearForm

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

section MapArzelaAscoli

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem bdd_of_eventually_bdd {U : Set E} (hU : IsOpen U) {Φ : ℕ → E → F}
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M := by
  classical
  intro r K hK hKU
  obtain ⟨M, hM⟩ := hbdd r K hK hKU
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hM
  have hfin : ∀ k : ℕ, ∃ Mₖ : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ Mₖ := fun k => by
    obtain ⟨Mₖ, hMₖ⟩ := hK.exists_bound_of_continuousOn
      (((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
        hU.uniqueDiffOn).mono hKU)
    exact ⟨Mₖ, fun x hx => by
      rw [← iteratedFDerivWithin_of_isOpen r hU (hKU hx)]
      exact hMₖ x hx⟩
  choose Mₖ hMₖ using hfin
  let S : Finset ℝ := (Finset.range (k₀ + 1)).image Mₖ
  have hSne : S.Nonempty :=
    ⟨Mₖ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k₀), rfl⟩⟩
  refine ⟨max M (S.max' hSne), fun k x hx => ?_⟩
  rcases lt_or_ge k (k₀ + 1) with hk | hk
  · have hm : Mₖ k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact (hMₖ k x hx).trans
      ((Finset.le_max' S (Mₖ k) hm).trans (le_max_right M (S.max' hSne)))
  · exact (hk₀ k (Nat.le_of_succ_le hk) x hx).trans (le_max_left M (S.max' hSne))

theorem exists_cInf_subseq_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvergenceOnCompacts U (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq_on hU Φ hΦ (bdd_of_eventually_bdd hU hΦ hbdd)

end MapArzelaAscoli

section BilinearFormArzelaAscoli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (g k) x‖ ≤ C)
    (a b : ℝ)
    (hab : ∀ k : ℕ, ∀ z ∈ U, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ g k z v v ∧ g k z v v ≤ b * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvergenceOnCompacts U (fun k => g (φ k)) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          a * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ b * ‖v‖ ^ 2 :=
  exists_smooth_bilinear_form_limit_subsequence_on hU g hg
    (bdd_of_eventually_bdd hU hg hbdd) a b hab

end BilinearFormArzelaAscoli

end CheegerGromovCompactness
end DifferentialGeometry
