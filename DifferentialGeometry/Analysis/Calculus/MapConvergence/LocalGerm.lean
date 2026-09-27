import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

section

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCInfConvergenceOnCompacts.congr_eventually_locally
    {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvergenceOnCompacts U Φ Φinf)
    (hΦ : ∀ K, IsCompact K → K ⊆ U →
      ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ k in Filter.atTop, Set.EqOn (Φ' k) (Φ k) W)
    (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCInfConvergenceOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p
  obtain ⟨W, hW, hKW, hWU, hΦW⟩ := hΦ K hK hKU
  have hconv : MapCInfConvergenceOnCompacts W Φ Φinf :=
    fun L hL hLW q => h L hL (hLW.trans hWU) q
  exact (hconv.congr_eventually hW hΦW (hΦinf.mono hWU)) K hK hKW p

end DifferentialGeometry.CheegerGromovCompactness


end

section

set_option autoImplicit false
open Filter
open scoped Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCInfConvergenceOnCompacts.congr_eventually_germ
    {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvergenceOnCompacts U Φ Φinf)
    (hΦ : ∀ K, IsCompact K → K ⊆ U →
      ∀ᶠ k in atTop, ∀ z ∈ K, Φ' k =ᶠ[𝓝 z] Φ k)
    (hΦinf : ∀ z ∈ U, Φ'inf =ᶠ[𝓝 z] Φinf) :
    MapCInfConvergenceOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU p ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hΦ K hK hKU)
  refine ⟨max k0 N, fun k hk r hr z hz => ?_⟩
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[𝓝 z] (fun y => Φ k y - Φinf y) :=
    (hN k ((Nat.le_max_right k0 N).trans hk) z hz).sub (hΦinf z (hKU hz))
  have hval : mapDerivNorm r (Φ' k) Φ'inf z = mapDerivNorm r (Φ k) Φinf z := by
    simp only [mapDerivNorm]
    rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
  rw [hval]
  exact hk0 k ((Nat.le_max_left k0 N).trans hk) r hr z hz

end DifferentialGeometry.CheegerGromovCompactness


end
