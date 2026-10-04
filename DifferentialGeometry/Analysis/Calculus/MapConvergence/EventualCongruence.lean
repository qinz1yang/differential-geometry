import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCPConvergenceOn.congr_eventually
    {U K : Set E} {p : ℕ} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCPConvergenceOn K p Φ Φinf) (hU : IsOpen U) (hKU : K ⊆ U)
    (hΦ : ∀ᶠ k in atTop, Set.EqOn (Φ' k) (Φ k) U)
    (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCPConvergenceOn K p Φ' Φ'inf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hΦ
  refine ⟨max k0 N, fun k hk r hr x hx => ?_⟩
  have hk0k : k0 ≤ k := (Nat.le_max_left k0 N).trans hk
  have hNk : N ≤ k := (Nat.le_max_right k0 N).trans hk
  have hxU : x ∈ U := hKU hx
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[nhds x]
      (fun y => Φ k y - Φinf y) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [hN k hNk hy, hΦinf hy]
  have hval : mapDerivNorm r (Φ' k) Φ'inf x = mapDerivNorm r (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  exact hk0 k hk0k r hr x hx

end DifferentialGeometry.CheegerGromovCompactness
