import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCPConvergenceOn.fderiv
    {K : Set E} {p : ℕ} {f : ℕ → E → F} {g : E → F}
    (hconv : MapCPConvergenceOn K (p + 1) f g)
    (hf : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (f n) y)
    (hg : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y) :
    MapCPConvergenceOn K p (fun n => _root_.fderiv ℝ (f n)) (_root_.fderiv ℝ g) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  have htail : ∀ᶠ n in atTop, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (_root_.fderiv ℝ (f n)) (_root_.fderiv ℝ g) x ≤ ε := by
    filter_upwards [eventually_ge_atTop N, hf] with n hn hfn
    intro r hr x hx
    have heq : (fun y => _root_.fderiv ℝ (f n) y - _root_.fderiv ℝ g y) =ᶠ[𝓝 x]
        _root_.fderiv ℝ (fun y => f n y - g y) := by
      filter_upwards [hfn x hx, hg x hx] with y hfy hgy
      exact (fderiv_sub hfy hgy).symm
    have hnorm : mapDerivNorm r (_root_.fderiv ℝ (f n)) (_root_.fderiv ℝ g) x =
        mapDerivNorm (r + 1) (f n) g x := by
      simp only [mapDerivNorm]
      rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
      exact norm_iteratedFDeriv_fderiv
    rw [hnorm]
    exact hN n hn (r + 1) (Nat.add_le_add_right hr 1) x hx
  exact eventually_atTop.mp htail


theorem finite_fderiv_convergence
    {U L : Set E} (hU : IsOpen U) (hLU : L ⊆ U) (n : ℕ)
    {f : ℕ → E → F} {g : E → F}
    (hf : ∀ k, ContDiffOn ℝ (n + 1 : ℕ) (f k) U)
    (hg : ContDiffOn ℝ (n + 1 : ℕ) g U)
    (hconv : MapCPConvergenceOn L (n + 1) f g) :
    MapCPConvergenceOn L n (fun k => fderiv ℝ (f k)) (fderiv ℝ g) := by
  exact hconv.fderiv
    (Eventually.of_forall fun k x hx =>
      ((hf k).differentiableOn (by simp)).eventually_differentiableAt
        (hU.mem_nhds (hLU hx)))
    (fun x hx => (hg.differentiableOn (by simp)).eventually_differentiableAt
      (hU.mem_nhds (hLU hx)))

end

end DifferentialGeometry.CheegerGromovCompactness
