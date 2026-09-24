import DifferentialGeometry.External.RiemannMapping.RiemannMapExtremal
import DifferentialGeometry.Analysis.Complex.Univalent
import Mathlib.Analysis.Complex.Conformal

section

noncomputable section

open Set Metric
open scoped Topology

namespace Complex

theorem riemann_mapping
    {U : Set ℂ} (hU : IsOpen U) (hsc : IsSimplyConnected U) (hproper : U ≠ univ)
    {p : ℂ} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = ball 0 1 ∧ e p = 0 ∧
      DifferentiableOn ℂ e U ∧ DifferentiableOn ℂ e.symm (ball 0 1) ∧
      (∀ z ∈ U, deriv e z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, deriv e.symm z ≠ 0) := by
  obtain ⟨f, hf, hbij, hfp⟩ := exists_bijOn_unitBall_map_eq_zero hU hsc hproper hp
  obtain ⟨e, hes, het, heq, he, hei⟩ :=
    exists_openPartialHomeomorph_of_differentiableOn_of_bijOn hU hf hbij
  refine ⟨e, hes, het, (heq p).trans hfp, hes ▸ he, het ▸ hei, ?_, ?_⟩
  · intro z hz
    exact deriv_ne_zero_of_differentiableOn_of_injOn hU (hes ▸ he)
      (hes ▸ e.injOn) hz
  · intro z hz
    exact deriv_ne_zero_of_differentiableOn_of_injOn isOpen_ball (het ▸ hei)
      (het ▸ e.symm.injOn) hz

theorem exists_biholomorphic_map_to_unit_disk
    {U : Set ℂ} (hU : IsOpen U) (hsc : IsSimplyConnected U) (hproper : U ≠ univ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = ball 0 1 ∧
      DifferentiableOn ℂ e U ∧ DifferentiableOn ℂ e.symm (ball 0 1) ∧
      ∀ z ∈ U, deriv e z ≠ 0 := by
  obtain ⟨p, hp⟩ := hsc.nonempty
  obtain ⟨e, hes, het, _, he, hei, hne, _⟩ := riemann_mapping hU hsc hproper hp
  exact ⟨e, hes, het, he, hei, hne⟩

end Complex

end

end
