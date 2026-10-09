import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

theorem exists_real_linearIsometryEquiv_of_finrank_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : Module.finrank ℝ E = 1) :
    Nonempty (E ≃ₗᵢ[ℝ] ℝ) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hE]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  let b : OrthonormalBasis (Fin 1) ℝ E :=
    FiniteDimensional.orthonormalBasisSingleton (Fin 1) ℝ hE u hu
  let q : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ := by
    let f : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] ℝ :=
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
    have hf : ∀ x : EuclideanSpace ℝ (Fin 1), ‖f x‖ = ‖x‖ := by
      intro x
      change ‖x 0‖ = ‖x‖
      rw [PiLp.norm_eq_of_L2]
      rw [Fin.sum_univ_succ]
      simp only [Fin.isValue, Real.norm_eq_abs, sq_abs, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero, Real.sqrt_sq_eq_abs]
    apply LinearIsometryEquiv.ofBounds f
    · intro x
      exact (hf x).le
    · intro y
      have h := hf (f.symm y)
      simpa using h.symm.le
  exact ⟨b.repr.trans q⟩

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
