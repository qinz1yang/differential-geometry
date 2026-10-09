import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionSurjectivity
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionZeroEquivalence
import DifferentialGeometry.Topology.Manifold.Submersion

set_option autoImplicit false
noncomputable section
open scoped ContDiff Manifold
namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

theorem isSubmersionAt_orthogonalProjectionOnto_of_affine_error
    (P : Submodule ℝ H) (η : H → H) (o : H) {U : Set H}
    (hU : IsOpen U) (hη : ContDiffOn ℝ ∞ η U)
    (herror : ∀ x ∈ U,
      ‖fderiv ℝ (fun y => η y - P.starProjection (y - o)) x‖ < 1) :
    ∀ x ∈ U, Manifold.IsSubmersionAt 𝓘(ℝ, H) 𝓘(ℝ, P) ∞
      (fun y => P.orthogonalProjectionOnto (η y)) x := by
  intro x hx
  let f : H → P := fun y => P.orthogonalProjectionOnto (η y)
  have hf : ContDiffOn ℝ ∞ f U :=
    P.orthogonalProjectionOnto.contDiff.comp_contDiffOn hη
  have hηd : DifferentiableAt ℝ η x :=
    (hη.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hsurj : Function.Surjective (fderiv ℝ f x) :=
    surjective_fderiv_orthogonalProjectionOnto_of_error P η o x hηd (herror x hx)
  have hsplit : (fderiv ℝ f x).HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
  exact DifferentialGeometry.Topology.Manifold.isSubmersionAt_of_hasFDerivAt_hasRightInverse
    hf hU hx ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt hsplit

theorem orthogonalProjectionOnto_section_zeroSet_of_mem_of_close
    (P : Submodule ℝ H) (Q : H → Submodule ℝ H) (η : H → H) (U : Set H)
    (hmem : ∀ x ∈ U, η x ∈ Q x)
    (hclose : ∀ x ∈ U, ‖(Q x).starProjection - P.starProjection‖ < 1) :
    {x : H | x ∈ U ∧ P.orthogonalProjectionOnto (η x) = 0} =
      {x : H | x ∈ U ∧ η x = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      P (Q x) (hclose x hx) (hmem x hx)).mp hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      P (Q x) (hclose x hx) (hmem x hx)).mpr hz⟩

end Submodule
