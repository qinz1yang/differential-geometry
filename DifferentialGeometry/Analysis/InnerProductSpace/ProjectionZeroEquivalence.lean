import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionRankStability

set_option autoImplicit false
noncomputable section

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1)
    {v : H} (hv : v ∈ Q) :
    P.orthogonalProjectionOnto v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have hinj := injective_orthogonalProjectionOnto_restrict_of_norm_sub_lt_one Q P hclose
    have hsub : (⟨v, hv⟩ : Q) = 0 := hinj (by simpa using hz)
    exact congrArg (fun w : Q => (w : H)) hsub
  · rintro rfl
    exact map_zero P.orthogonalProjectionOnto

theorem starProjection_eq_zero_iff_of_mem_of_norm_sub_lt_one
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hclose : ‖Q.starProjection - P.starProjection‖ < 1)
    {v : H} (hv : v ∈ Q) :
    P.starProjection v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    apply (orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one P Q hclose hv).mp
    apply Subtype.ext
    change P.starProjection v = 0
    exact hz
  · rintro rfl
    exact map_zero P.starProjection

theorem orthogonalProjectionOnto_projected_displacement_zeroSet
    (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    (Q : H → Submodule 𝕜 H) [∀ x, (Q x).HasOrthogonalProjection]
    (μ : H → H) (U : Set H)
    (hclose : ∀ x ∈ U, ‖(Q x).starProjection - P.starProjection‖ < 1) :
    {x : H | x ∈ U ∧ P.orthogonalProjectionOnto ((Q x).starProjection (x - μ x)) = 0} =
      {x : H | x ∈ U ∧ (Q x).starProjection (x - μ x) = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      P (Q x) (hclose x hx) ((Q x).starProjection_apply_mem (x - μ x))).mp hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      P (Q x) (hclose x hx) ((Q x).starProjection_apply_mem (x - μ x))).mpr hz⟩

end Submodule
