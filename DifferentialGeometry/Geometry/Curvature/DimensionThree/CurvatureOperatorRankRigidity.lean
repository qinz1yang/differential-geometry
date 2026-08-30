import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped BigOperators

theorem curvatureOperator_rank_two_reaction_annihilation_impossible
    {A : Matrix (Fin 3) (Fin 3) Real}
    (hA : A.PosSemidef) (hrank : A.rank = 2)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) :
    False := by
  have hdim : A.rank +
      Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
    simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
  have hkerpos : 0 < Module.finrank Real (Matrix.mulVecLin A).ker := by
    omega
  obtain ⟨v, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkerpos
  have hvker : Matrix.mulVec A v = 0 := by
    exact LinearMap.mem_ker.mp v.2
  have hvreaction : Matrix.mulVec (curvatureOperatorReaction3 A) v = 0 :=
    hnull v hvker
  have hR : (curvatureOperatorReaction3 A).PosDef :=
    curvatureOperatorReaction3_posDef_of_rank_two hA hrank
  have hvne' : (v : Fin 3 → Real) ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext h
  have hpositive : 0 < dotProduct v
      (Matrix.mulVec (curvatureOperatorReaction3 A) v) := by
    simpa [show star (v : Fin 3 → Real) = v from rfl] using
      hR.dotProduct_mulVec_pos hvne'
  rw [hvreaction] at hpositive
  simp at hpositive

theorem curvatureOperator_rank_trichotomy_of_reaction_annihilation
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) :
    A.rank = 0 ∨ A.rank = 1 ∨ A.rank = 3 := by
  have hle : A.rank ≤ 3 := Matrix.rank_le_height A
  have htwo : A.rank ≠ 2 := by
    intro htwo
    exact curvatureOperator_rank_two_reaction_annihilation_impossible hA htwo hnull
  omega

theorem curvatureOperatorReaction3_preserves_kernel
    {A : Matrix (Fin 3) (Fin 3) Real} {v : Fin 3 → Real}
    (hv : Matrix.mulVec A v = 0) :
    Matrix.mulVec A (Matrix.mulVec (curvatureOperatorReaction3 A) v) = 0 := by
  have hcomm := curvatureOperatorReaction3_commute A
  have hvec := congrArg (fun B : Matrix (Fin 3) (Fin 3) Real => Matrix.mulVec B v) hcomm.eq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hvec
  exact hvec

theorem curvatureOperator_rank_zero_iff
    {A : Matrix (Fin 3) (Fin 3) Real} :
    A.rank = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hspan : Submodule.span Real (Set.range A.col) = ⊥ := by
      rw [← Matrix.range_mulVecLin]
      exact Submodule.finrank_eq_zero.mp h
    apply Matrix.ext
    intro i j
    have hc : A.col j ∈ Submodule.span Real (Set.range A.col) :=
      Submodule.subset_span (Set.mem_range_self j)
    have hc0 : A.col j = 0 := by
      have hc' : A.col j ∈ (⊥ : Submodule Real (Fin 3 → Real)) := by
        rw [← hspan]
        exact hc
      simpa using hc'
    have hi := congr_fun hc0 i
    simpa [Matrix.col] using hi
  · intro h
    subst A
    simp [Matrix.rank]

theorem curvatureOperator_rank_three_iff_injective
    {A : Matrix (Fin 3) (Fin 3) Real} :
    A.rank = 3 ↔ Function.Injective (Matrix.mulVecLin A) := by
  constructor
  · intro h
    apply LinearMap.ker_eq_bot.mp
    have hdim : A.rank +
        Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
      simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
    have hker : Module.finrank Real (Matrix.mulVecLin A).ker = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hker
  · intro h
    have hker : Module.finrank Real (Matrix.mulVecLin A).ker = 0 := by
      rw [Submodule.finrank_eq_zero]
      exact LinearMap.ker_eq_bot.mpr h
    have hdim : A.rank +
        Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
      simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
    omega

end DifferentialGeometry.Geometry.Curvature.DimensionThree
