import DifferentialGeometry.Topology.Morse.RegularLevel.LevelSet
import DifferentialGeometry.Topology.Manifold.ModelHomeomorph
import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold

namespace DifferentialGeometry.Topology.Morse

noncomputable def morseModelEuclideanEquiv (m : ℕ) :
    MorseModel (m + 1) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap (0 : Fin (m + 1)) (Fin.last m))).toContinuousLinearEquiv

@[simp]
theorem morseModelEuclideanEquiv_apply_zero (m : ℕ) (x : MorseModel (m + 1)) :
    morseModelEuclideanEquiv m x 0 = x (Fin.last m) := by
  simp [morseModelEuclideanEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

@[simp]
theorem morseModelEuclideanEquiv_symm_apply_last (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (morseModelEuclideanEquiv m).symm x (Fin.last m) = x 0 := by
  have h := morseModelEuclideanEquiv_apply_zero m ((morseModelEuclideanEquiv m).symm x)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

noncomputable def morseHalfSpaceEuclideanHomeomorph (m : ℕ) :
    MorseHalfSpace m ≃ₜ EuclideanHalfSpace (m + 1) where
  toFun x := ⟨morseModelEuclideanEquiv m x.1, by simpa using x.2⟩
  invFun x := ⟨(morseModelEuclideanEquiv m).symm x.1, by simpa using x.2⟩
  left_inv x := Subtype.ext ((morseModelEuclideanEquiv m).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((morseModelEuclideanEquiv m).apply_symm_apply x.1)
  continuous_toFun := ((morseModelEuclideanEquiv m).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((morseModelEuclideanEquiv m).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp]
theorem morseHalfSpaceEuclideanHomeomorph_apply_val (m : ℕ) (x : MorseHalfSpace m) :
    (morseHalfSpaceEuclideanHomeomorph m x).1 = morseModelEuclideanEquiv m x.1 := rfl

@[simp]
theorem morseHalfSpaceEuclideanHomeomorph_symm_apply_val (m : ℕ)
    (x : EuclideanHalfSpace (m + 1)) :
    ((morseHalfSpaceEuclideanHomeomorph m).symm x).1 =
      (morseModelEuclideanEquiv m).symm x.1 := rfl

@[simp]
theorem modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph
    (m : ℕ) (x : MorseHalfSpace m) :
    modelWithCornersEuclideanHalfSpace (m + 1) (morseHalfSpaceEuclideanHomeomorph m x) =
      morseModelEuclideanEquiv m (morseModelWithCornersHalfSpace m x) := rfl

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

theorem morseHalfSpaceEuclideanHomeomorph_isManifold {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (MorseHalfSpace m) M] {n : WithTop ℕ∞}
    [IsManifold (morseModelWithCornersHalfSpace m) n M] :
    letI := ChartedSpace.transHomeomorph (M := M) (morseHalfSpaceEuclideanHomeomorph m)
    IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) n M := by
  apply ChartedSpace.isManifold_transHomeomorph
    (I := (morseModelWithCornersHalfSpace m).transContinuousLinearEquiv
      (morseModelEuclideanEquiv m))
  exact fun _ => rfl

end DifferentialGeometry.Topology.Morse
