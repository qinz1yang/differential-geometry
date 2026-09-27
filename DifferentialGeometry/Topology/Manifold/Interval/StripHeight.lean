import DifferentialGeometry.Topology.Manifold.Interval.Tangent
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped ContDiff
namespace DifferentialGeometry.Manifold.Interval
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {J : ModelWithCorners ℝ E H}
  {a b : ℝ} [Fact (a < b)] (S : TopologicalSpace.Opens (B × Icc a b))


theorem mfderiv_stripHeight (q : S) (v : TangentSpace (J.prod (𝓡∂ 1)) q) :
    mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) (fun p : S => p.val.2.val) q v =
      tangentCoordinateIcc q.val.2 v.2 := by
  have hi := (contMDiff_subtypeVal_Icc (x := a) (y := b) (n := ∞)).mdifferentiableAt
    (x := q.val.2) (by simp)
  have hs := (mdifferentiableAt_snd (I := J) (I' := 𝓡∂ 1)).comp q
    ((contMDiff_subtype_val (U := S) (n := ∞)).mdifferentiableAt (by simp))
  have hh := mfderiv_comp q hi hs
  have hp := mfderiv_comp q (mdifferentiableAt_snd (I := J) (I' := 𝓡∂ 1))
    ((contMDiff_subtype_val (U := S) (n := ∞)).mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val, mfderiv_snd] at hp
  rw [hp] at hh
  exact congrArg (fun A => A v) hh


theorem mfderiv_stripHeight_ne_zero (q : S) :
    mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) (fun p : S => p.val.2.val) q ≠ 0 := by
  intro hz
  have hh := mfderiv_stripHeight (J := J) S q (0, (tangentCoordinateIcc q.val.2).symm 1)
  rw [hz] at hh
  change (0 : ℝ) = tangentCoordinateIcc q.val.2 ((tangentCoordinateIcc q.val.2).symm 1) at hh
  exact zero_ne_one (hh.trans ((tangentCoordinateIcc q.val.2).apply_symm_apply 1))

end DifferentialGeometry.Manifold.Interval
