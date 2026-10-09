import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_fderiv_normal_graph_map_sub_starProjection_le
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T : H → L) (z : H)
    (hg : DifferentiableAt ℝ g (T z)) (hT : DifferentiableAt ℝ T z) :
    ‖fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z -
      L.starProjection‖ ≤
        ‖fderiv ℝ T z - L.orthogonalProjectionOnto‖ +
          ‖fderiv ℝ g (T z)‖ * (1 + ‖fderiv ℝ T z - L.orthogonalProjectionOnto‖) := by
  let A : H →L[ℝ] L := fderiv ℝ T z
  let B : L →L[ℝ] Lᗮ := fderiv ℝ g (T z)
  let C : H →L[ℝ] L := A - L.orthogonalProjectionOnto
  have hmap : HasFDerivAt (fun y => o + orthogonalCoordinateSum L (T y, g (T y)))
      (L.subtypeL.comp A + Lᗮ.subtypeL.comp (B.comp A)) z := by
    exact ((L.subtypeL.hasFDerivAt.comp z hT.hasFDerivAt).add
      (Lᗮ.subtypeL.hasFDerivAt.comp z (hg.hasFDerivAt.comp z hT.hasFDerivAt))).const_add o
  rw [hmap.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hA : ‖A w‖ ≤ (1 + ‖C‖) * ‖w‖ := by
    have heq : A w = C w + L.orthogonalProjectionOnto w := by
      change A w = (A w - L.orthogonalProjectionOnto w) + L.orthogonalProjectionOnto w
      abel
    rw [heq]
    calc
      ‖C w + L.orthogonalProjectionOnto w‖ ≤ ‖C w‖ + ‖L.orthogonalProjectionOnto w‖ := norm_add_le _ _
      _ ≤ ‖C‖ * ‖w‖ + ‖w‖ := add_le_add (C.le_opNorm w) (L.norm_orthogonalProjectionOnto_apply_le w)
      _ = (1 + ‖C‖) * ‖w‖ := by ring
  have heq : ((L.subtypeL.comp A + Lᗮ.subtypeL.comp (B.comp A)) - L.starProjection) w =
      (C w : H) + (B (A w) : H) := by
    change ((A w : H) + (B (A w) : H)) - (L.orthogonalProjectionOnto w : H) =
      ((A w : H) - (L.orthogonalProjectionOnto w : H)) + (B (A w) : H)
    abel
  rw [heq]
  calc
    ‖(C w : H) + (B (A w) : H)‖ ≤ ‖C w‖ + ‖B (A w)‖ := norm_add_le _ _
    _ ≤ ‖C‖ * ‖w‖ + ‖B‖ * ((1 + ‖C‖) * ‖w‖) :=
      add_le_add (C.le_opNorm w) ((B.le_opNorm (A w)).trans
        (mul_le_mul_of_nonneg_left hA (norm_nonneg _)))
    _ = _ := by dsimp only [A, B, C]; ring

end DifferentialGeometry.Analysis
