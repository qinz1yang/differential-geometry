import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def crossingCornerFan : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 - p.2 / 2, p.2 + 2 * max (p.1 - p.2 / 2) 0)
  invFun p := (p.1 + (p.2 - 2 * max p.1 0) / 2, p.2 - 2 * max p.1 0)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by
    dsimp
    rw [show p.1 + (p.2 - 2 * max p.1 0) / 2 - (p.2 - 2 * max p.1 0) / 2 = p.1 by ring]
    ext <;> dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isPLHomeomorphOn_crossingCornerFan :
    IsPLHomeomorphOn crossingCornerFan univ univ := by
  let T : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - (1 / 2 : ℝ) • LinearMap.snd ℝ ℝ ℝ
  have hT : IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.1 - p.2 / 2) univ := by
    convert isPiecewiseAffineOn_of_affine T.toAffineMap isOpen_univ using 1
    ext p
    simp [T, div_eq_mul_inv, mul_comm]
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ _ 0) isOpen_univ
  have hR := isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hpl : IsPiecewiseAffineOn crossingCornerFan univ := by
    convert hT.prod_mk (hR.add ((hT.max hzero).add (hT.max hzero))) using 1
    ext p <;> dsimp [crossingCornerFan]; ring
  have hbij : BijOn crossingCornerFan univ univ :=
    ⟨mapsTo_univ _ _, crossingCornerFan.injective.injOn, fun y _ =>
      ⟨crossingCornerFan.symm y, mem_univ _,
        crossingCornerFan.apply_symm_apply y⟩⟩
  have hinv := IsPiecewiseAffineOn.symm
    (e := crossingCornerFan.toOpenPartialHomeomorph) hpl
  refine ⟨hbij, hpl, hinv.congr fun y hy => ?_⟩
  apply crossingCornerFan.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (crossingCornerFan.apply_symm_apply y).symm

theorem crossingCornerFan_horizontal_iff (p : ℝ × ℝ) :
    (crossingCornerFan p).2 = 2 * max (crossingCornerFan p).1 0 ↔
      p.2 = 0 := by
  change p.2 + 2 * max (p.1 - p.2 / 2) 0 = 2 * max (p.1 - p.2 / 2) 0 ↔ p.2 = 0
  exact add_eq_right

theorem crossingCornerFan_vertical_iff (p : ℝ × ℝ) :
    (crossingCornerFan p).2 = -2 * min (crossingCornerFan p).1 0 ↔
      p.1 = 0 := by
  change p.2 + 2 * max (p.1 - p.2 / 2) 0 = -2 * min (p.1 - p.2 / 2) 0 ↔ p.1 = 0
  have h := max_add_min (p.1 - p.2 / 2) 0
  constructor <;> intro hp <;> linarith

end DifferentialGeometry.Topology.PiecewiseLinear
