import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34ShellCrossingFan : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 - p.2 / 2, p.2 + 2 * max (p.1 - p.2 / 2) 0)
  invFun p := (p.1 + (p.2 - 2 * max p.1 0) / 2, p.2 - 2 * max p.1 0)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by
    dsimp
    rw [show p.1 + (p.2 - 2 * max p.1 0) / 2 - (p.2 - 2 * max p.1 0) / 2 = p.1 by ring]
    ext <;> dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isPLHomeomorphOn_section34ShellCrossingFan :
    IsPLHomeomorphOn section34ShellCrossingFan univ univ := by
  let T : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - (1 / 2 : ℝ) • LinearMap.snd ℝ ℝ ℝ
  have hT : IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.1 - p.2 / 2) univ := by
    convert isPiecewiseAffineOn_of_affine T.toAffineMap isOpen_univ using 1
    ext p
    simp [T, div_eq_mul_inv, mul_comm]
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ _ 0) isOpen_univ
  have hR := isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hpl : IsPiecewiseAffineOn section34ShellCrossingFan univ := by
    convert hT.prod_mk (hR.add ((hT.max hzero).add (hT.max hzero))) using 1
    ext p <;> dsimp [section34ShellCrossingFan]; ring
  have hbij : BijOn section34ShellCrossingFan univ univ :=
    ⟨mapsTo_univ _ _, section34ShellCrossingFan.injective.injOn, fun y _ =>
      ⟨section34ShellCrossingFan.symm y, mem_univ _,
        section34ShellCrossingFan.apply_symm_apply y⟩⟩
  have hinv := IsPiecewiseAffineOn.symm
    (e := section34ShellCrossingFan.toOpenPartialHomeomorph) hpl
  refine ⟨hbij, hpl, hinv.congr fun y hy => ?_⟩
  apply section34ShellCrossingFan.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (section34ShellCrossingFan.apply_symm_apply y).symm

theorem section34ShellCrossingFan_horizontal_iff (p : ℝ × ℝ) :
    (section34ShellCrossingFan p).2 = 2 * max (section34ShellCrossingFan p).1 0 ↔
      p.2 = 0 := by
  change p.2 + 2 * max (p.1 - p.2 / 2) 0 = 2 * max (p.1 - p.2 / 2) 0 ↔ p.2 = 0
  exact add_eq_right

theorem section34ShellCrossingFan_vertical_iff (p : ℝ × ℝ) :
    (section34ShellCrossingFan p).2 = -2 * min (section34ShellCrossingFan p).1 0 ↔
      p.1 = 0 := by
  change p.2 + 2 * max (p.1 - p.2 / 2) 0 = -2 * min (p.1 - p.2 / 2) 0 ↔ p.1 = 0
  have h := max_add_min (p.1 - p.2 / 2) 0
  constructor <;> intro hp <;> linarith

end DifferentialGeometry.Topology.PiecewiseLinear
