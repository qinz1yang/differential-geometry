import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Basic
import Mathlib.Topology.MetricSpace.Holder

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {T : ℝ}

theorem holderOnWith_toFun (u : timeH1 X T) :
    HolderOnWith ‖u.deriv‖₊ (1 / 2) u.toFun (Set.Icc 0 T) := by
  intro x hx y hy
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  change (nndist (u.toFun x) (u.toFun y) : ℝ) ≤
    (‖u.deriv‖₊ * nndist x y ^ ((1 / 2 : ℝ≥0) : ℝ) : ℝ≥0)
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, coe_nnnorm, dist_eq_norm, Real.norm_eq_abs,
    ← Real.sqrt_eq_rpow]
  simpa only [mul_comm] using u.toFun_sub_le hy hx

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
