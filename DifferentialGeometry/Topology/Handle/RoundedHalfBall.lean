import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import DifferentialGeometry.Topology.Diffeomorph.Convex
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

noncomputable def roundedHalfBallFunction (n : ℕ) (ε η : ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  Real.smoothMax ε (‖z‖ ^ 2 - 1) (-(EuclideanSpace.equivProdLast n z).2 - η)

theorem convexOn_roundedHalfBallFunction (n : ℕ) {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    ConvexOn ℝ univ (roundedHalfBallFunction n ε η) := by
  apply Real.smoothMax.comp_convexOn hε
  · convert! ((convexOn_norm (E := EuclideanSpace ℝ (Fin (n + 1))) convex_univ).pow
      (fun _ _ => norm_nonneg _) 2).add_const (-1) using 1
  · let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
    let L := -((LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp A.toLinearMap)
    convert! (L.convexOn convex_univ).add_const (-η) using 1

theorem contDiff_roundedHalfBallFunction (n : ℕ) (ε η : ℝ) :
    ContDiff ℝ ∞ (roundedHalfBallFunction n ε η) :=
  (Real.smoothMax.contDiff ε).comp
    (((contDiff_norm_sq ℝ).sub contDiff_const).prodMk
      ((EuclideanSpace.equivProdLast (𝕜 := ℝ) n).contDiff.snd.neg.sub contDiff_const))

theorem roundedHalfBallFunction_nonpos_bounds (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : roundedHalfBallFunction n ε η z ≤ 0) :
    ‖z‖ ≤ 1 ∧ -η ≤ (EuclideanSpace.equivProdLast n z).2 := by
  have hmax := (Real.smoothMax.max_le hε (‖z‖ ^ 2 - 1)
    (-(EuclideanSpace.equivProdLast n z).2 - η)).trans hz
  obtain ⟨hx, hy⟩ := max_le_iff.mp hmax
  constructor <;> nlinarith [norm_nonneg z]

theorem roundedHalfBallFunction_eq_norm_sq_sub_one (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hsep : ε ≤ ‖z‖ ^ 2 - 1 + (EuclideanSpace.equivProdLast n z).2 + η) :
    roundedHalfBallFunction n ε η z = ‖z‖ ^ 2 - 1 := by
  rw [roundedHalfBallFunction, Real.smoothMax.eq_max_of_le hε]
  · exact max_eq_left (by linarith)
  · exact (by linarith : ε ≤ (‖z‖ ^ 2 - 1) -
      (-(EuclideanSpace.equivProdLast n z).2 - η)).trans (le_abs_self _)

theorem roundedHalfBallFunction_eq_neg_height_sub (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hsep : ε ≤ 1 - ‖z‖ ^ 2 - (EuclideanSpace.equivProdLast n z).2 - η) :
    roundedHalfBallFunction n ε η z = -(EuclideanSpace.equivProdLast n z).2 - η := by
  rw [roundedHalfBallFunction, Real.smoothMax.eq_max_of_le hε]
  · exact max_eq_right (by linarith)
  · exact (by linarith : ε ≤ -((‖z‖ ^ 2 - 1) -
      (-(EuclideanSpace.equivProdLast n z).2 - η))).trans (neg_le_abs _)

theorem roundedHalfBallFunction_eq_zero_iff_norm_eq_one (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hsep : ε ≤ ‖z‖ ^ 2 - 1 + (EuclideanSpace.equivProdLast n z).2 + η) :
    roundedHalfBallFunction n ε η z = 0 ↔ ‖z‖ = 1 := by
  rw [roundedHalfBallFunction_eq_norm_sq_sub_one n hε hsep]
  constructor <;> intro hz <;> nlinarith [norm_nonneg z]

theorem roundedHalfBallFunction_eq_zero_iff_height_eq_neg (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hsep : ε ≤ 1 - ‖z‖ ^ 2 - (EuclideanSpace.equivProdLast n z).2 - η) :
    roundedHalfBallFunction n ε η z = 0 ↔ (EuclideanSpace.equivProdLast n z).2 = -η := by
  rw [roundedHalfBallFunction_eq_neg_height_sub n hε hsep]
  constructor <;> intro hz <;> linarith

theorem roundedHalfBallFunction_eq_zero_sphere (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : ‖z‖ = 1)
    (hy : ε - η ≤ (EuclideanSpace.equivProdLast n z).2) :
    roundedHalfBallFunction n ε η z = 0 := by
  apply (roundedHalfBallFunction_eq_zero_iff_norm_eq_one n hε ?_).mpr hz
  rw [hz]
  linarith

theorem roundedHalfBallFunction_eq_zero_disk (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : ‖z‖ ^ 2 ≤ 1 - ε)
    (hy : (EuclideanSpace.equivProdLast n z).2 = -η) :
    roundedHalfBallFunction n ε η z = 0 := by
  apply (roundedHalfBallFunction_eq_zero_iff_height_eq_neg n hε ?_).mpr hy
  rw [hy]
  linarith

theorem roundedHalfBallFunction_nonpos_of_mem_upperHalfBall (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : ε ≤ η) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : ‖z‖ ≤ 1) (hy : 0 ≤ (EuclideanSpace.equivProdLast n z).2) :
    roundedHalfBallFunction n ε η z ≤ 0 := by
  have hx : ‖z‖ ^ 2 - 1 ≤ 0 := by nlinarith [norm_nonneg z]
  have hheight : -(EuclideanSpace.equivProdLast n z).2 - η ≤ -ε := by linarith
  have hbound := (Real.smoothMax.monotone_left ε
    (-(EuclideanSpace.equivProdLast n z).2 - η) hx).trans
      (Real.smoothMax.monotone_right ε 0 hheight)
  have hzero : Real.smoothMax ε 0 (-ε) = 0 := by
    have hsep : ε ≤ |(0 : ℝ) - -ε| := by simp [abs_of_pos hε]
    rw [Real.smoothMax.eq_max_of_le hε hsep]
    exact max_eq_left (by linarith)
  exact hbound.trans_eq hzero

theorem isCompact_sublevel_roundedHalfBallFunction (n : ℕ) {ε η : ℝ} (hε : 0 < ε) :
    IsCompact {z | roundedHalfBallFunction n ε η z ≤ 0} :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).of_isClosed_subset
    (isClosed_le (contDiff_roundedHalfBallFunction n ε η).continuous continuous_const)
    (fun _ hz => mem_closedBall_zero_iff.mpr (roundedHalfBallFunction_nonpos_bounds n hε hz).1)

theorem exists_diffeomorph_roundedHalfBall_at (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (c : EuclideanSpace ℝ (Fin (n + 1)))
    (hsmall : ε < min (1 - ‖c‖ ^ 2) ((EuclideanSpace.equivProdLast n c).2 + η)) :
    ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))),
      D 0 = c ∧
      D '' closedBall 0 1 = {z | roundedHalfBallFunction n ε η z ≤ 0} ∧
      D '' ball 0 1 = {z | roundedHalfBallFunction n ε η z < 0} ∧
      D '' sphere 0 1 = {z | roundedHalfBallFunction n ε η z = 0} := by
  have hneg : roundedHalfBallFunction n ε η c < 0 := by
    have hb := Real.smoothMax.le_max_add hε (‖c‖ ^ 2 - 1)
      (-(EuclideanSpace.equivProdLast n c).2 - η)
    have hmax : max (‖c‖ ^ 2 - 1) (-(EuclideanSpace.equivProdLast n c).2 - η) < -ε :=
      max_lt (by linarith [hsmall.trans_le (min_le_left _ _)])
        (by linarith [hsmall.trans_le (min_le_right _ _)])
    exact hb.trans_lt (by linarith)
  obtain ⟨D, hD0, _, hclosed, hopen, hsphere⟩ :=
    Diffeomorph.exists_diffeomorph_convex_sublevel (convexOn_roundedHalfBallFunction n hε η)
      (contDiff_roundedHalfBallFunction n ε η)
      (isCompact_sublevel_roundedHalfBallFunction n hε).isBounded hneg
  exact ⟨D, hD0, hclosed, hopen, hsphere⟩

theorem exists_diffeomorph_roundedHalfBall (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 η) :
    ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))),
      D 0 = 0 ∧
      D '' closedBall 0 1 = {z | roundedHalfBallFunction n ε η z ≤ 0} ∧
      D '' ball 0 1 = {z | roundedHalfBallFunction n ε η z < 0} ∧
      D '' sphere 0 1 = {z | roundedHalfBallFunction n ε η z = 0} := by
  exact exists_diffeomorph_roundedHalfBall_at n hε 0 (by simpa using hsmall)

theorem exists_diffeomorph_roundedHalfBall_zero (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2) :
    ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))),
      D 0 = (EuclideanSpace.equivProdLast n).symm (0, 1 / 2) ∧
      D '' closedBall 0 1 = {z | roundedHalfBallFunction n ε 0 z ≤ 0} ∧
      D '' ball 0 1 = {z | roundedHalfBallFunction n ε 0 z < 0} ∧
      D '' sphere 0 1 = {z | roundedHalfBallFunction n ε 0 z = 0} := by
  apply exists_diffeomorph_roundedHalfBall_at n hε
  rw [EuclideanSpace.norm_sq_equivProdLast_symm]
  norm_num
  exact hsmall

end DifferentialGeometry.Topology.Handle
