import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRestriction

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

private def rescaleInterval (r lambda : ℝ) (hlambda : 0 < lambda) :
    Diffeomorph 𝓘(ℝ) 𝓘(ℝ) (symmetricOpenInterval (lambda * r)) (symmetricOpenInterval r) ∞ where
  toFun t := ⟨t.val / lambda, by
    constructor
    · apply (lt_div_iff₀ hlambda).mpr
      nlinarith [t.property.1]
    · apply (div_lt_iff₀ hlambda).mpr
      nlinarith [t.property.2]⟩
  invFun t := ⟨lambda * t.val, by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  left_inv t := Subtype.ext (by field_simp)
  right_inv t := Subtype.ext (by simp [hlambda.ne'])
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval r) _).mp
    (contMDiff_subtype_val.div_const lambda)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval (lambda * r)) _).mp
    (contMDiff_const.mul contMDiff_subtype_val)

variable {E H F G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def rescaleParameter (lambda : ℝ) (hlambda : 0 < lambda) : SmoothTwoSidedCollar I J e where
  radius := lambda * c.radius
  radius_pos := mul_pos hlambda c.radius_pos
  neighborhood := c.neighborhood
  toDiffeomorph := ((Diffeomorph.refl I S ∞).prodCongr
    (rescaleInterval c.radius lambda hlambda)).trans c.toDiffeomorph
  zero_eq s := by
    change c.toFun (s, ⟨(0 : ℝ) / lambda, _⟩) = e s
    exact (congrArg (fun t : symmetricOpenInterval c.radius => c.toFun (s, t))
      (Subtype.ext (zero_div lambda))).trans (c.toFun_zero s)

@[simp] theorem rescaleParameter_radius (lambda : ℝ) (hlambda : 0 < lambda) :
    (c.rescaleParameter lambda hlambda).radius = lambda * c.radius := rfl

@[simp] theorem rescaleParameter_neighborhood (lambda : ℝ) (hlambda : 0 < lambda) :
    (c.rescaleParameter lambda hlambda).neighborhood = c.neighborhood := rfl

@[simp] theorem rescaleParameter_toFun (lambda : ℝ) (hlambda : 0 < lambda)
    (p : S × symmetricOpenInterval (lambda * c.radius)) :
    (c.rescaleParameter lambda hlambda).toFun p = c.toFun (p.1, ⟨p.2.val / lambda, by
      constructor
      · apply (lt_div_iff₀ hlambda).mpr
        nlinarith [p.2.property.1]
      · apply (div_lt_iff₀ hlambda).mpr
        nlinarith [p.2.property.2]⟩) := rfl

theorem rescaleParameter_symm_toDiffeomorph (lambda : ℝ) (hlambda : 0 < lambda)
    (p : c.neighborhood) :
    (c.rescaleParameter lambda hlambda).toDiffeomorph.symm p =
      ((c.toDiffeomorph.symm p).1, ⟨lambda * (c.toDiffeomorph.symm p).2.val, by
        change -(lambda * c.radius) < lambda * (c.toDiffeomorph.symm p).2.val ∧
          lambda * (c.toDiffeomorph.symm p).2.val < lambda * c.radius
        constructor <;> nlinarith [(c.toDiffeomorph.symm p).2.property.1,
          (c.toDiffeomorph.symm p).2.property.2]⟩) := rfl

theorem rescaleParameter_radius_add_le (hc : c.radius ≤ 1 / 2)
    (R : ℝ) (hR : 0 < R) :
    (c.rescaleParameter (2 * R) (mul_pos (by norm_num) hR)).radius + R ≤ 2 * R := by
  rw [rescaleParameter_radius]
  nlinarith

theorem restrictRadius_rescaleParameter_radius_add_lt (R : ℝ) (hR : 0 < R) :
    ((c.restrictRadius (min c.radius (1 / 4))
      (lt_min c.radius_pos (by norm_num)) (min_le_left _ _)).rescaleParameter
      (2 * R) (mul_pos (by norm_num) hR)).radius + R < 2 * R := by
  rw [rescaleParameter_radius, restrictRadius_radius]
  have hr : min c.radius (1 / 4) ≤ (1 / 4 : ℝ) := min_le_right _ _
  nlinarith

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
