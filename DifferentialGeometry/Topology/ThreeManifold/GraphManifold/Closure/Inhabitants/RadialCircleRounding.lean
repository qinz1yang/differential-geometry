import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleDefiners

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialRoundingAmbient (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (‖z‖ ^ 2 - (3 / 4 : ℝ)) * (‖z‖ ^ 2 - (7 / 8 : ℝ))

def radialCircleRounding (b : radialCircleBase) : ℝ := radialRoundingAmbient b.val.val

theorem radialRoundingAmbient_smooth : ContDiff ℝ ∞ radialRoundingAmbient :=
  ((contDiff_norm_sq ℝ).sub contDiff_const).mul
    ((contDiff_norm_sq ℝ).sub contDiff_const)

theorem radialCircleRounding_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ radialCircleRounding :=
  radialRoundingAmbient_smooth.contMDiff.comp
    (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem radialRoundingAmbient_deriv (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt radialRoundingAmbient
      ((‖z‖ ^ 2 - (3 / 4 : ℝ)) • ((2 : ℕ) • innerSL ℝ z) +
        (‖z‖ ^ 2 - (7 / 8 : ℝ)) • ((2 : ℕ) • innerSL ℝ z)) z :=
  ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const (3 / 4 : ℝ)).mul
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const (7 / 8 : ℝ))

theorem radialCircleRounding_mfderiv (b : radialCircleBase) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) radialCircleRounding b =
      (radialBaseNorm b - (3 / 4 : ℝ)) • ((2 : ℕ) • innerSL ℝ b.val.val) +
        (radialBaseNorm b - (7 / 8 : ℝ)) • ((2 : ℕ) • innerSL ℝ b.val.val) := by
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (fun y : radialCircleBase => (fun v : loopCircleBase =>
      radialRoundingAmbient v.val) y.val) b = _
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun v : loopCircleBase => radialRoundingAmbient v.val) radialCircleBase b]
  rw [DifferentialGeometry.mfderiv_restrict_open
    radialRoundingAmbient loopCircleBase b.val, mfderiv_eq_fderiv]
  change fderiv ℝ radialRoundingAmbient b.val.val = _
  exact (radialRoundingAmbient_deriv b.val.val).fderiv

theorem radialCircleRounding_regular (b : radialCircleBase)
    (hb : radialCircleRounding b = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) radialCircleRounding b ≠ 0 := by
  intro hz
  have hg : (radialBaseNorm b - (3 / 4 : ℝ)) • ((2 : ℕ) • innerSL ℝ b.val.val) +
      (radialBaseNorm b - (7 / 8 : ℝ)) • ((2 : ℕ) • innerSL ℝ b.val.val) = 0 :=
    (radialCircleRounding_mfderiv b).symm.trans hz
  have he := congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => A b.val.val) hg
  rw [two_nsmul] at he
  change (radialBaseNorm b - (3 / 4 : ℝ)) *
      (inner ℝ b.val.val b.val.val + inner ℝ b.val.val b.val.val) +
    (radialBaseNorm b - (7 / 8 : ℝ)) *
      (inner ℝ b.val.val b.val.val + inner ℝ b.val.val b.val.val) = 0 at he
  rw [real_inner_self_eq_norm_sq] at he
  change (radialBaseNorm b - (3 / 4 : ℝ)) * (radialBaseNorm b - (7 / 8 : ℝ)) = 0 at hb
  rcases mul_eq_zero.mp hb with ha | hc
  · have hn := sub_eq_zero.mp ha
    change radialBaseNorm b = (3 / 4 : ℝ) at hn
    change (radialBaseNorm b - (3 / 4 : ℝ)) * (radialBaseNorm b + radialBaseNorm b) +
      (radialBaseNorm b - (7 / 8 : ℝ)) * (radialBaseNorm b + radialBaseNorm b) = 0 at he
    rw [hn] at he
    norm_num at he
  · have hn := sub_eq_zero.mp hc
    change radialBaseNorm b = (7 / 8 : ℝ) at hn
    change (radialBaseNorm b - (3 / 4 : ℝ)) * (radialBaseNorm b + radialBaseNorm b) +
      (radialBaseNorm b - (7 / 8 : ℝ)) * (radialBaseNorm b + radialBaseNorm b) = 0 at he
    rw [hn] at he
    norm_num at he

theorem radialCircleRounding_sublevel : {b | radialCircleRounding b ≤ 0} =
    radialCircleCornerBase := by
  ext b
  change (radialBaseNorm b - (3 / 4 : ℝ)) * (radialBaseNorm b - (7 / 8 : ℝ)) ≤ 0 ↔
    (3 / 4 : ℝ) ≤ radialBaseNorm b ∧ radialBaseNorm b ≤ (7 / 8 : ℝ)
  constructor
  · intro h
    constructor
    · by_contra! hl
      have hp : 0 < ((3 / 4 : ℝ) - radialBaseNorm b) *
          ((7 / 8 : ℝ) - radialBaseNorm b) := mul_pos (sub_pos.mpr hl) (by linarith)
      nlinarith
    · by_contra! hh
      have hp : 0 < (radialBaseNorm b - (3 / 4 : ℝ)) *
          (radialBaseNorm b - (7 / 8 : ℝ)) := mul_pos (by linarith) (sub_pos.mpr hh)
      linarith
  · rintro ⟨hl, hh⟩
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (sub_nonpos.mpr hh)

theorem radialCircleRounding_compact : IsCompact {b | radialCircleRounding b ≤ 0} := by
  rw [radialCircleRounding_sublevel]
  exact radialCircleCornerBase_compact

end GC.GraphManifold.Assembly.FC39P0.X135Radial
