import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleProduct
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialBaseNorm (b : radialCircleBase) : ℝ := ‖b.val.val‖ ^ 2

theorem radialBaseNorm_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ radialBaseNorm :=
  (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem radialBaseNorm_mfderiv (b : radialCircleBase) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) radialBaseNorm b = 2 • innerSL ℝ b.val.val := by
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (fun y : radialCircleBase => (fun v : loopCircleBase => ‖v.val‖ ^ 2) y.val) b = _
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun v : loopCircleBase => ‖v.val‖ ^ 2) radialCircleBase b]
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ 2) loopCircleBase b.val]
  rw [mfderiv_eq_fderiv, fderiv_norm_sq_apply]
  rfl

theorem radialBaseNorm_regular (b : radialCircleBase) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) radialBaseNorm b ≠ 0 := by
  intro hz
  have hg : (2 : ℕ) • innerSL ℝ b.val.val = 0 :=
    (radialBaseNorm_mfderiv b).symm.trans hz
  have hh := congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => A b.val.val) hg
  rw [two_nsmul] at hh
  change inner ℝ b.val.val b.val.val + inner ℝ b.val.val b.val.val = 0 at hh
  rw [real_inner_self_eq_norm_sq] at hh
  have hp : (1 / 2 : ℝ) < ‖b.val.val‖ ^ 2 := b.property
  linarith

def radialDefiningAmbient (l : Fin 2) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if l = 0 then (3 / 4 : ℝ) - ‖z‖ ^ 2 else ‖z‖ ^ 2 - (7 / 8 : ℝ)

def radialCircleDefining (l : Fin 2) (b : radialCircleBase) : ℝ :=
  radialDefiningAmbient l b.val.val

theorem radialDefiningAmbient_smooth (l : Fin 2) :
    ContDiff ℝ ∞ (radialDefiningAmbient l) := by
  by_cases hl : l = 0
  · have hf : radialDefiningAmbient l =
        (fun z : EuclideanSpace ℝ (Fin 2) => (3 / 4 : ℝ) - ‖z‖ ^ 2) := by
      funext z
      unfold radialDefiningAmbient
      rw [ite_eq_left hl]
    rw [hf]
    exact contDiff_const.sub (contDiff_norm_sq ℝ)
  · have hf : radialDefiningAmbient l =
        (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2 - (7 / 8 : ℝ)) := by
      funext z
      unfold radialDefiningAmbient
      rw [ite_eq_right hl]
    rw [hf]
    exact (contDiff_norm_sq ℝ).sub contDiff_const

theorem radialCircleDefining_smooth (l : Fin 2) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (radialCircleDefining l) :=
  (radialDefiningAmbient_smooth l).contMDiff.comp
    (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem radialCircleDefining_mfderiv (l : Fin 2) (b : radialCircleBase) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (radialCircleDefining l) b =
      if l = 0 then -(2 • innerSL ℝ b.val.val) else 2 • innerSL ℝ b.val.val := by
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (fun y : radialCircleBase => (fun v : loopCircleBase =>
      radialDefiningAmbient l v.val) y.val) b = _
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun v : loopCircleBase => radialDefiningAmbient l v.val) radialCircleBase b]
  rw [DifferentialGeometry.mfderiv_restrict_open
    (radialDefiningAmbient l) loopCircleBase b.val, mfderiv_eq_fderiv]
  change fderiv ℝ (radialDefiningAmbient l) b.val.val = _
  by_cases hl : l = 0
  · have hf : radialDefiningAmbient l =
        (fun z : EuclideanSpace ℝ (Fin 2) => (3 / 4 : ℝ) - ‖z‖ ^ 2) := by
      funext z
      unfold radialDefiningAmbient
      rw [ite_eq_left hl]
    rw [hf, ite_eq_left hl]
    exact ((hasStrictFDerivAt_norm_sq b.val.val).hasFDerivAt.const_sub (3 / 4 : ℝ)).fderiv
  · have hf : radialDefiningAmbient l =
        (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2 - (7 / 8 : ℝ)) := by
      funext z
      unfold radialDefiningAmbient
      rw [ite_eq_right hl]
    rw [hf, ite_eq_right hl]
    exact ((hasStrictFDerivAt_norm_sq b.val.val).hasFDerivAt.sub_const (7 / 8 : ℝ)).fderiv

theorem radialCircleDefining_regular (l : Fin 2) (b : radialCircleBase) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (radialCircleDefining l) b ≠ 0 := by
  rw [radialCircleDefining_mfderiv]
  have hn : (2 : ℕ) • innerSL ℝ b.val.val ≠ 0 := by
    have hh := radialBaseNorm_regular b
    rw [radialBaseNorm_mfderiv] at hh
    exact hh
  split
  · exact neg_ne_zero.mpr hn
  · exact hn

theorem radialCircleDefining_no_double (b : radialCircleBase) {l l' : Fin 2}
    (hn : l ≠ l') (hl : radialCircleDefining l b = 0)
    (hl' : radialCircleDefining l' b = 0) : False := by
  fin_cases l <;> fin_cases l'
  · exact hn rfl
  · change (3 / 4 : ℝ) - ‖b.val.val‖ ^ 2 = 0 at hl
    change ‖b.val.val‖ ^ 2 - (7 / 8 : ℝ) = 0 at hl'
    linarith
  · change ‖b.val.val‖ ^ 2 - (7 / 8 : ℝ) = 0 at hl
    change (3 / 4 : ℝ) - ‖b.val.val‖ ^ 2 = 0 at hl'
    linarith
  · exact hn rfl

def radialCircleCornerBase : Set radialCircleBase :=
  {b | (3 / 4 : ℝ) ≤ radialBaseNorm b ∧ radialBaseNorm b ≤ (7 / 8 : ℝ)}

theorem radialCircleCornerBase_eq : radialCircleCornerBase =
    {b | ∀ l : Fin 2, radialCircleDefining l b ≤ 0} := by
  ext b
  constructor
  · rintro ⟨hlo, hhi⟩ l
    fin_cases l
    · change (3 / 4 : ℝ) - radialBaseNorm b ≤ 0
      linarith
    · change radialBaseNorm b - (7 / 8 : ℝ) ≤ 0
      linarith
  · intro h
    have hlo := h (0 : Fin 2)
    have hhi := h (1 : Fin 2)
    change (3 / 4 : ℝ) - radialBaseNorm b ≤ 0 at hlo
    change radialBaseNorm b - (7 / 8 : ℝ) ≤ 0 at hhi
    exact ⟨by linarith, by linarith⟩

def radialCircleCornerAmbient : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | (3 / 4 : ℝ) ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ (7 / 8 : ℝ)}

theorem radialCircleCornerAmbient_compact : IsCompact radialCircleCornerAmbient := by
  have hc : IsClosed radialCircleCornerAmbient :=
    (isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hhi : ‖z‖ ^ 2 ≤ (7 / 8 : ℝ) := hz.2
  nlinarith [norm_nonneg z]

theorem radialCircleCornerBase_image :
    (fun b : radialCircleBase => b.val.val) '' radialCircleCornerBase =
      radialCircleCornerAmbient := by
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hz
    have hnorm : ‖z‖ < 1 := by nlinarith [hz.2, norm_nonneg z]
    have hpos : (1 / 2 : ℝ) < ‖z‖ ^ 2 := by linarith [hz.1]
    exact ⟨⟨⟨z, hnorm⟩, hpos⟩, hz, rfl⟩

theorem radialCircleCornerBase_compact : IsCompact radialCircleCornerBase := by
  have he : Topology.IsEmbedding (fun b : radialCircleBase => b.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  apply he.isCompact_iff.mpr
  rw [radialCircleCornerBase_image]
  exact radialCircleCornerAmbient_compact

end GC.GraphManifold.Assembly.FC39P0.X135Radial
