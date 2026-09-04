import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

theorem timeOp_inner_comm
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (u v : timeL2 X T) :
    inner ℝ (timeOp A hA C hC u) v =
      inner ℝ u (timeOp A hA C hC v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeOp_apply_ae A hA C hC u,
    timeOp_apply_ae A hA C hC v, hself] with t hu hv ht
  rw [hu, hv]
  exact ht.isSymmetric (u t) (v t)

theorem timeQuad_line
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (u v : timeL2 X T) :
    HasDerivAt (fun c : ℝ ↦ timeQuad A hA C hC (u + c • v))
      (2 * inner ℝ (timeOp A hA C hC u) v) 0 := by
  let L : timeL2 X T →L[ℝ] timeL2 X T := timeOp A hA C hC
  have huv : HasDerivAt (fun c : ℝ ↦ u + c • v) v 0 := by
    simpa only [id_eq, one_smul, zero_smul, add_zero] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hLuv : HasDerivAt (fun c : ℝ ↦ L (u + c • v)) (L v) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 huv
  have hinner := hLuv.inner ℝ huv
  have hsymm : inner ℝ (L v) u = inner ℝ (L u) v := by
    calc
      inner ℝ (L v) u = inner ℝ u (L v) := (real_inner_comm (L v) u).symm
      _ = inner ℝ (L u) v := by
        simpa only [L] using (timeOp_inner_comm A hA C hC hself u v).symm
  simpa only [timeQuad, L, zero_smul, add_zero, hsymm, two_mul] using hinner

def sameTimeEnds (u : timeH1 X T) : Set (timeH1 X T) :=
  {v | v.init = u.init ∧ v.toFun T = u.toFun T}

def timeQuadPot
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (P : timeH1 X T → ℝ) (u : timeH1 X T) : ℝ :=
  timeQuad A hA C hC u.deriv + P u

theorem timeQuad_weak_euler
    (hT : 0 ≤ T)
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (P : timeH1 X T → ℝ) (u : timeH1 X T) (F : timeL2 X T)
    (hP : HasFDerivAt P
      ((innerSL ℝ F).comp (timeH1.toTimeL2 X T)) u)
    (hmin : IsLocalMinOn (timeQuadPot A hA C hC P) (sameTimeEnds u) u)
    (v : timeH1 X T) (hv0 : v.init = 0) (hvT : v.toFun T = 0) :
    2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
      inner ℝ F v.toFunL2 = 0 := by
  let line : ℝ → timeH1 X T := fun c ↦ u + c • v
  have hline0 : line 0 = u := by simp only [line, zero_smul, add_zero]
  have hline : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul, zero_smul, add_zero] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hmaps : univ ⊆ line ⁻¹' sameTimeEnds u := by
    intro c _
    constructor
    · simp only [line, timeH1.init_add, timeH1.init_smul, hv0, smul_zero, add_zero]
    · change (u + c • v).toFun T = u.toFun T
      rw [timeH1.toFun_add u (c • v) ⟨hT, le_rfl⟩,
        timeH1.toFun_smul c v ⟨hT, le_rfl⟩, hvT, smul_zero, add_zero]
  have hline_cont : Continuous line := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hscalar : IsLocalMin (timeQuadPot A hA C hC P ∘ line) 0 := by
    rw [← isLocalMinOn_univ_iff]
    have hmin' : IsLocalMinOn (timeQuadPot A hA C hC P) (sameTimeEnds u) (line 0) := by
      simpa only [hline0] using hmin
    exact hmin'.comp_continuousOn hmaps hline_cont.continuousOn (mem_univ (0 : ℝ))
  have hkin : HasDerivAt
      (fun c : ℝ ↦ timeQuad A hA C hC ((line c).deriv))
      (2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv) 0 := by
    simpa only [line, timeH1.deriv_add, timeH1.deriv_smul] using
      timeQuad_line A hA C hC hself u.deriv v.deriv
  have hpot : HasDerivAt (fun c : ℝ ↦ P (line c)) (inner ℝ F v.toFunL2) 0 := by
    have hP' : HasFDerivAt P
        ((innerSL ℝ F).comp (timeH1.toTimeL2 X T)) (line 0) := by
      simpa only [hline0] using hP
    change HasDerivAt (P ∘ line) (inner ℝ F v.toFunL2) 0
    simpa only [ContinuousLinearMap.comp_apply, timeH1.toTimeL2_apply,
      innerSL_apply_apply] using hP'.comp_hasDerivAt 0 hline
  have henergy : HasDerivAt (timeQuadPot A hA C hC P ∘ line)
      (2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        inner ℝ F v.toFunL2) 0 := by
    rw [show (timeQuadPot A hA C hC P ∘ line) =
      (fun c : ℝ ↦ timeQuad A hA C hC ((line c).deriv)) +
        fun c : ℝ ↦ P (line c) by rfl]
    exact hkin.add hpot
  have hzero := hscalar.deriv_eq_zero
  rw [henergy.deriv] at hzero
  exact hzero

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
