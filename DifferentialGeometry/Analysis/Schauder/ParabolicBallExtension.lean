import DifferentialGeometry.Analysis.Schauder.BallCutoff
import DifferentialGeometry.Analysis.Schauder.Localization

noncomputable section

open Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicBallCutoffExtension
    (center : V) (r R : Real)
    (f0 : F) (f : ParabolicPoint V → F) : ParabolicPoint V → F :=
  cutoffExtension (fun p ↦ ballCutoff center r R p.space) f0 f

def parabolicBallCutoffExtensionHolderConst
    (r R : Real) (Kf Mf : NNReal) (f0 : F) : NNReal :=
  Kf + (Mf + ‖f0‖₊) * ballCutoffHolderConst r R

def parabolicBallCutoffExtensionSupConst
    (Mf : NNReal) (f0 : F) : NNReal :=
  ‖f0‖₊ + (Mf + ‖f0‖₊)

omit [InnerProductSpace Real V] [FiniteDimensional Real V] in
theorem parabolicBallCutoffExtension_apply
    (center : V) (r R : Real)
    (f0 : F) (f : ParabolicPoint V → F) (p : ParabolicPoint V) :
    parabolicBallCutoffExtension center r R f0 f p =
      f0 + ballCutoff center r R p.space • (f p - f0) :=
  rfl

omit [InnerProductSpace Real V] [FiniteDimensional Real V] in
theorem parabolicBallCutoffExtension_eq_of_mem_closedBall
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (f0 : F) (f : ParabolicPoint V → F) (p : ParabolicPoint V)
    (hp : p.space ∈ Metric.closedBall center r) :
    parabolicBallCutoffExtension center r R f0 f p = f p := by
  apply cutoffExtension_eq_of_eq_one
  exact ballCutoff_eq_one_of_mem_closedBall hr hrR hp

omit [InnerProductSpace Real V] [FiniteDimensional Real V] in
theorem parabolicBallCutoffExtension_eq_of_not_mem_ball
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (f0 : F) (f : ParabolicPoint V → F) (p : ParabolicPoint V)
    (hp : p.space ∉ Metric.ball center R) :
    parabolicBallCutoffExtension center r R f0 f p = f0 := by
  apply cutoffExtension_eq_of_eq_zero
  exact ballCutoff_eq_zero_of_not_mem_ball hr hrR hp

omit [FiniteDimensional Real V] in
theorem parabolicBallCutoffExtension_holderWith
    {J : Set Real} {alpha Kf Mf : NNReal}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (f0 : F) (f : ParabolicPoint V → F)
    (hf : HolderWith Kf alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict f))
    (hfNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖f p‖ ≤ Mf) :
    HolderWith (parabolicBallCutoffExtensionHolderConst r R Kf Mf f0)
      alpha ((parabolicCylinder J Set.univ).restrict
        (parabolicBallCutoffExtension center r R f0 f)) := by
  let Q := parabolicCylinder J (Set.univ : Set V)
  let U := parabolicCylinder J (Metric.ball center R)
  let chi : ParabolicPoint V → Real := fun p ↦ ballCutoff center r R p.space
  have hspace : LipschitzWith 1 (fun p : ParabolicPoint V ↦ p.space) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one, one_mul]
    rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
      dist_parabolicPoint]
    exact le_max_right _ _
  have hchiGlobal : HolderWith (ballCutoffHolderConst r R) alpha chi := by
    have hcomp := (ballCutoff_holderWith (center := center)
      hr hrR halpha0 halpha1).comp
      hspace.holderWith
    simpa only [chi, NNReal.one_rpow, mul_one, Function.comp_apply] using hcomp
  have hchi : HolderWith (ballCutoffHolderConst r R) alpha
      (Q.restrict chi) := hchiGlobal.holderOnWith Q |>.holderWith
  have hQU : Q ∩ U = U := by
    apply Set.inter_eq_right.mpr
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  have hf' : HolderWith Kf alpha ((Q ∩ U).restrict f) := by
    rw [hQU]
    exact hf
  have hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ (1 : NNReal) := by
    intro p _hpQ _hpU
    change ‖ballCutoff center r R p.space‖ ≤ (1 : NNReal)
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc center r R p.space).1]
    exact_mod_cast (ballCutoff_mem_Icc center r R p.space).2
  have hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0 := by
    intro p hpQ hpU
    apply ballCutoff_eq_zero_of_not_mem_ball hr hrR
    intro hpball
    exact hpU ⟨hpQ.1, hpball⟩
  simpa only [parabolicBallCutoffExtension,
    parabolicBallCutoffExtensionHolderConst, one_mul, Q, U, chi] using
    (cutoffExtension_holderWith chi f0 f hchi hf' hchiNorm
      (fun p _ hp ↦ hfNorm p hp) hchiZero)

omit [InnerProductSpace Real V] [FiniteDimensional Real V] in
theorem norm_parabolicBallCutoffExtension_le
    {J : Set Real} {Mf : NNReal}
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (f0 : F) (f : ParabolicPoint V → F)
    (hfNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖f p‖ ≤ Mf) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖parabolicBallCutoffExtension center r R f0 f p‖ ≤
        parabolicBallCutoffExtensionSupConst Mf f0 := by
  let Q := parabolicCylinder J (Set.univ : Set V)
  let U := parabolicCylinder J (Metric.ball center R)
  let chi : ParabolicPoint V → Real := fun p ↦ ballCutoff center r R p.space
  have hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ (1 : NNReal) := by
    intro p _hpQ _hpU
    change ‖ballCutoff center r R p.space‖ ≤ (1 : NNReal)
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc center r R p.space).1]
    exact_mod_cast (ballCutoff_mem_Icc center r R p.space).2
  have hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0 := by
    intro p hpQ hpU
    apply ballCutoff_eq_zero_of_not_mem_ball hr hrR
    intro hpball
    exact hpU ⟨hpQ.1, hpball⟩
  simpa only [parabolicBallCutoffExtension,
    parabolicBallCutoffExtensionSupConst, one_mul, Q, U, chi,
    NNReal.coe_add, NNReal.coe_one] using
    (norm_cutoffExtension_le chi f0 f hchiNorm
      (fun p _ hp ↦ hfNorm p hp) hchiZero)

end DifferentialGeometry.Analysis.Schauder

end
