import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammData
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Realization of Koch--Lamm cylinder germs

The complete ambients in `KochLammData` store *scaled* local `Lp` classes.
This file constructs those classes from an actual measurable field satisfying
one of the exact Koch--Lamm bounds.  In particular, none of the cylinder
coordinates is postulated: its `MemLp` proof follows from the finite scaled
bound and the strict positivity of the radius scale.

The resulting maps are the first half of the realized-carrier construction.
The remaining half is the closed compatibility condition between overlapping
germs (and, for paths, the weak spatial-derivative identity).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Generic

variable {X I E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {f : X → E} {mu : Measure X} {s : ℝ} {A : ℝ≥0}

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- A finite bound on a strictly positively scaled `eLpNorm` gives local
`MemLp`. -/
theorem klScaleMemLp (hs : 0 < s) (hf : AEStronglyMeasurable f mu)
    (h : ENNReal.ofReal s * eLpNorm f p mu ≤ (A : ℝ≥0∞)) :
    MemLp f p mu := by
  refine ⟨hf, ?_⟩
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hmul : ENNReal.ofReal s * eLpNorm f p mu < ∞ :=
    lt_of_le_of_lt h ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

/-- The real norm of a scaled `Lp` germ is controlled by the same finite
`ENNReal` bound from which it was constructed. -/
theorem klScaleToLpLe (hs : 0 < s) (hm : MemLp f p mu)
    (h : ENNReal.ofReal s * eLpNorm f p mu ≤ (A : ℝ≥0∞)) :
    ‖s • hm.toLp f‖ ≤ (A : ℝ) := by
  have hr := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le,
    ENNReal.coe_toReal, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
    Lp.norm_toLp] using hr

/-- A bounded family of scaled local `Lp` classes, packaged in dependent
`lp ∞`. -/
def klMkGerm (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) :
    lp (fun i : I ↦ Lp E p (mu i)) ∞ :=
  ⟨fun i ↦ s i • (hm i).toLp f,
    memℓp_infty ⟨(A : ℝ), by
      rintro _ ⟨i, rfl⟩
      exact hA i⟩⟩

@[simp]
theorem klMkGerm_apply (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) (i : I) :
    klMkGerm mu s f hm A hA i = s i • (hm i).toLp f :=
  rfl

/-- The `lp ∞` norm of the realized germ family is the advertised uniform
bound. -/
theorem klMkGermNormLe (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) :
    ‖klMkGerm mu s f hm A hA‖ ≤ (A : ℝ) := by
  apply lp.norm_le_of_forall_le A.coe_nonneg
  intro i
  simpa using hA i

end Generic

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
theorem klL2ScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < klL2ScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [MeasurableSpace V] [BorelSpace V] in
theorem klLpScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < klLpScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [MeasurableSpace V] [BorelSpace V] in
theorem klL1ScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < klL1ScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [MeasurableSpace V] [BorelSpace V] in
theorem klLqScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < klLqScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

section SourceZero

variable {T : ℝ} {A₁ A_q : ℝ≥0} {f : ℝ × V → F}
  [Fact (1 ≤ klQ V)]

def src0L1Mem (h : KLSource0 T A₁ A_q f) (i : KLCylIndex V T) :
    MemLp f 1 (klCylMeasure i) := by
  apply klScaleMemLp (s := klL1ScaleR (V := V) i.radius)
    (A := A₁) (klL1ScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [klL1Scale, klCylMeasure] using
      h.local_l1 i.center i.radius i.radius_pos i.time_le

def src0LqMem (h : KLSource0 T A₁ A_q f) (i : KLCylIndex V T) :
    MemLp f (klQ V) (klLateMeasure i) := by
  apply klScaleMemLp (s := klLqScaleR (V := V) i.radius)
    (A := A_q) (klLqScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [klLqScale, klLateMeasure] using
      h.late_lq i.center i.radius i.radius_pos i.time_le

def src0L1Germ (h : KLSource0 T A₁ A_q f) :
    KLL1Data (V := V) T F :=
  klMkGerm (fun i ↦ klCylMeasure i)
    (fun i ↦ klL1ScaleR (V := V) i.radius) f (src0L1Mem h) A₁ fun i ↦ by
      apply klScaleToLpLe (klL1ScaleR_pos i.radius_pos)
      simpa [klL1Scale, klCylMeasure] using
        h.local_l1 i.center i.radius i.radius_pos i.time_le

def src0LqGerm (h : KLSource0 T A₁ A_q f) :
    KLLqData (V := V) T F :=
  klMkGerm (fun i ↦ klLateMeasure i)
    (fun i ↦ klLqScaleR (V := V) i.radius) f (src0LqMem h) A_q fun i ↦ by
      apply klScaleToLpLe (klLqScaleR_pos i.radius_pos)
      simpa [klLqScale, klLateMeasure] using
        h.late_lq i.center i.radius i.radius_pos i.time_le

/-- Realization of an actual ordinary Koch--Lamm source in the complete norm
data ambient. -/
def src0Data (h : KLSource0 T A₁ A_q f) :
    KLSrc0Data (V := V) (F := F) T :=
  ⟨src0L1Germ h, src0LqGerm h⟩

omit [Fact (1 ≤ klQ V)] in
theorem src0L1_norm_le (h : KLSource0 T A₁ A_q f) :
    ‖src0L1Germ h‖ ≤ (A₁ : ℝ) := by
  apply klMkGermNormLe

theorem src0Lq_norm_le (h : KLSource0 T A₁ A_q f) :
    ‖src0LqGerm h‖ ≤ (A_q : ℝ) := by
  apply klMkGermNormLe

end SourceZero

section SourceOne

variable {T : ℝ} {A₂ Aₚ : ℝ≥0} {f : ℝ × V → F}
  [Fact (1 ≤ klP V)]

def src1L2Mem (h : KLSource1 T A₂ Aₚ f) (i : KLCylIndex V T) :
    MemLp f 2 (klCylMeasure i) := by
  apply klScaleMemLp (s := klL2ScaleR (V := V) i.radius)
    (A := A₂) (klL2ScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [klL2Scale, klCylMeasure] using
      h.local_l2 i.center i.radius i.radius_pos i.time_le

def src1LpMem (h : KLSource1 T A₂ Aₚ f) (i : KLCylIndex V T) :
    MemLp f (klP V) (klLateMeasure i) := by
  apply klScaleMemLp (s := klLpScaleR (V := V) i.radius)
    (A := Aₚ) (klLpScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [klLpScale, klLateMeasure] using
      h.late_lp i.center i.radius i.radius_pos i.time_le

def src1L2Germ (h : KLSource1 T A₂ Aₚ f) :
    KLL2Data (V := V) T F :=
  klMkGerm (fun i ↦ klCylMeasure i)
    (fun i ↦ klL2ScaleR (V := V) i.radius) f (src1L2Mem h) A₂ fun i ↦ by
      apply klScaleToLpLe (klL2ScaleR_pos i.radius_pos)
      simpa [klL2Scale, klCylMeasure] using
        h.local_l2 i.center i.radius i.radius_pos i.time_le

def src1LpGerm (h : KLSource1 T A₂ Aₚ f) :
    KLLpData (V := V) T F :=
  klMkGerm (fun i ↦ klLateMeasure i)
    (fun i ↦ klLpScaleR (V := V) i.radius) f (src1LpMem h) Aₚ fun i ↦ by
      apply klScaleToLpLe (klLpScaleR_pos i.radius_pos)
      simpa [klLpScale, klLateMeasure] using
        h.late_lp i.center i.radius i.radius_pos i.time_le

/-- Realization of an actual divergence Koch--Lamm source in the complete norm
data ambient. -/
def src1Data (h : KLSource1 T A₂ Aₚ f) :
    KLSrc1Data (V := V) (F := F) T :=
  ⟨src1L2Germ h, src1LpGerm h⟩

omit [Fact (1 ≤ klP V)] in
theorem src1L2_norm_le (h : KLSource1 T A₂ Aₚ f) :
    ‖src1L2Germ h‖ ≤ (A₂ : ℝ) := by
  apply klMkGermNormLe

theorem src1Lp_norm_le (h : KLSource1 T A₂ Aₚ f) :
    ‖src1LpGerm h‖ ≤ (Aₚ : ℝ) := by
  apply klMkGermNormLe

end SourceOne

section PathGradient

variable {T : ℝ} {A₀ A₂ Aₚ : ℝ≥0}
  {u : ℝ × V → F} {d : ℝ × V → G}
  [Fact (1 ≤ klP V)]

def pathL2Mem (h : KLPath T A₀ A₂ Aₚ u d) (i : KLCylIndex V T) :
    MemLp d 2 (klCylMeasure i) := by
  apply klScaleMemLp (s := klL2ScaleR (V := V) i.radius)
    (A := A₂) (klL2ScaleR_pos i.radius_pos)
  · exact h.grad_ae.mono_measure Measure.restrict_le_self
  · simpa [klL2Scale, klCylMeasure] using
      h.grad_l2 i.center i.radius i.radius_pos i.time_le

def pathLpMem (h : KLPath T A₀ A₂ Aₚ u d) (i : KLCylIndex V T) :
    MemLp d (klP V) (klLateMeasure i) := by
  apply klScaleMemLp (s := klLpScaleR (V := V) i.radius)
    (A := Aₚ) (klLpScaleR_pos i.radius_pos)
  · exact h.grad_ae.mono_measure Measure.restrict_le_self
  · simpa [klLpScale, klLateMeasure] using
      h.grad_lp i.center i.radius i.radius_pos i.time_le

def pathL2Germ (h : KLPath T A₀ A₂ Aₚ u d) :
    KLL2Data (V := V) T G :=
  klMkGerm (fun i ↦ klCylMeasure i)
    (fun i ↦ klL2ScaleR (V := V) i.radius) d (pathL2Mem h) A₂ fun i ↦ by
      apply klScaleToLpLe (klL2ScaleR_pos i.radius_pos)
      simpa [klL2Scale, klCylMeasure] using
        h.grad_l2 i.center i.radius i.radius_pos i.time_le

def pathLpGerm (h : KLPath T A₀ A₂ Aₚ u d) :
    KLLpData (V := V) T G :=
  klMkGerm (fun i ↦ klLateMeasure i)
    (fun i ↦ klLpScaleR (V := V) i.radius) d (pathLpMem h) Aₚ fun i ↦ by
      apply klScaleToLpLe (klLpScaleR_pos i.radius_pos)
      simpa [klLpScale, klLateMeasure] using
        h.grad_lp i.center i.radius i.radius_pos i.time_le

/-- The two realized gradient arms of a Koch--Lamm path.  The bounded
continuous value arm is supplied separately because `KLPath` deliberately
contains only its quantitative bound, not continuity. -/
def pathGradData (h : KLPath T A₀ A₂ Aₚ u d) :
    KLL2Data (V := V) T G × KLLpData (V := V) T G :=
  ⟨pathL2Germ h, pathLpGerm h⟩

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ klP V)] in
theorem pathL2_norm_le (h : KLPath T A₀ A₂ Aₚ u d) :
    ‖pathL2Germ h‖ ≤ (A₂ : ℝ) := by
  apply klMkGermNormLe

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem pathLp_norm_le (h : KLPath T A₀ A₂ Aₚ u d) :
    ‖pathLpGerm h‖ ≤ (Aₚ : ℝ) := by
  apply klMkGermNormLe

end PathGradient

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
