import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic

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
theorem kochLammScaleMemLp (hs : 0 < s) (hf : AEStronglyMeasurable f mu)
    (h : ENNReal.ofReal s * eLpNorm f p mu ≤ (A : ℝ≥0∞)) :
    MemLp f p mu := by
  refine ⟨hf, ?_⟩
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hmul : ENNReal.ofReal s * eLpNorm f p mu < ∞ :=
    lt_of_le_of_lt h ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

theorem kochLammScaleToLpLe (hs : 0 < s) (hm : MemLp f p mu)
    (h : ENNReal.ofReal s * eLpNorm f p mu ≤ (A : ℝ≥0∞)) :
    ‖s • hm.toLp f‖ ≤ (A : ℝ) := by
  have hr := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le,
    ENNReal.coe_toReal, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
    Lp.norm_toLp] using hr

def kochLammMkGerm (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) :
    lp (fun i : I ↦ Lp E p (mu i)) ∞ :=
  ⟨fun i ↦ s i • (hm i).toLp f,
    memℓp_infty ⟨(A : ℝ), by
      rintro _ ⟨i, rfl⟩
      exact hA i⟩⟩

@[simp]
theorem kochLammMkGerm_apply (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) (i : I) :
    kochLammMkGerm mu s f hm A hA i = s i • (hm i).toLp f :=
  rfl

theorem kochLammMkGermNormLe (mu : I → Measure X) (s : I → ℝ) (f : X → E)
    (hm : ∀ i, MemLp f p (mu i)) (A : ℝ≥0)
    (hA : ∀ i, ‖s i • (hm i).toLp f‖ ≤ (A : ℝ)) :
    ‖kochLammMkGerm mu s f hm A hA‖ ≤ (A : ℝ) := by
  apply lp.norm_le_of_forall_le A.coe_nonneg
  intro i
  simpa using hA i

end Generic

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kochLammL2ScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < kochLammL2ScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kochLammLpScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < kochLammLpScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kochLammL1ScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < kochLammL1ScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kochLammLqScaleR_pos {R : ℝ} (hR : 0 < R) :
    0 < kochLammLqScaleR (V := V) R :=
  Real.rpow_pos_of_pos hR _

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

section SourceZero

variable {T : ℝ} {A₁ A_q : ℝ≥0} {f : ℝ × V → F}
  [Fact (1 ≤ kochLammQ V)]

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ kochLammQ V)] in
lemma sourceZeroL1Mem (h : KochLammSourceZero T A₁ A_q f) (i : KochLammCylinderIndex V T) :
    MemLp f 1 (kochLammCylinderMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammL1ScaleR (V := V) i.radius)
    (A := A₁) (kochLammL1ScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammL1Scale, kochLammCylinderMeasure] using
      h.local_l1 i.center i.radius i.radius_pos i.time_le

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ kochLammQ V)] in
lemma sourceZeroLqMem (h : KochLammSourceZero T A₁ A_q f) (i : KochLammCylinderIndex V T) :
    MemLp f (kochLammQ V) (kochLammLateMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammLqScaleR (V := V) i.radius)
    (A := A_q) (kochLammLqScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammLqScale, kochLammLateMeasure] using
      h.late_lq i.center i.radius i.radius_pos i.time_le

def kochLammSourceZeroL1Family (h : KochLammSourceZero T A₁ A_q f) :
    KochLammL1Family (V := V) T F :=
  kochLammMkGerm (fun i ↦ kochLammCylinderMeasure i)
    (fun i ↦ kochLammL1ScaleR (V := V) i.radius) f (sourceZeroL1Mem h) A₁ fun i ↦ by
      apply kochLammScaleToLpLe (kochLammL1ScaleR_pos i.radius_pos)
      simpa [kochLammL1Scale, kochLammCylinderMeasure] using
        h.local_l1 i.center i.radius i.radius_pos i.time_le

def kochLammSourceZeroLqFamily (h : KochLammSourceZero T A₁ A_q f) :
    KochLammLqFamily (V := V) T F :=
  kochLammMkGerm (fun i ↦ kochLammLateMeasure i)
    (fun i ↦ kochLammLqScaleR (V := V) i.radius) f (sourceZeroLqMem h) A_q fun i ↦ by
      apply kochLammScaleToLpLe (kochLammLqScaleR_pos i.radius_pos)
      simpa [kochLammLqScale, kochLammLateMeasure] using
        h.late_lq i.center i.radius i.radius_pos i.time_le

def kochLammSourceZeroProductOfBounds (h : KochLammSourceZero T A₁ A_q f) :
    KochLammSourceZeroProduct (V := V) (F := F) T :=
  ⟨kochLammSourceZeroL1Family h, kochLammSourceZeroLqFamily h⟩

omit [CompleteSpace F] [Fact (1 ≤ kochLammQ V)] in
theorem kochLammSourceZeroL1Family_norm_le (h : KochLammSourceZero T A₁ A_q f) :
    ‖kochLammSourceZeroL1Family h‖ ≤ (A₁ : ℝ) := by
  apply kochLammMkGermNormLe

omit [CompleteSpace F] in
theorem kochLammSourceZeroLqFamily_norm_le (h : KochLammSourceZero T A₁ A_q f) :
    ‖kochLammSourceZeroLqFamily h‖ ≤ (A_q : ℝ) := by
  apply kochLammMkGermNormLe

end SourceZero

section SourceOne

variable {T : ℝ} {A₂ Aₚ : ℝ≥0} {f : ℝ × V → F}
  [Fact (1 ≤ kochLammP V)]

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ kochLammP V)] in
lemma sourceOneL2Mem (h : KochLammSourceOne T A₂ Aₚ f) (i : KochLammCylinderIndex V T) :
    MemLp f 2 (kochLammCylinderMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammL2ScaleR (V := V) i.radius)
    (A := A₂) (kochLammL2ScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammL2Scale, kochLammCylinderMeasure] using
      h.local_l2 i.center i.radius i.radius_pos i.time_le

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ kochLammP V)] in
lemma sourceOneLpMem (h : KochLammSourceOne T A₂ Aₚ f) (i : KochLammCylinderIndex V T) :
    MemLp f (kochLammP V) (kochLammLateMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammLpScaleR (V := V) i.radius)
    (A := Aₚ) (kochLammLpScaleR_pos i.radius_pos)
  · exact h.ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammLpScale, kochLammLateMeasure] using
      h.late_lp i.center i.radius i.radius_pos i.time_le

def kochLammSourceOneL2Family (h : KochLammSourceOne T A₂ Aₚ f) :
    KochLammL2Family (V := V) T F :=
  kochLammMkGerm (fun i ↦ kochLammCylinderMeasure i)
    (fun i ↦ kochLammL2ScaleR (V := V) i.radius) f (sourceOneL2Mem h) A₂ fun i ↦ by
      apply kochLammScaleToLpLe (kochLammL2ScaleR_pos i.radius_pos)
      simpa [kochLammL2Scale, kochLammCylinderMeasure] using
        h.local_l2 i.center i.radius i.radius_pos i.time_le

def kochLammSourceOneLpFamily (h : KochLammSourceOne T A₂ Aₚ f) :
    KochLammLpFamily (V := V) T F :=
  kochLammMkGerm (fun i ↦ kochLammLateMeasure i)
    (fun i ↦ kochLammLpScaleR (V := V) i.radius) f (sourceOneLpMem h) Aₚ fun i ↦ by
      apply kochLammScaleToLpLe (kochLammLpScaleR_pos i.radius_pos)
      simpa [kochLammLpScale, kochLammLateMeasure] using
        h.late_lp i.center i.radius i.radius_pos i.time_le

def kochLammSourceOneProductOfBounds (h : KochLammSourceOne T A₂ Aₚ f) :
    KochLammSourceOneProduct (V := V) (F := F) T :=
  ⟨kochLammSourceOneL2Family h, kochLammSourceOneLpFamily h⟩

omit [CompleteSpace F] [Fact (1 ≤ kochLammP V)] in
theorem kochLammSourceOneL2Family_norm_le (h : KochLammSourceOne T A₂ Aₚ f) :
    ‖kochLammSourceOneL2Family h‖ ≤ (A₂ : ℝ) := by
  apply kochLammMkGermNormLe

omit [CompleteSpace F] in
theorem kochLammSourceOneLpFamily_norm_le (h : KochLammSourceOne T A₂ Aₚ f) :
    ‖kochLammSourceOneLpFamily h‖ ≤ (Aₚ : ℝ) := by
  apply kochLammMkGermNormLe

end SourceOne

section PathGradient

variable {T : ℝ} {A₀ A₂ Aₚ : ℝ≥0}
  {u : ℝ × V → F} {d : ℝ × V → G}
  [Fact (1 ≤ kochLammP V)]

omit [NormedSpace ℝ F] [CompleteSpace F] [NormedSpace ℝ G] [CompleteSpace G]
    [Fact (1 ≤ kochLammP V)] in
lemma pathL2Mem (h : KochLammPath T A₀ A₂ Aₚ u d) (i : KochLammCylinderIndex V T) :
    MemLp d 2 (kochLammCylinderMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammL2ScaleR (V := V) i.radius)
    (A := A₂) (kochLammL2ScaleR_pos i.radius_pos)
  · exact h.grad_ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammL2Scale, kochLammCylinderMeasure] using
      h.grad_l2 i.center i.radius i.radius_pos i.time_le

omit [NormedSpace ℝ F] [CompleteSpace F] [NormedSpace ℝ G] [CompleteSpace G]
    [Fact (1 ≤ kochLammP V)] in
lemma pathLpMem (h : KochLammPath T A₀ A₂ Aₚ u d) (i : KochLammCylinderIndex V T) :
    MemLp d (kochLammP V) (kochLammLateMeasure i) := by
  apply kochLammScaleMemLp (s := kochLammLpScaleR (V := V) i.radius)
    (A := Aₚ) (kochLammLpScaleR_pos i.radius_pos)
  · exact h.grad_ae.mono_measure Measure.restrict_le_self
  · simpa [kochLammLpScale, kochLammLateMeasure] using
      h.grad_lp i.center i.radius i.radius_pos i.time_le

def kochLammPathL2Family (h : KochLammPath T A₀ A₂ Aₚ u d) :
    KochLammL2Family (V := V) T G :=
  kochLammMkGerm (fun i ↦ kochLammCylinderMeasure i)
    (fun i ↦ kochLammL2ScaleR (V := V) i.radius) d (pathL2Mem h) A₂ fun i ↦ by
      apply kochLammScaleToLpLe (kochLammL2ScaleR_pos i.radius_pos)
      simpa [kochLammL2Scale, kochLammCylinderMeasure] using
        h.grad_l2 i.center i.radius i.radius_pos i.time_le

def kochLammPathLpFamily (h : KochLammPath T A₀ A₂ Aₚ u d) :
    KochLammLpFamily (V := V) T G :=
  kochLammMkGerm (fun i ↦ kochLammLateMeasure i)
    (fun i ↦ kochLammLpScaleR (V := V) i.radius) d (pathLpMem h) Aₚ fun i ↦ by
      apply kochLammScaleToLpLe (kochLammLpScaleR_pos i.radius_pos)
      simpa [kochLammLpScale, kochLammLateMeasure] using
        h.grad_lp i.center i.radius i.radius_pos i.time_le

def kochLammPathGradientProduct (h : KochLammPath T A₀ A₂ Aₚ u d) :
    KochLammL2Family (V := V) T G × KochLammLpFamily (V := V) T G :=
  ⟨kochLammPathL2Family h, kochLammPathLpFamily h⟩

omit [NormedSpace ℝ F] [CompleteSpace F] [CompleteSpace G] [Fact (1 ≤ kochLammP V)] in
theorem kochLammPathL2Family_norm_le (h : KochLammPath T A₀ A₂ Aₚ u d) :
    ‖kochLammPathL2Family h‖ ≤ (A₂ : ℝ) := by
  apply kochLammMkGermNormLe

omit [NormedSpace ℝ F] [CompleteSpace F] [CompleteSpace G] in
theorem kochLammPathLpFamily_norm_le (h : KochLammPath T A₀ A₂ Aₚ u d) :
    ‖kochLammPathLpFamily h‖ ≤ (Aₚ : ℝ) := by
  apply kochLammMkGermNormLe

end PathGradient

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
