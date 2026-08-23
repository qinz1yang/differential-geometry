import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Cross

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem timeIncl_trans
    {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s σ) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hρτ.trans hτσ) f =
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hρτ
        (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hτσ f) := by
  refine timeModeCoeff_injective (I := I) (M := M) hcompact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    timeModeCoeff_timeL2Inclusion (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem homMode_zero (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  have hsq := norm_homModeCoeff_sq_le (I := I) (M := M)
    (a := a) (T := T) hT.le
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i
  rw [tensorHs.zero_coeff] at hsq
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg
    (homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i)]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem ha1_down
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 1 by linarith)
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
          a hT 0 f) =
      maxRegDuhamelSolField (I := I) (M := M)
        (a - 1) hT 0
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) := by
  refine timeModeCoeff_injective (I := I) (M := M) hcompact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    maxRegDuhamelSolFieldHa1, maxRegDuhamelSolField,
    timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_add (I := I) (M := M),
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le,
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M)
      (a := a - 1) (T := T) hT.le,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT hT1,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a - 1) hT.le,
    homMode_zero (I := I) (M := M) (a := a) hT i,
    homMode_zero (I := I) (M := M) (a := a - 1) hT i,
    zero_add]
  unfold solModeCoeff
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M)]
  simp only [zero_add]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem duhamel_down
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 f) =
      maxRegDuhamelSolField (I := I) (M := M)
        (a - 1) hT 0
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) := by
  let hmid : a + 1 ≤ a + 2 := by linarith
  let heq : (a - 1) + 2 ≤ a + 1 := by linarith
  have htrans := timeIncl_trans (I := I) (M := M) heq hmid hcompact
    (maxRegDuhamelSolField (I := I) (M := M)
      a hT (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f)
  have hduh := duhamel_incl (I := I) (M := M)
    hT hT1 hcompact
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f
  calc
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 f) =
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        heq
        (timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hmid
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 f)) := by simpa only using htrans
    _ = timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) heq
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
            a hT 0 f) := congrArg _ hduh
    _ = maxRegDuhamelSolField (I := I) (M := M)
        (a - 1) hT 0
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) :=
      ha1_down (I := I) (M := M) hT hT1 hcompact f

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem duhamel_mid_down
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a - 1) + 1 ≤ a + 1 by linarith)
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
          a hT 0 f) =
      maxRegDuhamelSolFieldHa1 (I := I) (M := M)
        (a - 1) hT 0
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) := by
  refine timeModeCoeff_injective (I := I) (M := M) hcompact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    maxRegDuhamelSolFieldHa1, maxRegDuhamelSolFieldHa1,
    timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_add (I := I) (M := M),
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le,
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M)
      (a := a - 1) (T := T) hT.le,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT hT1,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a - 1) hT hT1,
    homMode_zero (I := I) (M := M) (a := a) hT i,
    homMode_zero (I := I) (M := M) (a := a - 1) hT i,
    zero_add]
  unfold solModeCoeff
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M)]
  simp only [zero_add]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem zeroRepr_down_ae
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (fun t =>
      tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 1 ≤ a + 1 by linarith)
        ((zeroDuhamelCross (I := I) (M := M)
          hT hcompact f).repr t)) =ᵐ[timeMeasure T]
      fun t =>
        (zeroDuhamelCross (I := I) (M := M)
          (a := a - 1) hT hcompact
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f)).repr t := by
  let hmid : (a - 1) + 1 ≤ a + 1 := by linarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s) hmid
  let fLo := timeL2Inclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show a - 1 ≤ a by linarith) f
  let uHi := maxRegDuhamelSolFieldHa1 (I := I) (M := M)
    a hT (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f
  let uLo := maxRegDuhamelSolFieldHa1 (I := I) (M := M)
    (a - 1) hT
      (0 : tensorHs (I := I) (M := M) g r s ((a - 1) + 2)) fLo
  have hcoe :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hmid uHi =ᵐ[timeMeasure T]
        fun t => J (uHi t) :=
    J.coeFn_compLpL (p := 2) (μ := timeMeasure T) uHi
  have hfield :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hmid uHi = uLo := by
    simpa only [hmid, uHi, uLo, fLo] using
      duhamel_mid_down (I := I) (M := M) hT hT1 hcompact f
  have hpoint : (fun t => J (uHi t)) =ᵐ[timeMeasure T] fun t => uLo t := by
    refine hcoe.symm.trans ?_
    rw [hfield]
  have hhi := zeroRepr_ae (I := I) (M := M)
    hT hT1 hcompact f
  have hlo := zeroRepr_ae (I := I) (M := M)
    (a := a - 1) hT hT1 hcompact fLo
  filter_upwards [hhi, hpoint, hlo] with t hhit hpointt hlot
  change J ((zeroDuhamelCross (I := I) (M := M)
    hT hcompact f).repr t) =
      (zeroDuhamelCross (I := I) (M := M)
        (a := a - 1) hT hcompact fLo).repr t
  rw [hhit, hlot]
  exact hpointt

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem timeOp_down
    (AHi : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hAHi : AEStronglyMeasurable AHi (timeMeasure T))
    (CHi : NNReal) (hCHi : ∀ᵐ t ∂timeMeasure T, ‖AHi t‖ ≤ (CHi : ℝ))
    (ALo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hALo : AEStronglyMeasurable ALo (timeMeasure T))
    (CLo : NNReal) (hCLo : ∀ᵐ t ∂timeMeasure T, ‖ALo t‖ ≤ (CLo : ℝ))
    (hcompat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (AHi t) =
        (ALo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 2 ≤ a + 2 by linarith)))
    (u : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith)
        (timeOp AHi hAHi CHi hCHi u) =
      timeOp ALo hALo CLo hCLo
        (timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show (a - 1) + 2 ≤ a + 2 by linarith) u) := by
  let Jout := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show a - 1 ≤ a by linarith)
  let Jin := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show (a - 1) + 2 ≤ a + 2 by linarith)
  have hout :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)
          (timeOp AHi hAHi CHi hCHi u) =ᵐ[timeMeasure T]
        fun t => Jout (timeOp AHi hAHi CHi hCHi u t) :=
    Jout.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (timeOp AHi hAHi CHi hCHi u)
  have hin :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show (a - 1) + 2 ≤ a + 2 by linarith) u =ᵐ[timeMeasure T]
        fun t => Jin (u t) :=
    Jin.coeFn_compLpL (p := 2) (μ := timeMeasure T) u
  apply Lp.ext
  filter_upwards [hout, hin,
    timeOp_apply_ae AHi hAHi CHi hCHi u,
    timeOp_apply_ae ALo hALo CLo hCLo
      (timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith) u),
    hcompat] with t houtt hint hhit hlot hct
  rw [houtt, hhit, hlot, hint]
  have happ := congrArg (fun L => L (u t)) hct
  simpa only [Jout, Jin, ContinuousLinearMap.comp_apply] using happ

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem a1L2_down
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (AHi : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hAHi : MemLp AHi 2 (timeMeasure T))
    (ALo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hALo : MemLp ALo 2 (timeMeasure T))
    (hcompat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (AHi t) =
        (ALo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 1 ≤ a + 1 by linarith)))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith)
        (a1L2Term (I := I) (M := M)
          hT hT1 hcompact AHi hAHi f) =
      a1L2Term (I := I) (M := M)
        (a := a - 1) hT hT1 hcompact ALo hALo
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) := by
  let Jout := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show a - 1 ≤ a by linarith)
  let Jin := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show (a - 1) + 1 ≤ a + 1 by linarith)
  let fLo := timeL2Inclusion (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (show a - 1 ≤ a by linarith) f
  have hout :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)
          (a1L2Term (I := I) (M := M)
            hT hT1 hcompact AHi hAHi f) =ᵐ[timeMeasure T]
        fun t => Jout
          (a1L2Term (I := I) (M := M)
            hT hT1 hcompact AHi hAHi f t) :=
    Jout.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (a1L2Term (I := I) (M := M)
        hT hT1 hcompact AHi hAHi f)
  have hhi :
      a1L2Term (I := I) (M := M)
          hT hT1 hcompact AHi hAHi f =ᵐ[timeMeasure T]
        fun t => AHi t
          ((zeroDuhamelCross (I := I) (M := M)
            hT hcompact f).repr t) := by
    simpa only [a1L2Term] using
      timeOpL2_apply_ae AHi hAHi
        (fun t => (zeroDuhamelCross (I := I) (M := M)
          hT hcompact f).repr t)
        (zeroRepr_meas (I := I) (M := M)
          hT hT1 hcompact f)
        (zeroReprNN (I := I) (M := M) hT f)
        (zeroRepr_ae_le (I := I) (M := M)
          hT hcompact f)
  have hlo :
      a1L2Term (I := I) (M := M)
          (a := a - 1) hT hT1 hcompact ALo hALo fLo =ᵐ[timeMeasure T]
        fun t => ALo t
          ((zeroDuhamelCross (I := I) (M := M)
            (a := a - 1) hT hcompact fLo).repr t) := by
    simpa only [a1L2Term] using
      timeOpL2_apply_ae ALo hALo
        (fun t => (zeroDuhamelCross (I := I) (M := M)
          (a := a - 1) hT hcompact fLo).repr t)
        (zeroRepr_meas (I := I) (M := M)
          (a := a - 1) hT hT1 hcompact fLo)
        (zeroReprNN (I := I) (M := M) (a := a - 1) hT fLo)
        (zeroRepr_ae_le (I := I) (M := M)
          (a := a - 1) hT hcompact fLo)
  have hrepr := zeroRepr_down_ae (I := I) (M := M)
    hT hT1 hcompact f
  apply Lp.ext
  filter_upwards [hout, hhi, hlo, hrepr, hcompat] with
      t houtt hhit hlot hrept hct
  rw [houtt, hhit, hlot]
  have happ := congrArg
    (fun L => L ((zeroDuhamelCross (I := I) (M := M)
      hT hcompact f).repr t)) hct
  have happ' :
      Jout (AHi t
        ((zeroDuhamelCross (I := I) (M := M)
          hT hcompact f).repr t)) =
        ALo t (Jin
          ((zeroDuhamelCross (I := I) (M := M)
            hT hcompact f).repr t)) := by
    simpa only [Jout, Jin, ContinuousLinearMap.comp_apply] using happ
  have hrept' :
      Jin ((zeroDuhamelCross (I := I) (M := M)
          hT hcompact f).repr t) =
        (zeroDuhamelCross (I := I) (M := M)
          (a := a - 1) hT hcompact fLo).repr t := by
    simpa only [Jin, fLo] using hrept
  change Jout (AHi t
      ((zeroDuhamelCross (I := I) (M := M)
        hT hcompact f).repr t)) =
    ALo t ((zeroDuhamelCross (I := I) (M := M)
      (a := a - 1) hT hcompact fLo).repr t)
  rw [happ', hrept']

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem nonautL2_down
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2Hi : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2Hi : AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    (A2Lo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hA2Lo : AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 2 ≤ a + 2 by linarith)))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 1 ≤ a + 1 by linarith)))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith)
        (nonautL2Map (I := I) (M := M)
          hT hT1 hcompact A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f) =
      nonautL2Map (I := I) (M := M)
        (a := a - 1) hT hT1 hcompact
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo
          (timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) f) := by
  unfold nonautL2Map
  rw [map_add]
  have htop := timeOp_down (I := I) (M := M)
    A2Hi hA2Hi C2Hi hC2Hi A2Lo hA2Lo C2Lo hC2Lo hA2compat
    (maxRegDuhamelSolField (I := I) (M := M)
      a hT (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f)
  rw [htop, duhamel_down (I := I) (M := M) hT hT1 hcompact f,
    a1L2_down (I := I) (M := M)
      hT hT1 hcompact A1Hi hA1Hi A1Lo hA1Lo hA1compat f]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem affine_unique
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2 : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hsmall :
      (C2 : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1)
    {f q : timeL2 (tensorHs (I := I) (M := M) g r s a) T}
    (hf : f =
      nonautL2Map (I := I) (M := M)
        hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 f + f0)
    (hq : q =
      nonautL2Map (I := I) (M := M)
        hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 q + f0) :
    f = q := by
  let K : NNReal :=
    ⟨(C2 : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖,
      add_nonneg
        (mul_nonneg C2.coe_nonneg (by linarith [hT.le]))
        (by positivity)⟩
  let F : timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
    fun z =>
      nonautL2Map (I := I) (M := M)
        hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 z + f0
  have hbase := nonautL2_contract (I := I) (M := M)
    hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 hsmall
  have hcontr : ContractingWith K F := by
    refine ⟨hbase.1, ?_⟩
    refine LipschitzWith.of_dist_le_mul (fun z z' => ?_)
    change dist
      (nonautL2Map (I := I) (M := M)
          hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 z + f0)
      (nonautL2Map (I := I) (M := M)
          hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 z' + f0) ≤
        (K : ℝ) * dist z z'
    rw [dist_add_right]
    exact hbase.2.dist_le_mul z z'
  have hfixf : Function.IsFixedPt F f := by
    change nonautL2Map (I := I) (M := M)
        hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 f + f0 = f
    exact hf.symm
  have hfixq : Function.IsFixedPt F q := by
    change nonautL2Map (I := I) (M := M)
        hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 q + f0 = q
    exact hq.symm
  exact hcontr.fixedPoint_unique' hfixf hfixq

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem nonautL2_lift
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2Hi : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2Hi : AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    (f0Hi : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hsmallHi :
      (C2Hi : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
    (A2Lo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hA2Lo : AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → tensorHs (I := I) (M := M) g r s ((a - 1) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s (a - 1))
    (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    (f0Lo : timeL2 (tensorHs (I := I) (M := M) g r s (a - 1)) T)
    (hsmallLo :
      (C2Lo : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1)
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 2 ≤ a + 2 by linarith)))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith)).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 1 ≤ a + 1 by linarith)))
    (hf0compat :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith) f0Hi = f0Lo)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g r s (a - 1)) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M)
        (a := a - 1) hT hT1 hcompact
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo) :
    ∃ (uHi : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := r) (s := s) a T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      uHi = maxRegDuhamelMap (I := I) (M := M)
          a hT 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M)
              hT hT1 hcompact
                A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        TimeSobolev.timeH1.trace0 _ T uHi =
          (0 : tensorHs (I := I) (M := M) g r s a) ∧
        TimeSobolev.timeH1.timeDeriv _ T uHi =
          timeScaleLaplacian (I := I) (M := M) a
              (maxRegDuhamelSolField (I := I) (M := M)
                a hT 0 fHi) +
            (timeOp A2Hi hA2Hi C2Hi hC2Hi
                (maxRegDuhamelSolField (I := I) (M := M)
                  a hT 0 fHi) +
              a1L2Term (I := I) (M := M)
                hT hT1 hcompact A1Hi hA1Hi fHi +
              f0Hi) ∧
        timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) fHi = fLo ∧
        timeL2Inclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show (a - 1) + 2 ≤ a + 2 by linarith)
            (maxRegDuhamelSolField (I := I) (M := M)
              a hT 0 fHi) =
          maxRegDuhamelSolField (I := I) (M := M)
            (a - 1) hT 0 fLo := by
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv⟩ :=
    nonautL2_forced (I := I) (M := M)
      hT hT1 hcompact A2Hi hA2Hi C2Hi hC2Hi
        A1Hi hA1Hi f0Hi hsmallHi
  have hmap := nonautL2_down (I := I) (M := M)
    hT hT1 hcompact
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo
      hA2compat hA1compat fHi
  have hdownFix :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith) fHi =
        nonautL2Map (I := I) (M := M)
            (a := a - 1) hT hT1 hcompact
              A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo
              (timeL2Inclusion (I := I) (M := M)
                (g := g) (r := r) (s := s)
                (show a - 1 ≤ a by linarith) fHi) +
          f0Lo := by
    let J : timeL2 (tensorHs (I := I) (M := M) g r s a) T →L[ℝ]
        timeL2 (tensorHs (I := I) (M := M) g r s (a - 1)) T :=
      timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith)
    calc
      J fHi =
          J (nonautL2Map (I := I) (M := M)
              hT hT1 hcompact
                A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi) :=
        congrArg J hfHi
      _ = J (nonautL2Map (I := I) (M := M)
              hT hT1 hcompact
                A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi) +
            J f0Hi := map_add J _ _
      _ = nonautL2Map (I := I) (M := M)
              (a := a - 1) hT hT1 hcompact
                A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo (J fHi) +
            f0Lo := by
        rw [show J (nonautL2Map (I := I) (M := M)
            hT hT1 hcompact
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi) =
          nonautL2Map (I := I) (M := M)
            (a := a - 1) hT hT1 hcompact
              A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo (J fHi) by
            simpa only [J] using hmap,
          show J f0Hi = f0Lo by simpa only [J] using hf0compat]
  have hforce :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show a - 1 ≤ a by linarith) fHi = fLo :=
    affine_unique (I := I) (M := M)
      (a := a - 1) hT hT1 hcompact
        A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo
        f0Lo hsmallLo hdownFix hfLo
  have hfield0 := duhamel_down (I := I) (M := M)
    hT hT1 hcompact fHi
  have hfield :
      timeL2Inclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show (a - 1) + 2 ≤ a + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 fHi) =
        maxRegDuhamelSolField (I := I) (M := M)
          (a - 1) hT 0 fLo := by
    rw [hfield0, hforce]
  exact ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield⟩

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
