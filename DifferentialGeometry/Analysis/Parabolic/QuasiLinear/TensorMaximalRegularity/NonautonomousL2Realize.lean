import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.StrongDuhamelBack
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy

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
private theorem crossRepr_lo
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith) (u.repr t) = u.lo.toFun t := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, u.repr_coeff hT ht]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem crossRepr_hi_ae
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) :
    (fun t => u.repr t) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t) := by
  filter_upwards [u.ae_coeffFun_eq_hiL2,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t hcoeff ht
  refine TensorHs.ext ?_
  funext i
  rw [u.repr_coeff hT ht, tensorHsInclusion_coeff_apply]
  exact hcoeff i

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem nonautL2_realize
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2 : ℝ → TensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → TensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g r s (a - 1)) T)
    (uHi : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := r) (s := s) a T)
    (fHi : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (hduh : uHi = maxRegDuhamelMap (I := I) (M := M)
      a hT 0 fHi)
    (hfixed : fHi =
      nonautL2Map (I := I) (M := M)
          hT hT1 hcompact A2 hA2 C2 hC2 A1 hA1 fHi + f0)
    (htrace : timeH1.trace0 _ T uHi =
      (0 : TensorHs (I := I) (M := M) g r s a))
    (hpde : timeH1.timeDeriv _ T uHi =
      timeScaleLaplacian (I := I) (M := M) a
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 fHi) +
        (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M)
              a hT 0 fHi) +
          a1L2Term (I := I) (M := M)
            hT hT1 hcompact A1 hA1 fHi +
          f0))
    (hforce : timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith) fHi = fLo)
    (hfield : timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 fHi) =
      maxRegDuhamelSolField (I := I) (M := M)
        (a - 1) hT 0 fLo) :
    ∃ u : CrossScaleField (I := I) (M := M) g r s a T,
      u.lo = uHi ∧
      u.hiL2 = maxRegDuhamelSolField (I := I) (M := M)
        a hT 0 fHi ∧
      timeH1.trace0 _ T u.lo =
        (0 : TensorHs (I := I) (M := M) g r s a) ∧
      timeH1.timeDeriv _ T u.lo =
        timeScaleLaplacian (I := I) (M := M) a u.hiL2 + fHi ∧
      timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith) fHi = fLo ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) (u.lo.toFun t) =
          (maxRegDuhamelMap (I := I) (M := M)
            (a - 1) hT 0 fLo).toFun t) ∧
      u.repr 0 = (0 : TensorHs (I := I) (M := M) g r s (a + 1)) ∧
      ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a ≤ a + 1 by linarith) (u.repr t) =
          u.lo.toFun t) ∧
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 1 by linarith) (u.repr t)) =ᵐ[timeMeasure T]
          fun t => maxRegDuhamelSolField (I := I) (M := M)
            (a - 1) hT 0 fLo t := by
  have hlink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 fHi) =
        timeH1.toTimeL2 (TensorHs (I := I) (M := M) g r s a) T uHi := by
    have h := duhField_pin (I := I) (M := M)
      hT hcompact
        (0 : TensorHs (I := I) (M := M) g r s (a + 2)) fHi
    rwa [← hduh] at h
  let u : CrossScaleField (I := I) (M := M) g r s a T :=
    strongCross (I := I) (M := M)
      (maxRegDuhamelSolField (I := I) (M := M)
        a hT 0 fHi) uHi hlink
  have hlo : u.lo = uHi := rfl
  have hhi : u.hiL2 = maxRegDuhamelSolField (I := I) (M := M)
      a hT 0 fHi := rfl
  have htrace' : timeH1.trace0 _ T u.lo =
      (0 : TensorHs (I := I) (M := M) g r s a) := by
    simpa only [hlo] using htrace
  have hpde' : timeH1.timeDeriv _ T u.lo =
      timeScaleLaplacian (I := I) (M := M) a u.hiL2 + fHi := by
    calc
      timeH1.timeDeriv _ T u.lo =
          timeH1.timeDeriv _ T uHi := by rw [hlo]
      _ = timeScaleLaplacian (I := I) (M := M) a
            (maxRegDuhamelSolField (I := I) (M := M)
              a hT 0 fHi) +
          (timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M)
                a hT 0 fHi) +
            a1L2Term (I := I) (M := M)
              hT hT1 hcompact A1 hA1 fHi +
            f0) := hpde
      _ = timeScaleLaplacian (I := I) (M := M) a
            (maxRegDuhamelSolField (I := I) (M := M)
              a hT 0 fHi) + fHi :=
        congrArg
          (fun z => timeScaleLaplacian (I := I) (M := M) a
            (maxRegDuhamelSolField (I := I) (M := M)
              a hT 0 fHi) + z)
          hfixed.symm
      _ = timeScaleLaplacian (I := I) (M := M) a u.hiL2 + fHi := by
        rw [hhi]
  have hzero : u.repr 0 =
      (0 : TensorHs (I := I) (M := M) g r s (a + 1)) := by
    have hinit : u.lo.init =
        (0 : TensorHs (I := I) (M := M) g r s a) := by
      simpa only [timeH1.trace0_apply] using htrace'
    refine TensorHs.ext ?_
    funext i
    rw [u.repr_coeff hT ⟨le_rfl, hT.le⟩,
      CrossScaleField.coeffFun, timeH1.toFun_zero, hinit,
      TensorHs.zero_coeff, TensorHs.zero_coeff]
  have hrepr_hi := crossRepr_hi_ae (I := I) (M := M) u hT
  have hincl :
      ⇑(timeL2Inclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 fHi)) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 fHi t) :=
    (tensorHsInclusion (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (show (a - 1) + 2 ≤ a + 2 by linarith)).coeFn_compLpL
        (p := 2) (μ := timeMeasure T)
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 fHi)
  have hfield_coe :
      (fun t => tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (show (a - 1) + 2 ≤ a + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 fHi t)) =ᵐ[timeMeasure T]
      fun t => maxRegDuhamelSolField (I := I) (M := M)
        (a - 1) hT 0 fLo t := by
    refine hincl.symm.trans ?_
    rw [hfield]
  have hlow_link := solField_toFun_ae (I := I) (M := M)
    (a := a - 1) hT hcompact
      (0 : TensorHs (I := I) (M := M) g r s ((a - 1) + 2)) fLo
  have hcarrier_ae :
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith) (u.lo.toFun t)) =ᵐ[timeMeasure T]
          fun t => (maxRegDuhamelMap (I := I) (M := M)
            (a - 1) hT 0 fLo).toFun t := by
    filter_upwards [u.link, hfield_coe, hlow_link] with t hu hf hl
    refine TensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply]
    have huc := congrArg (fun z => z.coeff i) hu
    change
      ((tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (u.hiL2 t)).coeff i) =
          (u.lo.toFun t).coeff i at huc
    rw [tensorHsInclusion_coeff_apply, hhi] at huc
    have hfc := congrArg (fun z => z.coeff i) hf
    change
      ((tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 fHi t)).coeff i) =
        (maxRegDuhamelSolField (I := I) (M := M)
          (a - 1) hT 0 fLo t).coeff i at hfc
    rw [tensorHsInclusion_coeff_apply] at hfc
    have hlc := congrArg (fun z => z.coeff i) hl
    change
      ((tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ (a - 1) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (a - 1) hT 0 fLo t)).coeff i) =
        ((maxRegDuhamelMap (I := I) (M := M)
          (a - 1) hT 0 fLo).toFun t).coeff i at hlc
    rw [tensorHsInclusion_coeff_apply] at hlc
    exact huc.symm.trans (hfc.trans hlc)
  have hleft_cont : ContinuousOn
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a - 1 ≤ a by linarith) (u.lo.toFun t))
      (Icc (0 : ℝ) T) :=
    (tensorHsInclusion (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (show a - 1 ≤ a by linarith)).continuous.comp_continuousOn
        u.lo.continuousOn_toFun
  have hright_cont : ContinuousOn
      (fun t => (maxRegDuhamelMap (I := I) (M := M)
        (a - 1) hT 0 fLo).toFun t) (Icc (0 : ℝ) T) :=
    (maxRegDuhamelMap (I := I) (M := M)
      (a - 1) hT 0 fLo).continuousOn_toFun
  have hregular : Icc (0 : ℝ) T ⊆ closure (interior (Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have hcarrier_on :
      ∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s)
            (show a - 1 ≤ a by linarith) (u.lo.toFun t) =
          (maxRegDuhamelMap (I := I) (M := M)
            (a - 1) hT 0 fLo).toFun t :=
    MeasureTheory.Measure.eqOn_of_ae_eq
      hcarrier_ae hleft_cont hright_cont hregular
  have hrepr_lo :
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 1 by linarith) (u.repr t)) =ᵐ[timeMeasure T]
          fun t => maxRegDuhamelSolField (I := I) (M := M)
            (a - 1) hT 0 fLo t := by
    filter_upwards [hrepr_hi, hfield_coe] with t hrepr hlow
    refine TensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hrepr,
      tensorHsInclusion_coeff_apply]
    have hc := congrArg (fun z => z.coeff i) hlow
    change
      ((tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show (a - 1) + 2 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT 0 fHi t)).coeff i) =
        (maxRegDuhamelSolField (I := I) (M := M)
          (a - 1) hT 0 fLo t).coeff i at hc
    rw [tensorHsInclusion_coeff_apply] at hc
    rw [hhi]
    exact hc
  refine ⟨u, hlo, hhi, htrace', hpde', hforce, hcarrier_on, hzero,
    u.continuousOn_normSq_repr hT, ?_, hrepr_lo⟩
  intro t ht
  exact crossRepr_lo (I := I) (M := M) u hT ht

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
