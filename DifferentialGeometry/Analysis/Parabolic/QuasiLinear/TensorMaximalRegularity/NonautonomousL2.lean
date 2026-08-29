import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ZeroDuhamelCross
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperatorL2

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}

def zeroReprNN (hT : 0 < T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) : NNReal :=
  ⟨2 * Real.sqrt (1 + T) * ‖f‖, by positivity⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp]
theorem zeroReprNN_coe (hT : 0 < T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (zeroReprNN (I := I) (M := M) hT f : ℝ) =
      2 * Real.sqrt (1 + T) * ‖f‖ :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem zeroRepr_ae_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ∀ᵐ t ∂timeMeasure T,
      ‖(zeroDuhamelCross (I := I) (M := M)
        hT h_compact f).repr t‖ ≤
        (zeroReprNN (I := I) (M := M) hT f : ℝ) := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
  simpa only [zeroReprNN_coe] using
    zeroRepr_norm_le (I := I) (M := M) hT h_compact f ht

def a1L2Term (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  timeOpL2 A1 hA1
    (fun t => (zeroDuhamelCross (I := I) (M := M)
      hT h_compact f).repr t)
    (zeroRepr_meas (I := I) (M := M) hT hT1 h_compact f)
    (zeroReprNN (I := I) (M := M) hT f)
    (zeroRepr_ae_le (I := I) (M := M) hT h_compact f)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem a1L2Term_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f -
        a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f' =
      a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 (f - f') := by
  let uf : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) :=
    fun t => (zeroDuhamelCross (I := I) (M := M)
      hT h_compact f).repr t
  let uf' : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) :=
    fun t => (zeroDuhamelCross (I := I) (M := M)
      hT h_compact f').repr t
  let ud : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) :=
    fun t => (zeroDuhamelCross (I := I) (M := M)
      hT h_compact (f - f')).repr t
  have huf : AEStronglyMeasurable uf (timeMeasure T) := by
    simpa only [uf] using
      zeroRepr_meas (I := I) (M := M) hT hT1 h_compact f
  have huf' : AEStronglyMeasurable uf' (timeMeasure T) := by
    simpa only [uf'] using
      zeroRepr_meas (I := I) (M := M) hT hT1 h_compact f'
  have hud : AEStronglyMeasurable ud (timeMeasure T) := by
    simpa only [ud] using
      zeroRepr_meas (I := I) (M := M) hT hT1 h_compact (f - f')
  have hsub_meas : AEStronglyMeasurable
      (fun t => uf t - uf' t) (timeMeasure T) :=
    huf.sub huf'
  have huf_bound :
      ∀ᵐ t ∂timeMeasure T, ‖uf t‖ ≤
        (zeroReprNN (I := I) (M := M) hT f : ℝ) := by
    simpa only [uf] using
      zeroRepr_ae_le (I := I) (M := M) hT h_compact f
  have huf'_bound :
      ∀ᵐ t ∂timeMeasure T, ‖uf' t‖ ≤
        (zeroReprNN (I := I) (M := M) hT f' : ℝ) := by
    simpa only [uf'] using
      zeroRepr_ae_le (I := I) (M := M) hT h_compact f'
  have hud_bound :
      ∀ᵐ t ∂timeMeasure T, ‖ud t‖ ≤
        (zeroReprNN (I := I) (M := M) hT (f - f') : ℝ) := by
    simpa only [ud] using
      zeroRepr_ae_le (I := I) (M := M) hT h_compact (f - f')
  have hsub_ae : (fun t => uf t - uf' t) =ᵐ[timeMeasure T] ud := by
    simpa only [uf, uf', ud] using
      zeroRepr_sub_ae (I := I) (M := M) hT hT1 h_compact f f'
  have hsub_bound :
      ∀ᵐ t ∂timeMeasure T, ‖uf t - uf' t‖ ≤
        (zeroReprNN (I := I) (M := M) hT (f - f') : ℝ) := by
    filter_upwards [hsub_ae, hud_bound] with t ht hbound
    rw [ht]
    exact hbound
  have hsub := timeOpL2_sub A1 hA1 uf uf' huf huf' hsub_meas
    (zeroReprNN (I := I) (M := M) hT f)
    (zeroReprNN (I := I) (M := M) hT f')
    (zeroReprNN (I := I) (M := M) hT (f - f'))
    huf_bound huf'_bound hsub_bound
  have hcongr := timeOpL2_congr A1 hA1 (fun t => uf t - uf' t) ud
    hsub_meas hud
    (zeroReprNN (I := I) (M := M) hT (f - f'))
    (zeroReprNN (I := I) (M := M) hT (f - f'))
    hsub_bound hud_bound hsub_ae
  simpa only [a1L2Term, uf, uf', ud] using hsub.trans hcongr

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem a1L2Term_norm (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f‖ ≤
      (2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * ‖f‖ := by
  refine (timeOpL2_norm_le A1 hA1
    (fun t => (zeroDuhamelCross (I := I) (M := M)
      hT h_compact f).repr t)
    (zeroRepr_meas (I := I) (M := M) hT hT1 h_compact f)
    (zeroReprNN (I := I) (M := M) hT f)
    (zeroRepr_ae_le (I := I) (M := M) hT h_compact f)).trans_eq ?_
  rw [zeroReprNN_coe]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem a1L2_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f)
        (a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f') ≤
      (2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * dist f f' := by
  rw [dist_eq_norm, dist_eq_norm,
    a1L2Term_sub (I := I) (M := M) hT hT1 h_compact A1 hA1]
  exact a1L2Term_norm (I := I) (M := M)
    hT hT1 h_compact A1 hA1 (f - f')

def nonautL2Map (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2 : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T)) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun f =>
    timeOp A2 hA2 C2 hC2
        (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) +
      a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem nonautL2_dist_le
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2 : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (nonautL2Map (I := I) (M := M) hT hT1 h_compact
        A2 hA2 C2 hC2 A1 hA1 f)
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
        A2 hA2 C2 hC2 A1 hA1 f') ≤
      ((C2 : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * dist f f' := by
  have hfield2 := maxRegDuhamelSolField_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f f'
  have h2 :
      ‖timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) -
          timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f')‖ ≤
        (C2 : ℝ) * (1 + T) * ‖f - f'‖ := by
    rw [← map_sub]
    calc
      ‖timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f -
            maxRegDuhamelSolField (I := I) (M := M) a hT 0 f')‖
          ≤ ‖timeOp A2 hA2 C2 hC2‖ *
              ‖maxRegDuhamelSolField (I := I) (M := M) a hT 0 f -
                maxRegDuhamelSolField (I := I) (M := M) a hT 0 f'‖ :=
            (timeOp A2 hA2 C2 hC2).le_opNorm _
      _ ≤ (C2 : ℝ) *
              ‖maxRegDuhamelSolField (I := I) (M := M) a hT 0 f -
                maxRegDuhamelSolField (I := I) (M := M) a hT 0 f'‖ :=
          mul_le_mul_of_nonneg_right (timeOp_norm_le A2 hA2 C2 hC2)
            (norm_nonneg _)
      _ ≤ (C2 : ℝ) * ((1 + T) * ‖f - f'‖) :=
          mul_le_mul_of_nonneg_left hfield2 C2.coe_nonneg
      _ = (C2 : ℝ) * (1 + T) * ‖f - f'‖ := by ring
  have h1 := a1L2_dist_le (I := I) (M := M)
    hT hT1 h_compact A1 hA1 f f'
  rw [dist_eq_norm, dist_eq_norm] at h1 ⊢
  unfold nonautL2Map
  have hsplit :
      (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) +
          a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f) -
        (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f') +
          a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f') =
      (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) -
          timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f')) +
        (a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f -
          a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f') := by
    abel
  rw [hsplit]
  calc
    ‖(timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) -
        timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f')) +
      (a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f -
        a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f')‖
        ≤ ‖timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f) -
            timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M) a hT 0 f')‖ +
          ‖a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f -
            a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 f'‖ :=
          norm_add_le _ _
    _ ≤ (C2 : ℝ) * (1 + T) * ‖f - f'‖ +
          (2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * ‖f - f'‖ :=
        add_le_add h2 h1
    _ = ((C2 : ℝ) * (1 + T) +
          2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * ‖f - f'‖ := by
      ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem nonautL2_contract
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (A2 : ℝ → tensorHs (I := I) (M := M) g r s (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g r s (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (hsmall :
      (C2 : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1) :
    ContractingWith
      ⟨(C2 : ℝ) * (1 + T) +
          2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖,
        add_nonneg
          (mul_nonneg C2.coe_nonneg (by linarith [hT.le]))
          (by positivity)⟩
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
        A2 hA2 C2 hC2 A1 hA1) := by
  refine ⟨?_, ?_⟩
  · change
      (C2 : ℝ) * (1 + T) +
          2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1
    exact hsmall
  · refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
    have h := nonautL2_dist_le (I := I) (M := M)
      hT hT1 h_compact A2 hA2 C2 hC2 A1 hA1 f f'
    change dist
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
        A2 hA2 C2 hC2 A1 hA1 f)
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
        A2 hA2 C2 hC2 A1 hA1 f') ≤
      ((C2 : ℝ) * (1 + T) +
          2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖) * dist f f'
    exact h

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem nonautL2_forced
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
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
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := r) (s := s) a T)
      (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      u = maxRegDuhamelMap (I := I) (M := M) a hT 0 force ∧
        force =
          timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M)
                a hT 0 force) +
            a1L2Term (I := I) (M := M)
              hT hT1 h_compact A1 hA1 force +
            f0 ∧
        TimeSobolev.timeH1.trace0 _ T u =
          (0 : tensorHs (I := I) (M := M) g r s a) ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maxRegDuhamelSolField (I := I) (M := M)
                a hT 0 force) +
            (timeOp A2 hA2 C2 hC2
                (maxRegDuhamelSolField (I := I) (M := M)
                  a hT 0 force) +
              a1L2Term (I := I) (M := M)
                hT hT1 h_compact A1 hA1 force +
              f0) := by
  let K : NNReal :=
    ⟨(C2 : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖,
      add_nonneg
        (mul_nonneg C2.coe_nonneg (by linarith [hT.le]))
        (by positivity)⟩
  let F : timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
    fun force =>
      nonautL2Map (I := I) (M := M) hT hT1 h_compact
          A2 hA2 C2 hC2 A1 hA1 force + f0
  have hbase := nonautL2_contract (I := I) (M := M)
    hT hT1 h_compact A2 hA2 C2 hC2 A1 hA1 hsmall
  have hcontr : ContractingWith K F := by
    refine ⟨hbase.1, ?_⟩
    refine LipschitzWith.of_dist_le_mul (fun force force' => ?_)
    change dist
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
          A2 hA2 C2 hC2 A1 hA1 force + f0)
      (nonautL2Map (I := I) (M := M) hT hT1 h_compact
          A2 hA2 C2 hC2 A1 hA1 force' + f0) ≤
        (K : ℝ) * dist force force'
    rw [dist_add_right]
    exact hbase.2.dist_le_mul force force'
  set forceStar := ContractingWith.fixedPoint F hcontr with hforceStar_def
  have hforceStar_fix : F forceStar = forceStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hforceStar_eq : forceStar =
      timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT 0 forceStar) +
        a1L2Term (I := I) (M := M)
          hT hT1 h_compact A1 hA1 forceStar +
        f0 := by
    simpa only [F, nonautL2Map] using hforceStar_fix.symm
  refine ⟨maxRegDuhamelMap (I := I) (M := M)
      a hT 0 forceStar, forceStar, rfl, hforceStar_eq, ?_, ?_⟩
  · simpa only [map_zero] using
      maxRegDuhamelMap_trace0 (I := I) (M := M)
        (a := a) (T := T) hT
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) forceStar
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T)
      hT (0 : tensorHs (I := I) (M := M) g r s (a + 2)) forceStar]
    exact congrArg₂ (fun x y => x + y) rfl hforceStar_eq

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
