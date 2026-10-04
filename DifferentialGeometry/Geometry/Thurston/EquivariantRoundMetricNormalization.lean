import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyContinuity

/-!
# Area normalization of a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), normalization interface. For a Ricci flow
`S` on `[0, T)` on a compact surface whose initial metric has positive scalar curvature, put
`C = ∫ R dμ` and `A₀ = Area` at time `0`, and `T* = A₀ / C`.

* `surfaceFlow_totalScalarCurvature_eq_initial`, `surfaceFlow_area_eq_initial_sub`: on `[0, T)`
  the total scalar curvature is constant and `Area (g t) = A₀ - C t`
  (`totalScalarCurvature_hasDerivAt_zero`, `surfaceArea_hasDerivAt`; continuity at `0` from
  `surfaceFlow_integrals_continuousOn_compact`). No Gauss–Bonnet is used.
* `totalScalarCurvature_pos`: `C > 0`; `surfaceFlow_lt_extinctionTime` and
  `surfaceFlow_le_extinctionTime`: every `t ∈ [0, T)` is below `T*`, so `T ≤ T*`. That the
  maximal time equals `T*` is not claimed here.
* `normalizedSurfaceMetric g T* t` is `g / (2 (T* - t))`; for the flow it has area `C / 2`
  (`surfaceFlow_normalized_area`) and mean scalar curvature `2`
  (`surfaceFlow_normalized_meanScalarCurvature`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

private local instance normalizationMeasurable : MeasurableSpace M := borel M
private local instance normalizationBorel : BorelSpace M := ⟨rfl⟩
private local instance normalizationSmooth : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem eq_of_continuousOn_of_eqOn_Ioc {f : ℝ → ℝ} {t c : ℝ} (ht : 0 < t)
    (hcont : ContinuousOn f (Icc 0 t)) (hconst : ∀ s ∈ Ioc 0 t, f s = c) : f 0 = c := by
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    ((hcont 0 ⟨le_rfl, ht.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioc_mem_nhdsGT ht) Ioc_subset_Icc_self)).tendsto
  have heq : f =ᶠ[𝓝[>] 0] fun _ => c := by
    filter_upwards [Ioc_mem_nhdsGT ht] with s hs
    exact hconst s hs
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds

theorem totalScalarCurvature_pos [Nonempty M] (g : SmoothRiemannianMetric I M)
    (hscal : ∀ x, 0 < metricScalarAt g x) : 0 < totalScalarCurvature g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have hint : Integrable (metricScalarAt g) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsupp : Function.support (metricScalarAt g) = univ :=
    eq_univ_of_forall fun x => Function.mem_support.mpr (hscal x).ne'
  unfold totalScalarCurvature
  rw [integral_pos_iff_support_of_nonneg (fun x => (hscal x).le) hint, hsupp]
  have harea := surfaceArea_pos (I := I) (M := M) g
  unfold surfaceArea at harea
  rw [measureReal_def] at harea
  exact (ENNReal.toReal_pos_iff.mp harea).1

theorem carrier_of_mem_Icc {T t : ℝ} (hT : 0 < T) (ht : t < T) :
    Icc 0 t ⊆ (RealTimeInterval.closedOpen 0 T hT).carrier :=
  fun s hs => (⟨hs.1, lt_of_le_of_lt hs.2 ht⟩ : s ∈ Ico 0 T)

theorem regular_of_mem {T t s r : ℝ} (hT : 0 < T) (hs : 0 < s) (hr : r ∈ Ico s t) (ht : t < T) :
    r ∈ (RealTimeInterval.closedOpen 0 T hT).regular :=
  (⟨hs.trans_le hr.1, hr.2.trans ht⟩ : r ∈ Ioo 0 T)

variable [I.Boundaryless] [Nonempty M] {T : ℝ} (hT : 0 < T)

include hT in
theorem surfaceFlow_totalScalarCurvature_eq_initial
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2) {t : ℝ} (ht : t ∈ Ico 0 T) :
    totalScalarCurvature (S.family.metric t) = totalScalarCurvature (S.family.metric 0) := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0]
  have hcont : ContinuousOn (fun s => totalScalarCurvature (S.family.metric s)) (Icc 0 t) :=
    (surfaceFlow_integrals_continuousOn_compact S hS isCompact_Icc
      (carrier_of_mem_Icc hT ht.2)).2.1
  have hconst : ∀ s ∈ Ioc 0 t,
      totalScalarCurvature (S.family.metric s) = totalScalarCurvature (S.family.metric t) := by
    intro s hs
    have h := constant_of_has_deriv_right_zero (hcont.mono (Icc_subset_Icc hs.1.le le_rfl))
      (fun r hr => (totalScalarCurvature_hasDerivAt_zero S hS hdim
        (regular_of_mem hT hs.1 hr ht.2)).hasDerivWithinAt)
    exact (h t ⟨hs.2, le_rfl⟩).symm
  exact (eq_of_continuousOn_of_eqOn_Ioc hpos hcont hconst).symm

include hT in
theorem surfaceFlow_area_eq_initial_sub
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2) {t : ℝ} (ht : t ∈ Ico 0 T) :
    surfaceArea (S.family.metric t) =
      surfaceArea (S.family.metric 0) - totalScalarCurvature (S.family.metric 0) * t := by
  let C := totalScalarCurvature (S.family.metric 0)
  let F := fun s : ℝ => surfaceArea (S.family.metric s) + C * s
  change surfaceArea (S.family.metric t) = surfaceArea (S.family.metric 0) - C * t
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0]
    ring
  have hcont : ContinuousOn F (Icc 0 t) :=
    ((surfaceFlow_integrals_continuousOn_compact S hS isCompact_Icc
      (carrier_of_mem_Icc hT ht.2)).1).add
      (continuous_const.mul continuous_id).continuousOn
  have hconst : ∀ s ∈ Ioc 0 t, F s = F t := by
    intro s hs
    have h := constant_of_has_deriv_right_zero (hcont.mono (Icc_subset_Icc hs.1.le le_rfl))
      (fun r hr => by
        have hr' : r ∈ Ioo 0 T := ⟨hs.1.trans_le hr.1, hr.2.trans ht.2⟩
        have hA := surfaceArea_hasDerivAt S hS (regular_of_mem hT hs.1 hr ht.2)
        have hC := surfaceFlow_totalScalarCurvature_eq_initial hT S hS hdim
          ⟨hr'.1.le, hr'.2⟩
        exact ((hA.add (hasDerivAt_const_mul (x := r) C)).congr_deriv
          (by rw [hC]; ring)).hasDerivWithinAt)
    exact (h t ⟨hs.2, le_rfl⟩).symm
  have h0 := eq_of_continuousOn_of_eqOn_Ioc hpos hcont hconst
  change surfaceArea (S.family.metric 0) + C * 0 = surfaceArea (S.family.metric t) + C * t at h0
  linarith

include hT in
theorem surfaceFlow_lt_extinctionTime
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2)
    (hscal : ∀ x, 0 < metricScalarAt (S.family.metric 0) x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    t < surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) := by
  have hC := totalScalarCurvature_pos (S.family.metric 0) hscal
  have hA := surfaceArea_pos (I := I) (M := M) (S.family.metric t)
  rw [surfaceFlow_area_eq_initial_sub hT S hS hdim ht] at hA
  rw [lt_div_iff₀ hC]
  linarith

include hT in
theorem surfaceFlow_le_extinctionTime
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2)
    (hscal : ∀ x, 0 < metricScalarAt (S.family.metric 0) x) :
    T ≤ surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) := by
  by_contra hlt
  rw [not_le] at hlt
  have hstar : 0 ≤ surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) :=
    div_nonneg (surfaceArea_pos (I := I) (M := M) _).le
      (totalScalarCurvature_pos (S.family.metric 0) hscal).le
  exact lt_irrefl _ (surfaceFlow_lt_extinctionTime hT S hS hdim hscal ⟨hstar, hlt⟩)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [Nonempty M] in
theorem normalizedSurfaceMetric_pos {Tstar t : ℝ} (ht : t < Tstar) : 0 < 1 / (2 * (Tstar - t)) := by
  have : 0 < Tstar - t := sub_pos.mpr ht
  positivity

def normalizedSurfaceMetric (g : SmoothRiemannianMetric I M) {Tstar t : ℝ} (ht : t < Tstar) :
    SmoothRiemannianMetric I M :=
  scaleMetric (1 / (2 * (Tstar - t))) (normalizedSurfaceMetric_pos ht) g

include hT in
theorem surfaceFlow_normalized_area
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2)
    (hscal : ∀ x, 0 < metricScalarAt (S.family.metric 0) x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    surfaceArea (normalizedSurfaceMetric (S.family.metric t)
      (surfaceFlow_lt_extinctionTime hT S hS hdim hscal ht)) =
      totalScalarCurvature (S.family.metric 0) / 2 := by
  have hC := totalScalarCurvature_pos (S.family.metric 0) hscal
  have hlt := surfaceFlow_lt_extinctionTime hT S hS hdim hscal ht
  unfold normalizedSurfaceMetric
  rw [surfaceArea_scaleMetric _ hdim, surfaceFlow_area_eq_initial_sub hT S hS hdim ht]
  set A₀ := surfaceArea (S.family.metric 0)
  set C := totalScalarCurvature (S.family.metric 0)
  have hden : 0 < A₀ / C - t := sub_pos.mpr hlt
  have hA : A₀ - C * t = C * (A₀ / C - t) := by
    field_simp
  rw [hA]
  generalize A₀ / C - t = X at hden ⊢
  field_simp

include hT in
theorem surfaceFlow_normalized_meanScalarCurvature
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2)
    (hscal : ∀ x, 0 < metricScalarAt (S.family.metric 0) x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    meanScalarCurvature (normalizedSurfaceMetric (S.family.metric t)
      (surfaceFlow_lt_extinctionTime hT S hS hdim hscal ht)) = 2 := by
  have hC := totalScalarCurvature_pos (S.family.metric 0) hscal
  unfold meanScalarCurvature
  rw [surfaceFlow_normalized_area hT S hS hdim hscal ht]
  unfold normalizedSurfaceMetric
  rw [totalScalarCurvature_scaleMetric _ hdim,
    surfaceFlow_totalScalarCurvature_eq_initial hT S hS hdim ht]
  field_simp

end GC.Geometry
