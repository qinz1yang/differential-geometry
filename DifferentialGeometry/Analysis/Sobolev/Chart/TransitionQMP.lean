import DifferentialGeometry.Analysis.Sobolev.Chart.TransitionPipeline

/-!
# Quasi-measure-preservation of the chart-transition map

The Euclidean chart-transition map `chartTransitionEuclid γ α` is a `C^∞`
diffeomorphism between the two chart-overlap regions
`chartOverlapEuclid γ α` and `chartOverlapEuclid α γ` (see
`TransitionPipeline.lean`). Because it is smooth on the overlap, it carries
Lebesgue-null subsets of the overlap to Lebesgue-null sets. This file packages
that fact as a `QuasiMeasurePreserving` statement and derives the practically
useful corollary: almost-everywhere equalities transport across charts.

## Why a piecewise representative

`MeasureTheory.Measure.QuasiMeasurePreserving f μ ν` carries a *global*
measurability requirement on `f`. The global function `chartTransitionEuclid γ α`
is `toEuclidean ∘ extChartAt I α ∘ (extChartAt I γ).symm ∘ toEuclidean.symm`;
the partial-equiv coercions `extChartAt I α` and `(extChartAt I γ).symm` are
continuous only on their natural sources and take unconstrained junk values
elsewhere, so the global composition is not provably globally measurable. We
therefore work with the canonical Borel-measurable representative

  `chartTransitionEuclidRestr γ α :=
      (chartOverlapEuclid γ α).piecewise (chartTransitionEuclid γ α) 0`,

which agrees with `chartTransitionEuclid γ α` on the whole overlap and is `0`
off it. Its measurability follows from `ContinuousOn.measurable_piecewise`.

## Main results

* `chartTransitionEuclidRestr`: the measurable representative.
* `chartTransitionEuclidRestr_eqOn_overlap`,
  `chartTransitionEuclidRestr_measurable`: its defining properties.
* `chartTransitionEuclid_quasiMeasurePreserving_restrict`: the representative is
  quasi-measure-preserving from `volume.restrict (chartOverlapEuclid γ α)` to
  `volume`.
* `chartTransitionEuclid_comp_ae_eq_restrict`: an a.e.-equality on the
  chart-`α` overlap pulls back to an a.e.-equality of the composites with
  `chartTransitionEuclid γ α` on the chart-`γ` overlap.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The Borel-measurable representative of `chartTransitionEuclid γ α`: it agrees
with `chartTransitionEuclid γ α` on the chart overlap `chartOverlapEuclid γ α`
and is `0` off it. Unlike the bare `chartTransitionEuclid γ α`, this function is
globally measurable, which is what the `QuasiMeasurePreserving` API requires. -/
def chartTransitionEuclidRestr (γ α : M) : EuclN → EuclN := by
  classical
  exact (chartOverlapEuclid (I := I) (M := M) γ α).piecewise
    (chartTransitionEuclid (I := I) (M := M) γ α)
    (fun _ : EuclN => 0)

/-- On the chart overlap, the representative equals `chartTransitionEuclid γ α`. -/
lemma chartTransitionEuclidRestr_eqOn_overlap (γ α : M) :
    Set.EqOn (chartTransitionEuclidRestr (I := I) (M := M) γ α)
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  classical
  intro y hy
  change (chartOverlapEuclid (I := I) (M := M) γ α).piecewise
    (chartTransitionEuclid (I := I) (M := M) γ α) (fun _ : EuclN => 0) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

/-- The representative agrees with `chartTransitionEuclid γ α` on the overlap, as
an `=ᵐ` statement for the volume restricted to the overlap. -/
lemma chartTransitionEuclidRestr_ae_eq_restrict
    [I.Boundaryless] (γ α : M) :
    chartTransitionEuclidRestr (I := I) (M := M) γ α
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      chartTransitionEuclid (I := I) (M := M) γ α := by
  have h_overlap_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartOverlapEuclid_isOpen (I := I) (M := M) γ α).measurableSet
  refine (ae_restrict_iff' h_overlap_meas).2 ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hy)

/-- The representative is globally Borel-measurable. -/
lemma chartTransitionEuclidRestr_measurable
    [I.Boundaryless] (γ α : M) :
    Measurable (chartTransitionEuclidRestr (I := I) (M := M) γ α) := by
  classical
  have h_overlap_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have h_cont_on : ContinuousOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α).continuousOn
  have h_const_on : ContinuousOn (fun _ : EuclN => (0 : EuclN))
      ((chartOverlapEuclid (I := I) (M := M) γ α)ᶜ) :=
    continuousOn_const
  exact ContinuousOn.measurable_piecewise h_cont_on h_const_on
    h_overlap_open.measurableSet

/-- The preimage of `s` under `chartTransitionEuclid γ α`, intersected with the
chart-`γ` overlap, is the image under `chartTransitionEuclid α γ` of `s`
intersected with the chart-`α` overlap. This is the chart-transition analogue of
`SmoothDiffeoBoundedAtOrder.toFun_preimage_inter_eq_invFun_image`, derived from
the bijection of `chartTransitionEuclid γ α` between the two overlap regions. -/
lemma chartTransitionEuclid_preimage_inter_overlap
    [I.Boundaryless] (γ α : M) (s : Set EuclN) :
    chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
        chartOverlapEuclid (I := I) (M := M) γ α =
      chartTransitionEuclid (I := I) (M := M) α γ ''
        (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨hxs, hxΩ⟩
    refine ⟨chartTransitionEuclid (I := I) (M := M) γ α x, ⟨hxs, ?_⟩, ?_⟩
    · exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hxΩ
    · exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hxΩ
  · rintro ⟨y, ⟨hys, hyΩ⟩, hxy⟩
    refine ⟨?_, ?_⟩
    · have h_left : chartTransitionEuclid (I := I) (M := M) γ α
          (chartTransitionEuclid (I := I) (M := M) α γ y) = y :=
        chartTransitionEuclid_left_inv (I := I) (M := M) α γ hyΩ
      rw [← hxy, h_left]; exact hys
    · rw [← hxy]
      exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) α γ hyΩ

/-- A Lebesgue-null set has Lebesgue-null preimage (intersected with the
chart-`γ` overlap) under `chartTransitionEuclid γ α`. The image of a null set
under the smooth — hence differentiable — inverse transition map is null. -/
lemma chartTransitionEuclid_preimage_overlap_null
    [I.Boundaryless] (γ α : M)
    {s : Set EuclN} (hs : (volume : Measure EuclN) s = 0) :
    (volume : Measure EuclN)
        (chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α) = 0 := by
  rw [chartTransitionEuclid_preimage_inter_overlap (I := I) (M := M) γ α s]
  have h_diffOn : DifferentiableOn ℝ
      (chartTransitionEuclid (I := I) (M := M) α γ)
      (chartOverlapEuclid (I := I) (M := M) α γ) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ).differentiableOn
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_diffOn_sub : DifferentiableOn ℝ
      (chartTransitionEuclid (I := I) (M := M) α γ)
      (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) :=
    h_diffOn.mono Set.inter_subset_right
  have h_sub_null : (volume : Measure EuclN)
      (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) = 0 :=
    measure_mono_null Set.inter_subset_left hs
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume) h_diffOn_sub h_sub_null

/-- The chart-transition map (in its Borel-measurable representative) is
quasi-measure-preserving from the volume restricted to the chart-`γ` overlap to
the plain Lebesgue volume. Equivalently: it carries overlap-null sets to null
sets, so almost-everywhere equalities transport across the chart transition. -/
theorem chartTransitionEuclid_quasiMeasurePreserving_restrict
    [I.Boundaryless] (γ α : M) :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (chartTransitionEuclidRestr (I := I) (M := M) γ α)
      ((volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) γ α))
      (volume : Measure EuclN) := by
  refine ⟨chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α, ?_⟩
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs_meas hs_zero
  have h_overlap_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartOverlapEuclid_isOpen (I := I) (M := M) γ α).measurableSet
  have h_pre_meas : MeasurableSet
      (chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s) :=
    chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α hs_meas
  rw [MeasureTheory.Measure.map_apply
        (chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α) hs_meas,
      MeasureTheory.Measure.restrict_apply h_pre_meas]
  have h_inter_eq :
      chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α =
        chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
    intro hy
    rw [chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hy]
  rw [h_inter_eq]
  exact chartTransitionEuclid_preimage_overlap_null (I := I) (M := M) γ α hs_zero

/-- The Borel-measurable representative transports a.e.-equalities: if `f` and
`h` agree almost everywhere on the chart-`α` overlap, then `f` and `h`
pre-composed with the representative agree almost everywhere on the chart-`γ`
overlap. -/
theorem chartTransitionEuclidRestr_comp_ae_eq_restrict
    [I.Boundaryless] (γ α : M)
    {f h : EuclN → ℝ}
    (hfh : f =ᵐ[(volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) α γ)] h) :
    (fun y => f (chartTransitionEuclidRestr (I := I) (M := M) γ α y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclidRestr (I := I) (M := M) γ α y) := by
  have h_qmp_into :
      MeasureTheory.Measure.QuasiMeasurePreserving
        (chartTransitionEuclidRestr (I := I) (M := M) γ α)
        ((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α))
        ((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) α γ)) := by
    refine ⟨chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α, ?_⟩
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
    intro s hs_meas hs_zero
    have h_overlap_α_meas :
        MeasurableSet (chartOverlapEuclid (I := I) (M := M) α γ) :=
      (chartOverlapEuclid_isOpen (I := I) (M := M) α γ).measurableSet
    have h_pre_meas : MeasurableSet
        (chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s) :=
      chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α hs_meas
    rw [MeasureTheory.Measure.restrict_apply hs_meas] at hs_zero
    rw [MeasureTheory.Measure.map_apply
          (chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α) hs_meas,
        MeasureTheory.Measure.restrict_apply h_pre_meas]
    have h_inter_eq :
        chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s ∩
            chartOverlapEuclid (I := I) (M := M) γ α =
          chartTransitionEuclid (I := I) (M := M) γ α ⁻¹'
              (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) ∩
            chartOverlapEuclid (I := I) (M := M) γ α := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hys, hyΩ⟩
        have hy_eq : chartTransitionEuclidRestr (I := I) (M := M) γ α y =
            chartTransitionEuclid (I := I) (M := M) γ α y :=
          chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hyΩ
        refine ⟨⟨hy_eq ▸ hys, ?_⟩, hyΩ⟩
        exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hyΩ
      · rintro ⟨⟨hys, _⟩, hyΩ⟩
        have hy_eq : chartTransitionEuclidRestr (I := I) (M := M) γ α y =
            chartTransitionEuclid (I := I) (M := M) γ α y :=
          chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hyΩ
        exact ⟨hy_eq ▸ hys, hyΩ⟩
    rw [h_inter_eq]
    exact chartTransitionEuclid_preimage_overlap_null (I := I) (M := M) γ α hs_zero
  exact h_qmp_into.ae_eq hfh

/-- Transport of a.e.-equalities, stated directly for `chartTransitionEuclid γ α`
(no measurability of the bare transition map is required). If `f` and `h` agree
almost everywhere on the chart-`α` overlap, then `f ∘ chartTransitionEuclid γ α`
and `h ∘ chartTransitionEuclid γ α` agree almost everywhere on the chart-`γ`
overlap. This is the form consumed downstream when an off-kernel a.e.-vanishing
of a chart component is transported across `chartTransitionEuclid`. -/
theorem chartTransitionEuclid_comp_ae_eq_restrict
    [I.Boundaryless] (γ α : M)
    {f h : EuclN → ℝ}
    (hfh : f =ᵐ[(volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) α γ)] h) :
    (fun y => f (chartTransitionEuclid (I := I) (M := M) γ α y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclid (I := I) (M := M) γ α y) := by
  have h_repr := chartTransitionEuclidRestr_ae_eq_restrict (I := I) (M := M) γ α
  have h_f_repr : (fun y => f (chartTransitionEuclid (I := I) (M := M) γ α y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => f (chartTransitionEuclidRestr (I := I) (M := M) γ α y) := by
    filter_upwards [h_repr] with y hy
    rw [hy]
  have h_h_repr : (fun y => h (chartTransitionEuclidRestr (I := I) (M := M) γ α y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclid (I := I) (M := M) γ α y) := by
    filter_upwards [h_repr] with y hy
    rw [hy]
  exact (h_f_repr.trans
    (chartTransitionEuclidRestr_comp_ae_eq_restrict (I := I) (M := M) γ α hfh)).trans
    h_h_repr

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
