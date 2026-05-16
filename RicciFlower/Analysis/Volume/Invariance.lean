import RicciFlower.Analysis.Volume.ChartDensity
import RicciFlower.Analysis.Volume.Glue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Chart invariance of chart-local and global Riemannian measures

This file develops the chart-invariance story of the Riemannian volume measure
built in `ChartDensity.lean` and `Glue.lean`. The development is independent of
boundary assumptions on the model: every public statement holds for manifolds
modelled on `ModelWithCorners ℝ E H` regardless of whether the model has
boundary or corners.

Where the closed (boundaryless) case admits a stronger statement — for
instance the chart image of an open subset of the chart source is open in `E`,
not merely Borel-measurable — that variant is kept as a separate lemma carrying
the `[I.Boundaryless]` hypothesis explicitly.

## Main results

### Foundations

* `extChartAt_symm_preimage_inter_target_eq_empty`
* `chartLocalMeasure_apply_of_disjoint_source`
* `euclideanChangeOfVariablesMap`

### Metric transformation under chart change

* `chartBasisVecFiber_pullback`
* `chartGramMatrix_pullback_eq_sum`
* `chartGramMatrix_pullback_eq_mul`
* `chartGramMatrix_det_pullback`
* `chartDensity_pullback_eq_abs_det_jacobian`

### Transition derivative identification (bridge)

* `tangentCoordChange_eq_fderivWithin`
* `tangentCoordChange_hasFDerivWithinAt`

### Canonical global Riemannian volume measure

* `riemannianVolumeMeasure`
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace RicciFlower
namespace Analysis
namespace Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

File-local canonical Borel structures, matching those installed in `ChartDensity.lean`
and `Glue.lean`. Declared `local` so they do not pollute external typeclass search. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Preimage disjointness under the chart-symm map -/

/-- The symmetric map `(extChartAt I x₀).symm : E → M` sends the chart
target into the chart source, so the preimage of any set `A` disjoint from
the chart source intersects the target trivially. -/
lemma extChartAt_symm_preimage_inter_target_eq_empty
    (x₀ : M) {A : Set M} (hA : Disjoint A (chartAt H x₀).source) :
    (extChartAt I x₀).symm ⁻¹' A ∩ (extChartAt I x₀).target = ∅ := by
  ext y
  refine ⟨fun hy => ?_, fun hy => hy.elim⟩
  obtain ⟨hmem, htarget⟩ := hy
  have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target htarget
  have hchart_source :
      (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [extChartAt_source] at hsource
    exact hsource
  have hne : ((extChartAt I x₀).symm y) ∈ A ∩ (chartAt H x₀).source :=
    ⟨hmem, hchart_source⟩
  have : A ∩ (chartAt H x₀).source = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty] at hA
    exact hA
  rw [this] at hne
  exact hne

/-! ## Borel-measurability of the extended-chart target -/

/-- The extended-chart target is Borel-measurable in `E`. This works in the
boundary case as well, because `(extChartAt I x₀).target = I.symm ⁻¹' (chartAt H x₀).target ∩ range I`,
the first factor being the preimage of an open set under a continuous map and
the second factor being closed. -/
lemma measurableSet_extChartAt_target (x₀ : M) :
    MeasurableSet (extChartAt I x₀).target := by
  rw [extChartAt_target (I := I)]
  refine MeasurableSet.inter ?_ ?_
  · exact (I.continuous_symm.isOpen_preimage _ (chartAt H x₀).open_target).measurableSet
  · exact I.isClosed_range.measurableSet

/-! ## Chart-local measure vanishes outside the chart source -/

/-- The chart-local measure assigns zero mass to any measurable set disjoint
from the base-chart source. -/
theorem chartLocalMeasure_apply_of_disjoint_source
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {A : Set M} (hAmeas : MeasurableSet A)
    (hA : Disjoint A (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ A = 0 := by
  unfold chartLocalMeasure
  set w : E → ℝ≥0∞ :=
    fun y : E => ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))
  set ν : MeasureTheory.Measure E :=
    ((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity w with hν
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hcontOn : ContinuousOn (extChartAt I x₀).symm
      (extChartAt I x₀).target := continuousOn_extChartAt_symm (I := I) x₀
  have haemeas_base :
      AEMeasurable (extChartAt I x₀).symm
        ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    hcontOn.aemeasurable htarget_meas
  have hν_ac :
      ν ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target := by
    simpa [hν] using MeasureTheory.withDensity_absolutelyContinuous
      (μ := (modelHaar (E := E)).restrict (extChartAt I x₀).target) w
  have haemeas :
      AEMeasurable (extChartAt I x₀).symm ν := haemeas_base.mono_ac hν_ac
  rw [MeasureTheory.Measure.map_apply_of_aemeasurable haemeas hAmeas]
  have hbase_zero :
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target)
          ((extChartAt I x₀).symm ⁻¹' A) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' htarget_meas]
    rw [extChartAt_symm_preimage_inter_target_eq_empty (I := I) x₀ hA]
    exact MeasureTheory.measure_empty
  exact hν_ac hbase_zero

/-! ## Euclidean change-of-variables on the measure level -/

variable (E) in
/-- The Euclidean Jacobian change-of-variables identity for the canonical Haar measure
on `E`, measure form. -/
theorem euclideanChangeOfVariablesMap
    {s : Set E}
    (hs : NullMeasurableSet s (modelHaar (E := E)))
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f
        (((modelHaar (E := E)).restrict s).withDensity
          (fun x => ENNReal.ofReal |(f' x).det|)) =
      (modelHaar (E := E)).restrict (f '' s) :=
  MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar (modelHaar (E := E)) hs hf' hf

/-! ## Transition derivative identification -/

/-- On the overlap of two chart sources, `tangentCoordChange` is exactly the
Fréchet derivative (within `range I`) of the chart-transition map. -/
lemma tangentCoordChange_eq_fderivWithin
    (x₀ x₁ : M) {x : M}
    (_h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    tangentCoordChange I x₀ x₁ x =
      fderivWithin ℝ (extChartAt I x₁ ∘ (extChartAt I x₀).symm) (range I)
        (extChartAt I x₀ x) :=
  tangentCoordChange_def

/-- On the overlap, the chart-transition map has `tangentCoordChange` as its
Fréchet derivative within `range I`. -/
lemma tangentCoordChange_hasFDerivWithinAt
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
      (tangentCoordChange I x₀ x₁ x) (range I) (extChartAt I x₀ x) :=
  hasFDerivWithinAt_tangentCoordChange (I := I) h

/-! ## Metric transformation under chart change -/

/-- Expansion of a linear map on `E` applied to a model-basis vector as a sum
over the model basis with repr-coefficients. -/
lemma finBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((Module.finBasis ℝ E) i) =
      ∑ k, ((Module.finBasis ℝ E).repr (L ((Module.finBasis ℝ E) i)) k)
            • (Module.finBasis ℝ E) k :=
  (((Module.finBasis ℝ E).sum_repr (L ((Module.finBasis ℝ E) i)))).symm

/-- The transition matrix of the chart bases at `x` in the model basis: entry
`(k, i)` is the `k`-th coordinate (in the model basis) of the image of the
`i`-th model-basis vector under `tangentCoordChange I x₁ x₀ x`. -/
def transitionMatrix (x₀ x₁ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    (Module.finBasis ℝ E).repr
      ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k

@[simp] lemma transitionMatrix_apply (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrix (I := I) x₀ x₁ x k i =
      (Module.finBasis ℝ E).repr
        ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k := rfl

/-- The `tangentCoordChange` map applied to a model-basis vector decomposes
in the model basis via the transition matrix. -/
lemma tangentCoordChange_finBasis_eq_sum
    (x₀ x₁ : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i) =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i • (Module.finBasis ℝ E) k :=
  finBasis_repr_sum (tangentCoordChange I x₁ x₀ x) i

/-- On the overlap of two chart base sets, the `x₁`-chart-basis vector at `x`
decomposes in the `x₀`-chart-basis with coefficients given by the transition
matrix `transitionMatrix x₀ x₁ x`. -/
lemma chartBasisVecFiber_pullback
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₁ i x =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
        chartBasisVecFiber (I := I) x₀ k x := by
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₀
  set T₁ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₁
  have hx0' : x ∈ T₀.baseSet := hx0
  have hx1' : x ∈ T₁.baseSet := hx1
  -- By definition, chartBasisVecFiber x₁ i x = T₁.symm x (finBasis i).
  have hdef1 :
      chartBasisVecFiber (I := I) x₁ i x =
        T₁.symm x ((Module.finBasis ℝ E) i) := rfl
  -- Use the composition identity
  -- (T₁.cLEA x).symm.trans (T₀.cLEA x) = coordChangeL ℝ T₁ T₀ x
  -- evaluated at the model-basis vector, then apply (T₀.cLEA x).symm to both sides.
  have hcompeq' :=
    Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := ℝ) (F := E) (E := (TangentSpace I : M → Type _))
      T₁ T₀ (b := x) ⟨hx1', hx0'⟩
  have happ :
      (T₀.continuousLinearEquivAt ℝ x hx0')
          ((T₁.continuousLinearEquivAt ℝ x hx1').symm ((Module.finBasis ℝ E) i))
        = (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((Module.finBasis ℝ E) i) := by
    have := congrArg
      (fun L : E ≃L[ℝ] E => L ((Module.finBasis ℝ E) i)) hcompeq'
    simpa [ContinuousLinearEquiv.trans_apply] using this
  have hequiv :
      T₁.symm x ((Module.finBasis ℝ E) i) =
        T₀.symm x
          ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((Module.finBasis ℝ E) i)) := by
    have hL : (T₁.continuousLinearEquivAt ℝ x hx1').symm ((Module.finBasis ℝ E) i) =
              T₁.symm x ((Module.finBasis ℝ E) i) := rfl
    have hR : (T₀.continuousLinearEquivAt ℝ x hx0').symm
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((Module.finBasis ℝ E) i)) =
              T₀.symm x
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((Module.finBasis ℝ E) i)) := rfl
    have := congrArg (T₀.continuousLinearEquivAt ℝ x hx0').symm happ
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    rw [← hL, ← hR]
    exact this
  -- Convert `coordChangeL ℝ T₁ T₀ x` to `tangentCoordChange I x₁ x₀ x` via
  -- `VectorBundleCore.localTriv_coordChange_eq` applied to the tangent bundle core.
  have hcc :
      (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
          ((Module.finBasis ℝ E) i)
        = (tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i) := by
    change (Bundle.Trivialization.coordChangeL (R := ℝ)
          ((tangentBundleCore I M).localTriv (achart H x₁))
          ((tangentBundleCore I M).localTriv (achart H x₀)) x)
        ((Module.finBasis ℝ E) i) = _
    exact VectorBundleCore.localTriv_coordChange_eq
        (tangentBundleCore I M) (achart H x₁) (achart H x₀) (b := x)
        ⟨hx1', hx0'⟩ _
  rw [hdef1, hequiv, hcc, tangentCoordChange_finBasis_eq_sum (I := I) x₀ x₁ x i]
  -- Now use `T₀.symmL ℝ x` to apply linearity.
  have hsymmL : (T₀.symm x : E → TangentSpace I x) =
      (T₀.symmL ℝ x : E →L[ℝ] TangentSpace I x) := rfl
  rw [hsymmL]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]
  rfl

/-- Bilinear expansion of the Gram matrix at `x₁` in terms of the Gram matrix
at `x₀` and the transition matrix entries. -/
lemma chartGramMatrix_pullback_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₁ x i j =
      ∑ k, ∑ l,
        (transitionMatrix (I := I) x₀ x₁ x k i) *
        (transitionMatrix (I := I) x₀ x₁ x l j) *
        chartGramMatrix g x₀ x k l := by
  have hlhs :
      chartGramMatrix g x₁ x i j =
        g.inner x
          (chartBasisVecFiber (I := I) x₁ i x)
          (chartBasisVecFiber (I := I) x₁ j x) := rfl
  rw [hlhs]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 i]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 j]
  -- Left linearity.
  have hL :
      g.inner x
          (∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            chartBasisVecFiber (I := I) x₀ k x)
        = ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            g.inner x (chartBasisVecFiber (I := I) x₀ k x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply]
  have hR :
      g.inner x (chartBasisVecFiber (I := I) x₀ k x)
          (∑ l, transitionMatrix (I := I) x₀ x₁ x l j •
            chartBasisVecFiber (I := I) x₀ l x)
        = ∑ l, transitionMatrix (I := I) x₀ x₁ x l j *
            g.inner x (chartBasisVecFiber (I := I) x₀ k x)
              (chartBasisVecFiber (I := I) x₀ l x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
    rw [smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring

/-- Matrix form of the Gram pullback: `G_{x₁}(x) = J^T · G_{x₀}(x) · J`. -/
lemma chartGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartGramMatrix g x₁ x =
      (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
        chartGramMatrix g x₀ x *
        transitionMatrix (I := I) x₀ x₁ x := by
  ext i j
  rw [chartGramMatrix_pullback_eq_sum (I := I) g x₀ x₁ hx0 hx1 i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- The determinant of the transition matrix equals the determinant of the
transition continuous linear map. -/
lemma transitionMatrix_det (x₀ x₁ : M) (x : M) :
    (transitionMatrix (I := I) x₀ x₁ x).det =
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det := by
  have hL :
      transitionMatrix (I := I) x₀ x₁ x =
        LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
          (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).toLinearMap := by
    ext k i
    simp [transitionMatrix, LinearMap.toMatrix_apply]
  rw [hL]
  rw [LinearMap.det_toMatrix]

/-- Determinant form of the Gram pullback:
`det G_{x₁}(x) = (det J)² · det G_{x₀}(x)`. -/
lemma chartGramMatrix_det_pullback
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (chartGramMatrix g x₁ x).det =
      ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det) ^ 2 *
        (chartGramMatrix g x₀ x).det := by
  rw [chartGramMatrix_pullback_eq_mul (I := I) g x₀ x₁ hx0 hx1]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [transitionMatrix_det (I := I) x₀ x₁ x]
  ring

/-- Scalar form of the density pullback:
`density_{x₁}(x) = |det J| · density_{x₀}(x)`. -/
theorem chartDensity_pullback_eq_abs_det_jacobian
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartDensity g x₁ x =
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| *
        chartDensity g x₀ x := by
  unfold chartDensity
  rw [chartGramMatrix_det_pullback (I := I) g x₀ x₁ hx0 hx1]
  rw [Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq_eq_abs]

/-! ## Overlap measurability and related facts -/

/-- The trivialization base set coincides with the chart source. -/
lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source :=
  rfl

/-- The overlap of two chart sources is open. -/
lemma isOpen_chartAt_source_inter (x₀ x₁ : M) :
    IsOpen ((chartAt H x₀).source ∩ (chartAt H x₁).source) :=
  (chartAt H x₀).open_source.inter (chartAt H x₁).open_source

/-- The overlap of two chart sources is measurable in the Borel σ-algebra. -/
lemma measurableSet_chartAt_source_inter (x₀ x₁ : M) :
    MeasurableSet ((chartAt H x₀).source ∩ (chartAt H x₁).source) :=
  (isOpen_chartAt_source_inter (H := H) (M := M) x₀ x₁).measurableSet

/-- The extended-chart source coincides with the chart source. -/
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

/-- The `chartDensity` is continuous on the trivialization base set (the
chart source). Consequence: it is measurable on that set. -/
lemma chartDensity_continuousOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContinuousOn (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (chartDensity_contMDiffOn (I := I) g x₀).continuousOn

/-! ## Canonical Riemannian volume measure

We define the canonical Riemannian volume measure as the glued measure
using the chart-atlas partition of unity from `Glue.lean`. -/

variable (I M) in
/-- The canonical Riemannian volume measure on `M`, built from the canonical additive
Haar measure on the model space `E`, a smooth Riemannian metric, and the canonical
partition of unity subordinate to the chart atlas. -/
def riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : MeasureTheory.Measure M :=
  riemannianMeasure (I := I) g (chartAtlasPOU I M)

/-- Unfolding lemma for the canonical Riemannian volume measure. -/
lemma riemannianVolumeMeasure_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) := rfl

/-! ## Chart-local measure: integral characterisation -/

/-- `AEMeasurable` for `(extChartAt I x₀).symm` with respect to the restricted
canonical Haar measure on the chart target. Used repeatedly below. -/
lemma aemeasurable_extChartAt_symm_restrict_target
    (x₀ : M) :
    AEMeasurable ((extChartAt I x₀).symm)
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  exact (continuousOn_extChartAt_symm (I := I) x₀).aemeasurable htarget_meas

/-- The density `y ↦ ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))`
is `AEMeasurable` with respect to the restricted canonical Haar measure on the chart
target. -/
lemma aemeasurable_chartDensity_symm_pullback
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hcontOn : ContinuousOn (chartDensity g x₀ ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target := by
    refine (chartDensity_continuousOn (I := I) g x₀).comp
      (continuousOn_extChartAt_symm (I := I) x₀) ?_
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have haem_density : AEMeasurable
      (fun y : E => chartDensity g x₀ ((extChartAt I x₀).symm y))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    hcontOn.aemeasurable htarget_meas
  exact ENNReal.measurable_ofReal.comp_aemeasurable haem_density

/-- Basic integral characterisation of the chart-local measure. -/
theorem chartLocalMeasure_lintegral
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  unfold chartLocalMeasure
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have haem_base : AEMeasurable (extChartAt I x₀).symm
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
  have hw_aem : AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hwd_ac :
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))))
        ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have haem : AEMeasurable (extChartAt I x₀).symm
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
        (fun y : E =>
          ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))) :=
    haem_base.mono_ac hwd_ac
  -- Push `lintegral` through `Measure.map`.
  rw [MeasureTheory.lintegral_map' hF.aemeasurable haem]
  -- Use `lintegral_withDensity_eq_lintegral_mul₀` to unfold the `withDensity`.
  have hcomp :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
      (μ := (modelHaar (E := E)).restrict (extChartAt I x₀).target) hw_aem
      (g := fun y : E => F ((extChartAt I x₀).symm y))
      (hF.aemeasurable.comp_aemeasurable haem_base)
  simp only [Pi.mul_apply] at hcomp
  rw [hcomp]

/-! ## Inverse relation between `tangentCoordChange` in both directions -/

/-- At any point in the overlap of two chart sources, the two tangent
transition maps compose to the identity. -/
lemma tangentCoordChange_comp_self_overlap
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) (v : E) :
    tangentCoordChange I x₁ x₀ x (tangentCoordChange I x₀ x₁ x v) = v := by
  have h3 : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨h, h.1⟩
  have := tangentCoordChange_comp (I := I) (w := x₀) (x := x₁) (y := x₀)
    (z := x) (v := v) h3
  -- `tangentCoordChange I x₁ x₀ x (tangentCoordChange I x₀ x₁ x v)
  --   = tangentCoordChange I x₀ x₀ x v`
  rw [this]
  exact tangentCoordChange_self (I := I) h.1

/-- The continuous-linear determinant of the transition at `x` (from `x₀` to
`x₁`) multiplied by the determinant of the reverse transition equals `1`. -/
lemma tangentCoordChange_det_mul_inv_det_eq_one
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    (tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det *
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det = 1 := by
  classical
  -- Unfold `ContinuousLinearMap.det` to `LinearMap.det`
  have hcomp_id :
      ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E) :
            E →ₗ[ℝ] E).comp
          ((tangentCoordChange I x₀ x₁ x : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        LinearMap.id := by
    ext v
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      LinearMap.id_coe, id_eq]
    exact tangentCoordChange_comp_self_overlap (I := I) x₀ x₁ h v
  have := congrArg LinearMap.det hcomp_id
  rw [LinearMap.det_comp, LinearMap.det_id] at this
  -- `det TCC(x₁,x₀) * det TCC(x₀,x₁) = 1`, want `det TCC(x₀,x₁) * det TCC(x₁,x₀) = 1`.
  -- Use commutativity.
  have : (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det *
      (tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det = 1 := this
  linarith [this, mul_comm
    ((tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det)
    ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det)]

/-- The absolute values of the determinants of the two opposite transitions
multiply to `1`. -/
lemma abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← abs_mul, tangentCoordChange_det_mul_inv_det_eq_one (I := I) x₀ x₁ h,
    abs_one]

/-- ENNReal form of the inverse-determinant identity. -/
lemma ennreal_abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      ENNReal.ofReal
        |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [abs_det_tangentCoordChange_mul_abs_det_inv (I := I) x₀ x₁ h]
  exact ENNReal.ofReal_one

/-! ## Chart-local integral restricted to a subset of the chart source -/

/-- Set-integral form of the chart-local measure: for measurable `F` and
any measurable set `U`, the integral of `F` over `U` with respect to
`chartLocalMeasure` equals the Euclidean integral of
`ofReal (density ∘ symm) * (U.indicator F ∘ symm)`. -/
theorem chartLocalMeasure_setLintegral_indicator
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUmeas : MeasurableSet U)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          U.indicator F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  rw [← MeasureTheory.lintegral_indicator hUmeas]
  exact chartLocalMeasure_lintegral (I := I) g x₀ (hF.indicator hUmeas)

/-! ## Openness/measurability of the image of an overlap under a chart -/

/-- The image of an open subset `U` of `(chartAt H x₀).source` under
`extChartAt I x₀` is open in `E` under the Boundaryless assumption. -/
lemma extChartAt_image_isOpen_of_open_subset_source_of_boundaryless
    [I.Boundaryless] (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    IsOpen ((extChartAt I x₀) '' U) := by
  -- `extChartAt I x₀ = I ∘ chartAt H x₀`, so the image is `I '' (chartAt H x₀ '' U)`.
  have hchart_img : IsOpen ((chartAt H x₀) '' U) :=
    (chartAt H x₀).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq : (extChartAt I x₀) '' U = I '' ((chartAt H x₀) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  exact I.toHomeomorph.isOpenMap _ hchart_img

/-- Without any boundary assumption, the image of an open subset `U` of
`(chartAt H x₀).source` under `extChartAt I x₀` is Borel-measurable in `E`.
This is the boundary-tolerant analogue of
`extChartAt_image_isOpen_of_open_subset_source_of_boundaryless`: while the image
need not be open in the boundary case, it is always the image under the closed
embedding `I` of an open set in `H`, hence Borel-measurable. -/
lemma extChartAt_image_measurableSet_of_open_subset_source (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    MeasurableSet ((extChartAt I x₀) '' U) := by
  -- `extChartAt I x₀ = I ∘ chartAt H x₀`, so the image is `I '' (chartAt H x₀ '' U)`.
  have hchart_img : IsOpen ((chartAt H x₀) '' U) :=
    (chartAt H x₀).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq : (extChartAt I x₀) '' U = I '' ((chartAt H x₀) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  -- `I` is a closed embedding, so it is a measurable embedding;
  -- the image of any measurable set under a measurable embedding is measurable.
  exact I.isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
    hchart_img.measurableSet

/-- Without any boundary assumption, the overlap-image is Borel-measurable. -/
lemma extChartAt_image_measurableSet_of_overlap (x₀ x₁ : M) :
    MeasurableSet ((extChartAt I x₀) ''
      ((chartAt H x₀).source ∩ (chartAt H x₁).source)) :=
  extChartAt_image_measurableSet_of_open_subset_source (I := I) x₀
    (isOpen_chartAt_source_inter (H := H) (M := M) x₀ x₁)
    Set.inter_subset_left

/-! ## The chart-transition map and its derivative on the overlap -/

/-- The chart-transition map `extChartAt I x₁ ∘ (extChartAt I x₀).symm` is
well-defined on `(extChartAt I x₀).target` and carries the overlap image
`(extChartAt I x₀) '' U` to `(extChartAt I x₁) '' U`. -/
lemma extChartAt_transition_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (_hUsub1 : U ⊆ (chartAt H x₁).source) :
    (extChartAt I x₁ ∘ (extChartAt I x₀).symm) '' ((extChartAt I x₀) '' U) =
      (extChartAt I x₁) '' U := by
  rw [← Set.image_comp]
  refine Set.image_congr ?_
  intro x hx
  have hxsrc0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hx
  change extChartAt I x₁ ((extChartAt I x₀).symm (extChartAt I x₀ x)) = _
  rw [(extChartAt I x₀).left_inv hxsrc0]

/-- Injectivity of the chart transition on the overlap image. -/
lemma extChartAt_transition_injOn_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    Set.InjOn (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀) '' U) := by
  intro y hy z hz hyz
  -- `symm₀ y ∈ U ⊆ source₀, source₁`.
  obtain ⟨a, haU, rfl⟩ := hy
  obtain ⟨b, hbU, rfl⟩ := hz
  have haS0 : a ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 haU
  have hbS0 : b ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hbU
  have haS1 : a ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 haU
  have hbS1 : b ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hbU
  -- Apply `(extChartAt I x₀).left_inv` in the expression.
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv haS0,
    (extChartAt I x₀).left_inv hbS0] at hyz
  -- `φ₁ a = φ₁ b ⇒ a = b` since φ₁ injective on source₁.
  have := (extChartAt I x₁).injOn haS1 hbS1 hyz
  rw [this]

/-- The chart transition has Fréchet derivative `tangentCoordChange I x₀ x₁ x`
at each point `y = extChartAt I x₀ x` of the overlap image, within the image
set itself. -/
lemma extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    ∀ y ∈ (extChartAt I x₀) '' U,
      HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
        (tangentCoordChange I x₀ x₁ ((extChartAt I x₀).symm y))
        ((extChartAt I x₀) '' U) y := by
  intro y hy
  obtain ⟨x, hxU, rfl⟩ := hy
  have hxS0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hxU
  have hxS1 : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hxU
  -- Using the Mathlib lemma on `range I`.
  have hfull := hasFDerivWithinAt_tangentCoordChange (I := I) (x := x₀) (y := x₁)
    (z := x) ⟨hxS0, hxS1⟩
  -- Move to `HasFDerivWithinAt` on a smaller set:
  -- Each point `y' = extChartAt I x₀ z` for `z ∈ U` lies in
  -- `(extChartAt I x₀).target ⊆ range I`.
  have himage_sub : (extChartAt I x₀) '' U ⊆ Set.range I := by
    intro y' hy'
    rcases hy' with ⟨z, hzU, rfl⟩
    have hzS0 : z ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hzU
    exact extChartAt_target_subset_range (I := I) x₀ ((extChartAt I x₀).map_source hzS0)
  -- `symm (extChartAt x) = x`:
  have hsymm_eq : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x :=
    (extChartAt I x₀).left_inv hxS0
  rw [hsymm_eq]
  exact hfull.mono himage_sub

/-! ## Substep D: chart-local measures agree on the overlap -/

/-- Auxiliary: the set-lintegral of a function supported in the `φⱼ '' U`
overlap image can be rewritten as a set-lintegral over `φⱼ '' U`, given that
`U ⊆ source_j` is open. -/
lemma setLIntegral_target_eq_setLIntegral_image
    (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    (h : E → ℝ≥0∞) :
    ∫⁻ y in (extChartAt I x₀).target,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)) * h y
            ∂(modelHaar (E := E)) =
      ∫⁻ y in (extChartAt I x₀) '' U, h y ∂(modelHaar (E := E)) := by
  have hUsub' : U ⊆ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub
  have himg :
      (extChartAt I x₀) '' U =
        (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U :=
    (extChartAt I x₀).image_eq_target_inter_inv_preimage hUsub'
  -- Pointwise the integrand equals `(φ₀ '' U).indicator h`.
  have hptwise : ∀ y ∈ (extChartAt I x₀).target,
      U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y) * h y =
        ((extChartAt I x₀) '' U).indicator h y := by
    intro y hy
    by_cases hy' : (extChartAt I x₀).symm y ∈ U
    · have hy_img : y ∈ (extChartAt I x₀) '' U := by
        rw [himg]; exact ⟨hy, hy'⟩
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy_img, one_mul]
    · have hy_nimg : y ∉ (extChartAt I x₀) '' U := by
        rw [himg]; exact fun h => hy' h.2
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy_nimg, zero_mul]
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hptwise]
  have hV_meas : MeasurableSet ((extChartAt I x₀) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source (I := I) x₀
      hUopen hUsub
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  -- (V ∩ target) = V since V ⊆ target.
  rw [show ((extChartAt I x₀) '' U) ∩ (extChartAt I x₀).target =
        (extChartAt I x₀) '' U from by
    rw [himg]; ext y; constructor
    · rintro ⟨⟨hy_t, hy_u⟩, _⟩; exact ⟨hy_t, hy_u⟩
    · rintro ⟨hy_t, hy_u⟩; exact ⟨⟨hy_t, hy_u⟩, hy_t⟩]

/-- Variant: the `U.indicator`-form integral equals a straight
set-lintegral over `(extChartAt I x₀) '' U`. -/
lemma chartLocalMeasure_lintegral_U_eq_setLIntegral_image
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hUmeas : MeasurableSet U) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀) '' U,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ hUmeas hF]
  -- Convert `U.indicator F` to `1-indicator`-times-function.
  -- Pointwise: ofReal(d(symm y)) * U.indicator F (symm y)
  --          = U.indicator 1 (symm y) * (ofReal(d(symm y)) * F(symm y))
  have hpt : ∀ y : E,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          U.indicator F ((extChartAt I x₀).symm y) =
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)) *
          (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
            F ((extChartAt I x₀).symm y)) := by
    intro y
    by_cases hy : (extChartAt I x₀).symm y ∈ U
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
        mul_zero, zero_mul]
  conv_lhs => rw [MeasureTheory.setLIntegral_congr_fun
    (measurableSet_extChartAt_target (I := I) x₀)
    (fun y _ => hpt y)]
  exact setLIntegral_target_eq_setLIntegral_image (I := I) (E := E) x₀ hUopen hUsub _

/-- Core Substep D: chart-local measures agree on any measurable subset of the
chart-source overlap. -/
theorem chartLocalMeasure_lintegral_U_eq_of_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have hUopen : IsOpen U := isOpen_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUmeas : MeasurableSet U :=
    measurableSet_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUsub0 : U ⊆ (chartAt H x₀).source := Set.inter_subset_left
  have hUsub1 : U ⊆ (chartAt H x₁).source := Set.inter_subset_right
  -- Convert both sides to set-lintegrals over the respective image sets.
  rw [chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
    g x₀ hUopen hUsub0 hF hUmeas]
  rw [chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
    g x₁ hUopen hUsub1 hF hUmeas]
  -- LHS: over `φ₀ '' U`. RHS: over `φ₁ '' U`.
  -- Use Jacobian change-of-variables to relate these.
  -- Let `T := φ₁ ∘ symm₀`, with T '' (φ₀ '' U) = φ₁ '' U, and
  -- `HasFDerivWithinAt T (tangentCoordChange I x₀ x₁ (symm₀ y)) (φ₀ '' U) y`
  -- for all `y ∈ φ₀ '' U`.
  have hV0_meas : MeasurableSet ((extChartAt I x₀) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source (I := I) x₀
      hUopen hUsub0
  have hT_image :
      (extChartAt I x₁ ∘ (extChartAt I x₀).symm) '' ((extChartAt I x₀) '' U) =
        (extChartAt I x₁) '' U :=
    extChartAt_transition_image (I := I) x₀ x₁ hUsub0 hUsub1
  have hT_injOn :
      Set.InjOn (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
        ((extChartAt I x₀) '' U) :=
    extChartAt_transition_injOn_overlap_image (I := I) x₀ x₁ hUsub0 hUsub1
  have hT_fderiv :
      ∀ y ∈ (extChartAt I x₀) '' U,
        HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
          (tangentCoordChange I x₀ x₁ ((extChartAt I x₀).symm y))
          ((extChartAt I x₀) '' U) y :=
    extChartAt_transition_hasFDerivWithinAt_on_overlap_image (I := I) x₀ x₁
      hUsub0 hUsub1
  -- Apply `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
  rw [← hT_image]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hV0_meas hT_fderiv hT_injOn
    (g := fun z : E =>
      ENNReal.ofReal (chartDensity g x₁ ((extChartAt I x₁).symm z)) *
        F ((extChartAt I x₁).symm z))]
  -- Simplify `symm₁ (T y) = symm₀ y` and apply density pullback + det product = 1.
  refine MeasureTheory.setLIntegral_congr_fun hV0_meas ?_
  intro y hy
  obtain ⟨x, hxU, hx_eq⟩ := hy
  have hx0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hxU
  have hx1 : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hxU
  have hx_in_inter : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source :=
    ⟨hx0, hx1⟩
  have hx_trivBase0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hUsub0 hxU
  have hx_trivBase1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hUsub1 hxU
  -- `symm₀ y = x` and `T y = φ₁ x`, so `symm₁ (T y) = x`.
  have hsymm0 : (extChartAt I x₀).symm y = x := by
    rw [← hx_eq]; exact (extChartAt I x₀).left_inv hx0
  have hTy :
      (extChartAt I x₁ ∘ (extChartAt I x₀).symm) y = extChartAt I x₁ x := by
    change extChartAt I x₁ ((extChartAt I x₀).symm y) = _
    rw [hsymm0]
  have hsymm1 :
      (extChartAt I x₁).symm ((extChartAt I x₁ ∘ (extChartAt I x₀).symm) y) = x := by
    rw [hTy]; exact (extChartAt I x₁).left_inv hx1
  -- Density pullback.
  have hdens_pb :
      chartDensity g x₁ x
        = |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det|
            * chartDensity g x₀ x :=
    chartDensity_pullback_eq_abs_det_jacobian (I := I) g x₀ x₁
      hx_trivBase0 hx_trivBase1
  -- Det product identity.
  have hdet_mul :
      ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 :=
    ennreal_abs_det_tangentCoordChange_mul_abs_det_inv (I := I) x₀ x₁
      hx_in_inter
  -- Simplify both sides, landing in terms of `x`.
  simp only [hsymm0, hsymm1]
  -- After `simp only`:
  --  LHS: ofReal(density_0 x) * F x
  --  RHS: ofReal|det tcc x₀ x₁ x| * (ofReal(density_1 x) * F x)
  rw [hdens_pb]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  -- Reassociate and apply `hdet_mul`:
  rw [show
    ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        (ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| *
          ENNReal.ofReal (chartDensity g x₀ x) *
            F x) =
      (ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det|) *
        (ENNReal.ofReal (chartDensity g x₀ x) * F x) by ring]
  rw [hdet_mul, one_mul]

/-- Substep D (final form): the chart-local measures at `x₀` and `x₁` agree
on the overlap of the two chart sources. -/
theorem chartLocalMeasure_restrict_overlap_eq
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) :
    (chartLocalMeasure (I := I) g x₀).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source) =
      (chartLocalMeasure (I := I) g x₁).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source) := by
  refine MeasureTheory.Measure.ext_of_lintegral _ (fun F hF => ?_)
  exact chartLocalMeasure_lintegral_U_eq_of_overlap (I := I) g x₀ x₁ hF

/-! ## Chart-local measure: lintegral of a function supported in the overlap -/

/-- If a measurable function `f : M → ℝ≥0∞` is zero outside the overlap of
two chart sources, then its lintegrals against the two chart-local measures
agree. -/
lemma chartLocalMeasure_lintegral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {f : M → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have hUmeas : MeasurableSet U :=
    measurableSet_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUeq : ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
        ∫⁻ x in U, f x ∂(chartLocalMeasure (I := I) g x₀) := by
    rw [← MeasureTheory.lintegral_indicator hUmeas]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  have hUeq' : ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₁) =
        ∫⁻ x in U, f x ∂(chartLocalMeasure (I := I) g x₁) := by
    rw [← MeasureTheory.lintegral_indicator hUmeas]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  rw [hUeq, hUeq']
  exact chartLocalMeasure_lintegral_U_eq_of_overlap (I := I) g x₀ x₁ hf

/-! ## Substep E: independence from the choice of partition of unity

The key step swaps `∑' α` with `∑' β` inside the lintegral expansion,
relying on `ENNReal.tsum_comm` (valid for any pair of index types) and a
countability-aware application of `MeasureTheory.lintegral_tsum`. We extract
a countable subfamily of the POU indices corresponding to non-trivial bumps
using `LocallyFinite.countable_univ` on a σ-compact base. -/

/-- For any POU `ρ` subordinate to the chart atlas and any function `f`,
the `α, β`-integrand `ρ α * ρ' β * f` is supported in the overlap of the
two chart sources `α, β`. -/
lemma pou_product_support_subset_overlap
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source))
    (α β : M) (f : M → ℝ≥0∞) :
    ∀ x, x ∉ (chartAt H α).source ∩ (chartAt H β).source →
      ENNReal.ofReal (ρ α x) * ENNReal.ofReal (ρ' β x) * f x = 0 := by
  intro x hx
  have : x ∉ (chartAt H α).source ∨ x ∉ (chartAt H β).source := by
    by_contra h
    apply hx
    constructor <;> (by_contra habs; exact h (by tauto))
  rcases this with h | h
  · have : x ∉ tsupport (ρ α) := fun h' => h (hρ α h')
    have hρα : ρ α x = 0 := by
      by_contra hne
      exact this (subset_tsupport _ hne)
    rw [hρα, ENNReal.ofReal_zero, zero_mul, zero_mul]
  · have : x ∉ tsupport (ρ' β) := fun h' => h (hρ' β h')
    have hρβ : ρ' β x = 0 := by
      by_contra hne
      exact this (subset_tsupport _ hne)
    rw [hρβ, ENNReal.ofReal_zero, mul_zero, zero_mul]

/-- The α-indices for which `ρ α` is not identically zero form a countable
set, under `SigmaCompactSpace M`. -/
lemma countable_nonempty_support_of_pou
    [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M univ) :
    Set.Countable {α : M | (Function.support (ρ α)).Nonempty} := by
  have hloc : LocallyFinite (fun α : M => Function.support (ρ α)) :=
    ρ.locallyFinite
  set S : Set M := {α : M | (Function.support (ρ α)).Nonempty}
  have hsubfam :
      LocallyFinite (fun α : S => Function.support (ρ α.val)) :=
    hloc.comp_injective Subtype.val_injective
  have hne : ∀ α : S, (Function.support (ρ α.val)).Nonempty := fun α => α.2
  have hsub_univ : (Set.univ : Set S).Countable := hsubfam.countable_univ hne
  -- Transport: countability of `Set.univ : Set S` ⇒ Countable S ⇒ Countable (↥S) ⇒ S.Countable.
  have : Countable S := Set.countable_univ_iff.mp hsub_univ
  exact Set.countable_coe_iff.mp this

/-- If `Function.support f ⊆ s`, then `∑' x : M, f x = ∑' x : s, f x.val`. -/
lemma tsum_subtype_eq_of_support_subset {s : Set M} {f : M → ℝ≥0∞}
    (h : Function.support f ⊆ s) :
    ∑' x : M, f x = ∑' x : s, f x.val := by
  classical
  rw [tsum_subtype s f]
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_contra hne
    exact hx (h hne)

/-- The pointwise `ENNReal` sum of POU values equals `1` on `univ`. -/
lemma tsum_ofReal_pou_eq_one
    (ρ' : SmoothPartitionOfUnity M I M univ) (x : M) :
    ∑' β : M, ENNReal.ofReal (ρ' β x) = 1 := by
  classical
  have hfinsupp_sum :
      ∑ β ∈ ρ'.finsupport x, ρ' β x = 1 :=
    SmoothPartitionOfUnity.sum_finsupport (ρ := ρ') (x₀ := x) (mem_univ x)
  rw [tsum_eq_sum (s := ρ'.finsupport x) (f := fun β => ENNReal.ofReal (ρ' β x))]
  · rw [show (∑ β ∈ ρ'.finsupport x, ENNReal.ofReal (ρ' β x))
            = ENNReal.ofReal (∑ β ∈ ρ'.finsupport x, ρ' β x) by
      rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => ρ'.nonneg β x)]]
    rw [hfinsupp_sum, ENNReal.ofReal_one]
  · intro β hβ
    rw [ρ'.mem_finsupport] at hβ
    simp only [Function.mem_support, ne_eq, not_not] at hβ
    rw [hβ, ENNReal.ofReal_zero]

/-- When `ρ α = 0` identically, the lintegral `∫⁻ ρ α * F dμ` is zero. -/
lemma lintegral_ofReal_pou_zero_of_support_empty
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M)
    (h : Function.support (ρ α) = ∅)
    (μ : MeasureTheory.Measure M) (F : M → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (ρ α x) * F x ∂μ = 0 := by
  have h_zero : ∀ x, ENNReal.ofReal (ρ α x) * F x = 0 := by
    intro x
    have : ρ α x = 0 := by
      by_contra hne
      have : x ∈ Function.support (ρ α) := hne
      rw [h] at this
      exact (Set.notMem_empty _) this
    rw [this, ENNReal.ofReal_zero, zero_mul]
  simp [h_zero]

/-- Restrict the α-sum to the countable support. -/
lemma tsum_integral_pou_eq_subtype
    [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M univ)
    (cLM : M → MeasureTheory.Measure M) (F : M → ℝ≥0∞) :
    (∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * F x ∂(cLM α)) =
      ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ x, ENNReal.ofReal (ρ α.val x) * F x ∂(cLM α.val) := by
  classical
  refine tsum_subtype_eq_of_support_subset (s := {α : M | (Function.support (ρ α)).Nonempty})
    (f := fun α => ∫⁻ x, ENNReal.ofReal (ρ α x) * F x ∂(cLM α)) ?_
  intro α hα
  simp only [Set.mem_setOf_eq]
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  exact hα (lintegral_ofReal_pou_zero_of_support_empty ρ α hne (cLM α) F)

/-- Expand `ρ α x * F x = ∑' β : Tρ', ρ α x * ρ' β x * F x` using the POU identity
over the countable support of `ρ'`. -/
lemma ofReal_pou_mul_expand_on_subtype
    [T2Space M] [SigmaCompactSpace M]
    (ρ ρ' : SmoothPartitionOfUnity M I M univ) (α : M)
    (F : M → ℝ≥0∞) (x : M) :
    ENNReal.ofReal (ρ α x) * F x =
      ∑' β : {β : M | (Function.support (ρ' β)).Nonempty},
        ENNReal.ofReal (ρ α x) * ENNReal.ofReal (ρ' β.val x) * F x := by
  classical
  have h_inner :
      (∑' β : {β : M | (Function.support (ρ' β)).Nonempty},
          ENNReal.ofReal (ρ α x) * ENNReal.ofReal (ρ' β.val x) * F x) =
        ENNReal.ofReal (ρ α x) *
          (∑' β : {β : M | (Function.support (ρ' β)).Nonempty},
            ENNReal.ofReal (ρ' β.val x)) * F x := by
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [ENNReal.tsum_mul_left]
  -- The subtype-tsum equals the full tsum (vanishing off the subset).
  have h_full :
      (∑' β : {β : M | (Function.support (ρ' β)).Nonempty},
        ENNReal.ofReal (ρ' β.val x)) =
      ∑' β : M, ENNReal.ofReal (ρ' β x) := by
    symm
    refine tsum_subtype_eq_of_support_subset (s := {β : M | (Function.support (ρ' β)).Nonempty})
      (f := fun β => ENNReal.ofReal (ρ' β x)) ?_
    intro β hβ
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hβ
    refine Set.nonempty_iff_ne_empty.mpr ?_
    intro h_empty
    have : ρ' β x = 0 := by
      by_contra hne
      have : x ∈ Function.support (ρ' β) := hne
      rw [h_empty] at this
      exact (Set.notMem_empty _) this
    linarith
  rw [h_inner, h_full, tsum_ofReal_pou_eq_one (I := I) ρ' x, mul_one]

/-- Substep E (final): the Riemannian measure is independent of the chosen
POU subordinate to the chart atlas. -/
theorem riemannianMeasure_eq_of_pou_independent
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ  : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianMeasure (I := I) g ρ' := by
  classical
  refine MeasureTheory.Measure.ext_of_lintegral _ (fun F hF => ?_)
  rw [riemannianMeasure_lintegral_eq (I := I) g ρ hF]
  rw [riemannianMeasure_lintegral_eq (I := I) g ρ' hF]
  -- Restrict sums to countable support.
  set Tρ : Set M := {α : M | (Function.support (ρ α)).Nonempty}
  set Tρ' : Set M := {β : M | (Function.support (ρ' β)).Nonempty}
  haveI hCρ : Countable Tρ :=
    (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
  haveI hCρ' : Countable Tρ' :=
    (countable_nonempty_support_of_pou (I := I) ρ').to_subtype
  rw [tsum_integral_pou_eq_subtype (I := I) ρ (chartLocalMeasure (I := I) g) F]
  rw [tsum_integral_pou_eq_subtype (I := I) ρ' (chartLocalMeasure (I := I) g) F]
  -- Step 1: Expand `ρ α * F` via ρ'-POU, pulling the ∑' inside the integral.
  have hLHS :
      (∑' α : Tρ, ∫⁻ x, ENNReal.ofReal (ρ α.val x) * F x
          ∂(chartLocalMeasure (I := I) g α.val)) =
        ∑' α : Tρ, ∑' β : Tρ', ∫⁻ x,
          ENNReal.ofReal (ρ α.val x) * ENNReal.ofReal (ρ' β.val x) * F x
            ∂(chartLocalMeasure (I := I) g α.val) := by
    refine tsum_congr (fun α => ?_)
    have hpt : (fun x : M => ENNReal.ofReal (ρ α.val x) * F x)
        = fun x => ∑' β : Tρ',
            ENNReal.ofReal (ρ α.val x) * ENNReal.ofReal (ρ' β.val x) * F x := by
      funext x
      exact ofReal_pou_mul_expand_on_subtype (I := I) ρ ρ' α.val F x
    rw [hpt]
    refine MeasureTheory.lintegral_tsum (fun β => ?_)
    refine (((ENNReal.measurable_ofReal.comp
      (ρ α.val).contMDiff.continuous.measurable).mul
      (ENNReal.measurable_ofReal.comp
        (ρ' β.val).contMDiff.continuous.measurable)).mul hF).aemeasurable
  -- Step 2: Expand `ρ' β * F` via ρ-POU.
  have hRHS :
      (∑' β : Tρ', ∫⁻ x, ENNReal.ofReal (ρ' β.val x) * F x
          ∂(chartLocalMeasure (I := I) g β.val)) =
        ∑' β : Tρ', ∑' α : Tρ, ∫⁻ x,
          ENNReal.ofReal (ρ α.val x) * ENNReal.ofReal (ρ' β.val x) * F x
            ∂(chartLocalMeasure (I := I) g β.val) := by
    refine tsum_congr (fun β => ?_)
    have hpt : (fun x : M => ENNReal.ofReal (ρ' β.val x) * F x)
        = fun x => ∑' α : Tρ,
            ENNReal.ofReal (ρ α.val x) * ENNReal.ofReal (ρ' β.val x) * F x := by
      funext x
      -- Mirror: expand via ρ-POU on the ρ-side.
      have := ofReal_pou_mul_expand_on_subtype (I := I) ρ' ρ β.val
        (fun x => F x) x
      -- `ρ' β.val * F = ∑' α : Tρ', ρ' β.val * ρ α.val * F` — but this uses
      -- Tρ' as the outer subtype. We want it over Tρ instead.
      -- Use the analogous expansion with roles swapped.
      have h_inner :
          (∑' α : Tρ,
              ENNReal.ofReal (ρ α.val x) * ENNReal.ofReal (ρ' β.val x) * F x) =
            (∑' α : Tρ, ENNReal.ofReal (ρ α.val x)) *
              ENNReal.ofReal (ρ' β.val x) * F x := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      have h_full :
          (∑' α : Tρ, ENNReal.ofReal (ρ α.val x)) =
            ∑' α : M, ENNReal.ofReal (ρ α x) := by
        symm
        refine tsum_subtype_eq_of_support_subset (s := Tρ)
          (f := fun α => ENNReal.ofReal (ρ α x)) ?_
        intro α hα
        simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
        refine Set.nonempty_iff_ne_empty.mpr ?_
        intro h_empty
        have : ρ α x = 0 := by
          by_contra hne
          have : x ∈ Function.support (ρ α) := hne
          rw [h_empty] at this
          exact (Set.notMem_empty _) this
        linarith
      rw [h_inner, h_full, tsum_ofReal_pou_eq_one (I := I) ρ x, one_mul]
    rw [hpt]
    refine MeasureTheory.lintegral_tsum (fun α => ?_)
    refine (((ENNReal.measurable_ofReal.comp
      (ρ α.val).contMDiff.continuous.measurable).mul
      (ENNReal.measurable_ofReal.comp
        (ρ' β.val).contMDiff.continuous.measurable)).mul hF).aemeasurable
  rw [hLHS, hRHS]
  -- Swap the double sum using `ENNReal.tsum_comm`.
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun β => ?_)
  refine tsum_congr (fun α => ?_)
  -- For each (α, β): apply Substep D.
  apply chartLocalMeasure_lintegral_eq_of_support_in_overlap (I := I) g α.val β.val
  · refine (((ENNReal.measurable_ofReal.comp
      (ρ α.val).contMDiff.continuous.measurable).mul
      (ENNReal.measurable_ofReal.comp
        (ρ' β.val).contMDiff.continuous.measurable)).mul hF)
  · exact pou_product_support_subset_overlap (I := I) ρ ρ' hρ hρ' α.val β.val F

/-- Atlas-independence wrapper: the glued Riemannian measure does not depend on the
choice of smooth partition of unity subordinate to the canonical chart atlas
`fun α ↦ (chartAt H α).source`. This is a renaming of the POU-independence theorem
in the language of the canonical Mathlib-level chart atlas. -/
theorem riemannianMeasure_independent_of_atlas
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ  : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianMeasure (I := I) g ρ' :=
  riemannianMeasure_eq_of_pou_independent (I := I) g ρ ρ' hρ hρ'

/-! ## Substep F corollary: Riemannian volume measure POU agreement -/

/-- The canonical Riemannian volume measure equals `riemannianMeasure` for any
POU subordinate to the chart atlas. -/
theorem riemannianMeasure_eq_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_eq_of_pou_independent (I := I) g ρ
    (chartAtlasPOU I M) hρ (chartAtlasPOU_isSubordinate I M)

end Volume
end Analysis
end RicciFlower
