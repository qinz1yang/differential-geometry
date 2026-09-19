import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Topology.Manifold.ClosedBall.ChartMap
import DifferentialGeometry.Geometry.Coordinates.Frame.ClosedBall
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m
local instance : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

theorem gramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN}
    (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    gramOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j (toEuclidean y) =
      g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN i) (chartModelBasis EuN j) := by
  let x := (extChartAt (𝓡∂ (m + 1)) α).symm y
  have hxval : x.val = closedCellShiftSucc m (-1) y :=
    extChartAt_closedCell_symm_val hα hy
  have hx : ‖x.val‖ < 1 := by
    rw [hxval]
    rwa [extChartAt_closedCell_target hα] at hy
  unfold gramOnEuclid
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [chartGramMatrix_apply, SmoothRiemannianMetric.pullback_inner]
  change g.inner x.val (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val x
    (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x))
    (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val x
      (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α j x)) = _
  rw [mfderiv_closedCell_inclusion_of_norm_lt_one hx]
  change g.inner x.val (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x)
    (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α j x) = _
  rw [chartBasisVecFiber_closedCell_of_norm_lt_one hα hx,
    chartBasisVecFiber_closedCell_of_norm_lt_one hα hx, hxval]

theorem densityOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target) :
    densityOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α
        (toEuclidean y) =
      Real.sqrt (Matrix.det (Matrix.of fun i j => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN i) (chartModelBasis EuN j))) := by
  rw [densityOnEuclid, chartDensity]
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  exact gramOnEuclid_closedCell_pullback g hα hy i j

theorem invGramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    invGramOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j
        (toEuclidean y) =
      (Matrix.of fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l))⁻¹ i j := by
  have hgram : (Matrix.of fun k l => gramOnEuclid
      (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
        (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α k l
          (toEuclidean y)) =
      Matrix.of (fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l)) := by
    ext k l
    exact gramOnEuclid_closedCell_pullback g hα hy k l
  exact congrArg (fun B : Matrix (Fin (Module.finrank ℝ EuN)) (Fin (Module.finrank ℝ EuN)) ℝ =>
    B⁻¹ i j) hgram

theorem weightedInvGramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    weightedInvGramOnEuclid
      (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
        (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j
          (toEuclidean y) =
      let B := Matrix.of fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l)
      Real.sqrt B.det * B⁻¹ i j := by
  rw [weightedInvGramOnEuclid, densityOnEuclid_closedCell_pullback g hα hy,
    invGramOnEuclid_closedCell_pullback g hα hy]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gramOnEuclid_closedCell_chart_pullback
    (g : SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] E)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) β).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    let h := g.pullback (I := 𝓡∂ (m + 1))
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis E)
      e.toAffineEquiv.linear.toLinearMap
    gramOnEuclid h β i j (toEuclidean y) =
      (C.transpose * Matrix.of (fun k l => gramOnEuclid g α k l
        (toEuclidean (e (closedCellShiftSucc m (-1) y)))) * C) i j := by
  intro h C
  let x := (extChartAt (𝓡∂ (m + 1)) β).symm y
  have hxval : x.val = closedCellShiftSucc m (-1) y := extChartAt_closedCell_symm_val hβ hy
  have hx : ‖x.val‖ < 1 := by
    rw [hxval]
    rwa [extChartAt_closedCell_target hβ] at hy
  have hp : (extChartAt I α).symm (e x.val) ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target (interior_subset (he x))
  have hrange : range I ∈ 𝓝 (e x.val) := Filter.mem_of_superset
    (mem_interior_iff_mem_nhds.mp (he x)) (extChartAt_target_subset_range α)
  have hsymm := TangentBundle.symmL_trivializationAt (I := I) hp
  rw [(extChartAt I α).right_inv (interior_subset (he x)),
    mfderivWithin_of_mem_nhds hrange] at hsymm
  have hvec (r : Fin (Module.finrank ℝ EuN)) :
      mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)
        (e.toContinuousAffineMap.contLinear (chartModelBasis EuN r)) =
      ∑ k, C k r • chartBasisVecFiber (I := I) α k ((extChartAt I α).symm (e x.val)) := by
    rw [← hsymm]
    simp only [chartBasisVecFiber, ← map_smul, ← map_sum]
    apply congrArg
    change e.toAffineEquiv.linear (chartModelBasis EuN r) = ∑ k, C k r • chartModelBasis E k
    simpa only [C, LinearMap.toMatrix_apply, LinearEquiv.coe_coe] using
      ((chartModelBasis E).sum_repr (e.toAffineEquiv.linear (chartModelBasis EuN r))).symm
  unfold gramOnEuclid
  rw [ContinuousLinearEquiv.symm_apply_apply, chartGramMatrix_apply,
    SmoothRiemannianMetric.pullback_inner]
  change g.inner ((extChartAt I α).symm (e x.val))
    (mfderiv (𝓡∂ (m + 1)) I
      (fun z : ClosedCell (m + 1) => (extChartAt I α).symm (e z.val)) x
        (chartBasisVecFiber (I := 𝓡∂ (m + 1)) β i x))
    (mfderiv (𝓡∂ (m + 1)) I
      (fun z : ClosedCell (m + 1) => (extChartAt I α).symm (e z.val)) x
        (chartBasisVecFiber (I := 𝓡∂ (m + 1)) β j x)) = _
  rw [mfderiv_extChartAt_symm_comp_affine_closedCell_of_norm_lt_one α e (he x) hx,
    chartBasisVecFiber_closedCell_of_norm_lt_one hβ hx,
    chartBasisVecFiber_closedCell_of_norm_lt_one hβ hx]
  change g.inner ((extChartAt I α).symm (e x.val))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)
      (e.toContinuousAffineMap.contLinear (chartModelBasis EuN i)))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)
      (e.toContinuousAffineMap.contLinear (chartModelBasis EuN j))) = _
  rw [hvec i, hvec j]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [hxval]
  simp only [ContinuousLinearEquiv.symm_apply_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, chartGramMatrix_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem densityOnEuclid_closedCell_chart_pullback
    (g : SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] E)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) β).target) :
    let h := g.pullback (I := 𝓡∂ (m + 1))
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis E)
      e.toAffineEquiv.linear.toLinearMap
    let B := C.transpose * Matrix.of (fun k l => gramOnEuclid g α k l
      (toEuclidean (e (closedCellShiftSucc m (-1) y)))) * C
    densityOnEuclid h β (toEuclidean y) = Real.sqrt B.det := by
  intro h C B
  rw [densityOnEuclid, DifferentialGeometry.Integral.Measure.chartDensity]
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  exact gramOnEuclid_closedCell_chart_pullback g α e he hβ hy i j

theorem invGramOnEuclid_closedCell_chart_pullback
    (g : SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] E)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) β).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    let h := g.pullback (I := 𝓡∂ (m + 1))
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis E)
      e.toAffineEquiv.linear.toLinearMap
    let B := C.transpose * Matrix.of (fun k l => gramOnEuclid g α k l
      (toEuclidean (e (closedCellShiftSucc m (-1) y)))) * C
    invGramOnEuclid h β i j (toEuclidean y) = B⁻¹ i j := by
  intro h C B
  have hgram : Matrix.of (fun k l => gramOnEuclid h β k l (toEuclidean y)) = B := by
    ext k l
    exact gramOnEuclid_closedCell_chart_pullback g α e he hβ hy k l
  exact congrArg (fun A : Matrix (Fin (Module.finrank ℝ EuN)) (Fin (Module.finrank ℝ EuN)) ℝ =>
    A⁻¹ i j) hgram

theorem weightedInvGramOnEuclid_closedCell_chart_pullback
    (g : SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] E)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) β).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    let h := g.pullback (I := 𝓡∂ (m + 1))
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis E)
      e.toAffineEquiv.linear.toLinearMap
    let B := C.transpose * Matrix.of (fun k l => gramOnEuclid g α k l
      (toEuclidean (e (closedCellShiftSucc m (-1) y)))) * C
    weightedInvGramOnEuclid h β i j (toEuclidean y) = Real.sqrt B.det * B⁻¹ i j := by
  intro h C B
  rw [weightedInvGramOnEuclid, densityOnEuclid_closedCell_chart_pullback g α e he hβ hy,
    invGramOnEuclid_closedCell_chart_pullback g α e he hβ hy]

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
