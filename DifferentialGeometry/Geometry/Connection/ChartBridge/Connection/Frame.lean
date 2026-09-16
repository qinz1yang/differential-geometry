import DifferentialGeometry.Geometry.Coordinates.Connection.ChangeOfBasis
import DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

open Geometry.Connection Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [I.Boundaryless]

theorem christoffelSymbolInFrame_chartBasisVecFiber
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j k : Fin (Module.finrank ℝ E)) :
    christoffelSymbolInFrame (LeviCivita (I := I) g)
      (chartBasisVecFiber (I := I) α) (chartBasisVecFiber_isLocalFrame α) x i j k =
      chartChristoffel g α i j k (extChartAt I α x) := by
  classical
  have hx' := chartLeviCivitaGoodSet_mem_baseSet hx
  let hframe := chartBasisVecFiber_isLocalFrame (I := I) α
  unfold christoffelSymbolInFrame
  rw [LeviCivita_chartBasisVec_alpha_basis_apply g α i j hx]
  change hframe.coeff k x _ = _
  have hcoeff (r : Fin (Module.finrank ℝ E)) :
      hframe.coeff k x (chartBasisVecFiber (I := I) α r x) =
        if r = k then 1 else 0 := by
    rw [IsLocalFrameOn.coeff, dif_pos hx', ← hframe.toBasisAt_coe hx' r]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [map_sum, map_smul, smul_eq_mul, hcoeff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem chartChristoffel_eq_sum_coordinateFrame
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) α)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel g α i j k (extChartAt I α x) =
      ∑ a, ∑ d, ∑ m,
        ((Module.finBasis ℝ E).repr (chartModelBasis E j) a *
          (Module.finBasis ℝ E).repr (chartModelBasis E i) d *
          (chartModelBasis E).repr (Module.finBasis ℝ E m) k) *
        christoffelSymbolInFrame (LeviCivita (I := I) g)
          (coordinateFrameAt (I := I) α) (coordinateFrameAt_isLocalFrame_one α)
          x d a m := by
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source, extChartAt_source]
    exact hx
  have hmodel : christoffelSymbolInFrame (LeviCivita (I := I) g)
      ((trivializationAt E (TangentSpace I) α).localFrame (chartModelBasis E))
      ((trivializationAt E (TangentSpace I) α).isLocalFrameOn_localFrame_baseSet
        I 1 (chartModelBasis E)) x i j k =
      chartChristoffel g α i j k (extChartAt I α x) := by
    simpa only [chartBasisVecFiber_eq_localFrame] using
      christoffelSymbolInFrame_chartBasisVecFiber g α hxgood i j k
  rw [← hmodel]
  exact christoffelSymbolInFrame_change_basis (LeviCivita (I := I) g)
    (trivializationAt E (TangentSpace I) α) (Module.finBasis ℝ E) (chartModelBasis E)
    (chartLeviCivitaGoodSet_mem_baseSet hxgood) i j k

end DifferentialGeometry.Tensor.Coordinates
