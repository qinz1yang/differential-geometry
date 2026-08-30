import DifferentialGeometry.Geometry.Boundary.OutwardNormal
import DifferentialGeometry.Geometry.Operator.Hessian
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def normalFieldComp (νChart : E → E) (k : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => ((Module.finBasis ℝ E).repr (νChart y)) k

@[simp] lemma normalFieldComp_def (νChart : E → E)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    normalFieldComp (E := E) νChart k y =
      ((Module.finBasis ℝ E).repr (νChart y)) k := rfl

def chartChristoffelNormalCorrection
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    chartChristoffel (I := I) g α i l k y *
      normalFieldComp (E := E) νChart l y

omit hI in
@[simp] lemma chartChristoffelNormalCorrection_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffelNormalCorrection (I := I) g α νChart i k y =
      ∑ l : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i l k y *
          normalFieldComp (E := E) νChart l y := rfl

def chartCovariantDerivativeOfNormal
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (normalFieldComp (E := E) νChart k) y +
    chartChristoffelNormalCorrection (I := I) g α νChart i k y

omit hI in
@[simp] lemma chartCovariantDerivativeOfNormal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartCovariantDerivativeOfNormal (I := I) g α νChart i k y =
      partialDeriv (E := E) i (normalFieldComp (E := E) νChart k) y +
        chartChristoffelNormalCorrection (I := I) g α νChart i k y := rfl

def chartSecondFundamentalFormEntry
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g (x : M) (x : M) k j *
      chartCovariantDerivativeOfNormal (I := I) g (x : M) νChart i k
        (extChartAt I (x : M) (x : M))

omit hI in
@[simp] lemma chartSecondFundamentalFormEntry_def
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) (i j : Fin (Module.finrank ℝ E)) :
    chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
      ∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g (x : M) (x : M) k j *
          chartCovariantDerivativeOfNormal (I := I) g (x : M) νChart i k
            (extChartAt I (x : M) (x : M)) := rfl

def secondFundamentalForm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) :
    TangentSpace I (x : M) →ₗ[ℝ] TangentSpace I (x : M) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j)
    (fun X₁ X₂ Y => by
      classical
      have hrepr : (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr (X₁ + X₂) =
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X₁ +
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X₂ :=
        map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c X Y => by
      classical
      have hrepr : (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr (c • X) =
          c • (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)
    (fun X Y₁ Y₂ => by
      classical
      have hrepr : (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr (Y₁ + Y₂) =
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y₁ +
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y₂ :=
        map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c X Y => by
      classical
      have hrepr : (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr (c • Y) =
          c • (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hpull : ∀ j : Fin (Module.finrank ℝ E),
          (((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
              (c * ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j) *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) =
          c * (((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
              ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) := by
        intro j
        ring
      rw [show (∑ j : Fin (Module.finrank ℝ E),
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
                (c * ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j) *
              chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) =
          ∑ j : Fin (Module.finrank ℝ E),
            c * (((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
                ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j *
              chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) from
        Finset.sum_congr rfl (fun j _ => hpull j)]
      rw [← Finset.mul_sum])

omit hI in
@[simp] lemma secondFundamentalForm_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (X Y : TangentSpace I (x : M)) :
    secondFundamentalForm (I := I) (M := M) g x νChart X Y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr X) i *
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) (x : M)).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j := rfl

omit hI in
theorem secondFundamentalForm_symm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (h_codazzi : ∀ i j : Fin (Module.finrank ℝ E),
      chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
        chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart j i)
    (X Y : TangentSpace I (x : M)) :
    secondFundamentalForm (I := I) (M := M) g x νChart X Y =
      secondFundamentalForm (I := I) (M := M) g x νChart Y X := by
  classical
  rw [secondFundamentalForm_apply, secondFundamentalForm_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_codazzi j i]
  ring

def secondFundamentalFormBoundary
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (Xb Yb : hI.boundaryE) : ℝ :=
  secondFundamentalForm (I := I) (M := M) g x νChart
    (boundaryInclusionMfderiv (M := M) x Xb) (boundaryInclusionMfderiv (M := M) x Yb)

@[simp] lemma secondFundamentalFormBoundary_def
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (Xb Yb : hI.boundaryE) :
    secondFundamentalFormBoundary (I := I) (M := M) g x νChart Xb Yb =
      secondFundamentalForm (I := I) (M := M) g x νChart
        (boundaryInclusionMfderiv (M := M) x Xb) (boundaryInclusionMfderiv (M := M) x Yb) := rfl

theorem secondFundamentalFormBoundary_symm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (h_codazzi : ∀ i j : Fin (Module.finrank ℝ E),
      chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
        chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart j i)
    (Xb Yb : hI.boundaryE) :
    secondFundamentalFormBoundary (I := I) (M := M) g x νChart Xb Yb =
      secondFundamentalFormBoundary (I := I) (M := M) g x νChart Yb Xb := by
  unfold secondFundamentalFormBoundary
  exact secondFundamentalForm_symm (I := I) (M := M) g x νChart h_codazzi
    (boundaryInclusionMfderiv (M := M) x Xb) (boundaryInclusionMfderiv (M := M) x Yb)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
