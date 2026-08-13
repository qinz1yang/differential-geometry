import DifferentialGeometry.Analysis.Calculus.PartialDerivIteratedFDerivOrderBridge
import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.ParabolicChart
import DifferentialGeometry.Analysis.Schauder.Scaling
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Curvature.Realized.Operators

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem parabolicGradientComponent_euclideanChartRepresentation
    (alpha : M) (u : Real → M → Real)
    (k : Fin (Module.finrank Real E)) (p : ParabolicPoint (EuclN E)) :
    parabolicGradientComponent
        (parabolicEuclideanChartRepresentation I alpha u) k p =
      partialDeriv (E := E) k (scalarOnE (I := I) alpha (u p.time))
        ((toEuclidean (E := E)).symm p.space) := by
  let w : Real → E → Real := fun t y ↦ scalarOnE (I := I) alpha (u t) y
  have hjet := parabolicSpatialJet_linearEquiv
    (toEuclidean (E := E)).symm w 1 p
  unfold parabolicGradientComponent
  rw [show parabolicSpatialJet 1
      (parabolicEuclideanChartRepresentation I alpha u) p =
        (parabolicSpatialJet 1 w
          (parabolicLinearMap
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E) p)).compContinuousLinearMap
              (fun _ ↦ ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)) by
    exact hjet]
  simp only [continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  calc
    _ = (parabolicSpatialJet 1 w
          (parabolicLinearMap
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E) p))
        ![(toEuclidean (E := E)).symm
          (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real k)] := by
      congr 1
      funext q
      fin_cases q
      rfl
    _ = _ := by
      change iteratedFDeriv Real 1 (w p.time)
        ((toEuclidean (E := E)).symm p.space)
        ![(toEuclidean (E := E)).symm
          (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real k)] = _
      rw [show (toEuclidean (E := E)).symm
          (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real k) =
            chartModelBasis E k by
        rw [EuclideanSpace.basisFun_apply, chartModelBasis_apply]]
      exact (DifferentialGeometry.Analysis.Calculus.partialDeriv_eq_iteratedFDeriv_one
        (scalarOnE (I := I) alpha (u p.time)) k
          ((toEuclidean (E := E)).symm p.space)).symm

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem parabolicHessianComponent_euclideanChartRepresentation
    (alpha : M) (u : Real → M → Real)
    (i j : Fin (Module.finrank Real E)) (p : ParabolicPoint (EuclN E))
    (hu : ContDiffAt Real ∞ (scalarOnE (I := I) alpha (u p.time))
      ((toEuclidean (E := E)).symm p.space)) :
    parabolicHessianComponent
        (parabolicEuclideanChartRepresentation I alpha u) i j p =
      partialDeriv (E := E) i
        (partialDeriv (E := E) j (scalarOnE (I := I) alpha (u p.time)))
        ((toEuclidean (E := E)).symm p.space) := by
  let w : Real → E → Real := fun t y ↦ scalarOnE (I := I) alpha (u t) y
  have hjet := parabolicSpatialJet_linearEquiv
    (toEuclidean (E := E)).symm w 2 p
  unfold parabolicHessianComponent
  rw [show parabolicSpatialJet 2
      (parabolicEuclideanChartRepresentation I alpha u) p =
        (parabolicSpatialJet 2 w
          (parabolicLinearMap
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E) p)).compContinuousLinearMap
              (fun _ ↦ ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)) by
    exact hjet]
  simp only [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryRightEquiv_apply',
    continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  calc
    _ = (parabolicSpatialJet 2 w
          (parabolicLinearMap
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E) p))
        ![(toEuclidean (E := E)).symm
            (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real i),
          (toEuclidean (E := E)).symm
            (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real j)] := by
      congr 1
      funext q
      fin_cases q <;> rfl
    _ = _ := by
      change iteratedFDeriv Real 2 (w p.time)
        ((toEuclidean (E := E)).symm p.space)
        ![(toEuclidean (E := E)).symm
            (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real i),
          (toEuclidean (E := E)).symm
            (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real j)] = _
      rw [show (toEuclidean (E := E)).symm
          (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real i) =
            chartModelBasis E i by
        rw [EuclideanSpace.basisFun_apply, chartModelBasis_apply]]
      rw [show (toEuclidean (E := E)).symm
          (EuclideanSpace.basisFun (Fin (Module.finrank Real E)) Real j) =
            chartModelBasis E j by
        rw [EuclideanSpace.basisFun_apply, chartModelBasis_apply]]
      exact (DifferentialGeometry.Analysis.Calculus.partialDeriv_partialDeriv_eq_iteratedFDeriv_two
        (scalarOnE (I := I) alpha (u p.time)) hu i j).symm

def euclideanChartPoint
    (alpha : M) (p : ParabolicPoint (EuclN E)) : M :=
  (extChartAt I alpha).symm ((toEuclidean (E := E)).symm p.space)

def parabolicChartPrincipalCoefficient
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (i j : Fin (Module.finrank Real E)) :
    ParabolicPoint (EuclN E) → Real :=
  fun p ↦ chartInvGramMatrix (I := I) (g p.time) alpha
    (euclideanChartPoint (I := I) alpha p) i j

def parabolicChartChristoffelCoefficient
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (i j k : Fin (Module.finrank Real E)) :
    ParabolicPoint (EuclN E) → Real :=
  fun p ↦ chartChristoffel (I := I) (g p.time) alpha i j k
    ((toEuclidean (E := E)).symm p.space)

def parabolicChartDriftCoefficient
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (k : Fin (Module.finrank Real E)) :
    ParabolicPoint (EuclN E) → Real :=
  fun p ↦ -∑ i, ∑ j,
    parabolicChartPrincipalCoefficient (I := I) g alpha i j p *
      parabolicChartChristoffelCoefficient (I := I) g alpha i j k p

def parabolicChartPotentialCoefficient
    (V : Real → M → Real) (alpha : M) :
    ParabolicPoint (EuclN E) → Real :=
  fun p ↦ V p.time (euclideanChartPoint (I := I) alpha p)

def parabolicNondivergenceOperatorInEuclideanChart
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (alpha : M) (u : Real → M → Real) :
    ParabolicPoint (EuclN E) → Real :=
  parabolicNondivergenceOperator
    (parabolicChartPrincipalCoefficient (I := I) g alpha)
    (parabolicChartDriftCoefficient (I := I) g alpha)
    (parabolicChartPotentialCoefficient (I := I) V alpha)
    (parabolicEuclideanChartRepresentation I alpha u)

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
@[simp]
theorem euclideanChartPoint_apply
    (alpha : M) (p : ParabolicPoint (EuclN E)) :
    euclideanChartPoint (I := I) alpha p =
      (extChartAt I alpha).symm ((toEuclidean (E := E)).symm p.space) :=
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp]
theorem parabolicChartPrincipalCoefficient_apply
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (i j : Fin (Module.finrank Real E)) (p : ParabolicPoint (EuclN E)) :
    parabolicChartPrincipalCoefficient (I := I) g alpha i j p =
      chartInvGramMatrix (I := I) (g p.time) alpha
        (euclideanChartPoint (I := I) alpha p) i j :=
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp]
theorem parabolicChartChristoffelCoefficient_apply
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (i j k : Fin (Module.finrank Real E)) (p : ParabolicPoint (EuclN E)) :
    parabolicChartChristoffelCoefficient (I := I) g alpha i j k p =
      chartChristoffel (I := I) (g p.time) alpha i j k
        ((toEuclidean (E := E)).symm p.space) :=
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp]
theorem parabolicChartDriftCoefficient_apply
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (k : Fin (Module.finrank Real E)) (p : ParabolicPoint (EuclN E)) :
    parabolicChartDriftCoefficient (I := I) g alpha k p =
      -∑ i, ∑ j,
        parabolicChartPrincipalCoefficient (I := I) g alpha i j p *
          parabolicChartChristoffelCoefficient (I := I) g alpha i j k p :=
  rfl

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
@[simp]
theorem parabolicChartPotentialCoefficient_apply
    (V : Real → M → Real) (alpha : M) (p : ParabolicPoint (EuclN E)) :
    parabolicChartPotentialCoefficient (I := I) V alpha p =
      V p.time (euclideanChartPoint (I := I) alpha p) :=
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp]
theorem parabolicNondivergenceOperatorInEuclideanChart_apply
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (alpha : M) (u : Real → M → Real) (p : ParabolicPoint (EuclN E)) :
    parabolicNondivergenceOperatorInEuclideanChart (I := I)
        g V alpha u p =
      parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficient (I := I) g alpha)
        (parabolicChartDriftCoefficient (I := I) g alpha)
        (parabolicChartPotentialCoefficient (I := I) V alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p :=
  rfl

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem euclideanChartPoint_mem_source
    (alpha : M) (p : ParabolicPoint (EuclN E))
    (hp : (toEuclidean (E := E)).symm p.space ∈ (extChartAt I alpha).target) :
    euclideanChartPoint (I := I) alpha p ∈ (chartAt H alpha).source := by
  rw [← extChartAt_source (I := I) alpha]
  exact (extChartAt I alpha).map_target hp

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem extChartAt_euclideanChartPoint
    (alpha : M) (p : ParabolicPoint (EuclN E))
    (hp : (toEuclidean (E := E)).symm p.space ∈ (extChartAt I alpha).target) :
    extChartAt I alpha (euclideanChartPoint (I := I) alpha p) =
      (toEuclidean (E := E)).symm p.space := by
  exact (extChartAt I alpha).right_inv hp

omit [NeZero (Module.finrank Real E)] in
theorem parabolicVariableMatrixLap_euclideanChartRepresentation
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (u : Real → M → Real) (p : ParabolicPoint (EuclN E))
    (hu : ContDiffAt Real ∞ (scalarOnE (I := I) alpha (u p.time))
      ((toEuclidean (E := E)).symm p.space)) :
    parabolicVariableMatrixLap (parabolicChartPrincipalCoefficient (I := I) g alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p =
      ∑ i, ∑ j, parabolicChartPrincipalCoefficient (I := I) g alpha i j p *
        partialDeriv (E := E) i
          (partialDeriv (E := E) j (scalarOnE (I := I) alpha (u p.time)))
          ((toEuclidean (E := E)).symm p.space) := by
  classical
  unfold parabolicVariableMatrixLap matrixLap
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change parabolicChartPrincipalCoefficient (I := I) g alpha i j p *
      parabolicHessianComponent
        (parabolicEuclideanChartRepresentation I alpha u) i j p = _
  rw [parabolicHessianComponent_euclideanChartRepresentation (I := I) alpha u i j p hu]

omit [NeZero (Module.finrank Real E)] in
theorem parabolicDriftTerm_euclideanChartRepresentation
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (u : Real → M → Real) (p : ParabolicPoint (EuclN E)) :
    parabolicDriftTerm (parabolicChartDriftCoefficient (I := I) g alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p =
      -∑ i, ∑ j,
        parabolicChartPrincipalCoefficient (I := I) g alpha i j p *
          (∑ k, parabolicChartChristoffelCoefficient (I := I) g alpha i j k p *
            partialDeriv (E := E) k (scalarOnE (I := I) alpha (u p.time))
              ((toEuclidean (E := E)).symm p.space)) := by
  classical
  unfold parabolicDriftTerm parabolicChartDriftCoefficient
  simp_rw [parabolicGradientComponent_euclideanChartRepresentation (I := I) alpha u]
  simp only [smul_eq_mul, neg_mul]
  rw [Finset.sum_neg_distrib]
  apply neg_inj.mpr
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem parabolicTimeDerivative_euclideanChartRepresentation
    (alpha : M) (u : Real → M → Real) (p : ParabolicPoint (EuclN E)) :
    parabolicTimeDerivative
        (parabolicEuclideanChartRepresentation I alpha u) p =
      fderiv Real (fun t ↦ u t (euclideanChartPoint (I := I) alpha p)) p.time 1 := by
  rfl

omit [NeZero (Module.finrank Real E)] [IsManifold I ∞ M] in
theorem parabolicPotentialTerm_euclideanChartRepresentation
    (V : Real → M → Real) (alpha : M) (u : Real → M → Real)
    (p : ParabolicPoint (EuclN E)) :
    parabolicPotentialTerm (parabolicChartPotentialCoefficient (I := I) V alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p =
      V p.time (euclideanChartPoint (I := I) alpha p) *
        u p.time (euclideanChartPoint (I := I) alpha p) := by
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem parabolicVariableMatrixLap_add_driftTerm_eq_laplacian_in_euclideanChart
    [I.Boundaryless] [T2Space M]
    (g : Real → SmoothRiemannianMetric I M) (alpha : M)
    (u : Real → M → Real) (p : ParabolicPoint (EuclN E))
    (hu : ContMDiff I 𝓘(Real, Real) ∞ (u p.time))
    (hp : (toEuclidean (E := E)).symm p.space ∈ (extChartAt I alpha).target) :
    parabolicVariableMatrixLap (parabolicChartPrincipalCoefficient (I := I) g alpha)
          (parabolicEuclideanChartRepresentation I alpha u) p +
        parabolicDriftTerm (parabolicChartDriftCoefficient (I := I) g alpha)
          (parabolicEuclideanChartRepresentation I alpha u) p =
      laplacian (I := I) (LeviCivita (I := I) (g p.time)) (g p.time)
        (u p.time) (euclideanChartPoint (I := I) alpha p) := by
  classical
  have hcoord : ContDiffAt Real ∞ (scalarOnE (I := I) alpha (u p.time))
      ((toEuclidean (E := E)).symm p.space) :=
    (scalarOnE_contDiffOn (I := I) alpha hu).contDiffAt
      ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hp)
  rw [parabolicVariableMatrixLap_euclideanChartRepresentation (I := I) g alpha u p hcoord,
    parabolicDriftTerm_euclideanChartRepresentation (I := I) g alpha u p,
    laplacian_eq_chart_hessian_trace (I := I) (g p.time) alpha hu
      (euclideanChartPoint_mem_source (I := I) alpha p hp)]
  simp_rw [chartHessianTensor_def, chartIteratedPartialDeriv_def,
    extChartAt_euclideanChartPoint (I := I) alpha p hp]
  unfold parabolicChartPrincipalCoefficient parabolicChartChristoffelCoefficient
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

omit [NeZero (Module.finrank Real E)] in
theorem parabolicNondivergenceOperator_eq_intrinsic_in_euclideanChart
    [I.Boundaryless] [T2Space M]
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (alpha : M) (u : Real → M → Real) (p : ParabolicPoint (EuclN E))
    (hu : ContMDiff I 𝓘(Real, Real) ∞ (u p.time))
    (hp : (toEuclidean (E := E)).symm p.space ∈ (extChartAt I alpha).target) :
    parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficient (I := I) g alpha)
        (parabolicChartDriftCoefficient (I := I) g alpha)
        (parabolicChartPotentialCoefficient (I := I) V alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p =
      fderiv Real (fun t ↦ u t (euclideanChartPoint (I := I) alpha p)) p.time 1 -
        laplacian (I := I) (LeviCivita (I := I) (g p.time)) (g p.time)
          (u p.time) (euclideanChartPoint (I := I) alpha p) -
        V p.time (euclideanChartPoint (I := I) alpha p) *
          u p.time (euclideanChartPoint (I := I) alpha p) := by
  rw [show parabolicNondivergenceOperator
      (parabolicChartPrincipalCoefficient (I := I) g alpha)
      (parabolicChartDriftCoefficient (I := I) g alpha)
      (parabolicChartPotentialCoefficient (I := I) V alpha)
      (parabolicEuclideanChartRepresentation I alpha u) p =
        parabolicTimeDerivative
            (parabolicEuclideanChartRepresentation I alpha u) p -
          (parabolicVariableMatrixLap (parabolicChartPrincipalCoefficient (I := I) g alpha)
              (parabolicEuclideanChartRepresentation I alpha u) p +
            parabolicDriftTerm (parabolicChartDriftCoefficient (I := I) g alpha)
              (parabolicEuclideanChartRepresentation I alpha u) p) -
          parabolicPotentialTerm (parabolicChartPotentialCoefficient (I := I) V alpha)
            (parabolicEuclideanChartRepresentation I alpha u) p by
    unfold parabolicNondivergenceOperator parabolicVariableMatrixOperator
      parabolicLowerOrderTerm
    simp only [Pi.sub_apply, Pi.add_apply]
    abel]
  rw [parabolicTimeDerivative_euclideanChartRepresentation (I := I) alpha u p,
    parabolicVariableMatrixLap_add_driftTerm_eq_laplacian_in_euclideanChart
      (I := I) g alpha u p hu hp,
    parabolicPotentialTerm_euclideanChartRepresentation (I := I) V alpha u p]

omit [NeZero (Module.finrank Real E)] in
theorem parabolicNondivergenceOperatorInEuclideanChart_eq_intrinsic
    [I.Boundaryless] [T2Space M]
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (alpha : M) (u : Real → M → Real) (p : ParabolicPoint (EuclN E))
    (hu : ContMDiff I 𝓘(Real, Real) ∞ (u p.time))
    (hp : (toEuclidean (E := E)).symm p.space ∈
      (extChartAt I alpha).target) :
    parabolicNondivergenceOperatorInEuclideanChart (I := I)
        g V alpha u p =
      fderiv Real (fun t ↦ u t (euclideanChartPoint (I := I) alpha p))
          p.time 1 -
        laplacian (I := I) (LeviCivita (I := I) (g p.time)) (g p.time)
          (u p.time) (euclideanChartPoint (I := I) alpha p) -
        V p.time (euclideanChartPoint (I := I) alpha p) *
          u p.time (euclideanChartPoint (I := I) alpha p) := by
  exact parabolicNondivergenceOperator_eq_intrinsic_in_euclideanChart
    (I := I) g V alpha u p hu hp

omit [NeZero (Module.finrank Real E)] in
theorem parabolicNondivergenceOperator_euclideanChartRepresentation_eq_laplacianAt
    [I.Boundaryless] [T2Space M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (V : Real → M → Real) (alpha : M) (u : Real → M → Real)
    (p : ParabolicPoint (EuclN E))
    (hu : ContMDiff I 𝓘(Real, Real) ∞ (u p.time))
    (hp : (toEuclidean (E := E)).symm p.space ∈ (extChartAt I alpha).target)
    (hconn : G.connection p.time = LeviCivita (I := I) (G.metric p.time)) :
    parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficient (I := I) G.metric alpha)
        (parabolicChartDriftCoefficient (I := I) G.metric alpha)
        (parabolicChartPotentialCoefficient (I := I) V alpha)
        (parabolicEuclideanChartRepresentation I alpha u) p =
      fderiv Real (fun t ↦ u t (euclideanChartPoint (I := I) alpha p)) p.time 1 -
        laplacianAt (I := I) G p.time (u p.time)
          (euclideanChartPoint (I := I) alpha p) -
        V p.time (euclideanChartPoint (I := I) alpha p) *
          u p.time (euclideanChartPoint (I := I) alpha p) := by
  rw [parabolicNondivergenceOperator_eq_intrinsic_in_euclideanChart
    (I := I) G.metric V alpha u p hu hp]
  unfold laplacianAt
  rw [hconn]

end DifferentialGeometry.Analysis.Schauder
