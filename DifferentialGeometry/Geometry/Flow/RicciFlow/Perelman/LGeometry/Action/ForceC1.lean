import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Force

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lChartPosRep
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) :
    E →L[Real] Real :=
  ∑ i : Fin (Module.finrank Real E),
    (inner Real
        (((1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p)
            (T - (a + r) ^ 2, u.toFun r))
            (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
        (q r) +
      2 * (a + r) ^ 2 *
        chartScalCov (I := I) S p (T - (a + r) ^ 2, u.toFun r)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) •
      chartCoordCLM E i

noncomputable def lChartForceRep
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) : E :=
  (lChartPosRep (I := I) S T a p u q r).adjoint 1

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem chartScalCov_basis
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (p : M)
    (z : Real × E)
    (hz : z ∈ D.regular ×ˢ interior (extChartAt I p).target)
    (i : Fin (Module.finrank Real E)) :
    chartScalCov (I := I) S p z (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) =
      let x := (extChartAt I p).symm z.2
      mvfderiv (I := I) (S.scalar z.1) x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i x) := by
  let f : M → Real := S.scalar z.1
  let x : M := (extChartAt I p).symm z.2
  have hzt : z.2 ∈ (extChartAt I p).target := interior_subset hz.2
  have hxsrc : x ∈ (chartAt H p).source := by
    have hxext : x ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hzt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hright : extChartAt I p x = z.2 :=
    (extChartAt I p).right_inv hzt
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    simpa only [f] using scalarSmoothOfSol (I := I) S z.1
  rw [chartScalCov_apply (I := I) S hS p hz.1 hz.2]
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (I := I) p (hf.mdifferentiableAt (by simp)) hxsrc
      (by simpa only [hright] using hz.2) i]
  simp only [partialDeriv, hright, f, x]
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartForceRep_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : ContinuousOn q (Icc (0 : Real) L)) :
    ContinuousOn (lChartForceRep (I := I) S T a p u q)
      (Icc (0 : Real) L) := by
  classical
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I p).target
  have htau : ContinuousOn tau (Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r))
      (Icc (0 : Real) L) := htau.prodMk u.continuousOn_toFun
  have hpair_mem : MapsTo (fun r ↦ (tau r, u.toFun r))
      (Icc (0 : Real) L) U := by
    intro r hr
    exact ⟨hreg r hr, hchart hr⟩
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hGram : ContDiffOn Real ∞
      (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hGramFd : ContinuousOn
      (fderiv Real (chartGramOp (I := I) S.family p)) U :=
    hGram.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hScal : ContinuousOn (chartScalCov (I := I) S p) U := by
    simpa only [U] using (chartScalCov_smooth (I := I) S hS p).continuousOn
  have hcoord (i : Fin (Module.finrank Real E)) : ContinuousOn
      (fun r ↦
        inner Real
          (((1 / 2 : Real) •
            (fderiv Real (chartGramOp (I := I) S.family p)
              (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
          (q r) +
        2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p (tau r, u.toFun r)
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
      (Icc (0 : Real) L) := by
    have hdir : ContinuousOn
        (fun z ↦ (1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p) z)
            (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) U :=
      by
        have hvec : ContinuousOn
            (fun _ : Real × E ↦ ((0 : Real), DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) U :=
          continuousOn_const
        have h := (hGramFd.clm_apply hvec).const_smul (1 / 2 : Real)
        with_unfolding_all exact h
    have hdir' : ContinuousOn
        (fun r ↦ (1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p)
            (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
        (Icc (0 : Real) L) := hdir.comp hpair hpair_mem
    have hkin : ContinuousOn
        (fun r ↦ inner Real
          (((1 / 2 : Real) •
            (fderiv Real (chartGramOp (I := I) S.family p)
              (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
          (q r)) (Icc (0 : Real) L) :=
      (hdir'.clm_apply hq).inner (𝕜 := Real) hq
    have hscal : ContinuousOn
        (fun r ↦ chartScalCov (I := I) S p (tau r, u.toFun r)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (Icc (0 : Real) L) :=
      (hScal.comp hpair hpair_mem).clm_apply continuousOn_const
    exact hkin.add
      ((continuousOn_const.mul
        ((continuousOn_const.add continuousOn_id).pow 2)).mul hscal)
  have hpos : ContinuousOn
      (lChartPosRep (I := I) S T a p u q) (Icc (0 : Real) L) := by
    with_unfolding_all exact
      continuousOn_finsetSum Finset.univ fun i _ ↦
        (hcoord i).smul continuousOn_const
  have hadj : Continuous
      (fun A : E →L[Real] Real ↦ A.adjoint (1 : Real)) :=
    (ContinuousLinearMap.adjoint (E := E) (F := Real)).continuous.clm_apply
      continuous_const
  with_unfolding_all exact hadj.comp_continuousOn hpos

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartForceRep_ae
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : u.deriv =ᵐ[timeMeasure L] q) :
    lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartForceRep (I := I) S T a p u q := by
  classical
  filter_upwards [hq, ae_restrict_mem measurableSet_Icc] with r hrq hr
  have hz : (T - (a + r) ^ 2, u.toFun r) ∈
      D.regular ×ˢ interior (extChartAt I p).target :=
    ⟨hreg r hr, hchart hr⟩
  have hscal := chartScalCov_basis (I := I) S hS p
    (T - (a + r) ^ 2, u.toFun r) hz
  have hpos : lChartPosDeriv (I := I) S T a p u r =
      lChartPosRep (I := I) S T a p u q r := by
    rw [lChartPosDeriv, lChartPosRep]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrq, hscal i]
    rfl
  rw [lChartForce, lChartForceRep, hpos]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
