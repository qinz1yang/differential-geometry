import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.EulerLagrange
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramSmooth

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private noncomputable def lGramDir
    (S : SolutionOn (I := I) (M := M) D) (p : M)
    (i : Fin (Module.finrank Real E)) (q : Real × E) : E →L[Real] E :=
  (1 / 2 : Real) •
    (fderiv Real (chartGramOp (I := I) S.family p) q) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)

private noncomputable def lScalarDir
    (S : SolutionOn (I := I) (M := M) D) (p : M)
    (i : Fin (Module.finrank Real E)) (q : Real × E) : Real :=
  let x := (extChartAt I p).symm q.2
  mvfderiv (I := I) (S.scalar q.1) x
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i x)

noncomputable def lChartPosDeriv
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : E →L[Real] Real :=
  ∑ i : Fin (Module.finrank Real E),
    (inner Real
        (lGramDir (I := I) S p i
          (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
        (u.deriv r) +
      2 * (a + r) ^ 2 *
        lScalarDir (I := I) S p i
          (T - (a + r) ^ 2, u.toFun r)) •
      chartCoordCLM E i

noncomputable def lChartForce
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : E :=
  (lChartPosDeriv (I := I) S T a p u r).adjoint 1

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem lChartForce_inner
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) (v : E) :
    inner Real (lChartForce (I := I) S T a p u r) v =
      lChartPosDeriv (I := I) S T a p u r v := by
  rw [lChartForce, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartForce_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    IntegrableOn (lChartForce (I := I) S T a p u)
      (Icc (0 : Real) L) volume := by
  classical
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let J : Set Real := tau '' Icc (0 : Real) L
  let K : Set E := u.toFun '' Icc (0 : Real) L
  let U : Set (Real × E) := D.regular ×ˢ interior (extChartAt I p).target
  have htau : ContinuousOn tau (Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn htau
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hreg r hr
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r))
      (Icc (0 : Real) L) := htau.prodMk u.continuousOn_toFun
  have hpair_mem : MapsTo (fun r ↦ (tau r, u.toFun r))
      (Icc (0 : Real) L) U := by
    intro r hr
    exact ⟨hreg r hr, hchart hr⟩
  have hGram : ContDiffOn Real ∞
      (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hGramFd : ContinuousOn
      (fderiv Real (chartGramOp (I := I) S.family p)) U :=
    hGram.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hkin (i : Fin (Module.finrank Real E)) : IntegrableOn
      (fun r ↦ inner Real
        (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
        (u.deriv r)) (Icc (0 : Real) L) volume := by
    let A : Real → E →L[Real] E := fun r ↦
      lGramDir (I := I) S p i (tau r, u.toFun r)
    have hdir : ContinuousOn
        (fun q ↦ lGramDir (I := I) S p i q) U := by
      exact (hGramFd.clm_apply continuousOn_const).const_smul (1 / 2 : Real)
    have hAcont : ContinuousOn A (Icc (0 : Real) L) :=
      hdir.comp hpair hpair_mem
    have hA : AEStronglyMeasurable A (timeMeasure L) := by
      simpa only [timeMeasure] using
        hAcont.aestronglyMeasurable measurableSet_Icc
    have hdirJK : ContinuousOn
        (fun q ↦ lGramDir (I := I) S p i q) (J ×ˢ K) :=
      hdir.mono (prod_mono hJreg hKchart)
    obtain ⟨C0, hC0⟩ := (hJc.prod hKc).bddAbove_image hdirJK.norm
    let C : NNReal := ⟨max C0 0, le_max_right C0 0⟩
    have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hmem : (tau r, u.toFun r) ∈ J ×ˢ K :=
        ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
      exact (hC0 ⟨(tau r, u.toFun r), hmem, rfl⟩).trans
        (le_max_left C0 0)
    have hq := timeQuad_int A hA C hC hL.le u.deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL.le] at hq
    simpa only [A] using hq
  have hscalar (i : Fin (Module.finrank Real E)) : IntegrableOn
      (fun r ↦ 2 * (a + r) ^ 2 *
        lScalarDir (I := I) S p i (tau r, u.toFun r))
      (Icc (0 : Real) L) volume := by
    have hsmooth : ContDiffOn Real ∞
        (fun q : Real × E ↦ lScalarDir (I := I) S p i q) U := by
      with_unfolding_all exact chartScalarDeriv (I := I) S hS p i
    have hcomp : ContinuousOn
        (fun r ↦ lScalarDir (I := I) S p i (tau r, u.toFun r))
        (Icc (0 : Real) L) :=
      hsmooth.continuousOn.comp hpair hpair_mem
    exact (((continuousOn_const.mul
      ((continuousOn_const.add continuousOn_id).pow 2)).mul hcomp)).integrableOn_Icc
  have hcov : IntegrableOn
    (fun r ↦ ∑ i : Fin (Module.finrank Real E),
      (inner Real
          (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
          (u.deriv r) +
        2 * (a + r) ^ 2 *
          lScalarDir (I := I) S p i (tau r, u.toFun r)) •
        chartCoordCLM E i)
    (Icc (0 : Real) L) volume := by
    change Integrable (fun r ↦ ∑ i : Fin (Module.finrank Real E),
      (inner Real
          (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
          (u.deriv r) +
        2 * (a + r) ^ 2 *
          lScalarDir (I := I) S p i (tau r, u.toFun r)) •
        chartCoordCLM E i) (volume.restrict (Icc (0 : Real) L))
    refine integrable_finsetSum Finset.univ
      (f := fun i r ↦
        (inner Real
            (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
            (u.deriv r) +
          2 * (a + r) ^ 2 *
            lScalarDir (I := I) S p i (tau r, u.toFun r)) •
          chartCoordCLM E i) ?_
    intro i _
    exact (hkin i).add (hscalar i) |>.smul_const (chartCoordCLM E i)
  have hadj : Continuous
      (fun A : E →L[Real] Real ↦ A.adjoint (1 : Real)) :=
    (ContinuousLinearMap.adjoint (E := E) (F := Real)).continuous.clm_apply
      continuous_const
  have hcov' : IntegrableOn
      (lChartPosDeriv (I := I) S T a p u) (Icc (0 : Real) L) volume := by
    with_unfolding_all exact hcov
  change Integrable (lChartForce (I := I) S T a p u)
    (volume.restrict (Icc (0 : Real) L))
  refine Integrable.mono' hcov'.norm
    (hadj.comp_aestronglyMeasurable hcov'.aestronglyMeasurable) ?_
  filter_upwards [] with r
  change ‖(lChartPosDeriv (I := I) S T a p u r).adjoint (1 : Real)‖ ≤
    ‖lChartPosDeriv (I := I) S T a p u r‖
  simpa using
    (lChartPosDeriv (I := I) S T a p u r).adjoint.le_opNorm (1 : Real)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
