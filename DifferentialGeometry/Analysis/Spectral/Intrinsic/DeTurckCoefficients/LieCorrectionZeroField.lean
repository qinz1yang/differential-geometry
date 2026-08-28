import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroCore
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffOperatorFieldApplicationValue

open DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
    DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator









noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff Matrix

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckVectorFieldCovariantDerivativeEndomorphism deTurckVectorFieldCovariantDerivativeEndomorphism_apply deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff
    deTurckVFCovDeriv connectionDifferenceOp_homSection_contMDiff metricConnectionDifferenceLoweredFib
    metricConnectionDifferenceLoweredFib_toModel metricConnectionDifferenceLoweredFib_contMDiff domDomCongrFibRank
    domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

open LieCorrectionZeroCore

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma lieArm_rawComponent_eq_unitModel_frame (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx b =
      unitModel (I := I) (M := M) g s W b
        (fun j => (show E from chartBasisVecFiber (I := I) x (Jdx j) b)) := by
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W x hb ![] Jdx]
  have hidx : (![] : Fin 0 → Fin (Module.finrank ℝ E)) = fun _ => 0 := by
    funext i; exact Fin.elim0 i
  rw [hidx, chartFrameBasisModel_zero_eq_constOfIsEmpty (I := I) (M := M) x b]
  rfl
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_symmS_rawComponent (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (x : M)
    (c d : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (ccTensor02Symm (I := I) (M := M) g S) x ![] ![c, d] b =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![c, d] b +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b) := by
  classical
  have hswap : tensorChartComponentRaw (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) x ![] ![c, d] b =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b := by
    rw [lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 _ x ![c, d] hb,
      lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 S x ![d, c] hb]
    rw [domDomCongrSection_unitModel (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g 2 S b t) ?_
    funext j
    fin_cases j <;> rfl
  rw [show ccTensor02Symm (I := I) (M := M) g S =
      (1 / 2 : ℝ) • (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) from rfl]
  rw [tensorChartComponentRaw_smul, tensorChartComponentRaw_add, hswap]
  rw [smul_eq_mul]
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d]) =ᶠ[𝓝 (extChartAt I x x)]
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d := by
  classical
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget, hev] with y hy_tgt hev_y
  rw [hev_y]
  have hb : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
  rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x c d hb]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) : chartInvGramOnE (I := I) g x a b (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x a b :=
  PDE.DeTurck.RicciLinearization.chartInvGramOnE_extChartAt_self (I := I) g x a b
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) : chartGramOnE (I := I) g x a b (extChartAt I x x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b :=
  PDE.DeTurck.DeTurckLinearization.chartGramOnE_extChartAt_self (I := I) g x a b
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartInvGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x a b = chartInvGramMatrix (I := I) g x x b a :=
  PDE.DeTurck.RicciLinearization.chartInvGramMatrix_self_symm (I := I) g x a b
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_gram_invGram_collapse (g : SmoothRiemannianMetric I M) (x : M)
    (l j : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l) =
      if l = j then (1 : ℝ) else 0 :=
  PDE.DeTurck.DeTurckLinearization.sum_chartGram_mul_chartInvGram_self (I := I) g x j l
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_inner_chartBasis_center (g : SmoothRiemannianMetric I M) (x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    g.inner x (centeredChartTangentBasis (I := I) x p)
        (centeredChartTangentBasis (I := I) x q) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x p q := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x p,
    DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x q]
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_connectionDifference_chartBasis_center (gA gB : SmoothRiemannianMetric I M) (x : M)
    (j k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connectionDifference (I := I) gA gB x
        (centeredChartTangentBasis (I := I) x j)
        (centeredChartTangentBasis (I := I) x k) =
      ∑ p : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) gA x k j p
            (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) gB x k j p
            (extChartAt I x x)) •
          centeredChartTangentBasis (I := I) x p := by
  rw [show centeredChartTangentBasis (I := I) x j =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x j x from
    (DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x j).symm]
  rw [show centeredChartTangentBasis (I := I) x k =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x k x from
    (DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x k).symm]
  rw [PDE.DeTurck.connectionDifference_chartBasis_pair_eq_sum (I := I) gA gB x
    (DifferentialGeometry.Geometry.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
    j k]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x p]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b
    = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x b a := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  exact g.symm _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_tangentModel_symm_chartBasis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (chartModelBasis E i) =
      centeredChartTangentBasis (I := I) x i := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    tangent_model_equiv_centered_chart_basis]
omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma lieArm_realizedGramDeriv_symm (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b
    = realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a := by
  funext y
  change DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y
    - DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y
    = DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x b a y
    - DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x b a y
  rw [DifferentialGeometry.Geometry.Operator.chartGramOnE_symm (I := I) _ x a b,
    DifferentialGeometry.Geometry.Operator.chartGramOnE_symm (I := I) _ x a b]
section LieCorrectionZeroEval
open DifferentialGeometry.Integral.DivergenceTheorem
  (partialDeriv)
open DifferentialGeometry.Geometry.Operator
  (chartInvGramMatrix chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieCovariantDerivativeW_chartBasis_eq)
variable (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
private noncomputable def lieCorrectionZeroNScalar (x : M) (i p : Fin (Module.finrank ℝ E)) : ℝ :=
  (∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)))
    - (∑ m : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x m
            (extChartAt I x x) *
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)))
    - (partialDeriv (E := E) i
        (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
        (extChartAt I x x) +
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
            (extChartAt I x x))
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_connectionDifferenceVF_chartBasis (gP : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x)
        (centeredChartTangentBasis (I := I) x i) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
              (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
              chartChristoffel (I := I) g₀ x i m p (extChartAt I x x))) •
          centeredChartTangentBasis (I := I) x p := by
  classical
  have hflip : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x)
      (centeredChartTangentBasis (I := I) x i) =
      ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip
        (centeredChartTangentBasis (I := I) x i))
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x) := rfl
  rw [hflip]
  rw [show (PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gP :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x from rfl]
  rw [PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) g₁ gP x]
  rw [map_sum]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip
        (centeredChartTangentBasis (I := I) x i))
        (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
            (extChartAt I x x) •
          centeredChartTangentBasis (I := I) x m)) =
    ∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) •
        (∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)) •
          centeredChartTangentBasis (I := I) x p) from
    Finset.sum_congr rfl (fun m _ => by
      rw [map_smul]
      refine congrArg (fun t => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        g₁ gP x m (extChartAt I x x) • t) ?_
      exact lieArm_connectionDifference_chartBasis_center (I := I) g₁ g₀ x m i)]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) •
        (∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)) •
          centeredChartTangentBasis (I := I) x p)) =
    ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
      (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x i m p (extChartAt I x x))) •
        centeredChartTangentBasis (I := I) x p from
    Finset.sum_congr rfl (fun m _ => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [smul_smul])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_smul]
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZeroNEndo_chartBasis (x : M) (i : Fin (Module.finrank ℝ E)) :
    lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x
        (centeredChartTangentBasis (I := I) x i) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
          centeredChartTangentBasis (I := I) x p := by
  classical
  rw [lieCorrectionZeroNEndo]
  rw [sub_apply, sub_apply]
  rw [lieCorrectionZero_connectionDifferenceVF_chartBasis (I := I) g₀ g₁ g₀ x i,
    lieCorrectionZero_connectionDifferenceVF_chartBasis (I := I) g₀ g₁ g_bg x i]
  rw [deTurckVectorFieldCovariantDerivativeEndomorphism_apply (I := I) g₁ g₀ x
    (centeredChartTangentBasis (I := I) x i)]
  rw [deTurckLieCovariantDerivativeW_chartBasis_eq (I := I) g₁ g₀ x i]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) i
          (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
          (extChartAt I x x) +
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
              (extChartAt I x x)) •
        DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x p x) =
    ∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) i
          (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
          (extChartAt I x x) +
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
              (extChartAt I x x)) •
        centeredChartTangentBasis (I := I) x p from
    Finset.sum_congr rfl (fun p _ => by
      rw [DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x p])]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [lieCorrectionZeroNScalar, sub_smul, sub_smul]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd0 (a b w : E) :
    Function.update ![a, b] (0 : Fin 2) w = ![w, b] := by
  funext k
  fin_cases k <;> simp [Function.update]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd1 (a b w : E) :
    Function.update ![a, b] (1 : Fin 2) w = ![a, w] := by
  funext k
  fin_cases k <;> simp [Function.update]
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_cmm2_expand_slot0 (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : E) :
    f ![∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p, w] =
      ∑ p : Fin (Module.finrank ℝ E), c p * f ![(chartModelBasis E) p, w] := by
  classical
  rw [show (![∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p, w] :
      Fin 2 → E) =
    Function.update ![w, w] (0 : Fin 2)
      (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p) from by
    rw [lieCorrectionZero_upd0]]
  change f.toMultilinearMap (Function.update ![w, w] (0 : Fin 2)
    (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p)) = _
  rw [f.toMultilinearMap.map_update_sum (t := Finset.univ) (i := (0 : Fin 2))
    (g := fun p : Fin (Module.finrank ℝ E) => c p • (chartModelBasis E) p) (m := ![w, w])]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [f.toMultilinearMap.map_update_smul (m := ![w, w]) (i := (0 : Fin 2)) (c := c p)
    (x := (chartModelBasis E) p)]
  rw [lieCorrectionZero_upd0]
  rfl
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_cmm2_expand_slot1 (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : E) :
    f ![w, ∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p] =
      ∑ p : Fin (Module.finrank ℝ E), c p * f ![w, (chartModelBasis E) p] := by
  classical
  rw [show (![w, ∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p] :
      Fin 2 → E) =
    Function.update ![w, w] (1 : Fin 2)
      (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p) from by
    rw [lieCorrectionZero_upd1]]
  change f.toMultilinearMap (Function.update ![w, w] (1 : Fin 2)
    (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p)) = _
  rw [f.toMultilinearMap.map_update_sum (t := Finset.univ) (i := (1 : Fin 2))
    (g := fun p : Fin (Module.finrank ℝ E) => c p • (chartModelBasis E) p) (m := ![w, w])]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [f.toMultilinearMap.map_update_smul (m := ![w, w]) (i := (1 : Fin 2)) (c := c p)
    (x := (chartModelBasis E) p)]
  rw [lieCorrectionZero_upd1]
  rfl
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZeroInsertionFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p *
          Tensor0SSpace.toModel D ![(chartModelBasis E) p, (chartModelBasis E) j])
      + (∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x j p *
          Tensor0SSpace.toModel D ![(chartModelBasis E) i, (chartModelBasis E) p]) := by
  classical
  rw [lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g_bg x D]
  have h0 : Function.update
      (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) (0 : Fin 2)
      (tangentLinearMapToModel (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 0)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x
            (centeredChartTangentBasis (I := I) x i)),
        (chartModelBasis E) j] := by
    rw [lieCorrectionZero_upd0, tangentLinearMapToModel_apply, Matrix.cons_val_zero,
      lieArm_tangentModel_symm_chartBasis]
  have h1 : Function.update
      (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) (1 : Fin 2)
      (tangentLinearMapToModel (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 1)) =
      ![(chartModelBasis E) i,
        tangentSpaceModelContinuousLinearEquiv (I := I) x
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x
            (centeredChartTangentBasis (I := I) x j))] := by
    rw [lieCorrectionZero_upd1, tangentLinearMapToModel_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero,
      lieArm_tangentModel_symm_chartBasis]
  rw [h0, h1]
  rw [lieCorrectionZeroNEndo_chartBasis (I := I) g₀ g₁ g_bg x i,
    lieCorrectionZeroNEndo_chartBasis (I := I) g₀ g₁ g_bg x j]
  rw [show tangentSpaceModelContinuousLinearEquiv (I := I) x
      (∑ p : Fin (Module.finrank ℝ E),
      lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
        centeredChartTangentBasis (I := I) x p) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
          chartModelBasis E p from by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [map_smul, tangent_model_equiv_centered_chart_basis]]
  rw [show tangentSpaceModelContinuousLinearEquiv (I := I) x
      (∑ p : Fin (Module.finrank ℝ E),
      lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x j p •
        centeredChartTangentBasis (I := I) x p) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x j p •
          chartModelBasis E p from by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [map_smul, tangent_model_equiv_centered_chart_basis]]
  rw [lieCorrectionZero_cmm2_expand_slot0 (Tensor0SSpace.toModel D)
    (fun p => lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p) ((chartModelBasis E) j),
    lieCorrectionZero_cmm2_expand_slot1 (Tensor0SSpace.toModel D)
    (fun p => lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x j p) ((chartModelBasis E) i)]
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply
  cometricFinBasisTrace_eq_chartInvGram_bilin)
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroTraceStep_toModel (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) (T : Tensor0SSpace (p + 2) I x)
    (u : Fin p → E) :
    Tensor0SSpace.toModel (lieCorrectionZeroTraceStep (I := I) g p σ x T) u =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel T
          (fun i => (Fin.cons (DeTurck.cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) u) : Fin (p + 2) → E) (σ i)) := by
  classical
  rw [lieCorrectionZeroTraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply,
    cometricDoubleTraceFib_toModel]
  rw [DeTurck.modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_vbArg (a b v0 v1 : E) : (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E) (lieCorrectionZeroVectorBundleTracePermutation i)) =
      ![b, v0, v1, a] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd4_30 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (3 : Fin 4) a)
        (0 : Fin 4) b = ![b, z1, z2, a] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_prodKappa_toModel {pq q : ℕ} (x : M) (κ : Tensor0SSpace q I x)
    (D : Tensor0SSpace pq I x) (v : Fin (pq + q) → E) :
    Tensor0SSpace.toModel (tensor0SProdKappaFib (I := I) x κ D) v =
      Tensor0SSpace.toModel D (fun i => v (Fin.castAdd q i)) *
        Tensor0SSpace.toModel κ (fun i => v (Fin.natAdd pq i)) := by
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_ip_toModel (x : M) (V : TangentSpace I x) (D : Tensor0SSpace 2 I x) (b : E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V D) ![b] =
      Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x V, b] := by
  rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_castAdd1 (b v0 v1 a : E) :
    (fun i : Fin 1 => (![b, v0, v1, a] : Fin 4 → E) (Fin.castAdd 3 i)) = ![b] := by
  funext i
  fin_cases i
  rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_natAdd1 (b v0 v1 a : E) :
    (fun i : Fin 3 => (![b, v0, v1, a] : Fin 4 → E) (Fin.natAdd 1 i)) = ![v0, v1, a] := by
  funext i
  fin_cases i <;> rfl
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_D_VF_expand (g₁ gP : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (b : E) :
    Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x),
          b] =
      ∑ ρ : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
            (extChartAt I x x) *
          Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, b] := by
  have hV : tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x) =
      ∑ ρ : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
            (extChartAt I x x) •
          chartModelBasis E ρ := by
    have h1 : (PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x =
        (PDE.DeTurck.deTurckVF (I := I) g₁ gP :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := rfl
    rw [h1, PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) g₁ gP x,
      map_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [map_smul, tangent_model_equiv_centered_chart_basis]
  rw [hV]
  exact lieCorrectionZero_cmm2_expand_slot0 (Tensor0SSpace.toModel D)
    (fun ρ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
      (extChartAt I x x)) b
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZeroVBFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroVBFib (I := I) g₀ g₁ x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      2 * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l *
          ((∑ c : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
              chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
              chartGramMatrix (I := I) g₁ x x c l) *
            (∑ ρ : Fin (Module.finrank ℝ E),
              PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x ρ
                  (extChartAt I x x) *
                Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, (chartModelBasis E) k])) := by
  classical
  rw [show lieCorrectionZeroVBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x
        (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)) from by
    rw [lieCorrectionZeroVBFib]
    rfl]
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  set P4 : Tensor0SSpace 4 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)
    with hP4
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x P4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorrectionZeroVectorBundleTracePermutation i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      quadrilinearMapSlotBilinearAt (E := E) (Tensor0SSpace.toModel P4) 3 0 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) i, (chartModelBasis E) j,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [unitModel4SlotBilin_apply, lieCorrectionZero_upd4_30, lieCorrectionZero_vbArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k l * t) ?_
  rw [unitModel4SlotBilin_apply, lieCorrectionZero_upd4_30]
  rw [hP4]
  rw [lieCorrectionZero_prodKappa_toModel (I := I) (pq := 1) (q := 3) x _ _
    ![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
      (chartModelBasis E) l]]
  rw [show (fun i' : Fin 1 =>
      (![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
        (chartModelBasis E) l] : Fin 4 → E) (Fin.castAdd 3 i')) =
    ![(chartModelBasis E) k] from by
    funext i'
    fin_cases i'
    rfl]
  rw [show (fun i' : Fin 3 =>
      (![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
        (chartModelBasis E) l] : Fin 4 → E) (Fin.natAdd 1 i')) =
    ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) l] from by
    funext i'
    fin_cases i' <;> rfl]
  rw [lieCorrectionZero_ip_toModel (I := I) x _ D ((chartModelBasis E) k)]
  rw [show Tensor0SSpace.toModel (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) l] =
    g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      (centeredChartTangentBasis (I := I) x i)
      (centeredChartTangentBasis (I := I) x j))
      (centeredChartTangentBasis (I := I) x l) from by
    rw [metricConnectionDifferenceLoweredFib_toModel]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, lieArm_tangentModel_symm_chartBasis]]
  rw [lieArm_connectionDifference_chartBasis_center (I := I) g₁ g₀ x i j]
  rw [show g₁.inner x (∑ c : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
        chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) •
      centeredChartTangentBasis (I := I) x c)
      (centeredChartTangentBasis (I := I) x l) =
    ∑ c : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
        chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
        chartGramMatrix (I := I) g₁ x x c l from by
    rw [show g₁.inner x (∑ c : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) •
        centeredChartTangentBasis (I := I) x c)
        (centeredChartTangentBasis (I := I) x l) =
      ∑ c : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
          g₁.inner x (centeredChartTangentBasis (I := I) x c)
            (centeredChartTangentBasis (I := I) x l) from by
      rw [map_sum (g₁.inner x)]
      rw [sum_apply]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_smul (g₁.inner x), smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [lieArm_inner_chartBasis_center (I := I) g₁ x c l]]
  rw [lieCorrectionZero_D_VF_expand (I := I) g₁ g₀ x D ((chartModelBasis E) k)]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  ring
private noncomputable def lieCorrectionZeroSlotBilin {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (i j : Fin n) (hij : i ≠ j) (base : Fin n → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        change f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        change f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij (r • c) v base, Function.update_comm hij c v base,
          f.map_update_smul (Function.update base j v) i r c] }
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZeroSlotBilin_apply {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (i j : Fin n) (hij : i ≠ j) (base : Fin n → E) (c v : E) :
    lieCorrectionZeroSlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl
section LieCorrectionZeroMixedConnectionEval
variable (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_amixQArg (a b : E) (u : Fin 3 → E) : (fun i : Fin 5 =>
      (Fin.cons a (Fin.cons b u) : Fin 5 → E) (lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour i)) =
      ![b, u 2, u 0, u 1, a] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd5_40 (z0 z1 z2 z3 z4 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4] : Fin 5 → E) (4 : Fin 5) a)
        (0 : Fin 5) b = ![b, z1, z2, z3, a] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_castAdd2of5 (b u2 u0 u1 a : E) :
    (fun i : Fin 2 => (![b, u2, u0, u1, a] : Fin 5 → E) (Fin.castAdd 3 i)) = ![b, u2] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_natAdd3of5 (b u2 u0 u1 a : E) :
    (fun i : Fin 3 => (![b, u2, u0, u1, a] : Fin 5 → E) (Fin.natAdd 2 i)) = ![u0, u1, a] := by
  funext i
  fin_cases i <;> rfl
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZeroQ_value (x : M) (D : Tensor0SSpace 2 I x) (u : Fin 3 → E) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
          (tensor0SProdKappaFib (I := I) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D)) u =
      ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k kl *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, u 2] *
            Tensor0SSpace.toModel (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
              ![u 0, u 1, (chartModelBasis E) kl]) := by
  classical
  set P5 : Tensor0SSpace 5 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D with hP5
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x P5 u]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P5
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) u) : Fin 5 → E) (lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      lieCorrectionZeroSlotBilin (E := E) (Tensor0SSpace.toModel P5) 4 0 (by decide)
        ![u 0, u 2, u 0, u 1, u 1]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd5_40, lieCorrectionZero_amixQArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
  rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd5_40]
  rw [hP5]
  rw [lieCorrectionZero_prodKappa_toModel (I := I) (pq := 2) (q := 3) x _ _
    ![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl]]
  rw [show (fun i' : Fin 2 =>
      (![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl] : Fin 5 → E)
        (Fin.castAdd 3 i')) = ![(chartModelBasis E) k, u 2] from
    lieCorrectionZero_castAdd2of5 (E := E) _ _ _ _ _]
  rw [show (fun i' : Fin 3 =>
      (![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl] : Fin 5 → E)
        (Fin.natAdd 2 i')) = ![u 0, u 1, (chartModelBasis E) kl] from
    lieCorrectionZero_natAdd3of5 (E := E) _ _ _ _ _]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_amixT4Arg (a b : E) (w : Fin 4 → E) : (fun i : Fin 6 =>
      (Fin.cons a (Fin.cons b w) : Fin 6 → E) (lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne i)) =
      ![w 0, a, w 1, b, w 2, w 3] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd6_13 (z0 z1 z2 z3 z4 z5 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4, z5] : Fin 6 → E) (1 : Fin 6) a)
        (3 : Fin 6) b = ![z0, a, z2, b, z4, z5] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_castAdd3of6 (w0 a w1 b w2 w3 : E) :
    (fun i : Fin 3 => (![w0, a, w1, b, w2, w3] : Fin 6 → E) (Fin.castAdd 3 i)) =
      ![w0, a, w1] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_natAdd3of6 (w0 a w1 b w2 w3 : E) :
    (fun i : Fin 3 => (![w0, a, w1, b, w2, w3] : Fin 6 → E) (Fin.natAdd 3 i)) =
      ![b, w2, w3] := by
  funext i
  fin_cases i <;> rfl
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZeroT4_value (x : M) (D : Tensor0SSpace 2 I x) (w : Fin 4 → E) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
          (tensor0SProdKappaFib (I := I) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
            (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
              (tensor0SProdKappaFib (I := I) x
                (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D)))) w =
      ∑ j : Fin (Module.finrank ℝ E), ∑ jl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x j jl *
          (Tensor0SSpace.toModel
              (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
                (tensor0SProdKappaFib (I := I) x
                  (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D))
              ![w 0, (chartModelBasis E) jl, w 1] *
            Tensor0SSpace.toModel (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
              ![(chartModelBasis E) j, w 2, w 3]) := by
  classical
  set QD : Tensor0SSpace 3 I x :=
    lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
      (tensor0SProdKappaFib (I := I) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D) with hQD
  set P6 : Tensor0SSpace 6 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x) QD
    with hP6
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x P6 w]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P6
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j)))
          (Fin.cons ((Module.finBasis ℝ E) j) w) : Fin 6 → E) (lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne i'))) =
    ∑ j : Fin (Module.finrank ℝ E),
      lieCorrectionZeroSlotBilin (E := E) (Tensor0SSpace.toModel P6) 1 3 (by decide)
        ![w 0, w 0, w 1, w 1, w 2, w 3]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis j)))
        ((Module.finBasis ℝ E) j) from
    Finset.sum_congr rfl (fun j _ => by
      rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd6_13, lieCorrectionZero_amixT4Arg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun jl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x j jl * t) ?_
  rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd6_13]
  rw [hP6]
  rw [lieCorrectionZero_prodKappa_toModel (I := I) (pq := 3) (q := 3) x _ _
    ![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3]]
  rw [show (fun i' : Fin 3 =>
      (![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3] : Fin 6 → E)
        (Fin.castAdd 3 i')) = ![w 0, (chartModelBasis E) jl, w 1] from
    lieCorrectionZero_castAdd3of6 (E := E) _ _ _ _ _ _]
  rw [show (fun i' : Fin 3 =>
      (![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3] : Fin 6 → E)
        (Fin.natAdd 3 i')) = ![(chartModelBasis E) j, w 2, w 3] from
    lieCorrectionZero_natAdd3of6 (E := E) _ _ _ _ _ _]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_amixTopArg (a b v0 v1 : E) : (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E)
        (lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne i)) = ![v0, a, b, v1] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd4_12 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (1 : Fin 4) a)
        (2 : Fin 4) b = ![z0, a, b, z3] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_lowered_basis_value (gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
        ![(chartModelBasis E) a, (chartModelBasis E) b, (chartModelBasis E) c] =
      ∑ d : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x b a d (extChartAt I x x) -
          chartChristoffel (I := I) gB x b a d (extChartAt I x x)) *
          chartGramMatrix (I := I) g₁ x x d c := by
  rw [show Tensor0SSpace.toModel (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
      ![(chartModelBasis E) a, (chartModelBasis E) b, (chartModelBasis E) c] =
    g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ gB x
      (centeredChartTangentBasis (I := I) x a)
      (centeredChartTangentBasis (I := I) x b))
      (centeredChartTangentBasis (I := I) x c) from by
    rw [metricConnectionDifferenceLoweredFib_toModel]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, lieArm_tangentModel_symm_chartBasis]]
  rw [lieArm_connectionDifference_chartBasis_center (I := I) g₁ gB x a b]
  rw [map_sum (g₁.inner x), sum_apply]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [map_smul (g₁.inner x), smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₁ x d c]
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZeroMixedConnectionHalfFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ al : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a al *
              ((∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k kl *
                  (Tensor0SSpace.toModel D
                      ![(chartModelBasis E) k, (chartModelBasis E) ml] *
                    (∑ c : Fin (Module.finrank ℝ E),
                      (chartChristoffel (I := I) g₁ x al i c (extChartAt I x x) -
                        chartChristoffel (I := I) g₀ x al i c (extChartAt I x x)) *
                        chartGramMatrix (I := I) g₁ x x c kl))) *
                (∑ d : Fin (Module.finrank ℝ E),
                  (chartChristoffel (I := I) g₁ x m a d (extChartAt I x x) -
                    chartChristoffel (I := I) g_bg x m a d (extChartAt I x x)) *
                    chartGramMatrix (I := I) g₁ x x d j)))) := by
  classical
  set QD : Tensor0SSpace 3 I x :=
    lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
      (tensor0SProdKappaFib (I := I) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D) with hQD
  set T4 : Tensor0SSpace 4 I x :=
    lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
      (tensor0SProdKappaFib (I := I) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x) QD) with hT4
  rw [show lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D =
      lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x T4 from by
    unfold lieCorrectionZeroMixedConnectionHalfFib
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hQD, ← hT4]]
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₁ 2 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x T4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel T4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis m)))
          (Fin.cons ((Module.finBasis ℝ E) m)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne i'))) =
    ∑ m : Fin (Module.finrank ℝ E),
      lieCorrectionZeroSlotBilin (E := E) (Tensor0SSpace.toModel T4) 1 2 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) i, (chartModelBasis E) j,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis m)))
        ((Module.finBasis ℝ E) m) from
    Finset.sum_congr rfl (fun m _ => by
      rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd4_12, lieCorrectionZero_amixTopArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
  rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd4_12]
  rw [hT4]
  rw [lieCorrectionZeroT4_value (I := I) g₀ g₁ g_bg x D
    ![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j]]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x a al * t) ?_
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 1) = (chartModelBasis E) ml from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 2) = (chartModelBasis E) m from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 3) = (chartModelBasis E) j from rfl]
  rw [lieCorrectionZeroQ_value (I := I) g₀ g₁ x D
    ![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml]]
  rw [lieCorrectionZero_lowered_basis_value (I := I) g₁ g_bg x a m j]
  refine congrArg (fun t : ℝ => t *
    (∑ d : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x m a d (extChartAt I x x) -
        chartChristoffel (I := I) g_bg x m a d (extChartAt I x x)) *
        chartGramMatrix (I := I) g₁ x x d j)) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 2) = (chartModelBasis E) ml from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 1) = (chartModelBasis E) al from rfl]
  refine congrArg (fun t : ℝ =>
    Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) ml] * t) ?_
  rw [lieCorrectionZero_lowered_basis_value (I := I) g₁ g₀ x i al kl]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_swapArg (v0 v1 : E) :
    (fun i : Fin 2 => (![v0, v1] : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![v1, v0] := by
  funext i
  fin_cases i <;> simp
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroMixedConnectionFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      2 * (Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) j, (chartModelBasis E) i]) := by
  rw [show lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x D =
      (2 : ℝ) • (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D +
        domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D)) from by
    rw [lieCorrectionZeroMixedConnectionFib]
    rfl]
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  rw [Tensor0SSpace.toModel_add, add_apply]
  refine congrArg (fun t : ℝ =>
    Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D)
      ![(chartModelBasis E) i, (chartModelBasis E) j] + t) ?_
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg (fun t => Tensor0SSpace.toModel
    (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D) t) ?_
  exact lieCorrectionZero_swapArg (E := E) _ _
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_riemT4Arg (a b : E) (w : Fin 4 → E) : (fun i : Fin 6 =>
      (Fin.cons a (Fin.cons b w) : Fin 6 → E) (lieCorrectionZeroRiemPerm1 i)) =
      ![b, w 3, w 0, w 1, w 2, a] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd6_50 (z0 z1 z2 z3 z4 z5 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4, z5] : Fin 6 → E) (5 : Fin 6) a)
        (0 : Fin 6) b = ![b, z1, z2, z3, z4, a] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_castAdd2of6 (b w3 w0 w1 w2 a : E) :
    (fun i : Fin 2 => (![b, w3, w0, w1, w2, a] : Fin 6 → E) (Fin.castAdd 4 i)) =
      ![b, w3] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_natAdd4of6 (b w3 w0 w1 w2 a : E) :
    (fun i : Fin 4 => (![b, w3, w0, w1, w2, a] : Fin 6 → E) (Fin.natAdd 2 i)) =
      ![w0, w1, w2, a] := by
  funext i
  fin_cases i <;> rfl
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroRiemT4_value (x : M) (D : Tensor0SSpace 2 I x) (w : Fin 4 → E) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x
          (tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) D)) w =
      ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₀ x x k kl *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, w 3] *
            Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
              ![w 0, w 1, w 2, (chartModelBasis E) kl]) := by
  classical
  set P6 : Tensor0SSpace 6 I x :=
    tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) D with hP6
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x P6 w]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P6
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 6 → E) (lieCorrectionZeroRiemPerm1 i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      lieCorrectionZeroSlotBilin (E := E) (Tensor0SSpace.toModel P6) 5 0 (by decide)
        ![w 0, w 3, w 0, w 1, w 2, w 2]
        (DeTurck.cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd6_50, lieCorrectionZero_riemT4Arg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₀ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₀ x x k kl * t) ?_
  rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd6_50]
  rw [hP6]
  rw [lieCorrectionZero_prodKappa_toModel (I := I) (pq := 2) (q := 4) x _ _
    ![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl]]
  rw [show (fun i' : Fin 2 =>
      (![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl] : Fin 6 → E)
        (Fin.castAdd 4 i')) = ![(chartModelBasis E) k, w 3] from
    lieCorrectionZero_castAdd2of6 (E := E) _ _ _ _ _ _]
  rw [show (fun i' : Fin 4 =>
      (![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl] : Fin 6 → E)
        (Fin.natAdd 2 i')) = ![w 0, w 1, w 2, (chartModelBasis E) kl] from
    lieCorrectionZero_natAdd4of6 (E := E) _ _ _ _ _ _]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_riemTopArg (a b v0 v1 : E) : (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E)
        (lieCorrectionZeroRiemPerm2 i)) = ![v0, v1, a, b] := by
  funext i
  fin_cases i <;> rfl
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_upd4_23 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (2 : Fin 4) a)
        (3 : Fin 4) b = ![z0, z1, a, b] := by
  funext i
  fin_cases i <;> simp [Function.update]
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_riemLowered_basis_value (x : M) (i j ml kl : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
        ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
          (chartModelBasis E) kl] =
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          chartGramMatrix (I := I) g₀ x x ρ kl := by
  rw [show Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
      ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
        (chartModelBasis E) kl] =
    g₀.inner x (DifferentialGeometry.Geometry.Curvature.riemannOp (LeviCivita (I := I) g₀) x
      (centeredChartTangentBasis (I := I) x i)
      (centeredChartTangentBasis (I := I) x j)
      (centeredChartTangentBasis (I := I) x ml))
      (centeredChartTangentBasis (I := I) x kl) from by
    rw [show (![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
        (chartModelBasis E) kl] : Fin 4 → E) =
      fun n => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![centeredChartTangentBasis (I := I) x i,
          centeredChartTangentBasis (I := I) x j,
          centeredChartTangentBasis (I := I) x ml,
          centeredChartTangentBasis (I := I) x kl] : Fin 4 → TangentSpace I x) n) from by
      funext n
      fin_cases n
      · exact (tangent_model_equiv_centered_chart_basis (I := I) x i).symm
      · exact (tangent_model_equiv_centered_chart_basis (I := I) x j).symm
      · exact (tangent_model_equiv_centered_chart_basis (I := I) x ml).symm
      · exact (tangent_model_equiv_centered_chart_basis (I := I) x kl).symm]
    rw [lieCorrectionZeroRiemLoweredFib_toModel]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]]
  rw [DifferentialGeometry.Geometry.Connection.riemannOp_eq_chartRiemannCLM_apply (I := I) g₀ x]
  rw [DifferentialGeometry.Geometry.Connection.chartRiemannCLM_basis_apply (I := I) g₀ x ml i j]
  rw [map_sum (g₀.inner x), sum_apply]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [map_smul (g₀.inner x), smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₀ x ρ kl]
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZeroRiemFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      -(∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          ∑ ρ : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
                ml i j ρ (extChartAt I x x) *
              Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, (chartModelBasis E) m]) := by
  classical
  set T4 : Tensor0SSpace 4 I x :=
    lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) D) with hT4
  rw [show lieCorrectionZeroRiemFib (I := I) g₀ g₁ x D =
      (-1 : ℝ) • lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroRiemPerm2 x T4 from by
    rw [lieCorrectionZeroRiemFib, hT4]
    rfl]
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
    neg_one_mul, neg_inj]
  rw [lieCorrectionZeroTraceStep_toModel (I := I) g₁ 2 lieCorrectionZeroRiemPerm2 x T4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel T4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis m)))
          (Fin.cons ((Module.finBasis ℝ E) m)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorrectionZeroRiemPerm2 i'))) =
    ∑ m : Fin (Module.finrank ℝ E),
      lieCorrectionZeroSlotBilin (E := E) (Tensor0SSpace.toModel T4) 2 3 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) i,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis m)))
        ((Module.finBasis ℝ E) m) from
    Finset.sum_congr rfl (fun m _ => by
      rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd4_23, lieCorrectionZero_riemTopArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
  rw [lieCorrectionZeroSlotBilin_apply, lieCorrectionZero_upd4_23]
  rw [hT4]
  rw [lieCorrectionZeroRiemT4_value (I := I) g₀ x D
    ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m]]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 3) = (chartModelBasis E) m from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 1) = (chartModelBasis E) j from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 2) = (chartModelBasis E) ml from rfl]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₀ x x k kl *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
            ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
              (chartModelBasis E) kl])) =
    ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
            (chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => by
      rw [lieCorrectionZero_riemLowered_basis_value (I := I) g₀ x i j ml kl]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring))]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
            (chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl))) =
    ∑ ρ : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          ∑ kl : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl) from by
    rw [Finset.sum_comm]
    rw [show (∑ kl : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ ρ : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
              ml i j ρ (extChartAt I x x) *
            (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
              (chartGramMatrix (I := I) g₀ x x ρ kl *
                chartInvGramMatrix (I := I) g₀ x x k kl))) =
      ∑ kl : Fin (Module.finrank ℝ E), ∑ ρ : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
              ml i j ρ (extChartAt I x x) *
            (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
              (chartGramMatrix (I := I) g₀ x x ρ kl *
                chartInvGramMatrix (I := I) g₀ x x k kl)) from
      Finset.sum_congr rfl (fun kl _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          ∑ kl : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl)) =
    ∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          (if k = ρ then (1 : ℝ) else 0)) from
    Finset.sum_congr rfl (fun k _ => by
      refine congrArg (fun t : ℝ =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] * t)) ?_
      rw [show (∑ kl : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g₀ x x ρ kl *
            chartInvGramMatrix (I := I) g₀ x x k kl) =
        ∑ kl : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g₀ x x kl ρ *
            chartInvGramMatrix (I := I) g₀ x x kl k from
        Finset.sum_congr rfl (fun kl _ => by
          rw [lieArm_chartGramMatrix_symm (I := I) g₀ x ρ kl,
            lieArm_chartInvGramMatrix_symm (I := I) g₀ x k kl])]
      exact lieArm_gram_invGram_collapse (I := I) g₀ x k ρ)]
  rw [Finset.sum_eq_single ρ]
  · rw [if_pos rfl, mul_one]
  · intro k _ hk
    rw [if_neg hk, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ ρ) h
end LieCorrectionZeroMixedConnectionEval
end LieCorrectionZeroEval
section LieCorrectionZeroValue
open DifferentialGeometry.Integral.DivergenceTheorem
  (partialDeriv)
open DifferentialGeometry.Geometry.Operator
  (chartInvGramMatrix chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ccTensor02Symm unitModel unitTensor deTurckLieCoeffField deTurckLieCoeffField_apply_eq
  deTurckConnectionDifferenceCovDeriv deTurckVFCovDeriv deTurckLieCovariantDerivativeW_chartBasis_eq
  deTurckLieCovariantDerivativeA_chartBasis_eq connectionDifferenceCovDerivOp deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend
  frameConnectionDifferenceCovDerivKernel frameConnectionDifferenceCovariantDerivativeKernel_apply double_frame_bilin_trace_eq_fixed
  unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv metricPerturbationPath)
variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_f_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  classical
  have hev := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hpt := hev.self_of_nhds
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def] at hpt
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src] at hpt
  rw [show (![(chartModelBasis E) c, (chartModelBasis E) d] : Fin 2 → E) =
      (fun k => chartModelBasis E ((![c, d] : Fin 2 → Fin (Module.finrank ℝ E)) k)) from by
    funext k
    fin_cases k <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ 2
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![c, d]]
  exact hpt
private noncomputable def lieCorrectionZeroCovASc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a m k p : Fin (Module.finrank ℝ E)) : ℝ :=
  partialDeriv (E := E) a
      (fun y => chartChristoffel (I := I) g₁ x k m p y -
        chartChristoffel (I := I) g_bg x k m p y) (extChartAt I x x) +
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x k m c (extChartAt I x x)) -
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x k c p (extChartAt I x x)) -
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_deTurckLieConnectionDifferenceDerivative_inner_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a b m k : Fin (Module.finrank ℝ E)) :
    g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
        (centeredChartTangentBasis (I := I) x a)
        (centeredChartTangentBasis (I := I) x m)
        (centeredChartTangentBasis (I := I) x k))
        (centeredChartTangentBasis (I := I) x b) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x a m k p *
          chartGramMatrix (I := I) g₁ x x p b := by
  classical
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (I := I) g₁ g_bg x
    (centeredChartTangentBasis (I := I) x a)
    (centeredChartTangentBasis (I := I) x m)
    (centeredChartTangentBasis (I := I) x k)]
  rw [deTurckLieCovariantDerivativeA_chartBasis_eq (I := I) g₁ g_bg x a m k]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) a
          (fun y => chartChristoffel (I := I) g₁ x k m p y -
            chartChristoffel (I := I) g_bg x k m p y) (extChartAt I x x) +
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m c (extChartAt I x x)) -
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k c p (extChartAt I x x)) -
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))) •
        DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x p x) =
    ∑ p : Fin (Module.finrank ℝ E),
      lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x a m k p •
        centeredChartTangentBasis (I := I) x p from
    Finset.sum_congr rfl (fun p _ => by
      rw [DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x p]
      rfl)]
  rw [map_sum (g₁.inner x), sum_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul (g₁.inner x), smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₁ x p b]
private noncomputable def lieCorrectionZeroCovWSc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a p : Fin (Module.finrank ℝ E)) : ℝ :=
  partialDeriv (E := E) a
      (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x p y)
      (extChartAt I x x) +
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x c
          (extChartAt I x x)
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_covW_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    deTurckVFCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x a)) x =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x a p •
          centeredChartTangentBasis (I := I) x p := by
  rw [deTurckLieCovariantDerivativeW_chartBasis_eq (I := I) g₁ g_bg x a]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) x p]
  rfl
omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
private lemma lieCorrectionZero_iteratedCovGrad0_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  rw [iteratedCovGrad_zero]
  exact lieCorrectionZero_f_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_ite_pair_eq (x : M) (u w : TangentSpace I x) :
    (fun j : Fin 2 => if j = 0 then u else w) = ![u, w] := by
  funext j
  fin_cases j <;> rfl
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_committed_value (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j] =
      -(∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x m ml *
          (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k kl *
              (((∑ p : Fin (Module.finrank ℝ E),
                  lieCorrectionZeroCovASc (I := I) (M := M)
                      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i m k p *
                    chartGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x p j)
                + (∑ p : Fin (Module.finrank ℝ E),
                  lieCorrectionZeroCovASc (I := I) (M := M)
                      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x j m k p *
                    chartGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x p i)) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                  (extChartAt I x x))))
      + ((∑ p : Fin (Module.finrank ℝ E),
          lieCorrectionZeroCovWSc (I := I) (M := M)
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i p *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j (extChartAt I x x))
        + (∑ p : Fin (Module.finrank ℝ E),
          lieCorrectionZeroCovWSc (I := I) (M := M)
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x j p *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p
              (extChartAt I x x))) := by
  classical
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) with hW₀
  rw [deTurckLieCoeffField_apply_eq (I := I) (M := M) g₀ g₁ g_bg W₀ x
    ![chartModelBasis E i, chartModelBasis E j]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    lieArm_tangentModel_symm_chartBasis]
  have hDLa : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 2 W₀ x
          (fun j' => tangentSpaceModelContinuousLinearEquiv (I := I) x
            (if j' = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x)) *
        (g₁.inner x
            (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x i))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
            (centeredChartTangentBasis (I := I) x j)
          + g₁.inner x
            (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x j))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
            (centeredChartTangentBasis (I := I) x i))) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k kl *
              (((∑ p : Fin (Module.finrank ℝ E),
                  lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x i m k p *
                    chartGramMatrix (I := I) g₁ x x p j)
                + (∑ p : Fin (Module.finrank ℝ E),
                  lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x j m k p *
                    chartGramMatrix (I := I) g₁ x x p i)) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                  (extChartAt I x x))) := by
    set K : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
      frameConnectionDifferenceCovDerivKernel (I := I) g₁ g_bg x
        (centeredChartTangentBasis (I := I) x i)
        (centeredChartTangentBasis (I := I) x j) with hK
    set D : Tensor0SSpace 2 I x :=
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (unitTensor (I := I) (M := M) x) with hD
    set Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
      (bilinFormToModel (TangentSpace I x)).symm
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x D) with hDd
    have hDdev : ∀ (u w : TangentSpace I x), Dd u w =
        unitModel (I := I) (M := M) g₀ 2 W₀ x
          (fun j' => tangentSpaceModelContinuousLinearEquiv (I := I) x
            (if j' = 0 then u else w)) := by
      intro u w
      rw [hDd, bilinFormToModel_symm_apply,
        tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
      change Tensor0SSpace.eval D ![u, w] = _
      rw [← Tensor0SSpace.toModel_apply_tangent, hD, unitModel]
      congr 1
      funext j'
      fin_cases j' <;> rfl
    have hterm : ∀ a b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 2 W₀ x
            (fun j' => tangentSpaceModelContinuousLinearEquiv (I := I) x
              (if j' = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x)) *
          (g₁.inner x
              (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x i))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              (centeredChartTangentBasis (I := I) x j)
            + g₁.inner x
              (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x j))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              (centeredChartTangentBasis (I := I) x i)) =
        K (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) *
          Dd (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) := by
      intro a b
      rw [hK, frameConnectionDifferenceCovariantDerivativeKernel_apply]
      rw [hDdev]
      rw [show (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
          (centeredChartTangentBasis (I := I) x i)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x i))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x from
        deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (I := I) g₁ g_bg x _ _ _]
      rw [show (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
          (centeredChartTangentBasis (I := I) x j)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x j))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x from
        deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (I := I) g₁ g_bg x _ _ _]
      ring
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
    rw [double_frame_bilin_trace_eq_fixed (I := I) g₁ x K Dd
      (fun a => smoothOrthoFrame (I := I) g₁ x a x)
      (fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a b)]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
    refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
    rw [hK, frameConnectionDifferenceCovariantDerivativeKernel_apply]
    rw [lieCorrectionZero_deTurckLieConnectionDifferenceDerivative_inner_basis (I := I) (M := M) g₁ g_bg x i j m k,
      lieCorrectionZero_deTurckLieConnectionDifferenceDerivative_inner_basis (I := I) (M := M) g₁ g_bg x j i m k]
    rw [hDdev]
    rw [show unitModel (I := I) (M := M) g₀ 2 W₀ x
        (fun j' => tangentSpaceModelContinuousLinearEquiv (I := I) x
          (if j' = 0 then centeredChartTangentBasis (I := I) x ml
            else centeredChartTangentBasis (I := I) x kl)) =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl (extChartAt I x x) from by
      rw [show (fun j' : Fin 2 => tangentSpaceModelContinuousLinearEquiv (I := I) x
          (if j' = 0 then centeredChartTangentBasis (I := I) x ml
            else centeredChartTangentBasis (I := I) x kl)) =
        ![chartModelBasis E ml, chartModelBasis E kl] from by
        funext q
        fin_cases q
        · change tangentSpaceModelContinuousLinearEquiv (I := I) x
              (centeredChartTangentBasis (I := I) x ml) = chartModelBasis E ml
          exact tangent_model_equiv_centered_chart_basis (I := I) x ml
        · change tangentSpaceModelContinuousLinearEquiv (I := I) x
              (centeredChartTangentBasis (I := I) x kl) = chartModelBasis E kl
          exact tangent_model_equiv_centered_chart_basis (I := I) x kl]
      rw [hW₀]
      exact lieCorrectionZero_iteratedCovGrad0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl]
  rw [hDLa]
  refine congrArg (fun t : ℝ => -(∑ m : Fin (Module.finrank ℝ E),
    ∑ ml : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x m ml *
        (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k kl *
            (((∑ p : Fin (Module.finrank ℝ E),
                lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x i m k p *
                  chartGramMatrix (I := I) g₁ x x p j)
              + (∑ p : Fin (Module.finrank ℝ E),
                lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x j m k p *
                  chartGramMatrix (I := I) g₁ x x p i)) *
              realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                (extChartAt I x x)))) + t) ?_
  have hW1 : unitModel (I := I) (M := M) g₀ 2 W₀ x
      (fun j' => if j' = 0 then
        tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x i)) x)
        else chartModelBasis E j) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x i p *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j (extChartAt I x x) := by
    rw [show (fun j' : Fin 2 => if j' = 0 then
        tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x
              (centeredChartTangentBasis (I := I) x i)) x)
        else chartModelBasis E j) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x
              (centeredChartTangentBasis (I := I) x i)) x),
        chartModelBasis E j] from by
      funext q
      fin_cases q <;> rfl]
    rw [lieCorrectionZero_covW_basis (I := I) (M := M) g₁ g_bg x i]
    rw [show tangentSpaceModelContinuousLinearEquiv (I := I) x
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x i p •
          centeredChartTangentBasis (I := I) x p) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x i p •
          chartModelBasis E p from by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [map_smul, tangent_model_equiv_centered_chart_basis]]
    rw [lieCorrectionZero_cmm2_expand_slot0 (unitModel (I := I) (M := M) g₀ 2 W₀ x)
      (fun p => lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x i p) ((chartModelBasis E) j)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x i p * t) ?_
    rw [hW₀]
    exact lieCorrectionZero_iteratedCovGrad0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j
  have hW2 : unitModel (I := I) (M := M) g₀ 2 W₀ x
      (fun j' => if j' = 0 then chartModelBasis E i
        else tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x (centeredChartTangentBasis (I := I) x j)) x)) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x j p *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p (extChartAt I x x) := by
    rw [show (fun j' : Fin 2 => if j' = 0 then chartModelBasis E i
        else tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x
              (centeredChartTangentBasis (I := I) x j)) x)) =
      ![chartModelBasis E i,
        tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFCovDeriv (I := I) g₁ g_bg
            (smoothExtensionTangent (I := I) x
              (centeredChartTangentBasis (I := I) x j)) x)] from by
      funext q
      fin_cases q <;> rfl]
    rw [lieCorrectionZero_covW_basis (I := I) (M := M) g₁ g_bg x j]
    rw [show tangentSpaceModelContinuousLinearEquiv (I := I) x
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x j p •
          centeredChartTangentBasis (I := I) x p) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x j p •
          chartModelBasis E p from by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [map_smul, tangent_model_equiv_centered_chart_basis]]
    rw [lieCorrectionZero_cmm2_expand_slot1 (unitModel (I := I) (M := M) g₀ 2 W₀ x)
      (fun p => lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x j p) ((chartModelBasis E) i)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x j p * t) ?_
    rw [hW₀]
    exact lieCorrectionZero_iteratedCovGrad0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p
  rw [hW1, hW2]
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_phi0b_value_split (_hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (_hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg +
            lieCorrectionZeroField (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)]
      + Tensor0SSpace.toModel
          (lieCorrectionZeroTotalFib (I := I) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
              (unitTensor (I := I) (M := M) x)))
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) with hW₀
  set D₀ : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) with hD₀
  have hunfold : ∀ (Φ : SmoothCcTensor g₀ 2 2),
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W₀) x
        ![((chartModelBasis E) i : TangentSpace I x),
          ((chartModelBasis E) j : TangentSpace I x)] =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Φ.toSection x) D₀)
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro Φ
    rw [unitModel, operatorFieldApplication_toSection]
    rfl
  rw [hunfold, hunfold]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) =
    ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) +
    (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x D₀) from by
    rw [SmoothCcTensor.toSection_add]
    rfl]
  rw [Tensor0SSpace.toModel_add, add_apply]
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (arm2ReadoutCovDerivPair arm1ReadoutCovDeriv arm1ReadoutCovDeriv_center_eq
  arm2ReadoutCovDerivPair_center_eq partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial)
open DifferentialGeometry.Analysis.Sobolev.Chart
  (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
  (euclidPartial euclidPartial_def chartChristoffelEuclid chartChristoffelEuclid_def
  chartPushedRaw_tensorChartComponentRaw_contDiffOn)
end LieCorrectionZeroValue
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma lieCorrectionZero_pd_christoffel_sub (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m a b k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (fun y => chartChristoffel (I := I) gA x a b k y -
      chartChristoffel (I := I) gB x a b k y) (extChartAt I x x) =
    partialDeriv (E := E) m (chartChristoffel (I := I) gA x a b k) (extChartAt I x x) -
      partialDeriv (E := E) m (chartChristoffel (I := I) gB x a b k) (extChartAt I x x) := by
  have hy := extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hA := ((chartChristoffel_contDiffOn_interior (I := I) gA x a b k).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
  have hB := ((chartChristoffel_contDiffOn_interior (I := I) gB x a b k).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
  exact PDE.DeTurck.RicciLinearization.partialDeriv_sub (i := m) _ _ hA hB
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_pd_vfcomp_center (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp
      (I := I) gA gB x k y) (extChartAt I x x) =
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) gA x a b) (extChartAt I x x) *
        (chartChristoffel (I := I) gA x a b k (extChartAt I x x) -
          chartChristoffel (I := I) gB x a b k (extChartAt I x x)) +
      chartInvGramMatrix (I := I) gA x x a b *
        (partialDeriv (E := E) m (chartChristoffel (I := I) gA x a b k) (extChartAt I x x) -
          partialDeriv (E := E) m (chartChristoffel (I := I) gB x a b k) (extChartAt I x x))) := by
  have hy := extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  rw [show (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k y) =
    PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k from rfl,
    partialDeriv_chartDeTurckVFComp_eq (I := I) gA gB x m k hy]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [lieArm_chartInvGramOnE_center (I := I) gA x a b]))
section LieCorrectionZeroMasterValue
open DifferentialGeometry.Integral.DivergenceTheorem
  (partialDeriv chartRiemannTensor chartInvGramOnE_symm
  extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Geometry.Operator
  (chartInvGramMatrix chartChristoffel chartGramOnE chartInvGramOnE
  chartChristoffel_symm chartGramOnE_symm partialDeriv_chartInvGramOnE_eq)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ccTensor02Symm unitModel unitTensor deTurckLieCoeffField arm2ReadoutCovDerivPair
  arm1ReadoutCovDeriv)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv metricPerturbationPath)
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
  (gramBracket gramBracketDeriv chartChristoffel_eq_sum_invGramOnE_bracket
  partialDeriv_chartChristoffel_eq partialDeriv_gramBracket_eq)
private noncomputable def lieCorrectionZeroIg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => chartInvGramMatrix (I := I) g₁ x x a b
private noncomputable def lieCorrectionZeroCg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => chartGramMatrix (I := I) g₁ x x a b
private noncomputable def lieCorrectionZeroEv (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => F a b (extChartAt I x x)
private noncomputable def lieCorrectionZeroPd (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (F a b) (extChartAt I x x)
private noncomputable def lieCorrectionZeroDg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (chartGramOnE (I := I) g₁ x a b) (extChartAt I x x)
private noncomputable def lieCorrectionZeroDDg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m k a b => partialDeriv (E := E) m
    (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ x a b)) (extChartAt I x x)
private noncomputable def lieCorrectionZeroDig (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x)
private noncomputable def lieCorrectionZeroGa (g : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b k => chartChristoffel (I := I) g x a b k (extChartAt I x x)
private noncomputable def lieCorrectionZeroDGa (g : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b k => partialDeriv (E := E) m (chartChristoffel (I := I) g x a b k)
    (extChartAt I x x)
private noncomputable def lieCorrectionZeroGb (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b l => gramBracket (I := I) g₁ x a b l (extChartAt I x x)
private noncomputable def lieCorrectionZeroDGb (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b l => partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
    (extChartAt I x x)
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_center_interior (x : M) :
    extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
  extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_vfcomp_center (g₁ gP : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x k
        (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x a b *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) gP x a b k (extChartAt I x x)) := by
  rw [PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b]))
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_gramBracket_symm (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracket (I := I) g₁ x a b l y = gramBracket (I := I) g₁ x b a l y := by
  unfold DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramBracket
  rw [show chartGramOnE (I := I) g₁ x a b = chartGramOnE (I := I) g₁ x b a from
    funext fun y' => chartGramOnE_symm (I := I) g₁ x a b y']
  ring
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_hga1e (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l *
          gramBracket (I := I) g₁ x a b l (extChartAt I x x) := by
  rw [chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g₁ x a b k (extChartAt I x x)]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_hdga1e (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g₁ x a b k) (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x k l) (extChartAt I x x) *
            gramBracket (I := I) g₁ x a b l (extChartAt I x x) +
          chartInvGramMatrix (I := I) g₁ x x k l *
            partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
              (extChartAt I x x)) := by
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ x m a b k (lieCorrectionZero_center_interior (I := I) x)]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l,
    partialDeriv_gramBracket_eq (I := I) g₁ x m a b l (lieCorrectionZero_center_interior (I := I) x)]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_hdige (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x) =
      -∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x a p * chartInvGramMatrix (I := I) g₁ x x q b *
          partialDeriv (E := E) m (chartGramOnE (I := I) g₁ x p q) (extChartAt I x x) := by
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g₁ x (extChartAt I x x) m a b
    (lieCorrectionZero_center_interior (I := I) x)]
  refine congrArg Neg.neg ?_
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
    lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma lieCorrectionZero_hdgbe (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b l : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l) (extChartAt I x x) =
      partialDeriv (E := E) m
          (partialDeriv (E := E) a (chartGramOnE (I := I) g₁ x l b)) (extChartAt I x x) +
        partialDeriv (E := E) m
          (partialDeriv (E := E) b (chartGramOnE (I := I) g₁ x l a)) (extChartAt I x x) -
        partialDeriv (E := E) m
          (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ x a b)) (extChartAt I x x) := by
  rw [partialDeriv_gramBracket_eq (I := I) g₁ x m a b l (lieCorrectionZero_center_interior (I := I) x)]
  rfl
variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma lieCorrectionZero_covASc_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a m k p : Fin (Module.finrank ℝ E)) :
    lieCorrectionZeroCovASc (I := I) (M := M) g₁ g_bg x a m k p =
      (partialDeriv (E := E) a (chartChristoffel (I := I) g₁ x k m p) (extChartAt I x x) -
          partialDeriv (E := E) a (chartChristoffel (I := I) g_bg x k m p)
            (extChartAt I x x)) +
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m c (extChartAt I x x))) -
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k c p (extChartAt I x x))) -
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))) := by
  simp only [lieCorrectionZeroCovASc]
  rw [lieCorrectionZero_pd_christoffel_sub (I := I) g₁ g_bg x a k m p]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_covWSc_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a p : Fin (Module.finrank ℝ E)) :
    lieCorrectionZeroCovWSc (I := I) (M := M) g₁ g_bg x a p =
      (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (chartInvGramOnE (I := I) g₁ x a' b')
              (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x a' b' p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x a' b' p (extChartAt I x x)) +
          chartInvGramMatrix (I := I) g₁ x x a' b' *
            (partialDeriv (E := E) a (chartChristoffel (I := I) g₁ x a' b' p)
                (extChartAt I x x) -
              partialDeriv (E := E) a (chartChristoffel (I := I) g_bg x a' b' p)
                (extChartAt I x x)))) +
      ∑ c : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
          (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a' b' *
              (chartChristoffel (I := I) g₁ x a' b' c (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x a' b' c (extChartAt I x x))) := by
  simp only [lieCorrectionZeroCovWSc]
  rw [lieCorrectionZero_pd_vfcomp_center (I := I) g₁ g_bg x a p]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) rfl
    (Finset.sum_congr rfl (fun c _ => ?_))
  rw [lieCorrectionZero_vfcomp_center (I := I) g₁ g_bg x c]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_nscalar_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (i p : Fin (Module.finrank ℝ E)) :
    lieCorrectionZeroNScalar (I := I) (M := M) g₀ g₁ g_bg x i p =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g₀ x) i p := by
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect, lieCorrectionZeroIg, lieCorrectionZeroDig, lieCorrectionZeroGa, lieCorrectionZeroDGa]
  simp only [lieCorrectionZeroNScalar]
  rw [lieCorrectionZero_pd_vfcomp_center (I := I) g₁ g₀ x i p]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
      (Finset.sum_congr rfl (fun m _ => ?_))
      (Finset.sum_congr rfl (fun m _ => ?_)))
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) rfl
      (Finset.sum_congr rfl (fun m _ => ?_)))
  · rw [lieCorrectionZero_vfcomp_center (I := I) g₁ g₀ x m]
  · rw [lieCorrectionZero_vfcomp_center (I := I) g₁ g_bg x m]
  · rw [lieCorrectionZero_vfcomp_center (I := I) g₁ g₀ x m]
omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
private lemma lieCorrectionZero_D0_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x))
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) :=
  lieCorrectionZero_iteratedCovGrad0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_chrCorr_center (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (a b k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.christoffelFirstOrderCorrRaw (I := I) g₁ x F a b k
        (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q l)) *
          gramBracket (I := I) g₁ x a b l (extChartAt I x x) := by
  simp only [PDE.DeTurck.DeTurckLinearization.christoffelFirstOrderCorrRaw]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
    (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p,
    lieArm_chartInvGramOnE_center (I := I) g₁ x q l]
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_wc_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrRaw (I := I) g₁ g_bg x F k
        (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q b)) *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) g_bg x a b k (extChartAt I x x)) +
        chartInvGramMatrix (I := I) g₁ x x a b *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x))) := by
  simp only [PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrRaw]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
  · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
      lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
  · exact lieArm_chartInvGramOnE_center (I := I) g₁ x a b
  · exact lieCorrectionZero_chrCorr_center (I := I) g₁ x F a b k
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_d0_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (m k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv0Raw (I := I) g₁ g_bg x
        F m k (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a p)
                  (extChartAt I x x) * F p q (extChartAt I x x) *
                chartInvGramMatrix (I := I) g₁ x x q b +
              chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
                partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x q b)
                  (extChartAt I x x)))) *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) g_bg x a b k (extChartAt I x x)) +
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q b)) *
          (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ x a b k)
              (extChartAt I x x) -
            partialDeriv (E := E) m (chartChristoffel (I := I) g_bg x a b k)
              (extChartAt I x x)) +
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x) *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x)) +
        chartInvGramMatrix (I := I) g₁ x x a b *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x k p)
                      (extChartAt I x x) * F p q (extChartAt I x x) *
                    chartInvGramMatrix (I := I) g₁ x x q l +
                  chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x q l)
                      (extChartAt I x x)))) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x) +
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
                (extChartAt I x x)))) := by
  simp only [PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv0Raw]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_) ?_) ?_
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p]
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) ?_
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
        lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
    · exact lieCorrectionZero_pd_christoffel_sub (I := I) g₁ g_bg x m a b k
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_
    exact lieCorrectionZero_chrCorr_center (I := I) g₁ x F a b k
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieArm_chartInvGramOnE_center (I := I) g₁ x a b)
      (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
        (Finset.sum_congr rfl (fun l _ => ?_)))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
        (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
        (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x q l]
      · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p]
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p,
        lieArm_chartInvGramOnE_center (I := I) g₁ x q l]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_O0_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.order0PartRaw (I := I) g₁ g_bg x F i j
        (extChartAt I x x) =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
        (lieCorrectionZeroEv (I := I) x F)
        (lieCorrectionZeroDg (I := I) g₁ x) (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g_bg x) (lieCorrectionZeroGb (I := I) g₁ x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g_bg x) (lieCorrectionZeroDGb (I := I) g₁ x) i j := by
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection, DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection,
    DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection, DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative,
    DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection, lieCorrectionZeroIg, lieCorrectionZeroCg, lieCorrectionZeroEv, lieCorrectionZeroDg, lieCorrectionZeroDig,
      lieCorrectionZeroGa,
    lieCorrectionZeroDGa, lieCorrectionZeroGb, lieCorrectionZeroDGb]
  simp only [PDE.DeTurck.DeTurckLinearization.order0PartRaw]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ rfl)
    exact lieCorrectionZero_wc_center (I := I) g₁ g_bg x F k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_)
    exact lieCorrectionZero_pd_vfcomp_center (I := I) g₁ g_bg x i k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_)
    exact lieCorrectionZero_pd_vfcomp_center (I := I) g₁ g_bg x j k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
    · exact lieArm_chartGramOnE_center (I := I) g₁ x k j
    · exact lieCorrectionZero_d0_center (I := I) g₁ g_bg x F i k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
    · exact lieArm_chartGramOnE_center (I := I) g₁ x i k
    · exact lieCorrectionZero_d0_center (I := I) g₁ g_bg x F j k
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma lieCorrectionZero_tail2 (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gA : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x k₁ l *
          (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
            + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
            - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁])) =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.t2F (lieCorrectionZeroIg (I := I) gA x) (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroDGa (I := I) g₀ x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lieCorrectionZeroPd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.t2F, DeTurckCoefficients.LieCorrectionZeroNormalForm.r4F, lieCorrectionZeroIg, lieCorrectionZeroGa,
    lieCorrectionZeroDGa, lieCorrectionZeroEv, lieCorrectionZeroPd]
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_
  rw [lieR4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i l j k₁,
    lieR4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j l i k₁,
    lieR4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j l k₁]
omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_tailpf (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gA : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x l j r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
                  (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x l i r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j i r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
                  (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
                  (extChartAt I x x)))))) =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.tpfF (lieCorrectionZeroIg (I := I) gA x) (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroPd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.tpfF, DeTurckCoefficients.LieCorrectionZeroNormalForm.r4pfB, lieCorrectionZeroIg,
    lieCorrectionZeroGa, lieCorrectionZeroPd]
omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieCorrectionZero_master_inst (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (hFsym : ∀ a b, F a b = F b a)
    (i j : Fin (Module.finrank ℝ E)) :
    DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
      (lieCorrectionZeroEv (I := I) x F)
        (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g_bg x) i j
      + DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g₀ x) (lieCorrectionZeroEv (I := I) x F) i j
      + DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroEv (I := I) x F) i j
      + (2 : ℝ) * (DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock (lieCorrectionZeroIg (I := I) g₁ x)
        (lieCorrectionZeroCg (I := I) g₁ x)
          (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
          (lieCorrectionZeroEv (I := I) x F) i j
        + DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
          (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
          (lieCorrectionZeroEv (I := I) x F) j i)
      + DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureContractionBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroDGa (I := I) g₀ x) (lieCorrectionZeroEv (I := I) x F) i j
    = DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
      (lieCorrectionZeroEv (I := I) x F)
        (lieCorrectionZeroDg (I := I) g₁ x) (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g_bg x) (lieCorrectionZeroGb (I := I) g₁ x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g_bg x) (lieCorrectionZeroDGb (I := I) g₁ x) i j
      - (DeTurckCoefficients.LieCorrectionZeroNormalForm.t2F (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x)
          (lieCorrectionZeroDGa (I := I) g₀ x) (lieCorrectionZeroEv (I := I) x F) (lieCorrectionZeroPd (I := I) x F) i j
        - DeTurckCoefficients.LieCorrectionZeroNormalForm.tpfF (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x)
          (lieCorrectionZeroPd (I := I) x F) i j)
      - DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
        (lieCorrectionZeroEv (I := I) x F)
        (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g_bg x)
        i j :=
  DeTurckCoefficients.LieCorrectionZeroNormalForm.lie_correction_zero_normal_form _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a b => lieArm_chartInvGramMatrix_symm (I := I) g₁ x a b)
    (fun a b => lieArm_chartGramMatrix_symm (I := I) g₁ x a b)
    (fun a b => congrFun (hFsym a b) (extChartAt I x x))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartGramOnE_symm (I := I) g₁ x a b y))
    (fun a b k => chartChristoffel_symm (I := I) g₀ x a b k (extChartAt I x x))
    (fun a b k => chartChristoffel_symm (I := I) g₁ x a b k (extChartAt I x x))
    (fun a b k => chartChristoffel_symm (I := I) g_bg x a b k (extChartAt I x x))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g₀ x a b k y))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g₁ x a b k y))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g_bg x a b k y))
    (fun m k a b => congrArg
      (fun G => partialDeriv (E := E) m (partialDeriv (E := E) k G) (extChartAt I x x))
      (funext fun y => chartGramOnE_symm (I := I) g₁ x a b y))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (hFsym a b))
    (fun a b l => lieCorrectionZero_gramBracket_symm (I := I) g₁ x a b l (extChartAt I x x))
    (fun m a b l => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => lieCorrectionZero_gramBracket_symm (I := I) g₁ x a b l y))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_symm (I := I)
        g₁ x a b y))
    (fun l e => lieArm_gram_invGram_collapse (I := I) g₁ x l e)
    (fun a b k => lieCorrectionZero_hga1e (I := I) g₁ x a b k)
    (fun m a b k => lieCorrectionZero_hdga1e (I := I) g₁ x m a b k)
    (fun m a b => lieCorrectionZero_hdige (I := I) g₁ x m a b)
    (fun _a _b _l => rfl)
    (fun m a b l => lieCorrectionZero_hdgbe (I := I) g₁ x m a b l)
    i j
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_insert_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroDig (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroDGa (I := I) g₁ x) (lieCorrectionZeroDGa (I := I) g₀ x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorrectionZeroInsertionFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion, lieCorrectionZeroEv]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (Finset.sum_congr rfl (fun p _ => ?_)) (Finset.sum_congr rfl (fun p _ => ?_))
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_nscalar_raw (I := I) g₀ g₁ g_bg x i p)
      (lieCorrectionZero_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j)
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_nscalar_raw (I := I) g₀ g₁ g_bg x j p)
      (lieCorrectionZero_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p)
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_vb_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroVBFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorrectionZeroVBFib_basis_value (I := I) g₀ g₁ x _ i j]
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock, lieCorrectionZeroIg, lieCorrectionZeroCg, lieCorrectionZeroGa, lieCorrectionZeroEv]
  refine congrArg (fun t : ℝ => 2 * t)
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun ρ _ => ?_)))
  exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
    (lieCorrectionZero_vfcomp_center (I := I) g₁ g₀ x ρ)
    (lieCorrectionZero_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ρ k)
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_amixhalf_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
        (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorrectionZeroMixedConnectionHalfFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock, lieCorrectionZeroIg, lieCorrectionZeroCg, lieCorrectionZeroGa, lieCorrectionZeroEv]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))) rfl)
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k ml) rfl)
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_riem_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureContractionBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x)
        (lieCorrectionZeroDGa (I := I) g₀ x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorrectionZeroRiemFib_basis_value (I := I) g₀ g₁ x _ i j]
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureContractionBlock, DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureConnectionActionBlock, lieCorrectionZeroIg, lieCorrectionZeroGa,
    lieCorrectionZeroDGa, lieCorrectionZeroEv]
  refine congrArg Neg.neg
    (Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (Finset.sum_congr rfl (fun ρ _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_
    (lieCorrectionZero_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ρ m)
  rfl
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_committed (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection (lieCorrectionZeroIg (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroCg (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lieCorrectionZeroDig (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroGa (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroGa (I := I) g_bg x)
        (lieCorrectionZeroDGa (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroDGa (I := I) g_bg x)
        i j := by
  refine (lieCorrectionZero_committed_value (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j).trans ?_
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection, DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference,
    DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference, DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative,
    DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference, lieCorrectionZeroIg, lieCorrectionZeroCg, lieCorrectionZeroEv, lieCorrectionZeroDig, lieCorrectionZeroGa, lieCorrectionZeroDGa,
    ]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg Neg.neg
    (Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))))
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (Finset.sum_congr rfl (fun p _ => ?_))
      (Finset.sum_congr rfl (fun p _ => ?_)))
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_)))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
          (Finset.sum_congr rfl (fun p _ => ?_))
          (Finset.sum_congr rfl (fun p _ => ?_))) rfl)
    · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (lieCorrectionZero_covASc_raw (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i m k p)
        rfl
    · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (lieCorrectionZero_covASc_raw (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x j m k p)
        rfl
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_covWSc_raw (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i p) rfl
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_covWSc_raw (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x j p) rfl
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieCorrectionZero_d1r (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv
      (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
        (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g_bg x k₁ l₁ q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix
          (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x a b *
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x a b w
          (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x k₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j i q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
        (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g_bg x k₁ l₁ q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix
          (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x a b *
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x a b w
          (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x k₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i j q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j i q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]))) =
      DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder (lieCorrectionZeroIg (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroCg (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
        (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x)
          (lieCorrectionZeroGa (I := I) g_bg x)
        i j := by
  simp only [DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder, DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference,
    DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B, lieCorrectionZeroIg, lieCorrectionZeroCg, lieCorrectionZeroEv,
    lieCorrectionZeroGa]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
          (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
            (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
              (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
                (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂) ?_ ?_) ?_) ?_) ?_) ?_))
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
          (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
            (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
              (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂) ?_ ?_) ?_) ?_) ?_) ?_)) ?_
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieCorrectionZero_vfcomp_center (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x w)
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x w i j)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p) rfl))
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j w)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k1)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p) rfl))
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i w)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k1)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieArm1_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q p k1)
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_amix_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      (2 : ℝ) * (DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock (lieCorrectionZeroIg (I := I) g₁ x)
        (lieCorrectionZeroCg (I := I) g₁ x)
          (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
          (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)) i j
        + DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock (lieCorrectionZeroIg (I := I) g₁ x) (lieCorrectionZeroCg (I := I) g₁ x)
          (lieCorrectionZeroGa (I := I) g₁ x) (lieCorrectionZeroGa (I := I) g₀ x) (lieCorrectionZeroGa (I := I) g_bg x)
          (lieCorrectionZeroEv (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)) j i) := by
  rw [lieCorrectionZeroMixedConnectionFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  exact congrArg (fun t : ℝ => 2 * t)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (lieCorrectionZero_amixhalf_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j)
      (lieCorrectionZero_amixhalf_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i))
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieCorrectionZero_totalfib_split (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      Tensor0SSpace.toModel (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorrectionZeroVBFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  rw [lieCorrectionZeroTotalFib]
  rw [add_apply, add_apply,
    add_apply]
  rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add]
  rw [add_apply, add_apply, add_apply]

omit [SigmaCompactSpace M] in
theorem lie0_order0_eq (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg +
            lieCorrectionZeroField (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      PDE.DeTurck.DeTurckLinearization.order0PartRaw (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]))
        - (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp
          (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) *
          arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
        (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g_bg x k₁ l₁ q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix
          (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x a b *
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x a b w
          (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x k₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j i q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
        (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ i q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g_bg x k₁ l₁ q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix
          (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x a b *
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x a b w
          (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x k₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i j q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin
          (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
          (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
          ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
            DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l₁ j q
            (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
          DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j i q
          (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])))
          - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix
            (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l j r
          (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E)
          i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i l r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i j r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
            (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E),
           (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l i r
           (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
           (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
           (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x l k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j l r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j i r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
            (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E),
           (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j l r
           (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
           (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
           (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x j k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i j r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i l r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
            (extChartAt I x x)
          + DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g₀ x i k₁ r
            (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
            (extChartAt I x x))))))) := by
  refine (lieCorrectionZero_phi0b_value_split (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x
    i j).trans ?_
  rw [lieCorrectionZero_totalfib_split (I := I) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x _ i j]
  rw [lieCorrectionZero_committed (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j]
  rw [lieCorrectionZero_insert_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    g_bg x i j]
  rw [lieCorrectionZero_vb_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i
    j]
  rw [lieCorrectionZero_amix_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    g_bg x i j]
  rw [lieCorrectionZero_riem_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
    i j]
  rw [lieCorrectionZero_O0_center (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j]
  rw [lieCorrectionZero_tail2 (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j]
  rw [lieCorrectionZero_d1r (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j]
  rw [lieCorrectionZero_tailpf (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j]
  linear_combination lieCorrectionZero_master_inst (I := I) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
    (fun a b => lieArm_realizedGramDeriv_symm (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
    i j

end LieCorrectionZeroMasterValue

end DifferentialGeometry.Analysis.Spectral

end
