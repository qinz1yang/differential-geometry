import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPathChartLieDerivative
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPathChartRicciDerivative
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnectionDifferenceCoefficients
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieTopReanchor
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Set Function MeasureTheory intervalIntegral
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] in
private theorem unitModel_add_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (A + B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v +
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A + B) x =
      unitModel (I := I) (M := M) g₀ 2 A x +
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [hfun, add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] in
private theorem unitModel_sub_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (A - B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v -
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A - B) x =
      unitModel (I := I) (M := M) g₀ 2 A x -
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]
  rw [hfun, sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem ccBilin_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w =
      smoothCcTensorBilinForm (I := I) g₀ T x v w - smoothCcTensorBilinForm (I := I) g₀ T' x v
        w := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T' x v w]
  exact unitModel_sub_app (I := I) (M := M) g₀ T T' x
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] i))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem symmS_eq_self
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hS : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x v w = smoothCcTensorBilinForm (I := I) g₀ S x w v) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hS x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  rw [ccTensor02Symm, hswap, ← two_smul ℝ S, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

def rhsPathSlope
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (s : ℝ) (y : E) : ℝ :=
  (-2 : ℝ) *
      (∑ j : Fin (Module.finrank ℝ E),
        deriv (fun t : ℝ =>
          chartRiemannTensor (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)
            α i j k j y) s) +
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg α i k s y

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem hasDerivAt_rhsPath
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun t : ℝ => chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y)
      (rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg α i k s y) s := by
  let _ : NormedAddCommGroup ℝ := Real.normedAddCommGroup
  let _ : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
  rw [show (fun t : ℝ => chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) =
      (fun t : ℝ =>
        (-2 : ℝ) * chartRicciTensor (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) α i k y +
          chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) by
    funext t
    rw [chartDeTurckRicciRHS_def]]
  have hRic := hasDerivAt_metricPerturbationPath_chartRicciTensor (I := I)
    g₀ T T' hδ hδ' α i k hy hs
  have hLie := hasDerivAt_metricPerturbationPath_chartLieDeTurckComp_chartSlope (I := I)
    g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg α i k hy hs
  have hsum := (hRic.const_mul (-2 : ℝ)).add hLie
  change HasDerivAt
    (fun t : ℝ =>
      (-2 : ℝ) * chartRicciTensor (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) α i k y +
        chartLieDeTurckComp (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y)
    (rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg α i k s y) s at hsum
  exact hsum

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem deriv_rhsPath
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => chartDeTurckRicciRHS (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) s =
      rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg α i k s y := by
  exact (hasDerivAt_rhsPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    g_bg α i k hy (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)).deriv
omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricPerturbationPath_zero
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    metricPerturbationPath (I := I) g₀ T T' hδ hδ' 0 =
      tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
  refine riemannianMetric_eq_of_inner _ _ (fun x v w => ?_)
  rw [metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨le_rfl, zero_le_one⟩),
    tensorSectionRealizeMetric_inner, convexPerturbation_zero]
omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricPerturbationPath_one
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    metricPerturbationPath (I := I) g₀ T T' hδ hδ' 1 =
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
  refine riemannianMetric_eq_of_inner _ _ (fun x v w => ?_)
  rw [metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨zero_le_one, le_rfl⟩),
    tensorSectionRealizeMetric_inner, convexPerturbation_one]

def rhsChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i k (extChartAt I x x)


def rhsSumSlope
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x i k s (extChartAt I x x)


def lieSumSlope
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x i k s (extChartAt I x x)


def lieTopSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)

def lieTopCovSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k]

def lieTopTailSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieTopTail (I := I) g₀ T T'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k

def lieTopTailSwap
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieTopTail (I := I) g₀ T T'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k i

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieTopRaw_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g x f i j y =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g x f j i y := by
  unfold chartDeTurckCorrPrincipalSymbolExprRaw
  have h₁ : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b y *
            chartDeTurckCorrHessBlockRaw (I := I) g x f i a b k y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x j k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g x a b y *
              chartDeTurckCorrHessBlockRaw (I := I) g x f i a b k y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x k j y]
  have h₂ : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x i k y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b y *
            chartDeTurckCorrHessBlockRaw (I := I) g x f j a b k y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x k i y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g x a b y *
              chartDeTurckCorrHessBlockRaw (I := I) g x f j a b k y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k y]
  rw [h₁, h₂]
  ring

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieTop_add_tail
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
        lieTopTailSum (I := I) g₀ T T' hδ hδ' x v w s =
      lieTopCovSum (I := I) g₀ T T' hδ hδ' x v w s := by
  classical
  unfold lieTopSum lieTopTailSum lieTopCovSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← mul_add]
  rw [← lieTop_cov_eq_raw (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieTop_add_swap
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
        lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) := by
  classical
  unfold lieTopSum lieTopTailSwap
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
            ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i] := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← mul_add]
      rw [lieTopRaw_symm (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i k
        (extChartAt I x x)]
      rw [← lieTop_cov_eq_raw (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k i]
    _ = _ := by
      simpa using unitModel_basis_expand_two (I := I) (M := M) g₀
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j))


def lieOneSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieDeTurckOrder1Raw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)


def lieZeroSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      order0PartRaw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieSum_eq_split
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold lieSumSlope lieTopSum lieOneSum lieZeroSum
  simp_rw [lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x _ _ s hy]
  simp only [mul_add, Finset.sum_add_distrib]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem ricciSum_eq_lin
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
        (∑ j : Fin (Module.finrank ℝ E),
          deriv (fun t : ℝ => chartRiemannTensor (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
              (extChartAt I x x)) s)) =
      linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hderiv := (hasDerivAt_realizedRicciChartSum_general (I := I)
    g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs).deriv
  calc
    _ = deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := hderiv.symm
    _ = linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s :=
      (linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I)
        g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs).symm

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSlope_eq_lin
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x v w s +
      lieSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSumSlope, lieSumSlope]
  simp only [rhsPathSlope, mul_add, Finset.sum_add_distrib]
  have hscale : (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
            ((-2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
              deriv (fun t : ℝ => chartRiemannTensor (I := I)
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
                  (extChartAt I x x)) s)) =
      (-2 : ℝ) *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
              ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
              (∑ j : Fin (Module.finrank ℝ E),
                deriv (fun t : ℝ => chartRiemannTensor (I := I)
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
                    (extChartAt I x x)) s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hscale, ricciSum_eq_lin (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs]

omit [SigmaCompactSpace M] in
theorem rhsSlope_eq_raw [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSlope_eq_lin (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w hs]
  have hRic := linearizedRicciAt_eq_threeArm_connectionDifferenceCoeff (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x ![v, w]
  have hRic' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w s = unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) := by
    simpa using hRic
  rw [hRic']
  rw [lieSum_eq_split (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s]
  ring

def rhsTopTerm
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ 4 2
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
    (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j))

def rhsLowTerm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
            (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
              linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
            (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
              linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
    lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
    lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s -
    lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rhsTop_eq_raw
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    rhsTopTerm (I := I) g₀ T T' hδ hδ' x v w s =
      (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s := by
  have hSsymm : ∀ (y : M) (u z : TangentSpace I y),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') y u z =
        smoothCcTensorBilinForm (I := I) g₀ (T - T') y z u := by
    intro y u z
    rw [ccBilin_sub (I := I) (M := M) g₀ T T' y u z,
      ccBilin_sub (I := I) (M := M) g₀ T T' y z u,
      hTsymm y u z, hT'symm y u z]
  have hsymmS : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self (I := I) (M := M) g₀ (T - T') hSsymm
  have hLie := lieTop_add_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x v w s
  rw [hsymmS] at hLie
  unfold rhsTopTerm
  rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq (I := I) (M := M) g₀ T T' hδ hδ' s,
    operatorFieldApplication_sub_left, operatorFieldApplication_add_left, unitModel_sub_app, unitModel_add_app,
    ← hLie]
  ring

omit [SigmaCompactSpace M] in
theorem rhsSlope_eq_split [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      rhsTopTerm (I := I) g₀ T T' hδ hδ' x v w s +
        rhsLowTerm (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSlope_eq_raw (I := I) g₀ g_bg T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w hs]
  rw [rhsTop_eq_raw (I := I) g₀ T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w s]
  unfold rhsLowTerm
  rw [unitModel_add_app, unitModel_add_app]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_contDiffAt [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have heq : rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i k (extChartAt I x x)) := by
    funext t
    unfold rhsChartSum
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [chartFComponentOnE_deTurckRicciRHS_eq (I := I) g_bg
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i k hy]
  rw [heq]
  exact realizedDeTurckRicciChartSum_contDiffAt (I := I)
    g₀ g_bg T T' hδ hδ' x v w hs

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_rhsSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    HasDerivAt (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s) s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold rhsChartSum rhsSumSlope
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  exact (hasDerivAt_rhsPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    g_bg x i k hy hs).const_mul _


omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv_rhsSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    deriv (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
      rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  exact (hasDerivAt_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)).deriv


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_continuous [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) (Icc (0 : ℝ) 1) := by
  intro s hs
  exact (rhsSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ'
    x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSlope_integrable [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      volume 0 1 := by
  let f : ℝ → ℝ := rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w
  have hcd : ContDiffOn ℝ ∞ f (metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    fun s hs => (rhsSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ'
      x v w hs).contDiffWithinAt
  have hcont : ContinuousOn (deriv f) (Icc (0 : ℝ) 1) :=
    (hcd.continuousOn_deriv_of_isOpen metricPerturbationPathDomain_isOpen
      (by exact_mod_cast le_top)).mono
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)
  have hint : IntervalIntegrable (deriv f) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  refine hint.congr_ae ?_
  have hsub : Ioo (0 : ℝ) 1 ⊆
      {s | deriv f s = rhsSumSlope (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact deriv_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w hs
  have hnull : (volume.restrict (uIoc (0 : ℝ) 1)) (Ioo (0 : ℝ) 1)ᶜ = 0 := by
    rw [uIoc_of_le zero_le_one]
    rw [Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Ioo (0 : ℝ) 1)ᶜ ∩ Ioc 0 1 ⊆ {1} := by
      intro s hs
      obtain ⟨hsc, hs0, hs1⟩ := hs
      rw [mem_compl_iff, mem_Ioo, not_and_or, not_lt, not_lt] at hsc
      rcases hsc with h | h
      · exact absurd hs0 (not_lt.mpr h)
      · exact (le_antisymm hs1 h) ▸ rfl
    exact measure_mono_null hsub1 (by simp)
  refine measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_sub_eq_int [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 1 -
        rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 0 =
      ∫ s in (0 : ℝ)..1,
        rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hcont := rhsSum_continuous (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
        (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s) s := by
    intro s hs
    exact hasDerivAt_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)
  have hint := rhsSlope_integrable (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w
  exact (integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint).symm

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
