import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace r s I y)]
      (x : M) :
    NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
private theorem bdMonoRefold_appCc_eq_pairTrace_appCc (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (G : SmoothCcTensor g₀ 0 4) (σ : Equiv.Perm (Fin 4)) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (domDomCongrSection (I := I) g₀
                (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G)))) S =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ) G := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection]
  apply ContinuousLinearMap.ext
  intro t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [bdTensor0S_zero_rank_decomp (I := I) (M := M) x t]
  simp only [map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  congr 1
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (domDomCongrSection (I := I) g₀
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x)) v]
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ).toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x))) =
    curvatureActionMonomialTrace (I := I) (M := M) g₁
      (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) from rfl]
  rw [curvatureActionMonomialTrace, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg₂ (· * ·) rfl ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) =
    unitModel (I := I) (M := M) g₀ 4 G x from rfl]
  refine congrArg _ ?_
  funext i
  rw [Equiv.trans_apply]
  generalize σ i = k
  fin_cases k <;> rfl

omit [BoundarylessManifold I M] in
theorem bdLiePairTraceFamily_appCc_eq_familySecondGradient
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ q ε s) T =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 T) := by
  rw [deTurckLieCovDerivRefoldPairTraceFamily, deTurckLieCovDerivRefoldC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_smul_left, appCc_add_left]
  rw [bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 0),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 1),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 2),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

omit [BoundarylessManifold I M] in
private lemma lrRealizedFam_zero [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    realizedFam (I := I) g₀ T 0 hδ hδZ 0 = g₀ := by
  by_cases h : |1 - (0 : ℝ)| * δ + |(0 : ℝ)| * δ < 1
  · refine riemannianMetric_eq_of_inner _ _ (fun b v w => ?_)
    have hmem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) := Set.mem_setOf.mpr h
    rw [realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hmem b v w,
      convexPerturbation_zero]
    have hz : ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) b v w = 0 := by
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
      ring
    rw [hz, add_zero]
  · rw [realizedFam, dif_neg h]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrKoszulCovec_congr {g g' : SmoothRiemannianMetric I M} (h : g = g')
    (S : SmoothCcTensor g 0 2) (S' : SmoothCcTensor g' 0 2)
    (hs : HEq S S') (x : M) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g S x u ζ = linearizedKoszulCovec (I := I) g' S' x u ζ := by
  subst h
  rw [eq_of_heq hs]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private lemma lrSymmS_eq_self (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
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
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]


private lemma lrConnDiff_linearization (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (u ζ : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ =
      s • DifferentialGeometry.Geometry.Operator.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
        (linearizedKoszulCovec (I := I) g₀ T x u ζ) := by
  classical
  have h0_mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨le_refl (0 : ℝ), zero_le_one⟩
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hzero := lrRealizedFam_zero (I := I) (M := M) g₀ T hδ hδZ
  have hkey := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T 0 hδ_lt hδ hδ_lt hδZ
    h0_mem hs_mem x u ζ
  rw [sub_zero] at hkey
  have hvel : HEq (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) T := by
    rw [show realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0 =
        ccTensorRetagMetric (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (ccTensor02Symm (I := I) (M := M) g₀ (T - 0)) from rfl]
    rw [sub_zero, lrSymmS_eq_self (I := I) (M := M) g₀ T hTsymm]
    rw [hzero]
    exact HEq.rfl
  have hlkc : linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
      (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x u ζ =
      linearizedKoszulCovec (I := I) g₀ T x u ζ :=
    lrKoszulCovec_congr (I := I) (M := M) hzero
      (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) T hvel x u ζ
  rw [hlkc] at hkey
  calc PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ
      = PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x u ζ := by rw [hzero]
    _ = s • DifferentialGeometry.Geometry.Operator.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
          (linearizedKoszulCovec (I := I) g₀ T x u ζ) := hkey


private lemma lrConnDiff_inner (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (u ζ z : TangentSpace I x) :
    (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ) z =
      s * linearizedKoszulCovec (I := I) g₀ T x u ζ z := by
  rw [lrConnDiff_linearization (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x u ζ,
    map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    DifferentialGeometry.Geometry.Operator.inner_metricSharp]


private def linearizedKoszulTensor [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) •
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
        (covGrad (I := I) (M := M) g₀ 0 2 T)
      + domDomCongrSection (I := I) g₀ (finRotate 3)
        (covGrad (I := I) (M := M) g₀ 0 2 T)
      - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (covGrad (I := I) (M := M) g₀ 0 2 T))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrKT_unitModel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (z u ζ : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![z, u, ζ] =
      linearizedKoszulCovec (I := I) g₀ T x u ζ z := by
  rw [linearizedKoszulTensor, bdUnitModel_smul, bdUnitModel_sub, bdUnitModel_add]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, smul_eq_mul]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [linearizedKoszulCovec_apply]
  have h1 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x)
      ((Equiv.swap (0 : Fin 3) 2) i)) = ![ζ, u, z] := by
    funext i
    fin_cases i <;> rfl
  have h2 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
      ![u, ζ, z] := by
    funext i
    fin_cases i <;> rfl
  have h3 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x)
      ((Equiv.swap (1 : Fin 3) 2) i)) = ![z, ζ, u] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, h3]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private lemma lrUnitEval_tsmdiffAt (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
          W.toSection y) (unitZeroSec (I := I) (M := M) y)) x := by
  have hsm := ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  exact ((hsm x).mdifferentiableAt (by simp))

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrUnitModel_covGrad_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) (v : Fin (n + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) x v =
      Tensor0SSpace.toModel
        (show Tensor0SSpace n I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
                W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) := by
  rw [unitModel]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 n W x
    (unitZeroSec (I := I) (M := M) x) v]
  congr 1
  rw [tensorCovDerivAt_def]
  rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 0 n
    (LeviCivita (I := I) g) W.toSection (unitZeroSec (I := I) (M := M)) x (v 0)]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
      (fun y : M => unitZeroSec (I := I) (M := M) y) x (v 0)) = 0 from
    Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (v 0)]
  rw [map_zero, sub_zero]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
private lemma lrExtDerivFun_apply_scalar (f : M → ℝ) {x : M} (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma lrCovDerivConnDiff_self_zero (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v0 p q : TangentSpace I x) :
    covDerivConnDiff (I := I) g₀ g₀
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x q)
        (smoothExtensionTangent (I := I) x p) x = 0 := by
  classical
  have hexpand : covDerivConnDiff (I := I) g₀ g₀
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x q)
      (smoothExtensionTangent (I := I) x p) x =
      (LeviCivita (I := I) g₀).toFun
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
            (smoothExtensionTangent (I := I) x q) (smoothExtensionTangent (I := I) x p)) x
          (smoothExtensionTangent (I := I) x v0 x)
        - PDE.DeTurck.connDiff (I := I) g₀ g₀ x (smoothExtensionTangent (I := I) x p x)
            (covApply (LeviCivita (I := I) g₀)
              (smoothExtensionTangent (I := I) x v0)
              (smoothExtensionTangent (I := I) x q) x)
        - PDE.DeTurck.connDiff (I := I) g₀ g₀ x
            (covApply (LeviCivita (I := I) g₀)
              (smoothExtensionTangent (I := I) x v0)
              (smoothExtensionTangent (I := I) x p) x)
            (smoothExtensionTangent (I := I) x q x) := rfl
  rw [hexpand]
  have hdz : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
      (smoothExtensionTangent (I := I) x q) (smoothExtensionTangent (I := I) x p) =
      (0 : ℝ) • smoothExtensionTangent (I := I) x v0 := by
    funext b
    rw [Pi.smul_apply, zero_smul]
    change PDE.DeTurck.connDiff (I := I) g₀ g₀ b
        (smoothExtensionTangent (I := I) x p b)
        (smoothExtensionTangent (I := I) x q b) = 0
    exact bdConnDiff_self_apply (I := I) (M := M) g₀ b _ _
  rw [hdz]
  have hσX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (smoothExtensionTangent (I := I) x v0 b)) x :=
    smoothExtensionTangent_mdiff (I := I) x v0 x
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := smoothExtensionTangent (I := I) x v0) (x := x) (0 : ℝ) hσX (Set.mem_univ x)
  rw [hsmul, ContinuousLinearMap.smul_apply]
  rw [bdConnDiff_self_apply (I := I) (M := M) g₀ x, bdConnDiff_self_apply (I := I) (M := M) g₀ x,
    zero_smul]
  simp


private theorem lrKernel_inner (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (v0 v1 p q : TangentSpace I x) :
    (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 p q) v1 =
      s * unitModel (I := I) (M := M) g₀ 4
          (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
          ![v0, v1, p, q]
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p q)
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v1 v0)
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
              (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p v0)
              q) v1
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p
              (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x q v0))
            v1 := by
  classical
  by_cases hs0 : s = 0
  · subst hs0
    rw [lrRealizedFam_zero (I := I) (M := M) g₀ T hδ hδZ]
    have hker0 : connDiffCovDerivOp (I := I) g₀ g₀ x v0 p q = 0 := by
      rw [DifferentialGeometry.Analysis.Sobolev.dLaCovKernel_backgroundSplit (I := I) (M := M) g₀ g₀ g₀ x v0 p q]
      simp only [bdConnDiff_self_apply (I := I) (M := M) g₀ x, sub_self, add_zero]
    rw [hker0]
    simp only [bdConnDiff_self_apply (I := I) (M := M) g₀ x, map_zero,
      ContinuousLinearMap.zero_apply, zero_mul, sub_self]
  · have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    rw [DifferentialGeometry.Analysis.Sobolev.dLaCovKernel_backgroundSplit (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 p q]
    rw [lrCovDerivConnDiff_self_zero (I := I) (M := M) g₀ x v0 p q, sub_zero]
    set gs := realizedFam (I := I) g₀ T 0 hδ hδZ s with hgs_def
    set X0 : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v0 with hX0_def
    set Z1 : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v1 with hZ1_def
    set Pe : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x p with hPe_def
    set Qe : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x q with hQe_def
    have hX0x : X0 x = v0 := smoothExtensionTangent_eq (I := I) x v0
    have hZ1x : Z1 x = v1 := smoothExtensionTangent_eq (I := I) x v1
    have hPex : Pe x = p := smoothExtensionTangent_eq (I := I) x p
    have hQex : Qe x = q := smoothExtensionTangent_eq (I := I) x q
    set Ψ : Π b : M, TangentSpace I b := fun b =>
      DifferentialGeometry.Geometry.Operator.metricSharp (I := I) gs b
        (linearizedKoszulCovec (I := I) g₀ T b (Pe b) (Qe b)) with hΨ_def
    have hpoint : ∀ (b : M) (u ζ : TangentSpace I b),
        PDE.DeTurck.connDiff (I := I) gs g₀ b u ζ =
          s • DifferentialGeometry.Geometry.Operator.metricSharp (I := I) gs b
            (linearizedKoszulCovec (I := I) g₀ T b u ζ) :=
      fun b u ζ => lrConnDiff_linearization (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs b u ζ
    have hinner_cd : ∀ (b : M) (u ζ z : TangentSpace I b),
        gs.inner b (PDE.DeTurck.connDiff (I := I) gs g₀ b u ζ) z =
          s * linearizedKoszulCovec (I := I) g₀ T b u ζ z :=
      fun b u ζ z => lrConnDiff_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs b u ζ z
    have hconn_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) gs g₀
        (smoothExtensionTangent_contMDiff (I := I) x p)
        (smoothExtensionTangent_contMDiff (I := I) x q)
    have hΨ_eq : Ψ = fun b : M => s⁻¹ •
        PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) := by
      funext b
      rw [hΨ_def]
      rw [hpoint b (Pe b) (Qe b), smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hΨ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Ψ b)) := by
      have hsmul' := ContMDiff.smul_section
        (f := fun _ : M => s⁻¹)
        (s := fun b : M => PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b))
        contMDiff_const hconn_smooth
      refine hsmul'.congr (fun b => ?_)
      refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b) ?_
      change Ψ b = ((fun _ : M => s⁻¹) • fun b : M =>
        PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b)) b
      rw [show ((fun _ : M => s⁻¹) • fun b : M =>
          PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b)) b =
          s⁻¹ • PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) from rfl]
      exact congrFun hΨ_eq b
    have hσΨ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Ψ b)) x :=
      (hΨ_smooth x).mdifferentiableAt (by simp)
    have hσZ1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Z1 b)) x :=
      smoothExtensionTangent_mdiff (I := I) x v1 x
    have hexpand : covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x =
        (LeviCivita (I := I) g₀).toFun
            (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gs) Qe Pe) x (X0 x)
          - PDE.DeTurck.connDiff (I := I) gs g₀ x (Pe x)
              (covApply (LeviCivita (I := I) g₀) X0 Qe x)
          - PDE.DeTurck.connDiff (I := I) gs g₀ x
              (covApply (LeviCivita (I := I) g₀) X0 Pe x) (Qe x) := rfl
    have hdiffSec : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gs) Qe Pe =
        s • Ψ := by
      funext b
      rw [Pi.smul_apply]
      change PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) = s • Ψ b
      rw [hΨ_def]
      exact hpoint b (Pe b) (Qe b)
    have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
      (σ := Ψ) (x := x) s hσΨ (Set.mem_univ x)
    have hE2 : gs.inner x (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x) v1 =
        s * gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
              (covApply (LeviCivita (I := I) g₀) X0 Qe x)) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (covApply (LeviCivita (I := I) g₀) X0 Pe x) q) v1 := by
      rw [hexpand, hdiffSec, hsmul, hX0x, hPex, hQex]
      rw [ContinuousLinearMap.smul_apply]
      rw [map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hmc : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x (X0 x)
        - gs.inner x ((LeviCivita (I := I) gs).toFun Ψ x (X0 x)) (Z1 x)
        - gs.inner x (Ψ x) ((LeviCivita (I := I) gs).toFun Z1 x (X0 x)) = 0 :=
      metricCovDeriv_self_eq_zero (I := I) gs hσΨ hσZ1
    rw [hX0x, hZ1x] at hmc
    have hΨhat : (LeviCivita (I := I) gs).toFun Ψ x v0 =
        (LeviCivita (I := I) g₀).toFun Ψ x v0
          + PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0 := by
      have h := PDE.DeTurck.connDiff_apply (I := I) gs g₀ (σ := Ψ) hσΨ v0
      rw [h]
      abel
    have hZ1hat : (LeviCivita (I := I) gs).toFun Z1 x v0 =
        (LeviCivita (I := I) g₀).toFun Z1 x v0
          + PDE.DeTurck.connDiff (I := I) gs g₀ x (Z1 x) v0 := by
      have h := PDE.DeTurck.connDiff_apply (I := I) gs g₀ (σ := Z1) hσZ1 v0
      rw [h]
      abel
    rw [hZ1x] at hZ1hat
    have hΨval : Ψ x = DifferentialGeometry.Geometry.Operator.metricSharp (I := I) gs x
        (linearizedKoszulCovec (I := I) g₀ T x p q) := by
      rw [hΨ_def]
      change DifferentialGeometry.Geometry.Operator.metricSharp (I := I) gs x
          (linearizedKoszulCovec (I := I) g₀ T x (Pe x) (Qe x)) = _
      rw [hPex, hQex]
    have hΨinner : ∀ w : TangentSpace I x, gs.inner x (Ψ x) w =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
          ![w, p, q] := by
      intro w
      rw [hΨval, DifferentialGeometry.Geometry.Operator.inner_metricSharp,
        lrKT_unitModel (I := I) (M := M) g₀ T x w p q]
    set Z1s : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x v1,
        smoothExtensionTangent_contMDiff (I := I) x v1⟩ with hZ1s_def
    set Ps : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x p,
        smoothExtensionTangent_contMDiff (I := I) x p⟩ with hPs_def
    set Qs : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x q,
        smoothExtensionTangent_contMDiff (I := I) x q⟩ with hQs_def
    set KTsec : Π y : M, Tensor0SSpace 3 I y := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (linearizedKoszulTensor (I := I) (M := M) g₀ T).toSection y)
          (unitZeroSec (I := I) (M := M) y)
      with hKTsec_def
    have hKTsec_toModel : ∀ (y : M) (w : Fin 3 → TangentSpace I y),
        Tensor0SSpace.toModel (KTsec y) w =
          unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) y w := by
      intro y w
      rw [hKTsec_def]
      rw [unitModel, show unitTensor (I := I) (M := M) y =
        unitZeroSec (I := I) (M := M) y from rfl]
    have hscal_eq : (fun b : M => gs.inner b (Ψ b) (Z1 b)) =
        Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M KTsec u (Z1s u)) z (Ps z))
            y (Qs y)) := by
      funext b
      rw [curried3_toModel_eval (I := I) (M := M) KTsec Z1s Ps Qs b]
      rw [hKTsec_toModel b ![Z1s b, Ps b, Qs b]]
      change gs.inner b (Ψ b) (Z1 b) =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) b
          ![Z1 b, Pe b, Qe b]
      rw [hΨ_def]
      change gs.inner b (DifferentialGeometry.Geometry.Operator.metricSharp (I := I) gs b
          (linearizedKoszulCovec (I := I) g₀ T b (Pe b) (Qe b))) (Z1 b) = _
      rw [DifferentialGeometry.Geometry.Operator.inner_metricSharp,
        lrKT_unitModel (I := I) (M := M) g₀ T b (Z1 b) (Pe b) (Qe b)]
    have hW_mdiff : TensorSectionMDiffAt (I := I) 3 KTsec x := by
      rw [hKTsec_def]
      exact lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3
        (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
    have hpeel := peel3_core (I := I) (M := M) g₀ KTsec hW_mdiff Z1s Ps Qs v0
    have hZ1s_coe : (fun y : M => (Z1s y : TangentSpace I y)) = Z1 := rfl
    have hPs_coe : (fun y : M => (Ps y : TangentSpace I y)) = Pe := rfl
    have hQs_coe : (fun y : M => (Qs y : TangentSpace I y)) = Qe := rfl
    have hZ1sx : (Z1s x : TangentSpace I x) = v1 := smoothExtensionTangent_eq (I := I) x v1
    have hPsx : (Ps x : TangentSpace I x) = p := smoothExtensionTangent_eq (I := I) x p
    have hQsx : (Qs x : TangentSpace I x) = q := smoothExtensionTangent_eq (I := I) x q
    rw [hZ1s_coe, hPs_coe, hQs_coe, hZ1sx, hPsx, hQsx] at hpeel
    have hbridge : unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
        ![v0, v1, p, q] =
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            KTsec x v0) ![v1, p, q] := by
      have h := lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
        (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![v0, v1, p, q]
      rw [h]
      rw [show (![v0, v1, p, q] : Fin 4 → TangentSpace I x) 0 = v0 from rfl]
      rw [show Matrix.vecTail (![v0, v1, p, q] : Fin 4 → TangentSpace I x) = ![v1, p, q] from by
        funext k
        fin_cases k <;> rfl]
    have hED : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0 =
        extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M KTsec u (Z1s u)) z (Ps z))
            y (Qs y))) x v0 := by
      rw [directionalDeriv_eq, lrExtDerivFun_apply_scalar, hscal_eq]
      rfl
    have hKW : ∀ (a b c : TangentSpace I x),
        Tensor0SSpace.toModel (KTsec x) ![a, b, c] =
          unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
            ![a, b, c] :=
      fun a b c => hKTsec_toModel x ![a, b, c]
    rw [hKW, hKW, hKW] at hpeel
    have hQL3 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
        (covApply (LeviCivita (I := I) g₀) X0 Qe x)) v1 =
        s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
          ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0] := by
      rw [hinner_cd x p (covApply (LeviCivita (I := I) g₀) X0 Qe x) v1]
      rw [show covApply (LeviCivita (I := I) g₀) X0 Qe x =
        (LeviCivita (I := I) g₀).toFun Qe x (X0 x) from rfl, hX0x]
      rw [← lrKT_unitModel (I := I) (M := M) g₀ T x v1 p
        ((LeviCivita (I := I) g₀).toFun Qe x v0)]
    have hQL2 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
        (covApply (LeviCivita (I := I) g₀) X0 Pe x) q) v1 =
        s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
          ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q] := by
      rw [hinner_cd x (covApply (LeviCivita (I := I) g₀) X0 Pe x) q v1]
      rw [show covApply (LeviCivita (I := I) g₀) X0 Pe x =
        (LeviCivita (I := I) g₀).toFun Pe x (X0 x) from rfl, hX0x]
      rw [← lrKT_unitModel (I := I) (M := M) g₀ T x v1
        ((LeviCivita (I := I) g₀).toFun Pe x v0) q]
    have hQ0 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
        (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0) v1 =
        s * gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1 := by
      have hcdpq : PDE.DeTurck.connDiff (I := I) gs g₀ x p q = s • Ψ x := by
        rw [hΨval]
        exact hpoint x p q
      rw [hcdpq]
      rw [show PDE.DeTurck.connDiff (I := I) gs g₀ x (s • Ψ x) v0 =
          s • PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0 from by
        rw [map_smul, ContinuousLinearMap.smul_apply]]
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hQ1 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) =
        s * gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hinner_cd x p q (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0)]
      rw [hΨval, DifferentialGeometry.Geometry.Operator.inner_metricSharp]
    have hΨZ1hat : gs.inner x (Ψ x) ((LeviCivita (I := I) gs).toFun Z1 x v0) =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
            ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
          + gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hZ1hat, map_add]
      rw [hΨinner ((LeviCivita (I := I) g₀).toFun Z1 x v0)]
    have hmc' : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0 =
        gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
          + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1
          + (unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
            + gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0)) := by
      have h1 : gs.inner x ((LeviCivita (I := I) gs).toFun Ψ x v0) v1 =
          gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
            + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1 := by
        rw [hΨhat, map_add, ContinuousLinearMap.add_apply]
      rw [← hΨZ1hat, ← h1]
      linarith [hmc]
    have hpeel' : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          KTsec x v0) ![v1, p, q] =
        directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q]
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0] := by
      rw [hED]
      exact hpeel
    have hE3 : s * gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1 =
        s * unitModel (I := I) (M := M) g₀ 4
            (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
            ![v0, v1, p, q]
          + s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q]
          + s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0]
          - s * gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1
          - s * gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hbridge, hpeel', hmc']
      ring
    rw [show (gs.inner x) (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x
        + PDE.DeTurck.connDiff (I := I) gs g₀ x
            (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0
        - PDE.DeTurck.connDiff (I := I) gs g₀ x
            (PDE.DeTurck.connDiff (I := I) gs g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) gs g₀ x p
            (PDE.DeTurck.connDiff (I := I) gs g₀ x q v0)) v1 =
        gs.inner x (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x) v1
          + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (PDE.DeTurck.connDiff (I := I) gs g₀ x p v0) q) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
              (PDE.DeTurck.connDiff (I := I) gs g₀ x q v0)) v1 from by
      rw [map_sub, map_sub, map_add]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
    rw [hE2, hQL3, hQL2, hQ0, hQ1]
    linear_combination hE3


def connDiffGmLoweredTensor [SigmaCompactSpace M] (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 3
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (fullRaisedEndoField (I := I) (M := M) gm g₀))
    (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ gm))

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrOmegaHat_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 2)) (m 0) := by
  rw [unitModel]
  rw [show (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 3 0 x
        (fullRaisedEndoField (I := I) (M := M) gm g₀ x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffGmLoweredTensor, appCcRS_toSection]
    rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (connDiffLoweredCc (I := I) g₀ gm)) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 3 =>
      Function.update (fun k : Fin 3 => (m k : E)) 0
        (fullRaisedEndoField (I := I) (M := M) gm g₀ x ((fun k : Fin 3 => (m k : E)) 0))
        ((finRotate 3) i)) =
    (fun i : Fin 3 => (((![m 1, m 2,
      (show TangentSpace I x from
        Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) gm g₀ x (m 0))] :
      Fin 3 → TangentSpace I x)) i : E)) from by
    funext i
    fin_cases i
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 0) = (m 1 : E)
      rw [show (finRotate 3) (0 : Fin 3) = 1 from by decide]
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 1) = (m 2 : E)
      rw [show (finRotate 3) (1 : Fin 3) = 2 from by decide]
      rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 2) =
        (show TangentSpace I x from
          Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) gm g₀ x (m 0))
      rw [show (finRotate 3) (2 : Fin 3) = 0 from by decide]
      rw [Function.update_self]
      rfl]
  rw [bdConnDiffLoweredCc_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  exact bdG0_inner_lambda (I := I) (M := M) g₀ gm x
    (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 2)) (m 0)


def connDiffQuadraticPairedTensor [SigmaCompactSpace M] (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ gm))
    (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)


def connDiffQuadraticComposedTensor (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ gm))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
      (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm))

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrArmSlotTuple (g₀ gm : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    (Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0))) =
      (fun i : Fin 3 => (((![(show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 2, m 3] :
        Fin 3 → TangentSpace I x)) i : E)) := by
  funext k
  fin_cases k
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (0 : Fin 3) =
      ((show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) : E)
    rw [Function.update_self]
    rfl
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (1 : Fin 3) = (m 2 : E)
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    rfl
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (2 : Fin 3) = (m 3 : E)
    rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrQB_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
        (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) := by
  rw [unitModel]
  rw [show (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      bilinearSlotInsertCLM (I := I) (M := M) 2 x (connDiffEndo (I := I) (M := M) g₀ gm x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffQuadraticPairedTensor, appCcRS_toSection]
    rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 2 x
    (connDiffEndo (I := I) (M := M) g₀ gm x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun k : Fin 4 => (m k : E))]
  rw [slotInsertEndoFib_apply_eval]
  rw [lrArmSlotTuple (I := I) (M := M) g₀ gm x m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3 (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm) x from rfl]
  rw [lrOmegaHat_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrQA_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
        (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) (m 3)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      bilinearSlotInsertCLM (I := I) (M := M) 2 x (connDiffEndo (I := I) (M := M) g₀ gm x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffQuadraticComposedTensor, appCcRS_toSection]
    rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 2 x
    (connDiffEndo (I := I) (M := M) g₀ gm x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
        (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun k : Fin 4 => (m k : E))]
  rw [slotInsertEndoFib_apply_eval]
  rw [lrArmSlotTuple (I := I) (M := M) g₀ gm x m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 3 =>
      (fun j : Fin 3 => (((![(show TangentSpace I x from
          PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 2, m 3] :
          Fin 3 → TangentSpace I x)) j : E)) ((Equiv.swap (0 : Fin 3) 1) i)) =
    (fun i : Fin 3 => (((![m 2, (show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 3] :
        Fin 3 → TangentSpace I x)) i : E)) from by
    funext i
    fin_cases i <;> rfl]
  rw [lrOmegaHat_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

def lrPermA : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 0, 1, 3] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 0, 3] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

def lrPermB : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 0, 1, 2] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

def lrPermC : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 1, 0, 2] : Fin 4 → Fin 4) i,
   fun i => (![2, 1, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩


def connDiffQuadraticCurvatureTerm (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm)
    + connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm
    + domDomCongrSection (I := I) g₀ lrPermA
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 2)
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ lrPermB
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ lrPermC
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrQuadF_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
          (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 0))
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1))
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 0)) (m 3)) (m 1)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 1)) (m 3)) (m 0)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 3) (m 0)) (m 2)) (m 1)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 3) (m 1)) (m 2)) (m 0) := by
  rw [connDiffQuadraticCurvatureTerm]
  rw [bdUnitModel_add, bdUnitModel_add, bdUnitModel_add, bdUnitModel_add, bdUnitModel_add]
  simp only [ContinuousMultilinearMap.add_apply]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [lrQB_unitModel_apply (I := I) (M := M) g₀ gm x
      (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)),
    lrQB_unitModel_apply (I := I) (M := M) g₀ gm x m,
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermA i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x
      (fun i => m ((Equiv.swap (0 : Fin 4) 2) i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermB i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermC i))]
  have hswap01 : ∀ k : Fin 4, m ((Equiv.swap (0 : Fin 4) 1) k) =
      (![m 1, m 0, m 2, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hswap02 : ∀ k : Fin 4, m ((Equiv.swap (0 : Fin 4) 2) k) =
      (![m 2, m 1, m 0, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hA : ∀ k : Fin 4, m (lrPermA k) =
      (![m 2, m 0, m 1, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hB : ∀ k : Fin 4, m (lrPermB k) =
      (![m 3, m 0, m 1, m 2] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hC : ∀ k : Fin 4, m (lrPermC k) =
      (![m 3, m 1, m 0, m 2] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  rw [hswap01 0, hswap01 1, hswap01 2, hswap01 3, hswap02 0, hswap02 1, hswap02 2,
    hswap02 3, hA 0, hA 1, hA 2, hA 3, hB 0, hB 1, hB 2, hB 3, hC 0, hC 1, hC 2, hC 3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]

private def lrSigmaW1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![0, 5, 2, 1, 3, 4] : Fin 6 → Fin 6) i,
   fun i => (![0, 3, 2, 4, 5, 1] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def lrSigmaW2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![4, 0, 2, 1, 3, 5] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 4, 0, 5] : Fin 6 → Fin 6) i,
   by decide, by decide⟩


def riemannLoweredContractionA [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))


def riemannLoweredContractionB [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

set_option backward.isDefEq.respectTransparency false in
private lemma lrRiemW1_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 3 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 5] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 3, w 4] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr lrSigmaW1
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) lrSigmaW1
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w (lrSigmaW1 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW1 0) = w 0
        rw [show lrSigmaW1 (0 : Fin 6) = 0 from by decide]
      · change w (lrSigmaW1 1) = w 5
        rw [show lrSigmaW1 (1 : Fin 6) = 5 from by decide]
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW1 2) = w 2
        rw [show lrSigmaW1 (2 : Fin 6) = 2 from by decide]
      · change w (lrSigmaW1 3) = w 1
        rw [show lrSigmaW1 (3 : Fin 6) = 1 from by decide]
      · change w (lrSigmaW1 4) = w 3
        rw [show lrSigmaW1 (4 : Fin 6) = 3 from by decide]
      · change w (lrSigmaW1 5) = w 4
        rw [show lrSigmaW1 (5 : Fin 6) = 4 from by decide]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, riemannLoweredContractionA]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 3 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 1 : E), (m 2 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 1 : E), (m 2 : E)]]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma lrRiemW2_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(m 2 : E), (smoothOrthoFrame (I := I) g₀ x e x : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 4, w 0] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 3, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr lrSigmaW2
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) lrSigmaW2
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w (lrSigmaW2 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW2 0) = w 4
        rw [show lrSigmaW2 (0 : Fin 6) = 4 from by decide]
      · change w (lrSigmaW2 1) = w 0
        rw [show lrSigmaW2 (1 : Fin 6) = 0 from by decide]
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW2 2) = w 2
        rw [show lrSigmaW2 (2 : Fin 6) = 2 from by decide]
      · change w (lrSigmaW2 3) = w 1
        rw [show lrSigmaW2 (3 : Fin 6) = 1 from by decide]
      · change w (lrSigmaW2 4) = w 3
        rw [show lrSigmaW2 (4 : Fin 6) = 3 from by decide]
      · change w (lrSigmaW2 5) = w 5
        rw [show lrSigmaW2 (5 : Fin 6) = 5 from by decide]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, riemannLoweredContractionB]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![(m 2 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 1 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 1 : E), (m 3 : E)]]
  rfl


def riemannCurvatureCoeffField [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionA (I := I) (M := M) g₀) T
    + ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
      (riemannLoweredContractionB (I := I) (M := M) g₀) T

set_option backward.isDefEq.respectTransparency false in
private lemma lrCurvF_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannCurvatureCoeffField (I := I) (M := M) g₀ T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2)) (m 3)
        + smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
            (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3)) := by
  classical
  rw [riemannCurvatureCoeffField, bdUnitModel_add, ContinuousMultilinearMap.add_apply]
  have hTu : ∀ (a b : TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x)) ![(a : E), (b : E)] =
        smoothCcTensorBilinForm (I := I) g₀ T x a b := by
    intro a b
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2 T x from rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x a b]
  have h1 : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
        (riemannLoweredContractionA (I := I) (M := M) g₀) T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2)) (m 3) := by
    rw [unitModel]
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
      (riemannLoweredContractionA (I := I) (M := M) g₀)
          T).toSection x (unitTensor (I := I) (M := M) x) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x))) from by
      rw [appCcRS_toSection]
      rfl]
    rw [lrRiemW1_toModel (I := I) (M := M) g₀ x _ m]
    have hexp : riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x := by
      have hrep := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
      conv_lhs => rw [hrep]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      exact g₀.symm x (smoothOrthoFrame (I := I) g₀ x e x)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
    conv_rhs => rw [hexp]
    rw [show smoothCcTensorBilinForm (I := I) g₀ T x
        (∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x)
        (m 3) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ T x (smoothOrthoFrame (I := I) g₀ x e x) (m 3) from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hTu (smoothOrthoFrame (I := I) g₀ x e x) (m 3)]
    ring
  have h2 : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
        (riemannLoweredContractionB (I := I) (M := M) g₀) T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3)) := by
    rw [unitModel]
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
      (riemannLoweredContractionB (I := I) (M := M) g₀)
          T).toSection x (unitTensor (I := I) (M := M) x) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x))) from by
      rw [appCcRS_toSection]
      rfl]
    rw [lrRiemW2_toModel (I := I) (M := M) g₀ x _ m]
    have hexp : riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x := by
      have hrep := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
      conv_lhs => rw [hrep]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      exact g₀.symm x (smoothOrthoFrame (I := I) g₀ x e x)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
    conv_rhs => rw [hexp]
    rw [show smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
        (∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ T x (m 2) (smoothOrthoFrame (I := I) g₀ x e x) from by
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul]]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hTu (m 2) (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [h1, h2]

private lemma lrVec2_upd_zero {F : Type*} (a b z : F) :
    Function.update ![a, b] 0 z = ![z, b] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma lrVec2_upd_one {F : Type*} (a b z : F) :
    Function.update ![a, b] 1 z = ![a, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lrTensor0sClmExtUnit {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lrCoeff_eq_unitScalarRSLift (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) :
    (P.toSection x : TensorRSSpace 0 2 I x) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) := by
  have h : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      P.toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        unitScalarRSLift (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SSpace 2 I x from P.toSection x)
            (unitZeroSec (I := I) (M := M) x))) := by
    apply lrTensor0sClmExtUnit (I := I) (M := M)
    rw [unitScalarRSLift_apply_unit]
  exact h


omit [NeZero (Module.finrank ℝ E)] in
private lemma lrRIC (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x ![a, b, c, d]
      - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
          ![b, a, c, d] =
    -(smoothCcTensorBilinForm (I := I) g₀ T x (riemannOp (LeviCivita (I := I) g₀) x a b c) d
      + smoothCcTensorBilinForm (I := I) g₀ T x c
        (riemannOp (LeviCivita (I := I) g₀) x a b d)) := by
  classical
  set X : Π b' : M, TangentSpace I b' := smoothExtensionTangent (I := I) x a with hX_def
  set Y : Π b' : M, TangentSpace I b' := smoothExtensionTangent (I := I) x b with hY_def
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x a
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) :=
    smoothExtensionTangent_contMDiff (I := I) x b
  have hXx : X x = a := smoothExtensionTangent_eq (I := I) x a
  have hYx : Y x = b := smoothExtensionTangent_eq (I := I) x b
  rw [← hXx, ← hYx]
  have hicg : iteratedCovGrad (I := I) g₀ 0 2 2 T =
      covGrad (I := I) (M := M) g₀ 0 (2 + 1) (covGrad (I := I) (M := M) g₀ 0 2 T) := rfl
  have hconsXY : (![X x, Y x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (X x) (Fin.cons (Y x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hconsYX : (![Y x, X x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (Y x) (Fin.cons (X x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hXY := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 T hX hY x ![c, d]
  have hYX := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 T hY hX x ![c, d]
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SSpace (2 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 0 2 T)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := by
    intro v
    rw [unitModel, hicg]
    rfl
  rw [hUM ![X x, Y x, c, d], hUM ![Y x, X x, c, d], hconsXY, hconsYX, hXY, hYX]
  have hdiff : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) ![c, d]
      - Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) ![c, d]
      = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannOp (tensorCov (I := I) g₀ 0 2) x (X x) (Y x)
            ((T.toSection x : TensorRSSpace 0 2 I x)))
          (unitZeroSec (I := I) (M := M) x)) ![c, d] := by
    rw [← tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g₀ 0 2 hX hY
      T.toSection.contMDiff]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SSpace 2 I x from
        (tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x -
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hdiff]
  rw [show ((T.toSection x : TensorRSSpace 0 2 I x)) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          T.toSection x) (unitZeroSec (I := I) (M := M) x)) from
    lrCoeff_eq_unitScalarRSLift (I := I) (M := M) g₀ T x]
  rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g₀ 2 x (X x) (Y x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      T.toSection x) (unitZeroSec (I := I) (M := M) x))]
  set Xb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b' => X b', hX⟩ with hXb_def
  set Yb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b' => Y b', hY⟩ with hYb_def
  set AP : Π y : M, Tensor0SSpace 2 I y := fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
      T.toSection y) (unitZeroSec (I := I) (M := M) y) with hAP_def
  have hAP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) y (AP y)) := by
    exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SSpace 2 I z)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SSpace 2 I y from T.toSection y))
      (v := fun y : M => unitZeroSec (I := I) (M := M) y)
      T.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff
  have hop : riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)) x (X x) (Y x) (AP x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
        (fun b' => Xb b') (fun b' => Yb b') AP x :=
    riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
      hX hY hAP_smooth
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SSpace 2 I x from T.toSection x)
        (unitZeroSec (I := I) (M := M) x)) = AP x from rfl]
  rw [hop]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g₀ 2 Xb Yb AP hAP_smooth x ![c, d]]
  rw [Fin.sum_univ_two]
  rw [show (![c, d] : Fin 2 → TangentSpace I x) 0 = c from rfl,
    show (![c, d] : Fin 2 → TangentSpace I x) 1 = d from rfl,
    lrVec2_upd_zero, lrVec2_upd_one]
  have hbase : ∀ u : TangentSpace I x,
      baseSlotCurv (I := I) g₀ Xb Yb x u =
        riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) u := by
    intro u
    rw [baseSlotCurv]
    have hu := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b' => Xb b') (Y := fun b' => Yb b')
      (Z := fun b' => smoothExtensionTangent (I := I) x u b') (x := x)
      hX hY (smoothExtensionTangent_contMDiff (I := I) x u)
    beta_reduce at hu
    rw [smoothExtensionTangent_eq (I := I) x u] at hu
    exact hu.symm
  rw [hbase c, hbase d]
  have hAPtoModel : ∀ (m : Fin 2 → TangentSpace I x),
      Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        smoothCcTensorBilinForm (I := I) g₀ T x (m 0) (m 1) := by
    intro m
    have h1 : Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        unitModel (I := I) (M := M) g₀ 2 T x m := rfl
    rw [h1, show m = ![m 0, m 1] from funext (fun i => by fin_cases i <;> rfl),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (m 0) (m 1)]
    rfl
  rw [show Tensor0SSpace.toModel (AP x)
        ![(riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c : E), (d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d from
    hAPtoModel ![riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c, d]]
  rw [show Tensor0SSpace.toModel (AP x)
        ![(c : E), (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ T x c
        (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d) from
    hAPtoModel ![c, riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d]]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private lemma lrUnitEval_ddc_rel (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (W : SmoothCcTensor g₀ 0 n) (y : M) :
    (show Tensor0SSpace n I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
        (domDomCongrSection (I := I) g₀ σ W).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr σ
      (show ContinuousMultilinearMap ℝ (fun _ : Fin n => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from W.toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ n (domDomCongrSection (I := I) g₀ σ W) y =
      ContinuousMultilinearMap.domDomCongr σ
        (unitModel (I := I) (M := M) g₀ n W y) := by
    rw [domDomCongrSection_unitModel]
  rw [unitModel, unitModel] at h
  exact h


omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGrad_ddc_unitModel (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (domDomCongrSection (I := I) g₀ σ W)) x w =
      unitModel (I := I) (M := M) g₀ 4 (covGrad (I := I) (M := M) g₀ 0 3 W) x
        (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j))) := by
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (domDomCongrSection (I := I) g₀ σ W) x w]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3 W x
    (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)))]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3 W x
  have hW' := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3
    (domDomCongrSection (I := I) g₀ σ W) x
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2 g₀ σ
    (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from W.toSection y)
      (unitZeroSec (I := I) (M := M) y))
    (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (domDomCongrSection (I := I) g₀ σ W).toSection y)
      (unitZeroSec (I := I) (M := M) y))
    x (w 0) hW hW'
    (fun y => lrUnitEval_ddc_rel (I := I) (M := M) g₀ 3 σ W y)
  rw [show (show Tensor0SSpace 3 I x from
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (domDomCongrSection (I := I) g₀ σ W).toSection y)
          (unitZeroSec (I := I) (M := M) y)) x (w 0)) =
    ContinuousMultilinearMap.domDomCongr σ
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (w 0)) from hstep]
  rw [show (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)) :
    Fin 4 → TangentSpace I x) 0 = w 0 from rfl]
  rw [show Matrix.vecTail (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)) :
      Fin 4 → TangentSpace I x) = (fun j => Matrix.vecTail w (σ j)) from
    Matrix.tail_cons _ _]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private lemma lrTsec_rel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (y : M) :
    (show Tensor0SSpace 2 I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ 2 T y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (unitModel (I := I) (M := M) g₀ 2 T y) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hveta : v = ![v 0, v 1] := funext fun i => by fin_cases i <;> rfl
    have hveta2 : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] :=
      funext fun i => by fin_cases i <;> rfl
    rw [hveta2]
    conv_lhs => rw [hveta]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T y (v 0) (v 1),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T y (v 1) (v 0)]
    exact hTsymm y (v 0) (v 1)
  rw [unitModel] at h
  exact h


omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGradT_argswap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (y : M) (w : Fin 3 → TangentSpace I y) :
    unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y w =
      unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y
        ![w 0, w 2, w 1] := by
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 2 T y w,
    lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 2 T y ![w 0, w 2, w 1]]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 2 T y
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 1 g₀
    (Equiv.swap (0 : Fin 2) 1)
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from T.toSection z)
      (unitZeroSec (I := I) (M := M) z))
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from T.toSection z)
      (unitZeroSec (I := I) (M := M) z))
    y (w 0) hW hW
    (fun z => lrTsec_rel (I := I) (M := M) g₀ T hTsymm z)
  conv_lhs => rw [show (show Tensor0SSpace 2 I y from
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
          T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (show Tensor0SSpace 2 I y from
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
            T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)) from hstep]
  rw [show (![w 0, w 2, w 1] : Fin 3 → TangentSpace I y) 0 = w 0 from rfl]
  rw [show Matrix.vecTail (![w 0, w 2, w 1] : Fin 3 → TangentSpace I y) = ![w 2, w 1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show Tensor0SSpace.toModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (show Tensor0SSpace 2 I y from
          Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
              T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)))
      (Matrix.vecTail w) =
    Tensor0SSpace.toModel
      (show Tensor0SSpace 2 I y from
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
            T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0))
      (fun i => Matrix.vecTail w ((Equiv.swap (0 : Fin 2) 1) i)) from rfl]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCgTsec_rel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (y : M) :
    (show Tensor0SSpace 3 I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g₀ 0 2 T).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g₀ 0 2 T).toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hveta : v = ![v 0, v 1, v 2] := funext fun i => by fin_cases i <;> rfl
    have hveta2 : (fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) = ![v 0, v 2, v 1] :=
      funext fun i => by fin_cases i <;> rfl
    rw [hveta2]
    conv_lhs => rw [hveta]
    exact lrCovGradT_argswap (I := I) (M := M) g₀ T hTsymm y ![v 0, v 1, v 2]
  rw [unitModel] at h
  exact h


omit [NeZero (Module.finrank ℝ E)] in
private lemma lrICG2_argswap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x ![a, b, c, d] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
        ![a, b, d, c] := by
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 T)) x v :=
    fun v => rfl
  rw [hUM ![a, b, c, d], hUM ![a, b, d, c]]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x ![a, b, c, d]]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x ![a, b, d, c]]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2 g₀
    (Equiv.swap (1 : Fin 3) 2)
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
      (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
      (unitZeroSec (I := I) (M := M) z))
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
      (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
      (unitZeroSec (I := I) (M := M) z))
    x ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0) hW hW
    (fun z => lrCgTsec_rel (I := I) (M := M) g₀ T hTsymm z)
  conv_lhs => rw [show (show Tensor0SSpace 3 I x from
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
        (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
          (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
          (unitZeroSec (I := I) (M := M) z)) x
        ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
            (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
            (unitZeroSec (I := I) (M := M) z)) x
          ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)) from hstep]
  rw [show ((![a, b, d, c] : Fin 4 → TangentSpace I x) 0) =
    ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0) from rfl]
  rw [show Tensor0SSpace.toModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (show Tensor0SSpace 3 I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
              (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
              (unitZeroSec (I := I) (M := M) z)) x
            ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)))
      (Matrix.vecTail (![a, b, c, d] : Fin 4 → TangentSpace I x)) =
    Tensor0SSpace.toModel
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
            (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
            (unitZeroSec (I := I) (M := M) z)) x
          ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0))
      (fun i => Matrix.vecTail (![a, b, c, d] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) from rfl]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl


omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGradKT_unitModel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (w0 w1 w2 w3 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
        ![w0, w1, w2, w3] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
            ![w0, w3, w2, w1]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![w0, w2, w3, w1]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![w0, w1, w3, w2]) := by
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 T)) x v :=
    fun v => rfl
  rw [hUM ![w0, w3, w2, w1], hUM ![w0, w2, w3, w1], hUM ![w0, w1, w3, w2]]
  rw [linearizedKoszulTensor, covGrad_smul, covGrad_sub, covGrad_add]
  rw [bdUnitModel_smul]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdUnitModel_add, ContinuousMultilinearMap.add_apply]
  rw [lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3],
    lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (finRotate 3)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3],
    lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3]]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (0 : Fin 3) 2) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w3, w2, w1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((finRotate 3) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w2, w3, w1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w1, w3, w2] from by
    funext k
    fin_cases k <;> rfl]


def lrR4 [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g₀ 0 4 :=
  (-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T
    - connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)


private theorem lrSummand (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (v0 v1 pf qf : TangentSpace I x) :
    ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 pf qf) v1
      + (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v1 pf qf) v0)
      + s * ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v0, v1, pf, qf]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v0, v1, qf, pf])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v0, pf, qf, v1]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v0, qf, pf, v1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v1, pf, qf, v0]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v1, qf, pf, v0])) =
      unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
        ![v0, v1, pf, qf] := by
  classical
  have hR4 : unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
      ![v0, v1, pf, qf] =
      (-(s / 2) : ℝ) * unitModel (I := I) (M := M) g₀ 4
        (riemannCurvatureCoeffField (I := I) (M := M) g₀ T) x
          ![v0, v1, pf, qf]
        - unitModel (I := I) (M := M) g₀ 4
            (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)) x
            ![v0, v1, pf, qf] := by
    rw [lrR4, bdUnitModel_sub, ContinuousMultilinearMap.sub_apply, bdUnitModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hR4, lrQuadF_unitModel_apply (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) x ![v0, v1, pf, qf],
    lrCurvF_unitModel_apply (I := I) (M := M) g₀ T x ![v0, v1, pf, qf]]
  rw [lrKernel_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x v0 v1 pf qf,
    lrKernel_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x v1 v0 pf qf]
  rw [lrCovGradKT_unitModel (I := I) (M := M) g₀ T x v0 v1 pf qf,
    lrCovGradKT_unitModel (I := I) (M := M) g₀ T x v1 v0 pf qf]
  have hswap := lrICG2_argswap (I := I) (M := M) g₀ T hTsymm x v1 v0 pf qf
  have hric := lrRIC (I := I) (M := M) g₀ T x v0 v1 pf qf
  have hcs1 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0)
        pf :=
    PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0)
  have hcs2 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1)
        pf :=
    PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1)
  rw [hcs1, hcs2]
  have hqswap : ∀ u w z : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u w =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x w u :=
    fun u w _ => PDE.DeTurck.connDiff_symm (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u w
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  linear_combination (s / 2) * hric + (s / 2) * hswap


theorem lrArm_sub_family_eq_pairTrace (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
      - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
          Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
        ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul_desc : ∀ (c : ℝ) (F : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((c • F).toSection x)) D) v =
      c * Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (F.toSection x)) D) v := by
    intro c F
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((c • F).toSection x)) =
        c • (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (F.toSection x)) from by
      rw [show (c • F).toSection x = c • F.toSection x from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
      ]
    rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hadd_desc : ∀ (F G : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((F + G).toSection x)) D) v =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (F.toSection x)) D) v
        + Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (G.toSection x)) D) v := by
    intro F G
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((F + G).toSection x)) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (F.toSection x))
          + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (G.toSection x)) from by
      rw [show (F + G).toSection x = F.toSection x + G.toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      ]
    rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.add_apply]
  have hsub_desc : ∀ (F G : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((F - G).toSection x)) D) v =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (F.toSection x)) D) v
        - Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (G.toSection x)) D) v := by
    intro F G
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((F - G).toSection x)) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (F.toSection x))
          - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (G.toSection x)) from by
      rw [show (F - G).toSection x = F.toSection x - G.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      ]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  have hARM : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x)) D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
            (v 1) +
          (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
            (v 0)) *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x)) D) =
      connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x D from rfl]
    rw [show (connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x :
        Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x) x from rfl]
    exact dLaBiContrFibFixedFrame_toModel (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x) x D v
  have hfield : deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s =
      s • ((-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                          Equiv.swap (0 : Fin 4) 1).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))) := by
    rw [deTurckLieCovDerivRefoldPairTraceFamily, Fin.sum_univ_three]
    rfl
  rw [hfield]
  simp only [hsub_desc, hsmul_desc, hadd_desc]
  rw [hARM]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
            Equiv.swap (0 : Fin 4) 1).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x D v]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
    from Finset.sum_comm]
  have hpoint : ∀ (b : Fin (Module.finrank ℝ E)) (a : Fin (Module.finrank ℝ E)),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
          ![v 0, v 1,
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] =
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
      + s * ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                    Equiv.swap (0 : Fin 4) 1).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + (1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x :
                  E)])))) := by
    intro b a
    have hddc : ∀ (σ : Equiv.Perm (Fin 4)) (m0 m1 m2 m3 : TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 4
          (domDomCongrSection (I := I) g₀ σ (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
          ![m0, m1, m2, m3] =
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
          (fun i => (![m0, m1, m2, m3] : Fin 4 → TangentSpace I x) (σ i)) := by
      intro σ m0 m1 m2 m3
      rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hddc, hddc, hddc, hddc, hddc, hddc]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        v 1] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        v 1] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
            Equiv.swap (0 : Fin 4) 1).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        v 0] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        v 0] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E)] from by
      funext i
      fin_cases i <;> rfl]
    have hsummand := lrSummand (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x
      (v 0) (v 1)
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x)
    linear_combination (-(Tensor0SSpace.toModel D
      ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)])) *
      hsummand
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
          ![v 0, v 1,
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        (((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
      + s * ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                    Equiv.swap (0 : Fin 4) 1).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + (1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)])))))
    from Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => hpoint b a]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
