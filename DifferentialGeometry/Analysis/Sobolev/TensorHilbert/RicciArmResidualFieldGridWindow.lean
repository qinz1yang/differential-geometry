import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

section helpers

variable (g₀ g₁ : SmoothRiemannianMetric I M)

private def gInvQuadRefoldArm : SmoothCcTensor g₀ 1 2 :=
  appCcRS (I := I) (M := M) g₀ 1 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (slotExtend (I := I) (M := M) g₀ 0 3 (connDiffLoweredCc (I := I) g₀ g₁))

private def gInvQuadRefoldWeight : SmoothCcTensor g₀ 2 1 :=
  appCcRS (I := I) (M := M) g₀ 2 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
    (reindexCoeffGen (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 2) 1))

set_option linter.unusedSectionVars false in
private lemma tensor0S_rank0_eq_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

set_option linter.unusedSectionVars false in
private theorem orthoFrame_basis_at_center (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (c j • smoothOrthoFrame (I := I) g₀ x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

set_option linter.unusedSectionVars false in
private theorem orthoFrame_expansion_at_center (x : M) (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
        smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  obtain ⟨bse, hbse⟩ := orthoFrame_basis_at_center (I := I) (M := M) g₀ x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x j x) = bse.repr u j := by
    intro j
    rw [g₀.symm x u (smoothOrthoFrame (I := I) g₀ x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
          smoothOrthoFrame (I := I) g₀ x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
private lemma connDiffLowered_unitModel_value (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  have hbase : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    rfl
  rw [hbase]
  rfl

set_option linter.unusedSectionVars false in
private lemma interiorProduct_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private lemma connDiffSection_eq_raise_lowered :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [interiorProduct_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

set_option linter.unusedSectionVars false in
private lemma rfns_icg_connDiffLowered_eq_connDiffSection (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

set_option linter.unusedSectionVars false in
private lemma cometricDoubleTraceFib_toModel_center (p : ℕ) (x : M)
    (D : Tensor0SSpace (p + 2) I x) (m : Fin p → E) :
    Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m)) := by
  rw [show Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) m =
      modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
        (Tensor0SSpace.toModel D) m from by
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ p x D]]
  rw [modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ x)
    (Tensor0SSpace.toModel D) m]
  exact cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := p) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) m

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private lemma slotExtend_connDiffLowered_toModel (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : E) (vs : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g₀ 0 3
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel om ![v0] *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (vs 0) (vs 1)) (vs 2) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 0 3
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (connDiffLoweredCc (I := I) g₀ g₁).toSection x) om) (Fin.cons v0 vs) := rfl
  rw [h0]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁).toSection x) om v0 vs]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x om v0 =
      Tensor0SSpace.toModel om ![v0] • unitTensor (I := I) (M := M) x := by
    have h1 := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x om v0)
    rw [h1]
    congr 1
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hu := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x vs
  rw [unitModel] at hu
  exact hu

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private lemma gInvQuadRefoldArm_toModel (x : M) (om : Tensor0SSpace 1 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) om) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel om ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)] *
          g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x c x) (m 0)) (m 1) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) om) m =
      Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtend (I := I) (M := M) g₀ 0 3
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om)) m := rfl
  rw [h0]
  rw [cometricDoubleTraceFib_toModel_center (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtend (I := I) (M := M) g₀ 0 3
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om) m]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [slotExtend_connDiffLowered_toModel (I := I) (M := M) g₀ g₁ x om
    ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m)]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private lemma gInvQuadRefoldWeight_toModel (x : M) (D : Tensor0SSpace 2 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
          (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) m =
      ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E)] *
          g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x c x) (smoothOrthoFrame (I := I) g₀ x a x))
            (m 0) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) m =
      Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ 1 x
          (reindexCoeffFibGen (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
              (slotExtend (I := I) (M := M) g₀ 1 2
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D)) m := rfl
  rw [h0]
  rw [cometricDoubleTraceFib_toModel_center (I := I) (M := M) g₀ 1 x
    (reindexCoeffFibGen (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D) m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) =
      slotExtendFib (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) from rfl]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) m)]
  rw [gInvQuadRefoldArm_toModel (I := I) (M := M) g₀ g₁ x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E))
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) m)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  · rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      (v0 := ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E))
      (vs := ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)])]
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem gInvDiffQuadResidualField_eq_refold :
    gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 2 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hsplit : ∀ u : TangentSpace I x,
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u (v 0)) (v 1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
    intro u
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
    rw [map_sum (PDE.DeTurck.connDiff (I := I) g₁ g₀ x) _ Finset.univ,
      ContinuousLinearMap.sum_apply, map_sum (g₀.inner x) _ Finset.univ,
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul (PDE.DeTurck.connDiff (I := I) g₁ g₀ x),
      ContinuousLinearMap.smul_apply, map_smul (g₀.inner x),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
          (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v =
      ∑ e : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
            ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
            (smoothOrthoFrame (I := I) g₀ x e x)) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
    have hr0 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 1 2
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x)
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
              (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D)) v := rfl
    rw [hr0]
    rw [gInvQuadRefoldArm_toModel (I := I) (M := M) g₀ g₁ x
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) v]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [gInvQuadRefoldWeight_toModel (I := I) (M := M) g₀ g₁ x D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)]]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rfl
  calc Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x) D) v
      = ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (v 0)) (v 1) *
            Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] := by
        rw [show Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x) D) v =
            Tensor0SSpace.toModel
              (connDiffBiContrFibFixedFrame (I := I) g₁ g₀ g₁ g₀
                (smoothOrthoFrame (I := I) g₀ x) x D) v from rfl]
        exact connDiffBiContrFibFixedFrame_toModel (I := I) g₁ g₀ g₁ g₀
          (smoothOrthoFrame (I := I) g₀ x) x D v
    _ = ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          ∑ e : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [hsplit (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = ∑ q : Fin (Module.finrank ℝ E), ∑ e : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ e : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_comm
    _ = ∑ e : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 1 2
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v := hRHS.symm

set_option linter.unusedSectionVars false in
private lemma sum_range_mono_of_nonneg (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    {m n : ℕ} (hmn : m ≤ n) :
    ∑ w ∈ Finset.range m, a w ≤ ∑ w ∈ Finset.range n, a w := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn) ?_
  intro j _ _
  exact ha j

set_option linter.unusedSectionVars false in
private lemma sum_rect_le_sum_triangle (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    {k l i : ℕ} (hkl : k + l ≤ i) :
    (∑ j₁ ∈ Finset.range (k + 1), a j₁) * (∑ j₂ ∈ Finset.range (l + 1), a j₂) ≤
      ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
  rw [Finset.sum_mul]
  have h1 : ∀ j₁ ∈ Finset.range (k + 1),
      a j₁ * ∑ j₂ ∈ Finset.range (l + 1), a j₂ ≤
        ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
    intro j₁ hj₁
    rw [Finset.mul_sum]
    simp only [Finset.mem_range] at hj₁
    have hle : l + 1 ≤ i + 1 - j₁ := by omega
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hle) ?_
    intro j _ _
    exact mul_nonneg (ha j₁) (ha j)
  calc ∑ j₁ ∈ Finset.range (k + 1), a j₁ * ∑ j₂ ∈ Finset.range (l + 1), a j₂
      ≤ ∑ j₁ ∈ Finset.range (k + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ :=
        Finset.sum_le_sum h1
    _ ≤ ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
        have hki : k + 1 ≤ i + 1 := by omega
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hki) ?_
        intro j _ _
        exact Finset.sum_nonneg fun j₂ _ => mul_nonneg (ha j) (ha j₂)

end helpers

set_option linter.unusedVariables false in

theorem exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          K i * ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Kd2 : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose
    with hKd2_def
  have hKd2_nn : ∀ u, 0 ≤ Kd2 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.1
  have hKd2_bound : ∀ u (b : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) b
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection b) ≤ Kd2 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.2
  set Kd1 : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose
    with hKd1_def
  have hKd1_nn : ∀ u, 0 ≤ Kd1 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose_spec.1
  have hKd1_bound : ∀ u (b : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + u) b
          ((iteratedCovGrad (I := I) g₀ 3 1 u
            (cometricDoubleTraceField (I := I) g₀ 1)).toSection b) ≤ Kd1 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose_spec.2
  set C1 : ℕ → ℝ := fun k =>
    appCcGdiag (E := E) k * ((∑ u ∈ Finset.range (k + 1), Kd2 u) * fr) with hC1_def
  have hG_nn : ∀ j, 0 ≤ appCcGdiag (E := E) j := fun j => by
    rw [appCcGdiag]
    positivity
  have hC1_nn : ∀ k, 0 ≤ C1 k := fun k =>
    mul_nonneg (hG_nn k)
      (mul_nonneg (Finset.sum_nonneg fun u _ => hKd2_nn u) hfr_nn)
  set C2 : ℕ → ℝ := fun l =>
    appCcGdiag (E := E) l *
      ((∑ u ∈ Finset.range (l + 1), Kd1 u) *
        (fr * ∑ w ∈ Finset.range (l + 1), C1 w)) with hC2_def
  have hC2_nn : ∀ l, 0 ≤ C2 l := fun l =>
    mul_nonneg (hG_nn l)
      (mul_nonneg (Finset.sum_nonneg fun u _ => hKd1_nn u)
        (mul_nonneg hfr_nn (Finset.sum_nonneg fun w _ => hC1_nn w)))
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l,
    fun i => mul_nonneg (hG_nn i) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hC1_nn k) (Finset.sum_nonneg fun l _ => hC2_nn l)), ?_⟩
  intro g₁ i x
  have ha_nn : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + j) x _
  have hT_nn : ∀ k : ℕ, 0 ≤ ∑ w ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
        ((iteratedCovGrad (I := I) g₀ 1 2 w (connDiffSection (I := I) g₁ g₀)).toSection x) :=
    fun k => Finset.sum_nonneg fun w _ => ha_nn w
  have hSEL : ∀ w : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 1 4 w
            (slotExtend (I := I) (M := M) g₀ 0 3
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
          ((iteratedCovGrad (I := I) g₀ 1 2 w
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro w
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) w x
    rw [rfns_icg_connDiffLowered_eq_connDiffSection (I := I) (M := M) g₀ g₁ w x] at h
    exact h
  have hArm : ∀ k : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 2 k
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C1 k * ∑ w ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 2 w
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro k
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ k 1 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
      (slotExtend (I := I) (M := M) g₀ 0 3 (connDiffLoweredCc (I := I) g₀ g₁)) x) ?_
    calc appCcGdiag (E := E) k *
          ∑ u ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
                ((iteratedCovGrad (I := I) g₀ 4 2 u
                  (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
              ∑ w ∈ Finset.range (k + 1 - u),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 4 w
                    (slotExtend (I := I) (M := M) g₀ 0 3
                      (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
        ≤ appCcGdiag (E := E) k *
            ∑ u ∈ Finset.range (k + 1), Kd2 u *
              (fr * ∑ w ∈ Finset.range (k + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (hG_nn k)
          refine mul_le_mul (hKd2_bound u x) ?_
            (Finset.sum_nonneg fun w _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (4 + w) x _)
            (hKd2_nn u)
          calc ∑ w ∈ Finset.range (k + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 1 4 w
                  (slotExtend (I := I) (M := M) g₀ 0 3
                    (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
              ≤ ∑ w ∈ Finset.range (k + 1 - u),
                  fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) :=
                Finset.sum_le_sum fun w _ => hSEL w
            _ = fr * ∑ w ∈ Finset.range (k + 1 - u),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [Finset.mul_sum]
            _ ≤ fr * ∑ w ∈ Finset.range (k + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) :=
                mul_le_mul_of_nonneg_left
                  (sum_range_mono_of_nonneg _ ha_nn (by omega)) hfr_nn
      _ = C1 k * ∑ w ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
              ((iteratedCovGrad (I := I) g₀ 1 2 w
                (connDiffSection (I := I) g₁ g₀)).toSection x) := by
          rw [← Finset.sum_mul, hC1_def]
          beta_reduce
          ring
  have hcore : ∀ w : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 3 w
            (reindexCoeffGen (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
              (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
        (fr * C1 w) * ∑ u ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 1 2 u
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro w
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 2) 1) w x]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁) w x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hArm w) hfr_nn
  have hW : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 1 l
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C2 l * ∑ w ∈ Finset.range (l + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 2 w
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro l
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ l 2 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
        (Equiv.swap (0 : Fin 2) 1)) x) ?_
    calc appCcGdiag (E := E) l *
          ∑ u ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + u) x
                ((iteratedCovGrad (I := I) g₀ 3 1 u
                  (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
              ∑ w ∈ Finset.range (l + 1 - u),
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
                  ((iteratedCovGrad (I := I) g₀ 2 3 w
                    (reindexCoeffGen (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2
                        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
                      (Equiv.swap (0 : Fin 2) 1))).toSection x)
        ≤ appCcGdiag (E := E) l *
            ∑ u ∈ Finset.range (l + 1), Kd1 u *
              ((fr * ∑ w ∈ Finset.range (l + 1), C1 w) *
                ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (hG_nn l)
          refine mul_le_mul (hKd1_bound u x) ?_
            (Finset.sum_nonneg fun w _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (3 + w) x _)
            (hKd1_nn u)
          calc ∑ w ∈ Finset.range (l + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 3 w
                  (reindexCoeffGen (I := I) (M := M) g₀ 2 3
                    (slotExtend (I := I) (M := M) g₀ 1 2
                      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
                    (Equiv.swap (0 : Fin 2) 1))).toSection x)
              ≤ ∑ w ∈ Finset.range (l + 1 - u),
                  (fr * C1 w) * ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                refine Finset.sum_le_sum fun w hw => ?_
                refine le_trans (hcore w) ?_
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg hfr_nn (hC1_nn w))
                refine sum_range_mono_of_nonneg _ ha_nn ?_
                simp only [Finset.mem_range] at hw
                omega
            _ = (∑ w ∈ Finset.range (l + 1 - u), fr * C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [Finset.sum_mul]
            _ ≤ (∑ w ∈ Finset.range (l + 1), fr * C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                refine mul_le_mul_of_nonneg_right ?_ (hT_nn l)
                refine sum_range_mono_of_nonneg _
                  (fun w => mul_nonneg hfr_nn (hC1_nn w)) (by omega)
            _ = (fr * ∑ w ∈ Finset.range (l + 1), C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [← Finset.mul_sum]
      _ = C2 l * ∑ w ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
              ((iteratedCovGrad (I := I) g₀ 1 2 w
                (connDiffSection (I := I) g₁ g₀)).toSection x) := by
          rw [← Finset.sum_mul, hC2_def]
          beta_reduce
          ring
  rw [gInvDiffQuadResidualField_eq_refold (I := I) (M := M) g₀ g₁]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ i 2 1 2 (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
    (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁) x) ?_
  calc appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 1 2 k
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - k),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 1 l
                  (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x)
      ≤ appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range (i + 1),
            (C1 k * ∑ w ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                ((iteratedCovGrad (I := I) g₀ 1 2 w
                  (connDiffSection (I := I) g₁ g₀)).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - k),
              (C2 l * ∑ w ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (hG_nn i)
        refine mul_le_mul (hArm k) (Finset.sum_le_sum fun l _ => hW l) ?_ ?_
        · exact Finset.sum_nonneg fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (1 + l) x _
        · exact mul_nonneg (hC1_nn k) (hT_nn k)
    _ ≤ appCcGdiag (E := E) i *
          ((∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
            ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                    (connDiffSection (I := I) g₁ g₀)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG_nn i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k hk => ?_
        calc (C1 k * ∑ w ∈ Finset.range (k + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) *
              ∑ l ∈ Finset.range (i + 1 - k),
                (C2 l * ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x))
            = ∑ l ∈ Finset.range (i + 1 - k),
                (C1 k * ∑ w ∈ Finset.range (k + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                (C2 l * ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
              rw [Finset.mul_sum]
          _ ≤ ∑ l ∈ Finset.range (i + 1 - k),
                (C1 k * C2 l) *
                  ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                          (connDiffSection (I := I) g₁ g₀)).toSection x) *
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                          (connDiffSection (I := I) g₁ g₀)).toSection x) := by
              refine Finset.sum_le_sum fun l hl => ?_
              have hkl : k + l ≤ i := by
                simp only [Finset.mem_range] at hk hl
                omega
              calc (C1 k * ∑ w ∈ Finset.range (k + 1),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 w
                          (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                    (C2 l * ∑ w ∈ Finset.range (l + 1),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 w
                          (connDiffSection (I := I) g₁ g₀)).toSection x))
                  = (C1 k * C2 l) *
                      ((∑ w ∈ Finset.range (k + 1),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                          ((iteratedCovGrad (I := I) g₀ 1 2 w
                            (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                       ∑ w ∈ Finset.range (l + 1),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                          ((iteratedCovGrad (I := I) g₀ 1 2 w
                            (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
                    ring
                _ ≤ (C1 k * C2 l) *
                      ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                            ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                              (connDiffSection (I := I) g₁ g₀)).toSection x) *
                          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                            ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                    refine mul_le_mul_of_nonneg_left ?_
                      (mul_nonneg (hC1_nn k) (hC2_nn l))
                    exact sum_rect_le_sum_triangle
                      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j
                          (connDiffSection (I := I) g₁ g₀)).toSection x)) ha_nn hkl
          _ = (C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
                ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                        (connDiffSection (I := I) g₁ g₀)).toSection x) *
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
          ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [mul_assoc]

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_gInvDiffQuadResidualFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set Cq : ℕ → ℝ := fun n => K n *
    ∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
      CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) with hCq_def
  have hCq_nn : ∀ n, 0 ≤ Cq n := by
    intro n
    refine mul_nonneg (hK_nn n) (Finset.sum_nonneg fun j₁ _ => Finset.sum_nonneg fun j₂ _ => ?_)
    exact mul_nonneg (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
      (Combinatorics.windowPairCellCount_nonneg _ _)
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hAjet : ∀ j : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        CA j * Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
      intro j
      have h := hCA g₁ P htie hδ_le hδ0 hbound j x
      have heq : (∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
      rw [← heq]
      exact h
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hK g₁ n x) ?_
      have hsum : (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                (connDiffSection (I := I) g₁ g₀)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
          (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
            CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2)) * W := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₁ hj₁ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₂ hj₂ => ?_
        rw [Finset.mem_range] at hj₁ hj₂
        have hA₁ := hAjet j₁
        have hA₂ := hAjet j₂
        have hrfns₂_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + j₂) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j₂ (connDiffSection (I := I) g₁ g₀)).toSection x)
        have hwin₁_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) :=
          Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x)
            ≤ (CA j₁ * Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2)) *
                (CA j₂ * Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) :=
              mul_le_mul hA₁ hA₂ hrfns₂_nn
                (mul_nonneg (hCA_nn j₁) hwin₁_nn)
          _ = (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) := by ring
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (i + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (j₂ + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((j₁ + 2) + (j₂ + 2) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (j₁ + 2)
                (j₂ + 2) (by omega) (by omega)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              rw [hW_def]
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W := by
              ring
      refine le_trans (mul_le_mul_of_nonneg_left hsum (hK_nn n)) (le_of_eq ?_)
      simp only [hCq_def]
      ring
    have hsubject : ccInputSymm (I := I) (M := M) g₀
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
            + appCcRS (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤ Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 2 2
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
        (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
                (ccSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section bgrConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

set_option linter.unusedSectionVars false in
private lemma unitModel_add_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  rw [unitModel, unitModel, unitModel,
    show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A + B).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x) from by
      rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma unitModel_smul_pt (s : ℕ) (c : ℝ) (A : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • A) x =
      c • unitModel (I := I) (M := M) g₀ s A x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • A).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      c • ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
        (unitTensor (I := I) (M := M) x)) := by
    rw [show ((c • A).toSection x) = c • (A.toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [unitModel, unitModel, h, Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in
private lemma unitModel_sub_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A - B).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) := by
    rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl
  rw [unitModel, unitModel, unitModel, h, Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
private lemma rfns_neg_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := riemannianFiberNormSq_smul_value (I := I) (M := M) g r s x (-1 : ℝ) v
  rw [neg_one_smul] at h
  rw [h]; norm_num

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
private lemma unitModel_eq_ccTensorBilin_pt (S : SmoothCcTensor g₀ 0 2) (b : M)
    (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma reindexCoeffGen_one_eq (r s : ℕ) (R : SmoothCcTensor g₀ r s) :
    reindexCoeffGen (I := I) (M := M) g₀ r s R 1 = R := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s R 1).toSection x) D =
      reindexCoeffFibGen (I := I) r s 1 x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma rfns_icg_rsDomDomCongrSection_eq (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g₀ r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i R).toSection x) := by
  have h := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ r s
    (1 : Equiv.Perm (Fin r)) σ R i x
  rw [reindexCoeffGen_one_eq (I := I) (M := M) g₀ r s
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)] at h
  exact h

def sigmaE : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def tauK3b : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 0, 2, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def tauM1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 4, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 1, 3, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def tauM2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 1, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def tauM3 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 2, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 4, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def tauM4 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 1, 2, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 4, 5, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in

def mvDoubleTraceField (s : ℕ) : SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma mvDoubleTraceField_self_eq (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₀ s = cometricDoubleTraceField (I := I) g₀ s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceField_toSection]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_add_local (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma fullRaisedEndoField_diff_split_local :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_slotInsert_id_eq (s c : ℕ) (Φ : SmoothCcTensor g₀ (s + 1) c) :
    appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = Φ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) D =
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval]
  rw [show (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x (m 0)) = m 0 from by
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [Function.update_eq_self]

set_option linter.unusedSectionVars false in
private lemma mvOrthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma mvDoubleTraceField_eq_trace_fullRaised (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := mvOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [show g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x) =
        g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
          (smoothOrthoFrame (I := I) g₁ x c x) from by
      rw [gInvRaisedEndo_apply]
      rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x)]
      rw [show cotangentToDualLinear (I := I) (x := x)
          (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
          (smoothOrthoFrame (I := I) g₁ x c x) =
          cotangentToDual (I := I) (x := x)
            (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
            (smoothOrthoFrame (I := I) g₁ x c x) from rfl]
      rw [cotangentToDual_g0FlatCLM]]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul (E := E) x
          (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := mvOrthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma mvDoubleTraceField_cross_split (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  rw [mvDoubleTraceField_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  rw [fullRaisedEndoField_diff_split_local (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add_local (I := I) (M := M) g₀ (s + 1)]
  rw [appCcRS_add_right (I := I) (M := M) g₀ (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rw [appCcRS_slotInsert_id_eq (I := I) (M := M) g₀ (s + 1) s
    (cometricDoubleTraceField (I := I) g₀ s)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtend_toModel_cons (r s : ℕ) (Φ : SmoothCcTensor g₀ r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : TangentSpace I x) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D)
        (Fin.cons (show E from v0) vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D v0)) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D) =
      slotExtendFib (I := I) (M := M) g₀ r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D from rfl]
  exact slotExtendFib_apply_eval (I := I) (M := M) g₀ r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D
    (show E from v0) vs

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_two_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1) (fun k : Fin 4 => (u (Fin.natAdd 2 k) : E))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change (u (Fin.succ (Fin.succ k2)) : E) = (u (Fin.natAdd 2 k2) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 1 5
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 5
    (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 0 4 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 4 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := (u 1 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := (u 0 : E)) (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_three_toModel (X : SmoothCcTensor g₀ 0 3) (x : M)
    (D : Tensor0SSpace 3 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] *
        unitModel (I := I) (M := M) g₀ 3 X x (fun k : Fin 3 => u (Fin.natAdd 3 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1)
          (Fin.cons (show E from u 2) (fun k : Fin 3 => (u (Fin.natAdd 3 k) : E)))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    refine Fin.cases rfl (fun k3 => ?_) k2
    change (u (Fin.succ (Fin.succ (Fin.succ k3))) : E) = (u (Fin.natAdd 3 k3) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 2 5
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 2 5
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X)).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 4
    (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 0 3 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 3 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (v0 := (u 2 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (v0 := (u 1 : E))
      (vs := Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0))
    rw [h2]
    have h3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := D) (v0 := (u 0 : E))
      (vs := Fin.cons (show E from u 1)
        (Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0)))
    rw [h3]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => ?_) i
    refine Fin.cases rfl (fun i3 => i3.elim0) i2
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

def mvPairTraceOp : SmoothCcTensor g₀ 6 2 :=
  appCcRS (I := I) (M := M) g₀ 6 4 2
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in

lemma mvPairTraceOp_apply_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

private def bgRArmWeight : SmoothCcTensor g₀ 2 4 :=
  appCcRS (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma bgRArmWeight_toModel (x : M) (D : Tensor0SSpace 2 I x)
    (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 1 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 3] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 4, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr (Equiv.swap (1 : Fin 6) 3)
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (1 : Fin 6) 3)
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w ((Equiv.swap (1 : Fin 6) 3) i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, bgRArmWeight]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  show Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 1 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 2 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 2 : E), (m 3 : E)]]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma metricCcTensor_unitModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma metricDifferenceCcTensor_eq_symmS (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ = symmS (I := I) g₀ P := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀ from rfl]
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 2
    (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
  rw [show unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) g₀ P) x m =
      unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) g₀ P) x ![m 0, m 1] from by
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl]
  rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ (symmS (I := I) g₀ P) x (m 0) (m 1)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
  rw [htie x (m 0) (m 1)]
  ring

set_option linter.unusedSectionVars false in
private lemma rfns_eq_sum_componentSq_of_horth_pt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  classical
  haveI : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x S e bse hn hbse horth

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_zero_toModel_pt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
  rfl

set_option linter.unusedSectionVars false in
private lemma rfns_symmS_zero_le_of_ball (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e hnE horth]
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ 2 x
        (symmS (I := I) (M := M) g₀ T) e K J]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k => (show E from e (J k))) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀
        (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_symmS_pointwise (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (symmS (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [htoSec]
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := hswap
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2 : ℝ),
          riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2 : ℝ)]
        ring
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hRB]; ring

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_koszulCovecCc_pointwise (T : SmoothCcTensor g₀ 0 2)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (symmS (I := I) g₀ T) x
    rw [hcomm]
    exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_real, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (3 + i) x (1 / 2 : ℝ)]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    rfns_neg_pt (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

set_option linter.unusedSectionVars false in
private lemma rfns_sub_le_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)) ?_
  rw [rfns_neg_pt (I := I) (M := M) g r s x b]

set_option linter.unusedVariables false in
private lemma exists_rfns_icg_mvDoubleTraceField_window (s : ℕ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (u K : ℕ) (huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s u
              (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨CΛ, hCΛ_nn, hCΛ⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u (cometricDoubleTraceField (I := I) g₀ s))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) y
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.2
  refine ⟨fun u => 2 * (appCcGdiag (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) +
      2 * KD u, fun u => by
    have h1 : 0 ≤ appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂ :=
      mul_nonneg (appCcGdiag_nonneg (E := E) u)
        (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hKD_nn u₁)
          (Finset.sum_nonneg fun u₂ _ => mul_nonneg (by positivity) (hCΛ_nn u₂)))
    have h2 := hKD_nn u
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (u + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hsec : (iteratedCovGrad (I := I) g₀ (s + 2) s u
      (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x =
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x +
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x := by
    rw [show mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
        appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
        cometricDoubleTraceField (I := I) g₀ s from
      mvDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ s]
    rw [iteratedCovGrad_add (I := I) g₀ (s + 2) s u _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 2) (s + u) x _ _) ?_
  have hSI : ∀ u₂ : ℕ, u₂ ≤ u →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    intro u₂ hu₂
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀
      (s + 1) (gInvDiffRaisedEndoField (I := I) g₀ g₁) u₂ x) ?_
    have hgrid := hCΛ g₁ P htie hδ_le hδ0 hbound u₂ x
    have hgw : (∑ n ∈ Finset.range (u₂ + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
          ∏ m : Fin n, b (e m)) ≤ W := by
      rw [show (∑ n ∈ Finset.range (u₂ + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
            ∏ m : Fin n, b (e m)) =
          Combinatorics.antidiagonalTupleGrid b u₂ from rfl]
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc (Module.finrank ℝ E : ℝ) ^ (s + 1) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + u₂) x
            ((iteratedCovGrad (I := I) g₀ 1 1 u₂
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ *
            ∑ n ∈ Finset.range (u₂ + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
                ∏ m : Fin n, b (e m)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hgrid
      _ ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ * W) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgw (hCΛ_nn u₂)) (by positivity)
      _ = ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by ring
  have hQ : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      (appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁),
            (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ u (s + 2) (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
      (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    calc appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u₁) x
                ((iteratedCovGrad (I := I) g₀ (s + 2) s u₁
                  (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
                  ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
                    (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun u₁ hu₁ => ?_) (appCcGdiag_nonneg (E := E) u)
          refine mul_le_mul (hKD u₁ x) (Finset.sum_le_sum fun u₂ hu₂ => ?_)
            (Finset.sum_nonneg fun u₂ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x _)
            (hKD_nn u₁)
          rw [Finset.mem_range] at hu₁ hu₂
          exact hSI u₂ (by omega)
      _ = (appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
          have hstep : ∀ u₁ : ℕ, (KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W)) =
              (KD u₁ * ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
            intro u₁
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun u₁ _ => hstep u₁, ← Finset.sum_mul]
          ring
  have hCDT : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ KD u * W := by
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        ≤ KD u := hKD u x
      _ = KD u * 1 := by ring
      _ ≤ KD u * W := mul_le_mul_of_nonneg_left hW_one (hKD_nn u)
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
            (cometricDoubleTraceField (I := I) g₀ s)
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
      ≤ 2 * ((appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) + 2 * (KD u * W) := by
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        linarith [hQ, hCDT]
    _ = (2 * (appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) + 2 * KD u) * W := by ring

set_option linter.unusedVariables false in

lemma exists_rfns_icg_mvPairTraceOp_window {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (u K : ℕ) (huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 6 2 u
              (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun u => appCcGdiag (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁),
          C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1),
    fun u => mul_nonneg (appCcGdiag_nonneg (E := E) u)
      (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hC2_nn u₁)
        (Finset.sum_nonneg fun u₂ _ => mul_nonneg (hC4_nn u₂)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ u 6 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4) x) ?_
  calc appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u₁) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u₁
                (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u₂) x
                ((iteratedCovGrad (I := I) g₀ 6 4 u₂
                  (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            (C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1)) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u₁ hu₁ => ?_) (appCcGdiag_nonneg (E := E) u)
        rw [Finset.mem_range] at hu₁
        refine mul_le_mul (hC2 g₁ P htie hδ_le hδ0 hbound u₁ K (by omega) x)
          (Finset.sum_le_sum fun u₂ hu₂ => ?_)
          (Finset.sum_nonneg fun u₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + u₂) x _)
          (mul_nonneg (hC2_nn u₁)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hu₂
        exact hC4 g₁ P htie hδ_le hδ0 hbound u₂ K (by omega) x
    _ ≤ (appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
          Combinatorics.boundedFactorGridWindow b K (u + 1) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) u)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u₁ hu₁ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun u₂ hu₂ => ?_
        rw [Finset.mem_range] at hu₁ hu₂
        calc C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1))
            = (C2 u₁ * C4 u₂) *
                (Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by ring
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K ((u₁ + 1) + (u₂ + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (u₁ + 1) (u₂ + 1)
                (by omega) (by omega)
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = C2 u₁ * (C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
                Combinatorics.boundedFactorGridWindow b K (u + 1) := by ring

private def ricciFoldWeightA (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

private def ricciFoldWeightB (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauK3b
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciFoldWeight_unitModel_gen (σ : Equiv.Perm (Fin 6))
    (S : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 2 S x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1))] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set R4 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ with hR4_def
  set Sval : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) with hSval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (appCcRS (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Sval ![(w (σ 0) : E), (w (σ 1) : E)] *
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr σ
            ((appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (appCcRS (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4).toSection x) Sval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ R4 x Sval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 4 R4 x
          (fun k : Fin 4 => ((fun i => w (σ i)) (Fin.natAdd 2 k) : E)) =
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_expand_left (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          ccTensorBilin (I := I) g₀ S x (smoothOrthoFrame (I := I) g₀ x e x) w := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
  rw [map_sum (ccTensorBilin (I := I) g₀ S x) _ Finset.univ, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (ccTensorBilin (I := I) g₀ S x), ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_expand_right (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x w (smoothOrthoFrame (I := I) g₀ x e x) *
          ccTensorBilin (I := I) g₀ S x u (smoothOrthoFrame (I := I) g₀ x e x) := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x w]
  rw [map_sum (ccTensorBilin (I := I) g₀ S x u) _ Finset.univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (ccTensorBilin (I := I) g₀ S x u), smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciFoldWeights_unitModel_eq_kernel (S : SmoothCcTensor g₀ 0 2) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (ricciFoldWeightA (I := I) (M := M) g₀ S +
          ricciFoldWeightB (I := I) (M := M) g₀ S) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 +
        ccTensorBilin (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
  classical
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (ricciFoldWeightA (I := I) (M := M) g₀ S) (ricciFoldWeightB (I := I) (M := M) g₀ S) x,
    ContinuousMultilinearMap.add_apply]
  have hA : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightA (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 := by
    rw [show ricciFoldWeightA (I := I) (M := M) g₀ S =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 6) 3) S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [ccTensorBilin_expand_left (I := I) (M := M) g₀ S x
      (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (q : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (q : E)]]
      rfl
    rw [h1, h2]
    rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₀ x e x) v1]
    ring
  have hB : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
    rw [show ricciFoldWeightB (I := I) (M := M) g₀ S =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauK3b
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ tauK3b S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [ccTensorBilin_expand_right (I := I) (M := M) g₀ S x q
      (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (v1 : E)]]
      rfl
    rw [h1, h2]
    rw [show unitModel (I := I) (M := M) g₀ 2 S x
        ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] =
        ccTensorBilin (I := I) g₀ S x q (smoothOrthoFrame (I := I) g₀ x e x) from
      unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x q
        (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [hA, hB]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciFoldRemainderField_eq_refold (S : SmoothCcTensor g₀ 0 2) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S =
      (-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) D) =
      (-(1 / 2) : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) D) := by
    rw [show ((((-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) =
        (-(1 / 2) : ℝ) •
          ((appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ S +
                  ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x) D) =
      ricciFoldBiContrFib (I := I) g₀ g₁ S x D from rfl]
  rw [show ricciFoldBiContrFib (I := I) g₀ g₁ S x =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [ricciFoldBiContrFibFixedFrame_toModel (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricciFoldKernelBilin_apply (I := I) g₀ S x
    (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) (v 0) (v 1)]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      ccTensorBilin (I := I) g₀ S x
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        ccTensorBilin (I := I) g₀ S x (smoothOrthoFrame (I := I) g₁ x b x)
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (v 1)) from
    ricciFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]
  ring

set_option linter.unusedSectionVars false in
private lemma single_b_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (q : ℕ) (hq : 1 ≤ q) :
    b q ≤ Combinatorics.antidiagonalTupleGrid b q := by
  have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 q hq
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  rwa [zero_add] at h

set_option linter.unusedVariables false in
private lemma exists_rfns_icg_ricciFoldWeightGen_window (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (w K : ℕ) (hwK : w ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (appCcRS (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                    (symmS (I := I) g₀ P))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 1) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  set KS : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose with hKS_def
  have hKS_nn : ∀ u, 0 ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.1
  have hKS : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + u) y
          ((iteratedCovGrad (I := I) g₀ 2 6 u
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection y) ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.2
  refine ⟨fun w => appCcGdiag (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1),
    fun w => by
      refine mul_nonneg (appCcGdiag_nonneg (E := E) w)
        (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
          (Finset.sum_nonneg fun w₂ _ => mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ => mul_nonneg (hKS_nn w₃)
              (Finset.sum_nonneg fun w₄ _ => by positivity)))), ?_⟩
  intro P δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hS : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 2 w₄
            (symmS (I := I) g₀ P)).toSection x) ≤ (fr ^ 2 + 1) * W := by
    intro w₄ hw₄
    match w₄, hw₄ with
    | 0, _ =>
        rw [iteratedCovGrad_zero]
        have hδ1 : δ ^ 2 ≤ 1 := by nlinarith
        have h0 := rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ P hδ0 hbound x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((symmS (I := I) (M := M) g₀ P).toSection x)
            ≤ fr ^ 2 * δ ^ 2 := h0
          _ ≤ fr ^ 2 * 1 := by
              refine mul_le_mul_of_nonneg_left hδ1 ?_
              positivity
          _ ≤ (fr ^ 2 + 1) * 1 := by nlinarith
          _ ≤ (fr ^ 2 + 1) * W := by
              refine mul_le_mul_of_nonneg_left hW_one ?_
              positivity
    | (k + 1), hw₄ =>
        refine le_trans (rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P
          (k + 1) x) ?_
        calc b (k + 1)
            ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
              single_b_le_grid b hb_nn (k + 1) (by omega)
          _ ≤ Combinatorics.boundedFactorGridWindow b K (w + 1) :=
              Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
                (by omega) (by omega)
          _ ≤ (fr ^ 2 + 1) * W := by
              rw [← hW_def]
              nlinarith [hW_nn]
  have hBase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (appCcRS (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                (symmS (I := I) g₀ P)))).toSection x) ≤
        (appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
    intro w₂ hw₂
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _ w₂ x]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ w₂ 0 2 6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
      (symmS (I := I) g₀ P) x) ?_
    calc appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 w₄
                    (symmS (I := I) g₀ P)).toSection x)
        ≤ appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hKS w₃ x) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + w₄) x _)
            (hKS_nn w₃)
          rw [Finset.mem_range] at hw₄
          exact hS w₄ (by omega)
      _ = (appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          have hstep : ∀ w₃ : ℕ, (KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W)) =
              (KS w₃ * ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
            intro w₃
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun w₃ _ => hstep w₃, ← Finset.sum_mul]
          ring
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
        (symmS (I := I) g₀ P))) x) ?_
  calc appCcGdiag (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (appCcRS (I := I) (M := M) g₀ 0 2 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                      (symmS (I := I) g₀ P)))).toSection x)
      ≤ appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (appCcGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        exact hBase w₂ (by omega)
    _ = (appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W)) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma bgRCommCoeffField_eq_refold (g : SmoothRiemannianMetric I M) :
    ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g =
      appCcRS (I := I) (M := M) g₀ 2 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g 2)
        (bgRArmWeight (I := I) (M := M) g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g).toSection x) D) =
      bgRBiContrFib (I := I) g₀ g x D from rfl]
  rw [show bgRBiContrFib (I := I) g₀ g x =
      bgRBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g x) x from rfl]
  rw [bgRBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g x) x D
    (fun j => (v j : E))]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g 2)
        (bgRArmWeight (I := I) (M := M) g₀)).toSection x) D) =
      cometricDoubleTraceFib (I := I) g 2 x
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) from by
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (bgRArmWeight (I := I) (M := M) g₀).toSection x) D))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [bgRArmWeight_toModel (I := I) (M := M) g₀ x D]
  show Tensor0SSpace.toModel D
      (Fin.cons (show E from riemannOp (LeviCivita (I := I) g₀) x
          (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
        (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
          (fun i : Fin 0 => i.elim0))) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
              (fun i : Fin 0 => i.elim0))) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x)
  have hu_exp : (show E from riemannOp (LeviCivita (I := I) g₀) x
      (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1)) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))]
  rw [hu_exp]
  rw [toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel D)
    (Module.finrank ℝ E)
    (fun e => g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
        (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
      (smoothOrthoFrame (I := I) g₀ x e x))
    (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
    (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
      (fun i : Fin 0 => i.elim0))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comm]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_vec3_slot0_sum_smul (x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![∑ c, t c • u c, a, b] = ∑ c, t c * Zm ![u c, a, b] := by
  classical
  have h1 : ∀ v : E, (![v, a, b] : Fin 3 → E) = Function.update ![(0 : E), a, b] 0 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![(0 : E), a, b] 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![(0 : E), a, b] 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_vec3_slot2_sum_smul (x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, b, ∑ c, t c • u c] = ∑ c, t c * Zm ![a, b, u c] := by
  classical
  have h1 : ∀ v : E, (![a, b, v] : Fin 3 → E) = Function.update ![a, b, (0 : E)] 2 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, b, (0 : E)] 2 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, b, (0 : E)] 2 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
private lemma sharpRaisedKoszulVec_symmS_eq_connDiff (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (symmS (I := I) g₀ P) x u ζ =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ := by
  rw [sharpRaisedKoszulVec, metricSharp_def, LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro z
  rw [show (metricFlatMap (I := I) g₁ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ)) z =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ) z from rfl]
  rw [linearizedKoszulCovec_apply (I := I) g₀ (symmS (I := I) g₀ P) x u ζ z]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x u ζ z]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma koszulCovecCc_unitModel_eq_g1_inner (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x a b c]
  rfl

private def k2FoldWeight (σ : Equiv.Perm (Fin 6)) (P : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (connDiffLoweredCc (I := I) g₀ g₁)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma k2FoldWeight_unitModel_gen (σ : Equiv.Perm (Fin 6))
    (P : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁)))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2))] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set κ3 : SmoothCcTensor g₀ 0 3 := koszulCovecCc (I := I) g₀ P with hκ3_def
  set Cval : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁).toSection x)
      (unitTensor (I := I) (M := M) x) with hCval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (appCcRS (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Cval ![(w (σ 0) : E), (w (σ 1) : E), (w (σ 2) : E)] *
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr σ
            ((appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (appCcRS (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3).toSection x) Cval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotExtendIter_three_toModel (I := I) (M := M) g₀ κ3 x Cval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 3 κ3 x
          (fun k : Fin 3 => ((fun i => w (σ i)) (Fin.natAdd 3 k) : E)) =
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (connDiffLoweredCc (I := I) g₀ g₁)))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma k2FoldWeights_unitModel_eq_kernel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (symmS (I := I) g₀ P) x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM1
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM1 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM2
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM2 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM3 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM3
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM3 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM4 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM4
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM4 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot2_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1)]
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p v1
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot0_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((p : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  have hT3 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot2_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT4 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)]
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0 v1
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot0_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v0 : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
      k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
      k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x]
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) x]
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [hM1, hM2, hM3, hM4]
  rw [sharpGradKoszulKernelBilin_apply (I := I) g₀ g₁ (symmS (I := I) g₀ P) x p q v0 v1]
  rw [sharpRaisedKoszulVec_symmS_eq_connDiff (I := I) (M := M) g₀ g₁ P htie x q v0,
    sharpRaisedKoszulVec_symmS_eq_connDiff (I := I) (M := M) g₀ g₁ P htie x q p]
  rw [hT1, hT2, hT3, hT4]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma sharpGradKoszulResidualField_eq_refold (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ (symmS (I := I) g₀ P) =
      (2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x)) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) D) := by
    rw [show ((((2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x)) =
        (2 : ℝ) •
          ((appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (symmS (I := I) g₀ P)).toSection x) D) =
      sharpGradKoszulBiContrFib (I := I) g₀ g₁ (symmS (I := I) g₀ P) x D from rfl]
  rw [show sharpGradKoszulBiContrFib (I := I) g₀ g₁ (symmS (I := I) g₀ P) x =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ (symmS (I := I) g₀ P)
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [sharpGradKoszulBiContrFibFixedFrame_toModel (I := I) g₀ g₁ (symmS (I := I) g₀ P)
    (smoothOrthoFrame (I := I) g₁ x) x D v]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (symmS (I := I) g₀ P) x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    k2FoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma exists_rfns_icg_k2FoldWeightGen_window (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (w K : ℕ) (hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (appCcRS (I := I) (M := M) g₀ 0 3 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                      (koszulCovecCc (I := I) g₀ P))
                    (connDiffLoweredCc (I := I) g₀ g₁))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 3) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  refine ⟨fun w => appCcGdiag (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2),
    fun w => mul_nonneg (appCcGdiag_nonneg (E := E) w)
      (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
        (Finset.sum_nonneg fun w₂ _ => mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
          (Finset.sum_nonneg fun w₃ _ =>
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                (Combinatorics.windowPairCellCount_nonneg _ _))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hκ : ∀ w₃ : ℕ, w₃ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
          ((iteratedCovGrad (I := I) g₀ 3 6 w₃
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovecCc (I := I) g₀ P))).toSection x) ≤
        (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
    intro w₃ hw₃
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P) =
        slotExtend (I := I) (M := M) g₀ 2 5 (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 5
      (slotExtend (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) w₃ x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P)) w₃ x)
      hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
        (koszulCovecCc (I := I) g₀ P) w₃ x) hfr_nn) hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (rfns_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ P w₃ x)
        hfr_nn) hfr_nn) hfr_nn) ?_
    have hb1 : b (w₃ + 1) ≤ Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
      refine le_trans (single_b_le_grid b hb_nn (w₃ + 1) (by omega)) ?_
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc fr * (fr * (fr * (10 * b (w₃ + 1))))
        = (10 * fr ^ 3) * b (w₃ + 1) := by ring
      _ ≤ (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
          refine mul_le_mul_of_nonneg_left hb1 ?_
          exact mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3)
  have hcdl : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 3 w₄
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) ≤
        CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2) := by
    intro w₄ hw₄
    rw [rfns_icg_connDiffLowered_eq_connDiffSection (I := I) (M := M) g₀ g₁ w₄ x]
    refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound w₄ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCA_nn w₄)
    have heq : (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k) =
        Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := by
      rw [Combinatorics.boundedFactorGridWindow]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
    calc (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k)
        = Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := heq
      _ ≤ Combinatorics.boundedFactorGridWindow b K (w₄ + 2) :=
          Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _)
  have hbase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (appCcRS (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovecCc (I := I) g₀ P))
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) ≤
        (appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
              CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
    intro w₂ hw₂
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _ w₂ x]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ w₂ 0 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
      (connDiffLoweredCc (I := I) g₀ g₁) x) ?_
    calc appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 3 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                    (koszulCovecCc (I := I) g₀ P))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 w₄
                    (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
        ≤ appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1),
              ((10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2)) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hκ w₃ (by omega)) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w₄) x _)
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
          rw [Finset.mem_range] at hw₄
          exact hcdl w₄ (by omega)
      _ ≤ (appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
            Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun w₃ hw₃ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_le_sum fun w₄ hw₄ => ?_
          rw [Finset.mem_range] at hw₃ hw₄
          calc (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2))
              = ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by ring
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K
                      ((w₃ + 2) + (w₄ + 2) - 1)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (w₃ + 2)
                  (w₄ + 2) (by omega) (by omega)
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₂ + 3)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                refine mul_le_mul_of_nonneg_left ?_
                  (Combinatorics.windowPairCellCount_nonneg _ _)
                exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _)
                  (by omega)
            _ = (10 * fr ^ 3) *
                  (CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                  Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by ring
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (connDiffLoweredCc (I := I) g₀ g₁))) x) ?_
  calc appCcGdiag (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (appCcRS (I := I) (M := M) g₀ 0 3 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                        (koszulCovecCc (I := I) g₀ P))
                      (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x)
      ≤ appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (appCcGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        refine le_trans (hbase w₂ (by omega)) ?_
        refine mul_le_mul_of_nonneg_left
          (Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega))
          (mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ =>
              mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                  (Combinatorics.windowPairCellCount_nonneg _ _))))
    _ = (appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w + 3) := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3))) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
              Combinatorics.boundedFactorGridWindow b K (w + 3) := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

end bgrConversion

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) y
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.2
  set KW : ℕ → ℝ := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w (bgRArmWeight (I := I) (M := M) g₀))).choose
    with hKW_def
  have hKW_nn : ∀ w, 0 ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (bgRArmWeight (I := I) (M := M) g₀))).choose_spec.1
  have hKW : ∀ w (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) y
          ((iteratedCovGrad (I := I) g₀ 2 4 w
            (bgRArmWeight (I := I) (M := M) g₀)).toSection y) ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (bgRArmWeight (I := I) (M := M) g₀))).choose_spec.2
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
        ∑ w ∈ Finset.range (i + 1 - u), KW w,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg
        (by have := hC2_nn u; have := hKD_nn u; linarith)
        (Finset.sum_nonneg fun w _ => hKW_nn w)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hdiff : ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
      - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀ =
      appCcRS (I := I) (M := M) g₀ 2 4 2
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField (I := I) g₀ 2)
        (bgRArmWeight (I := I) (M := M) g₀) := by
    rw [appCcRS_sub_left (I := I) (M := M) g₀ 2 4 2
      (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2) (cometricDoubleTraceField (I := I) g₀ 2)
      (bgRArmWeight (I := I) (M := M) g₀)]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₁]
    rw [← mvDoubleTraceField_self_eq (I := I) (M := M) g₀ 2]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₀]
  rw [hdiff]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ i 2 4 2
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField (I := I) g₀ 2)
    (bgRArmWeight (I := I) (M := M) g₀) x) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hAd : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2
              - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro u hu
    have hsec : (iteratedCovGrad (I := I) g₀ 4 2 u
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2
          - cometricDoubleTraceField (I := I) g₀ 2)).toSection x =
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x -
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x := by
      rw [sub_eq_add_neg (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
        (cometricDoubleTraceField (I := I) g₀ 2)]
      rw [iteratedCovGrad_add (I := I) g₀ 4 2 u _ _,
        iteratedCovGrad_neg (I := I) g₀ 4 2 u _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 4 2 u
            (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 4 2 u
            (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    rw [hsec]
    refine le_trans (rfns_sub_le_pt (I := I) (M := M) g₀ 4 (2 + u) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      refine le_trans (hC2 g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hC2_nn u)
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 4 2 u
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
          ≤ KD u := hKD u x
        _ = KD u * 1 := by ring
        _ ≤ KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
            refine mul_le_mul_of_nonneg_left ?_ (hKD_nn u)
            exact Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
        ≤ 2 * (C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
            2 * (KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          linarith [h1, h2]
      _ = (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          ring
  calc appCcGdiag (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u
                (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2
                  - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 4 w
                  (bgRArmWeight (I := I) (M := M) g₀)).toSection x)
      ≤ appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            ((2 * C2 u + 2 * KD u) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u hu => ?_) (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hAd u (by omega)) (Finset.sum_le_sum fun w _ => hKW w x)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + w) x _)
          (mul_nonneg (by have := hC2_nn u; have := hKD_nn u; linarith) hW_nn)
    _ = (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        have hstep : ∀ u : ℕ, ((2 * C2 u + 2 * KD u) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            (∑ w ∈ Finset.range (i + 1 - u), KW w) =
            ((2 * C2 u + 2 * KD u) * ∑ w ∈ Finset.range (i + 1 - u), KW w) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          intro u
          ring
        rw [Finset.sum_congr rfl fun u _ => hstep u, ← Finset.sum_mul]
        ring

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualFieldMetricDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ tauM1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ tauM2 hδ₀
  obtain ⟨CW3, hCW3_nn, hCW3⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ tauM3 hδ₀
  obtain ⟨CW4, hCW4_nn, hCW4⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ tauM4 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w =>
    fr ^ 2 * (4 * CW1 w + 4 * CW2 w + 4 * CW3 w + 4 * CW4 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h3 := hCW3_nn w
    have h4 := hCW4_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => 4 * (appCcGdiag (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [sharpGradKoszulResidualField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (2 : ℝ) _,
    show ((2 : ℝ)) ^ 2 = 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 sigmaE _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [sub_eq_add_neg (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)
        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have h12 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have h34 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM1
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM2
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P from rfl] at hA2
    have hA3 := hCW3 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM3
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P from rfl] at hA3
    have hA4 := hCW4 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM4
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P from rfl] at hA4
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
              (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact rfns_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))
          + 2 * (2 * (CW3 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW4 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hx12 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) := by
            rw [h12]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          have hx34 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) := by
            rw [h34]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          linarith [hA1, hA2, hA3, hA4, hx12, hx34]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I) (M := M) g₀ i 2 6 2
      (mvPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))) x)
    (by norm_num : (0 : ℝ) ≤ 4)) ?_
  calc (4 : ℝ) * (appCcGdiag (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                          k2FoldWeight (I := I) (M := M) g₀ g₁
                            tauM4 P))))).toSection x))
      ≤ 4 * (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ 4 * ((appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = (4 * (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CWA, hCWA_nn, hCWA⟩ :=
    exists_rfns_icg_ricciFoldWeightGen_window (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 6) 3) hδ₀
  obtain ⟨CWB, hCWB_nn, hCWB⟩ :=
    exists_rfns_icg_ricciFoldWeightGen_window (I := I) (M := M) g₀ tauK3b hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CWA w + 2 * CWB w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCWA_nn w
    have h2 := hCWB_nn w
    have h3 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => (1 / 4 : ℝ) * (appCcGdiag (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [ricciFoldRemainderField_eq_refold (I := I) (M := M) g₀ g₁ (symmS (I := I) g₀ P)]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P)))))).toSection x =
      (-(1 / 2) : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀
                  (symmS (I := I) g₀ P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (-(1 / 2) : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (-(1 / 2) : ℝ) _,
    show ((-(1 / 2) : ℝ)) ^ 2 = 1 / 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
                  ricciFoldWeightB (I := I) (M := M) g₀
                    (symmS (I := I) g₀ P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
    intro w hw
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 sigmaE _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P)) w x) hfr_nn) ?_
    have hsplit : (iteratedCovGrad (I := I) g₀ 0 4 w
        (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA := hCWA P hδ_le hδ0 hbound w (i + 1) (by omega) x
    have hB := hCWB P hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (symmS (I := I) g₀ P)))) =
        ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) from rfl] at hA
    rw [show (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauK3b
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (symmS (I := I) g₀ P)))) =
        ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P) from rfl] at hB
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
              ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsplit]
          exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr * (2 * (CWA w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
          + 2 * (CWB w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hnnA := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P))).toSection x)
          linarith [hA, hB]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I) (M := M) g₀ i 2 6 2
      (mvPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (symmS (I := I) g₀ P)))) x)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  calc (1 / 4 : ℝ) * (appCcGdiag (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (ricciFoldWeightA (I := I) (M := M) g₀ (symmS (I := I) g₀ P) +
                        ricciFoldWeightB (I := I) (M := M) g₀
                          (symmS (I := I) g₀ P))))).toSection x))
      ≤ (1 / 4 : ℝ) * (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (1 / 4 : ℝ) * ((appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((u + 1) + (w + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 1) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = ((1 / 4 : ℝ) * (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

private theorem appCcRS_smul_left_local (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (k : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (k • Φ) W =
      k • appCcRS (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • appCcRS (I := I) (M := M) g a b c Φ W).toSection x) =
      k • (appCcRS (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((k • Φ).toSection x : TensorRSSpace b c I x) = k • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

@[simp] private theorem appCcRS_ccSlotSwapField_involutive (g : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g 2 2) :
    appCcRS (I := I) (M := M) g 2 2 2
        (appCcRS (I := I) (M := M) g 2 2 2 C (ccSlotSwapField (I := I) (M := M) g))
        (ccSlotSwapField (I := I) (M := M) g) = C := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCcRS_toSection]
  apply ContinuousLinearMap.ext
  intro D
  simp only [ContinuousLinearMap.comp_apply]
  refine congrArg _ ?_
  change slotSwapFib (I := I) (M := M) x (slotSwapFib (I := I) (M := M) x D) = D
  rw [slotSwapFib_apply, slotSwapFib_apply, Tensor0SSpace.toModel_ofModel]
  rw [show ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel (𝕜 := ℝ) D)) = Tensor0SSpace.toModel (𝕜 := ℝ) D from by
    ext m
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    exact congrArg m (Equiv.swap_apply_self (0 : Fin 2) 1 i)]
  exact Tensor0SSpace.ofModel_toModel D

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_bgRDiffRefoldRemainderFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₃, hC₃_nn, hC₃⟩ :=
    rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set CB : ℕ → ℝ := fun n => 4 * C₁ n + 4 * C₂ n + 2 * C₃ n with hCB_def
  have hCB_nn : ∀ n, 0 ≤ CB n := by
    intro n
    have h1 := hC₁_nn n
    have h2 := hC₂_nn n
    have h3 := hC₃_nn n
    simp only [hCB_def]
    linarith
  refine ⟨fun i => (1 / 2 : ℝ) * CB i +
      (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), CB i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), CB i' := Finset.sum_nonneg fun i' _ => hCB_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ CB i := hCB_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set BD : SmoothCcTensor g₀ 2 2 :=
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
          - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
        + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
        - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) with hBD_def
    have hB : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x) ≤
        CB n * W := by
      intro n hn
      have hwin : Combinatorics.boundedFactorGridWindow b (n + 1) (n + 3) ≤ W := by
        rw [hW_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C₁ n * W :=
        le_trans (hC₁ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₁_nn n))
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W :=
        le_trans (hC₂ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₂_nn n))
      have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₃ n * W :=
        le_trans (hC₃ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₃_nn n))
      have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W := by
        rw [iteratedCovGrad_smul_real,
          show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x =
            (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x from by
            rw [SmoothCcTensor.toSection_smul]; rfl,
          riemannianFiberNormSq_smul_value,
          show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        linarith [h2]
      have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x =
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x
          + (iteratedCovGrad (I := I) g₀ 2 2 n
              ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
          - (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x := by
        rw [hBD_def, iteratedCovGrad_sub, iteratedCovGrad_add,
          SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
        rfl
      rw [hsplit]
      have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hCBW : CB n * W = 4 * (C₁ n * W) + 4 * (C₂ n * W) + 2 * (C₃ n * W) := by
        simp only [hCB_def]
        ring
      refine le_trans hsub ?_
      rw [hCBW]
      linarith [hadd, h1, h2', h3]
    have hsubject : ccInputSymm (I := I) (M := M) g₀
        (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (BD
          + appCcRS (I := I) (M := M) g₀ 2 2 2 BD
            (ccSlotSwapField (I := I) (M := M) g₀)) := by
      rw [show ccInputSymm (I := I) (M := M) g₀
          (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
          (1 / 2 : ℝ) • (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁
            + appCcRS (I := I) (M := M) g₀ 2 2 2
              (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀)) from rfl]
      refine congrArg (fun t => (1 / 2 : ℝ) • t) ?_
      rw [hBD_def]
      rw [show bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁ =
          appCcRS (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
              (ccSlotSwapField (I := I) (M := M) g₀)
            + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
            - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) from rfl]
      simp only [appCcRS_sub_left, appCcRS_add_left, appCcRS_smul_left_local,
        appCcRS_ccSlotSwapField_involutive]
      abel
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (BD
          + appCcRS (I := I) (M := M) g₀ 2 2 2 BD
            (ccSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (BD
            + appCcRS (I := I) (M := M) g₀ 2 2 2 BD
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit2 : (iteratedCovGrad (I := I) g₀ 2 2 i
        (BD
          + appCcRS (I := I) (M := M) g₀ 2 2 2 BD
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 2 2 BD
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit2]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x) ≤ CB i * W :=
      hB i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 2 2 BD
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 2 2 BD
        (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hBi' := hB i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' BD).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (CB i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hBi' hswapsum hswap_nn (mul_nonneg (hCB_nn i') hW_nn)
        _ = CB i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2 BD
                (ccSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (CB i * W)
            + 2 * (appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * CB i +
            (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), CB i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section qCommConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_vec3_slot1_sum_smul (x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, ∑ c, t c • u c, b] = ∑ c, t c * Zm ![a, u c, b] := by
  classical
  have h1 : ∀ v : E, (![a, v, b] : Fin 3 → E) = Function.update ![a, (0 : E), b] 1 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, (0 : E), b] 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, (0 : E), b] 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

private def sigmaQ1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 1, 2] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 5, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def sigmaQ2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 1, 4] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 1, 3, 5, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma qCommFoldWeights_unitModel_eq_kernel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ sigmaQ1 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ sigmaQ2 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0 v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [hM1, hM2]
  rw [connDiffAACommKernelBilin_apply (I := I) g₀ g₁ x p q v0 v1]
  rw [hT1, hT2]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciArmOrder0AACommCoeffField_eq_refold (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
      k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x) D) =
      connDiffAACommBiContrFib (I := I) g₀ g₁ x D from rfl]
  rw [connDiffAACommBiContrFib_toModel (I := I) g₀ g₁ x D v]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
        k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      connDiffAACommKernelBilin (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    qCommFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
lemma exists_rfns_icg_ricciArmOrder0AACommCoeffField_window
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ sigmaQ1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_rfns_icg_k2FoldWeightGen_window (I := I) (M := M) g₀ sigmaQ2 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CW1 w + 2 * CW2 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
        (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [ricciArmOrder0AACommCoeffField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                  k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 sigmaE _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
            k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x := by
      rw [sub_eq_add_neg (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P from rfl] at hA2
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact rfns_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          linarith [hA1, hA2]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ i 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) x) ?_
  calc appCcGdiag (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (k2FoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                        k2FoldWeight (I := I) (M := M) g₀ g₁
                          sigmaQ2 P)))).toSection x)
      ≤ appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
          (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (appCcGdiag (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

end qCommConversion

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_ricciArmOrder0AACommCoeffFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_rfns_icg_ricciArmOrder0AACommCoeffField_window (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hCq g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCq_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSymm (I := I) (M := M) g₀
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + appCcRS (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 2 2
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
                (ccSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

set_option maxHeartbeats 3200000 in

theorem refoldKernelContractionMonomialField_eq_mvPairTraceRefold
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 2 2 x (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x) D) =
      refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ x D from rfl]
  rw [refoldKernelContractionMonomialBiContrFib,
    refoldKernelContractionMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [domDomCongrSection_unitModel (I := I) g₀
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G x,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show unitModel (I := I) (M := M) g₀ 4 G x =
      Tensor0SSpace.toModel (𝕜 := ℝ)
        (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G x) from rfl]
  refine congrArg _ ?_
  funext j
  rw [show ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) j) =
      ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) (σ j)) from rfl]
  have hcons : ∀ k : Fin 4,
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) v) :
          Fin 4 → E) k =
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) k) := by
    intro k
    fin_cases k <;>
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> rfl
  exact hcons (σ j)

set_option linter.unusedVariables false in
private theorem exists_rfns_icg_refoldKernelContractionMonomialField_window
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                σ)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ n ∈ Finset.range (i + 1), CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun n _ => mul_nonneg (hCPT_nn n)
        (Finset.sum_nonneg fun l _ => by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) σ]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))))) x) ?_
  have hPT : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) :=
    fun n hn => hCPT g₁ P htie hδ_le hδ0 hbound n (i + 2) (by omega) x
  have hWb : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (symmS (I := I) (M := M) g₀ P)))))).toSection x) ≤
        fr ^ 2 * b (2 + l) := by
    intro l
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 sigmaE _ l x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))) =
        slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))))
        from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5 _ l x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 _ l x) hfr_nn) ?_
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) l x]
    rw [rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 l
      (symmS (I := I) (M := M) g₀ P) x]
    have hsymm := rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + l) x
    have hstep : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
          (symmS (I := I) (M := M) g₀ P)).toSection x) ≤ b (2 + l) := hsymm
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
              (symmS (I := I) (M := M) g₀ P)).toSection x))
        ≤ fr * (fr * b (2 + l)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep hfr_nn) hfr_nn
      _ = fr ^ 2 * b (2 + l) := by ring
  have hterm : ∀ n ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                    (iteratedCovGrad (I := I) g₀ 0 2 2
                      (symmS (I := I) (M := M) g₀ P)))))).toSection x) ≤
      (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hn' : n ≤ i := by omega
    have hsumW : (∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (symmS (I := I) (M := M) g₀ P)))))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2 * b (2 + l) :=
      Finset.sum_le_sum (fun l _ => hWb l)
    have hW_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (symmS (I := I) (M := M) g₀ P)))))).toSection x) :=
      Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
    refine le_trans (mul_le_mul (hPT n hn') hsumW hW_nn
      (mul_nonneg (hCPT_nn n)
        (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))) ?_
    rw [Finset.mul_sum]
    rw [show (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) =
        ∑ l ∈ Finset.range (i + 1 - n),
          CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    have habsorb : b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
      Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb_nn
        (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    calc CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) *
            (fr ^ 2 * b (2 + l))
        = (CPT n * fr ^ 2) *
            (b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1)) := by
          ring
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
          mul_le_mul_of_nonneg_left habsorb
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
          mul_le_mul_of_nonneg_left hmono
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ = CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

set_option linter.unusedVariables false in
private theorem exists_rfns_icg_refoldKernelContractionField_window
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2) hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C3, hC3_nn, hC3⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (1 : Equiv.Perm (Fin 4)) hδ₀
  refine ⟨fun i => 2 * C1 i + 2 * C2 i + C3 i + C4 i,
    fun i => by
      have := hC1_nn i; have := hC2_nn i; have := hC3_nn i; have := hC4_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set G : SmoothCcTensor g₀ 0 4 :=
    iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P) with hG_def
  set m1 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2) with hm1_def
  set m2 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (1 : Fin 4) 3) with hm2_def
  set m3 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) with hm3_def
  set m4 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (1 : Equiv.Perm (Fin 4)) with hm4_def
  have hker : refoldKernelContractionField (I := I) (M := M) g₀ g₁ G
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
      (1 / 2 : ℝ) • (m1 + m2 - m3 - m4) := rfl
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) • (m1 + m2 - m3 - m4))).toSection x =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (m1 + m2 - m3 - m4)).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i (m1 + m2 - m3 - m4)).toSection x =
      ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
        - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
        - (iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x := by
    rw [show m1 + m2 - m3 - m4 = (m1 + m2 - m3) - m4 from rfl, iteratedCovGrad_sub,
      show m1 + m2 - m3 = (m1 + m2) - m3 from rfl, iteratedCovGrad_sub, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add]
    rfl
  rw [hker, hsm, hsplit]
  rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
    show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
  have h1 := hC1 g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hC2 g₁ P htie hδ_le hδ0 hbound i x
  have h3 := hC3 g₁ P htie hδ_le hδ0 hbound i x
  have h4 := hC4 g₁ P htie hδ_le hδ0 hbound i x
  have hs1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x)
  have hs2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
  have hs3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
  have hgrid_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  nlinarith [h1, h2, h3, h4, hs1, hs2, hs3, hgrid_nn, hC1_nn i, hC2_nn i, hC3_nn i,
    hC4_nn i]

set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_refoldKernelContractionFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                  (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection
              x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨Ck, hCk_nn, hCk⟩ :=
    exists_rfns_icg_refoldKernelContractionField_window (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Ck i +
      (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Ck i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Ck i' :=
      Finset.sum_nonneg fun i' _ => hCk_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l :=
      Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Ck i := hCk_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set K : SmoothCcTensor g₀ 2 2 :=
      refoldKernelContractionField (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 with hK_def
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n K).toSection x) ≤ Ck n * W := by
      intro n hn
      refine le_trans (hCk g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCk_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSymm (I := I) (M := M) g₀ K =
        (1 / 2 : ℝ) • (K + appCcRS (I := I) (M := M) g₀ 2 2 2 K
          (ccSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (K + appCcRS (I := I) (M := M) g₀ 2 2 2 K
          (ccSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (K + appCcRS (I := I) (M := M) g₀ 2 2 2 K
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (K + appCcRS (I := I) (M := M) g₀ 2 2 2 K
          (ccSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 2 2 K
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x) ≤ Ck i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 2 2 K
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 2 2 K (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' K).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Ck i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCk_nn i') hW_nn)
        _ = Ck i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2 K
                (ccSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Ck i * W)
            + 2 * (appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Ck i +
            (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Ck i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section k4aRefoldCorner

private def k4aArrVal (i v : ℕ) : ℕ :=
  if v = 0 then i + 1
  else if v = 1 then i + 3
  else if v < i + 2 then v - 2
  else if v = i + 2 then i + 4
  else if v = i + 3 then i + 5
  else if v = i + 4 then i
  else i + 2

private lemma k4aArrVal_lt (i v : ℕ) (_hv : v < i + 6) : k4aArrVal i v < 6 + i := by
  unfold k4aArrVal
  split_ifs <;> omega

private lemma k4aArrVal_eq_sub (i v : ℕ) (h2 : 2 ≤ v) (h : v < i + 2) :
    k4aArrVal i v = v - 2 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_pos h]

private lemma k4aArrVal_at_i2 (i : ℕ) : k4aArrVal i (i + 2) = i + 4 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i3 (i : ℕ) : k4aArrVal i (i + 3) = i + 5 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i4 (i : ℕ) : k4aArrVal i (i + 4) = i := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i5 (i : ℕ) : k4aArrVal i (i + 5) = i + 2 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

private lemma k4a_decomposeFin_symm_val {m : ℕ} (ρ : Equiv.Perm (Fin m)) (j : Fin (m + 1)) :
    (((Equiv.Perm.decomposeFin.symm (0, ρ)) j : Fin (m + 1)) : ℕ) =
      if h : (j : ℕ) = 0 then 0
      else ((ρ ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin m) : ℕ) + 1 := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    simp
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [dif_neg (by simp [Fin.val_succ] : ¬((Fin.succ j' : Fin (m + 1)) : ℕ) = 0)]
    have harg : (⟨((Fin.succ j' : Fin (m + 1)) : ℕ) - 1,
        by have h1 := (Fin.succ j').isLt; have h2 := j'.isLt; omega⟩ : Fin m) = j' :=
      Fin.ext (by simp)
    rw [harg]
    simp [Fin.val_succ]

private lemma k4a_swap01_val {m : ℕ} (j : Fin (m + 2)) :
    (((Equiv.swap (0 : Fin (m + 2)) 1) j : Fin (m + 2)) : ℕ) =
      if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then 0 else (j : ℕ) := by
  rcases eq_or_ne j 0 with h0 | h0
  · subst h0
    rw [Equiv.swap_apply_left]
    simp
  · rcases eq_or_ne j 1 with h1 | h1
    · subst h1
      rw [Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      rw [if_neg (fun hv => h0 (Fin.ext (by simpa using hv))),
        if_neg (fun hv => h1 (Fin.ext (by simpa using hv)))]

private lemma k4a_step_perm_val {m : ℕ} (τ : Equiv.Perm (Fin (m + 2))) (i : ℕ)
    (hτ : ∀ j : Fin (m + 2), ((τ j : Fin (m + 2)) : ℕ) = k4aArrVal i (j : ℕ))
    (hm : m = 4 + i) (j : Fin (m + 3)) :
    ((((Equiv.Perm.decomposeFin.symm (0, Equiv.swap (0 : Fin (m + 2)) 1)).trans
          ((Equiv.swap (0 : Fin (m + 3)) 1).trans
            (Equiv.Perm.decomposeFin.symm (0, τ)))) j : Fin (m + 3)) : ℕ) =
      k4aArrVal (i + 1) (j : ℕ) := by
  rw [Equiv.trans_apply, Equiv.trans_apply]
  have hj1 := k4a_decomposeFin_symm_val (Equiv.swap (0 : Fin (m + 2)) 1) j
  set j1 : Fin (m + 3) := (Equiv.Perm.decomposeFin.symm (0, Equiv.swap (0 : Fin (m + 2)) 1)) j
    with hj1_def
  have hj2 := k4a_swap01_val (m := m + 1) ((Equiv.swap (0 : Fin (m + 3)) 1) j1)
  set j2 : Fin (m + 3) := (Equiv.swap (0 : Fin (m + 3)) 1) j1 with hj2_def
  have hj2v := k4a_swap01_val (m := m + 1) j1
  have hj3 := k4a_decomposeFin_symm_val τ j2
  rw [hj3]
  have hjlt : (j : ℕ) < m + 3 := j.isLt
  by_cases h0 : (j : ℕ) = 0
  · rw [dif_pos h0] at hj1
    have hj1v : (j1 : ℕ) = 0 := hj1
    have hj2vv : (j2 : ℕ) = 1 := by rw [hj2_def, hj2v, if_pos hj1v]
    rw [dif_neg (by omega)]
    rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
    have harg0 : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = 0 := by
      simp [hj2vv]
    rw [harg0]
    unfold k4aArrVal
    simp only [h0]
    split_ifs <;> omega
  · rw [dif_neg h0] at hj1
    rw [k4a_swap01_val (m := m) ⟨(j : ℕ) - 1, by omega⟩] at hj1
    simp only [] at hj1
    by_cases h1 : (j : ℕ) = 1
    · have hj1v : (j1 : ℕ) = 2 := by
        rw [hj1]
        simp [h1]
      have hj2vv : (j2 : ℕ) = 2 := by
        rw [hj2_def, hj2v, if_neg (by omega), if_neg (by omega), hj1v]
      rw [dif_neg (by omega)]
      rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
      have harg1 : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = 1 := by
        simp [hj2vv]
      rw [harg1]
      unfold k4aArrVal
      simp only [h1]
      split_ifs <;> omega
    · by_cases h2 : (j : ℕ) = 2
      · have hj1v : (j1 : ℕ) = 1 := by
          rw [hj1]
          simp [h2]
        have hj2vv : (j2 : ℕ) = 0 := by
          rw [hj2_def, hj2v, if_neg (by omega), if_pos hj1v]
        rw [dif_pos hj2vv]
        unfold k4aArrVal
        simp only [h2]
        split_ifs <;> omega
      · have hj1v : (j1 : ℕ) = (j : ℕ) := by
          rw [hj1]
          rw [if_neg (by omega), if_neg (by omega)]
          omega
        have hj2vv : (j2 : ℕ) = (j : ℕ) := by
          rw [hj2_def, hj2v, if_neg (by omega), if_neg (by omega), hj1v]
        rw [dif_neg (by omega)]
        rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
        have harg : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = (j : ℕ) - 1 := by
          simp [hj2vv]
        rw [harg]
        unfold k4aArrVal
        split_ifs <;> omega

private lemma k4a_covGrad_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r b (castRankCc_db g r h W) =
      castRankCc_db g r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g r a W) := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
private lemma k4a_rsDomDomCongrSection_comp (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ ρ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S) =
      rsDomDomCongrSection (I := I) (M := M) g r s (ρ.trans σ) S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection,
    rsDomDomCongrSection_toSection]
  exact rsDomDomCongr_rsDomDomCongr (I := I) (M := M) σ ρ (S.toSection x)

set_option linter.unusedSectionVars false in
private lemma k4a_covGrad_rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      rsDomDomCongrSection (I := I) (M := M) g r (s + 1)
        (Equiv.Perm.decomposeFin.symm (0, σ))
        (covGrad (I := I) (M := M) g r s S) := by
  classical
  have hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
            (rsDomDomCongrSection (I := I) (M := M) g r s σ S).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from S.toSection y) d)) := by
    intro y d
    rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hsec : (covGrad (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)).toSection x =
      rsDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
        ((covGrad (I := I) (M := M) g r s S).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ S)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
            ((covGrad (I := I) (M := M) g r s S).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
      ((covGrad (I := I) (M := M) g r s S).toSection x) d]
    exact ContinuousMultilinearMap.ext (fun v =>
      covGrad_rs_toModel_domDomCongr (I := I) (M := M) g r s σ S
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) hrel x d v)
  rw [hsec, rsDomDomCongrSection_toSection]

set_option linter.unusedSectionVars false in
private lemma k4a_slotExtend_rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ρ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S) =
      rsDomDomCongrSection (I := I) (M := M) g (r + 1) (s + 1)
        (Equiv.Perm.decomposeFin.symm (0, ρ))
        (slotExtend (I := I) (M := M) g r s S) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hsec : (slotExtend (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x =
      rsDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
        ((slotExtend (I := I) (M := M) g r s S).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
            ((slotExtend (I := I) (M := M) g r s S).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
      ((slotExtend (I := I) (M := M) g r s S).toSection x) d]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hlam : (fun k : Fin (s + 1) => v ((Equiv.Perm.decomposeFin.symm (0, ρ)) k)) =
        Fin.cons (v 0) (fun k : Fin s => v (Fin.succ (ρ k))) := by
      funext k
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cons_zero]
      · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
          Fin.cons_succ]
    rw [hlam]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s S).toSection x) d)
        (Fin.cons (v 0) (fun k : Fin s => v (Fin.succ (ρ k)))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (fun k : Fin s => v (Fin.succ (ρ k))) from
      slotExtendFib_apply_eval (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        d (v 0) (fun k : Fin s => v (Fin.succ (ρ k)))]
    conv_lhs => rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x) d)
        (Fin.cons (v 0) (Matrix.vecTail v)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (Matrix.vecTail v) from
      slotExtendFib_apply_eval (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
        d (v 0) (Matrix.vecTail v)]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
        (Matrix.vecTail v) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (fun k : Fin s => Matrix.vecTail v (ρ k)) from by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
        ContinuousMultilinearMap.domDomCongr_apply]]
    rfl
  rw [hsec, rsDomDomCongrSection_toSection]

set_option linter.unusedSectionVars false in
private lemma k4a_covGrad_slotExtend_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      rsDomDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

set_option linter.unusedSectionVars false in
private lemma k4a_covGrad_slotExtend (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ) =
      rsDomDomCongrSection (I := I) (M := M) g (r + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [k4a_covGrad_slotExtend_toSection (I := I) (M := M) g r s Φ x,
    rsDomDomCongrSection_toSection]

set_option linter.unusedSectionVars false in
private lemma k4a_icg_refoldArgument_structure (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 4) (i : ℕ) :
    ∃ τ : Equiv.Perm (Fin (((4 + i) + 1) + 1)),
      (∀ j : Fin (((4 + i) + 1) + 1),
        ((τ j : Fin (((4 + i) + 1) + 1)) : ℕ) = k4aArrVal i (j : ℕ)) ∧
      iteratedCovGrad (I := I) g₀ 2 6 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)) =
        castRankCc_db g₀ 2 (by omega : ((4 + i) + 1) + 1 = 6 + i)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
            (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
              (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
                (iteratedCovGrad (I := I) g₀ 0 4 i V)))) := by
  induction i with
  | zero =>
      refine ⟨sigmaE, by decide, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨τ, hτ, hEq⟩ := ih
      refine ⟨(Equiv.Perm.decomposeFin.symm
            (0, Equiv.swap (0 : Fin (((4 + i) + 1) + 1)) 1)).trans
          ((Equiv.swap (0 : Fin ((((4 + i) + 1) + 1) + 1)) 1).trans
            (Equiv.Perm.decomposeFin.symm (0, τ))), ?_, ?_⟩
      · intro j
        exact k4a_step_perm_val (m := 4 + i) τ i hτ rfl j
      · rw [iteratedCovGrad_succ, hEq]
        rw [k4a_covGrad_castRankCc_db]
        rw [k4a_covGrad_rsDomDomCongrSection]
        rw [k4a_covGrad_slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)]
        rw [k4a_covGrad_slotExtend (I := I) (M := M) g₀ 0 (4 + i)]
        rw [k4a_slotExtend_rsDomDomCongrSection]
        rw [k4a_rsDomDomCongrSection_comp, k4a_rsDomDomCongrSection_comp]
        rw [← iteratedCovGrad_succ]
        rfl

set_option linter.unusedSectionVars false in
private lemma k4a_castRankCc_db_toModel (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g r a) (x : M) (D : Tensor0SSpace r I x)
    (w : Fin b → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace b I x from
          (castRankCc_db g r h W).toSection x) D) (fun k => (w k : E)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from W.toSection x) D)
        (fun q : Fin a => (w (Fin.cast h q) : E)) := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
private lemma k4a_slotExtend_two_toModel (g₀ : SmoothRiemannianMetric I M) (c : ℕ)
    (S : SmoothCcTensor g₀ 0 c) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin ((c + 1) + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((c + 1) + 1) I x from
          (slotExtend (I := I) (M := M) g₀ 1 (c + 1)
            (slotExtend (I := I) (M := M) g₀ 0 c S)).toSection x) D)
        (fun k => (u k : E)) =
      Tensor0SSpace.toModel D ![(u 0 : E), (u 1 : E)] *
        unitModel (I := I) (M := M) g₀ c S x
          (fun k : Fin c => (u ⟨(k : ℕ) + 2, by omega⟩ : E)) := by
  have hu : (fun k : Fin ((c + 1) + 1) => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1)
          (fun k : Fin c => (u ⟨(k : ℕ) + 2, by omega⟩ : E))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change (u (Fin.succ (Fin.succ k2)) : E) = (u ⟨(k2 : ℕ) + 2, by omega⟩ : E)
    congr 1
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 (c + 1)
    (slotExtend (I := I) (M := M) g₀ 0 c S) x D (u 0)]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 c S x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![(u 0 : E), (u 1 : E)] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := (u 1 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := (u 0 : E)) (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option linter.unusedSectionVars false in
private lemma k4a_icg_refoldArgument_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 4) (i : ℕ) (x : M) (D : Tensor0SSpace 2 I x)
    (w : Fin (6 + i) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x) D)
        (fun k => (w k : E)) =
      Tensor0SSpace.toModel D
          ![(w ⟨i + 1, by omega⟩ : E), (w ⟨i + 3, by omega⟩ : E)] *
        unitModel (I := I) (M := M) g₀ (4 + i) (iteratedCovGrad (I := I) g₀ 0 4 i V) x
          (fun q : Fin (4 + i) =>
            (w ⟨k4aArrVal i ((q : ℕ) + 2), k4aArrVal_lt i _ (by have := q.isLt; omega)⟩ : E)) := by
  classical
  obtain ⟨τ, hτ, hEq⟩ := k4a_icg_refoldArgument_structure (I := I) (M := M) g₀ V i
  rw [hEq]
  rw [k4a_castRankCc_db_toModel (I := I) (M := M) g₀ 2
    (by omega : ((4 + i) + 1) + 1 = 6 + i)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
      (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
        (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
          (iteratedCovGrad (I := I) g₀ 0 4 i V)))) x D w]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (((4 + i) + 1) + 1) I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
        (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
          (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
            (iteratedCovGrad (I := I) g₀ 0 4 i V)))).toSection x) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (((4 + i) + 1) + 1) I x from
        rsDomDomCongr (I := I) (M := M) τ
          ((slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
            (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
              (iteratedCovGrad (I := I) g₀ 0 4 i V))).toSection x)) D) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) τ
    ((slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
      (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
        (iteratedCovGrad (I := I) g₀ 0 4 i V))).toSection x) D]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun k : Fin (((4 + i) + 1) + 1) =>
      (fun q : Fin (((4 + i) + 1) + 1) =>
        (w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) q) : E)) (τ k)) =
      (fun k : Fin (((4 + i) + 1) + 1) =>
        ((w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) (τ k)) : TangentSpace I x) : E))
      from rfl]
  rw [k4a_slotExtend_two_toModel (I := I) (M := M) g₀ (4 + i)
    (iteratedCovGrad (I := I) g₀ 0 4 i V) x D
    (fun k : Fin (((4 + i) + 1) + 1) =>
      w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) (τ k)))]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext k
    fin_cases k
    · change (w (Fin.cast _ (τ 0)) : E) = (w ⟨i + 1, _⟩ : E)
      congr 1
      refine Fin.ext ?_
      rw [Fin.val_cast, hτ 0]
      rfl
    · change (w (Fin.cast _ (τ 1)) : E) = (w ⟨i + 3, _⟩ : E)
      congr 1
      refine Fin.ext ?_
      rw [Fin.val_cast, hτ 1]
      rfl
  · refine congrArg _ ?_
    funext q
    congr 1
    refine Fin.ext ?_
    rw [Fin.val_cast, hτ ⟨(q : ℕ) + 2, by have := q.isLt; omega⟩]

set_option linter.unusedSectionVars false in
private def k4a_slotExtendIterFib (g : SmoothRiemannianMetric I M) (b c : ℕ) (x : M)
    (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) :
    ∀ w : ℕ, Tensor0SSpace (b + w) I x →L[ℝ] Tensor0SSpace (c + w) I x
  | 0 => A
  | (w + 1) => slotExtendFib (I := I) (M := M) g (b + w) (c + w) x
      (k4a_slotExtendIterFib g b c x A w)

set_option linter.unusedSectionVars false in
private lemma k4a_appCcLeibnizPsi_succ_succ_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        slotExtend (I := I) (M := M) g (b + j) (c + i)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
  rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castSrcCc g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castRankCc_db g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
  rw [castRankCc_db, castSrcCc]

set_option linter.unusedSectionVars false in
private lemma k4a_appCcLeibnizPsi_diag_toSection (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) (x : M) :
    ((appCcLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x :
        Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x) =
      k4a_slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hdiag : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) := by
        rw [k4a_appCcLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i i]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), zero_add]
      rw [hdiag]
      rw [show (k4a_slotExtendIterFib (I := I) (M := M) g b c x
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) (i + 1)) =
          slotExtendFib (I := I) (M := M) g (b + i) (c + i) x
            (k4a_slotExtendIterFib (I := I) (M := M) g b c x
              (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i)
          from rfl]
      rw [← ih]
      rfl

set_option linter.unusedSectionVars false in
private lemma k4a_mvPairTraceOp_fib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (Z : Tensor0SSpace 6 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
          (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Z)
        (fun j => (v j : E)) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                  (fun j => (v j : E)))))) := by
  classical
  rw [show ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
      (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Z) =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (cometricDoubleTraceFib (I := I) g₁ 4 x Z) from by
    rw [show mvPairTraceOp (I := I) (M := M) g₀ g₁ =
        appCcRS (I := I) (M := M) g₀ 6 4 2
          (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
          (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4) from rfl]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Z))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Z]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Z)
    (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]

private def k4aTuple (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    Fin (6 + i) → E := fun k =>
  if h : (k : ℕ) < i then ((u ⟨(k : ℕ), by omega⟩ : TangentSpace I x) : E)
  else if (k : ℕ) = i ∨ (k : ℕ) = i + 1 then
    ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
  else if (k : ℕ) = i + 2 ∨ (k : ℕ) = i + 3 then
    ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
  else if (k : ℕ) = i + 4 then ((u ⟨i, by omega⟩ : TangentSpace I x) : E)
  else ((u ⟨i + 1, by omega⟩ : TangentSpace I x) : E)

set_option linter.unusedSectionVars false in
private lemma k4aTuple_zero (g₁ : SmoothRiemannianMetric I M) (x : M)
    (u : Fin 2 → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    k4aTuple (I := I) (M := M) g₁ x 0 u a b =
      Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
              (fun j => (u j : E))))) := by
  funext k
  fin_cases k <;> rfl

set_option linter.unusedSectionVars false in
private lemma k4aTuple_succ (g₁ : SmoothRiemannianMetric I M) (x : M) (w : ℕ)
    (u : Fin (2 + (w + 1)) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    k4aTuple (I := I) (M := M) g₁ x (w + 1) u a b =
      Fin.cons ((u 0 : TangentSpace I x) : E)
        (k4aTuple (I := I) (M := M) g₁ x w (fun k => u (Fin.succ k)) a b) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Fin.cons_zero]
    unfold k4aTuple
    rw [dif_pos (by simp : ((0 : Fin (6 + (w + 1))) : ℕ) < w + 1)]
    exact congrArg u (Fin.ext (by simp))
  · rw [Fin.cons_succ]
    unfold k4aTuple
    by_cases h1 : (k' : ℕ) < w
    · rw [dif_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) < w + 1 by
        simp only [Fin.val_succ]; omega), dif_pos h1]
      beta_reduce
      exact congrArg u (Fin.ext (by simp [Fin.val_succ]))
    · rw [dif_neg (show ¬ ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) < w + 1 by
        simp only [Fin.val_succ]; omega), dif_neg h1]
      by_cases h2 : (k' : ℕ) = w ∨ (k' : ℕ) = w + 1
      · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) ∨
            ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 1 by
          simp only [Fin.val_succ]; omega), if_pos h2]
      · rw [if_neg (show ¬ (((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) ∨
            ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 1) by
          simp only [Fin.val_succ]; omega), if_neg h2]
        by_cases h3 : (k' : ℕ) = w + 2 ∨ (k' : ℕ) = w + 3
        · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 2 ∨
              ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 3 by
            simp only [Fin.val_succ]; omega), if_pos h3]
        · rw [if_neg (show ¬ (((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 2 ∨
              ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 3) by
            simp only [Fin.val_succ]; omega), if_neg h3]
          by_cases h4 : (k' : ℕ) = w + 4
          · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 4 by
              simp only [Fin.val_succ]; omega), if_pos h4]
            beta_reduce
            exact congrArg u (Fin.ext (by simp))
          · rw [if_neg (show ¬ ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 4 by
              simp only [Fin.val_succ]; omega), if_neg h4]
            beta_reduce
            exact congrArg u (Fin.ext (by simp))

set_option linter.unusedSectionVars false in
private lemma k4a_sEIterFib_mvPT_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ∀ (i : ℕ) (Y : Tensor0SSpace (6 + i) I x) (u : Fin (2 + i) → TangentSpace I x),
    Tensor0SSpace.toModel
        (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) i Y)
        (fun k => (u k : E)) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Y (k4aTuple (I := I) (M := M) g₁ x i u a b)
  | 0, Y, u => by
      rw [show k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) 0 Y =
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Y from rfl]
      rw [k4a_mvPairTraceOp_fib_toModel (I := I) (M := M) g₀ g₁ x Y u]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [k4aTuple_zero (I := I) (M := M) g₁ x u a b]
  | (w + 1), Y, u => by
      have hu : (fun k : Fin (2 + (w + 1)) => (u k : E)) =
          Fin.cons ((u 0 : TangentSpace I x) : E)
            (fun k : Fin (2 + w) => ((u (Fin.succ k) : TangentSpace I x) : E)) := by
        funext k
        exact Fin.cases rfl (fun k' => rfl) k
      rw [show k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) (w + 1) Y =
          slotExtendFib (I := I) (M := M) g₀ (6 + w) (2 + w) x
            (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
              (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
                (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) w) Y from rfl]
      rw [hu]
      refine Eq.trans (slotExtendFib_apply_eval (I := I) (M := M) g₀ (6 + w) (2 + w) x
        (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) w)
        Y ((u 0 : TangentSpace I x) : E)
        (fun k : Fin (2 + w) => ((u (Fin.succ k) : TangentSpace I x) : E))) ?_
      refine Eq.trans (k4a_sEIterFib_mvPT_toModel g₀ g₁ x w
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (6 + w) x) Y
          ((u 0 : TangentSpace I x) : E))
        (fun k : Fin (2 + w) => u (Fin.succ k))) ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 6 + w)
        (T := Y) (v0 := ((u 0 : TangentSpace I x) : E))
        (vs := k4aTuple (I := I) (M := M) g₁ x w (fun k => u (Fin.succ k)) a b)]
      refine congrArg _ ?_
      exact (k4aTuple_succ (I := I) (M := M) g₁ x w u a b).symm

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedSectionVars false in
private lemma k4a_frame_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v z : TangentSpace I x) :
    ∑ a : Fin (Module.finrank ℝ E),
        g₀.inner x v (smoothOrthoFrame (I := I) g₁ x a x) *
          g₀.inner x z (smoothOrthoFrame (I := I) g₁ x a x) =
      g₀.inner x v (gInvRaisedEndo (I := I) g₀ g₁ x z) := by
  classical
  have hg1w : ∀ u : TangentSpace I x,
      g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x z) u = g₀.inner x z u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner]
    rw [show cotangentToDualLinear (I := I) (x := x)
        (g0FlatCLM (I := I) g₀ x z) u =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x z) u from rfl]
    rw [cotangentToDual_g0FlatCLM]
  have hrepr := mvOrthoFrame_center_repr (I := I) (M := M) g₁ x
    (gInvRaisedEndo (I := I) g₀ g₁ x z)
  conv_rhs => rw [hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul]
  have hcoef : g₁.inner x (smoothOrthoFrame (I := I) g₁ x a x)
      (gInvRaisedEndo (I := I) g₀ g₁ x z) =
      g₀.inner x z (smoothOrthoFrame (I := I) g₁ x a x) := by
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x a x)
      (gInvRaisedEndo (I := I) g₀ g₁ x z)]
    exact hg1w (smoothOrthoFrame (I := I) g₁ x a x)
  rw [hcoef]
  ring

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedSectionVars false in
private lemma k4a_W_op_bound (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (x : M) (u : TangentSpace I x) :
    g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u) (gInvRaisedEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hs := sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
    (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
    (show δ < 1 from by linarith) hδ0 hbound x u
  have h0T : 0 ≤ g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u)
      (gInvRaisedEndo (I := I) g₀ g₁ x u) :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
  have h0u : 0 ≤ g₀.inner x u u :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ h1δ h1δ₀]
    linarith
  have hsq := Real.sq_sqrt h0T
  have hsqu := Real.sq_sqrt h0u
  have h1 : Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u)
      (gInvRaisedEndo (I := I) g₀ g₁ x u)) ≤
      (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
    le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
  calc g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u) (gInvRaisedEndo (I := I) g₀ g₁ x u)
      = Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u)
          (gInvRaisedEndo (I := I) g₀ g₁ x u)) ^ 2 := hsq.symm
    _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 := by
        nlinarith [h1, Real.sqrt_nonneg (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x u)
          (gInvRaisedEndo (I := I) g₀ g₁ x u))]
    _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
        rw [mul_pow, hsqu]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedSectionVars false in
private lemma k4a_W_absorption (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x,
      ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (B : Fin n → ℝ) :
    ∑ r : Fin n,
        (∑ p : Fin n, g₀.inner x (e r) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * B p) ^ 2 ≤
      (1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (B p) ^ 2 := by
  classical
  set u : TangentSpace I x := ∑ p : Fin n, B p • e p with hu_def
  have hlin : ∀ r : Fin n,
      (∑ p : Fin n, g₀.inner x (e r) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * B p) =
        g₀.inner x (e r) (gInvRaisedEndo (I := I) g₀ g₁ x u) := by
    intro r
    rw [hu_def, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun r _ => by rw [hlin r])]
  rw [hpars (gInvRaisedEndo (I := I) g₀ g₁ x u)]
  have hone : ∀ w : TangentSpace I x,
      g₀.inner x w u = ∑ q : Fin n, B q * g₀.inner x w (e q) := by
    intro w
    rw [hu_def, map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_smul, smul_eq_mul]
  have htwo : ∀ q : Fin n, g₀.inner x u (e q) = B q := by
    intro q
    rw [g₀.symm x u (e q), hone (e q)]
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => by
      rw [horth q p] :
      ∀ p ∈ Finset.univ, B p * g₀.inner x (e q) (e p) =
        B p * (if q = p then (1 : ℝ) else 0))]
    rw [Finset.sum_eq_single q (fun p _ hp => by rw [if_neg (fun hqp => hp hqp.symm), mul_zero])
      (fun hq => absurd (Finset.mem_univ q) hq)]
    rw [if_pos rfl, mul_one]
  have hnorm : g₀.inner x u u = ∑ p : Fin n, (B p) ^ 2 := by
    calc g₀.inner x u u = ∑ q : Fin n, B q * g₀.inner x u (e q) := hone u
      _ = ∑ p : Fin n, (B p) ^ 2 := Finset.sum_congr rfl fun q _ => by rw [htwo q]; ring
  rw [← hnorm]
  exact k4a_W_op_bound (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x u

set_option linter.unusedSectionVars false in
private lemma k4a_toModel_update_sum {m : ℕ} (Zm : Tensor0SModel m ℝ E)
    (w : Fin m → E) (t : Fin m) (d : ℕ) (c : Fin d → ℝ) (u : Fin d → E) :
    Zm (Function.update w t (∑ j, c j • u j)) =
      ∑ j, c j * Zm (Function.update w t (u j)) := by
  classical
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update w t (∑ j ∈ ss, c j • u j)) =
        ∑ j ∈ ss, c j * Zm (Function.update w t (u j)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  exact hgen Finset.univ

private def k4aR (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n) :
    Fin (4 + i) → Fin n := fun t =>
  if h : (t : ℕ) < 2 + i then J ⟨(t : ℕ), h⟩
  else if (t : ℕ) = 2 + i then p
  else q

set_option linter.unusedSectionVars false in
private lemma k4aTuple_apply_lt (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) < i) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨(t : ℕ), by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aTuple_apply_fa (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i ∨ (t : ℕ) = i + 1) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aTuple_apply_fb (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i + 2 ∨ (t : ℕ) = i + 3) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aTuple_apply_i4 (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i + 4) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨i, by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aTuple_apply_last (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : i + 5 ≤ (t : ℕ)) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨i + 1, by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

set_option linter.unusedSectionVars false in
private lemma k4a_mixTuple_eq_update (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin (2 + i) → Fin n)
    (a b : Fin (Module.finrank ℝ E)) :
    (fun q' : Fin (4 + i) =>
        k4aTuple (I := I) (M := M) g₁ x i (fun k => e (J k)) a b
          ⟨k4aArrVal i ((q' : ℕ) + 2),
            k4aArrVal_lt i ((q' : ℕ) + 2) (by have := q'.isLt; omega)⟩) =
      Function.update
        (Function.update
          (fun t : Fin (4 + i) =>
            if h : (t : ℕ) < 2 + i then ((e (J ⟨(t : ℕ), h⟩) : TangentSpace I x) : E)
            else (0 : E))
          ⟨2 + i, by omega⟩
          ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E))
        ⟨3 + i, by omega⟩
        ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
  classical
  funext t
  rw [Function.update_apply, Function.update_apply]
  by_cases h3 : (t : ℕ) = 3 + i
  · rw [if_pos (Fin.ext h3 : t = ⟨3 + i, by omega⟩)]
    have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
        k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
        ⟨i + 2, by omega⟩ := by
      refine Fin.ext ?_
      change k4aArrVal i ((t : ℕ) + 2) = i + 2
      rw [show (t : ℕ) + 2 = i + 5 from by omega]
      exact k4aArrVal_at_i5 i
    rw [hidx]
    exact k4aTuple_apply_fb (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ (Or.inl rfl)
  · rw [if_neg (fun ht' => h3 (by rw [ht']))]
    by_cases h2 : (t : ℕ) = 2 + i
    · rw [if_pos (Fin.ext h2 : t = ⟨2 + i, by omega⟩)]
      have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
          k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
          ⟨i, by omega⟩ := by
        refine Fin.ext ?_
        change k4aArrVal i ((t : ℕ) + 2) = i
        rw [show (t : ℕ) + 2 = i + 4 from by omega]
        exact k4aArrVal_at_i4 i
      rw [hidx]
      exact k4aTuple_apply_fa (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ (Or.inl rfl)
    · rw [if_neg (fun ht' => h2 (by rw [ht']))]
      have ht : (t : ℕ) < 2 + i := by have := t.isLt; omega
      rw [dif_pos ht]
      by_cases hlt : (t : ℕ) < i
      · have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
            k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
            ⟨(t : ℕ), by omega⟩ := by
          refine Fin.ext ?_
          change k4aArrVal i ((t : ℕ) + 2) = (t : ℕ)
          rw [k4aArrVal_eq_sub i ((t : ℕ) + 2) (by omega) (by omega)]
          omega
        rw [hidx]
        rw [k4aTuple_apply_lt (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _
          (show ((⟨(t : ℕ), by omega⟩ : Fin (6 + i)) : ℕ) < i from hlt)]
      · by_cases hi : (t : ℕ) = i
        · have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
              k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
              ⟨i + 4, by omega⟩ := by
            refine Fin.ext ?_
            change k4aArrVal i ((t : ℕ) + 2) = i + 4
            rw [show (t : ℕ) + 2 = i + 2 from by omega]
            exact k4aArrVal_at_i2 i
          rw [hidx]
          rw [k4aTuple_apply_i4 (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ rfl]
          exact congrArg e (congrArg J (Fin.ext hi.symm))
        · have hi1 : (t : ℕ) = i + 1 := by omega
          have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
              k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
              ⟨i + 5, by omega⟩ := by
            refine Fin.ext ?_
            change k4aArrVal i ((t : ℕ) + 2) = i + 5
            rw [show (t : ℕ) + 2 = i + 3 from by omega]
            exact k4aArrVal_at_i3 i
          rw [hidx]
          rw [k4aTuple_apply_last (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _
            (le_refl (i + 5))]
          exact congrArg e (congrArg J (Fin.ext hi1.symm))

set_option linter.unusedSectionVars false in
private lemma k4a_update_update_eq_R (x : M) (i : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin (2 + i) → Fin n) (p q : Fin n) :
    Function.update
        (Function.update
          (fun t : Fin (4 + i) =>
            if h : (t : ℕ) < 2 + i then ((e (J ⟨(t : ℕ), h⟩) : TangentSpace I x) : E)
            else (0 : E))
          ⟨2 + i, by omega⟩ ((e p : TangentSpace I x) : E))
        ⟨3 + i, by omega⟩ ((e q : TangentSpace I x) : E) =
      fun t : Fin (4 + i) => ((e (k4aR i J p q t) : TangentSpace I x) : E) := by
  classical
  funext t
  rw [Function.update_apply, Function.update_apply]
  unfold k4aR
  by_cases h3 : (t : ℕ) = 3 + i
  · rw [if_pos (Fin.ext h3 : t = ⟨3 + i, by omega⟩), dif_neg (by omega), if_neg (by omega)]
  · rw [if_neg (fun ht' => h3 (by rw [ht']))]
    by_cases h2 : (t : ℕ) = 2 + i
    · rw [if_pos (Fin.ext h2 : t = ⟨2 + i, by omega⟩), dif_neg (by omega), if_pos h2]
    · rw [if_neg (fun ht' => h2 (by rw [ht']))]
      have ht : (t : ℕ) < 2 + i := by have := t.isLt; omega
      rw [dif_pos ht, dif_pos ht]

set_option linter.unusedSectionVars false in
private lemma k4aR_apply_lt (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h : (t : ℕ) < 2 + i) :
    k4aR i J p q t = J ⟨(t : ℕ), h⟩ := by
  unfold k4aR
  rw [dif_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aR_apply_p (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h : (t : ℕ) = 2 + i) :
    k4aR i J p q t = p := by
  unfold k4aR
  rw [dif_neg (by omega), if_pos h]

set_option linter.unusedSectionVars false in
private lemma k4aR_apply_q (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h2 : ¬ (t : ℕ) < 2 + i) (h3 : ¬ (t : ℕ) = 2 + i) :
    k4aR i J p q t = q := by
  unfold k4aR
  rw [dif_neg h2, if_neg h3]

set_option linter.unusedSectionVars false in
private lemma k4a_rfns_icg_order_congr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {m m' : ℕ} (h : m = m') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + m) x
        ((iteratedCovGrad (I := I) g r s m S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + m') x
        ((iteratedCovGrad (I := I) g r s m' S).toSection x) := by
  subst h
  rfl

private lemma k4a_sum_reorg {d m : ℕ} (A B : Fin d → ℝ) (C D : Fin m → Fin d → ℝ)
    (Z : Fin m → Fin m → ℝ) :
    (∑ bb : Fin d, ∑ aa : Fin d, (A aa * B bb) *
        ∑ q : Fin m, C q bb * ∑ p : Fin m, D p aa * Z p q) =
      ∑ q : Fin m, (∑ bb : Fin d, B bb * C q bb) *
        ∑ p : Fin m, (∑ aa : Fin d, A aa * D p aa) * Z p q := by
  classical
  calc (∑ bb : Fin d, ∑ aa : Fin d, (A aa * B bb) *
        ∑ q : Fin m, C q bb * ∑ p : Fin m, D p aa * Z p q)
      = ∑ bb : Fin d, ∑ aa : Fin d, ∑ q : Fin m, ∑ p : Fin m,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) := by
        refine Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun aa _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ bb : Fin d, ∑ q : Fin m, ∑ aa : Fin d, ∑ p : Fin m,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun bb _ => Finset.sum_comm
    _ = ∑ bb : Fin d, ∑ q : Fin m, ∑ p : Fin m, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q : Fin m, ∑ bb : Fin d, ∑ p : Fin m, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) := Finset.sum_comm
    _ = ∑ q : Fin m, ∑ p : Fin m, ∑ bb : Fin d, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q : Fin m, (∑ bb : Fin d, B bb * C q bb) *
          ∑ p : Fin m, (∑ aa : Fin d, A aa * D p aa) * Z p q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun bb _ => ?_
        rw [show (B bb * C q bb) * ((∑ aa : Fin d, A aa * D p aa) * Z p q) =
            (∑ aa : Fin d, A aa * D p aa) * ((B bb * C q bb) * Z p q) from by ring]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun aa _ => ?_
        ring

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedVariables false in
set_option maxHeartbeats 6400000 in

theorem rfns_appCcRS_mvPairTraceOp_leibnizCorner_refoldArgument_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (symmS (I := I) (M := M) g₀ P))))))).toSection x) ≤
      ((1 / (1 - δ₀)) ^ 2) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
  classical
  set V : SmoothCcTensor g₀ 0 4 :=
    domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) with hV_def
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set Zm : Tensor0SModel (4 + i) ℝ E :=
    unitModel (I := I) (M := M) g₀ (4 + i) (iteratedCovGrad (I := I) g₀ 0 4 i V) x
    with hZm_def
  set Zc : (Fin (2 + i) → Fin n) → Fin n → Fin n → ℝ := fun J p q =>
    Zm (fun t => ((e (k4aR i J p q t) : TangentSpace I x) : E)) with hZc_def
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 2 (2 + i) x _ e hnE horth]
  have hexp_fa : ∀ c : Fin (Module.finrank ℝ E),
      ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) =
        ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x c x) •
          ((e p : TangentSpace I x) : E) :=
    fun c => hrepr (smoothOrthoFrame (I := I) g₁ x c x)
  have hupdcomm : ((⟨2 + i, by omega⟩ : Fin (4 + i))) ≠ (⟨3 + i, by omega⟩ : Fin (4 + i)) :=
    fun hcontra => by simpa using congrArg Fin.val hcontra
  have hcomp : ∀ (K : Fin 2 → Fin n) (J : Fin (2 + i) → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 2 (2 + i)
        ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)))).toSection x) n e K J =
        ∑ q : Fin n,
          g₀.inner x (e (K 1)) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e (K 0)) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q := by
    intro K J
    have hdiag := k4a_appCcLeibnizPsi_diag_toSection (I := I) (M := M) g₀ 6 2
      (mvPairTraceOp (I := I) (M := M) g₀ g₁) i x
    have h1 : fiberNormSqComponent (I := I) (M := M) g₀ x 2 (2 + i)
        ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)))).toSection x) n e K J =
        Tensor0SSpace.toModel
          ((k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
            (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
              (mvPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) i)
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
              (coframeS (I := I) (M := M) g₀ x 2 e K)))
          (fun k => (e (J k) : E)) := by
      rw [← hdiag]
      rfl
    rw [h1]
    refine Eq.trans (k4a_sEIterFib_mvPT_toModel g₀ g₁ x i
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
        (iteratedCovGrad (I := I) g₀ 2 6 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
        (coframeS (I := I) (M := M) g₀ x 2 e K))
      (fun k => e (J k))) ?_
    have hterm : ∀ (bb aa : Fin (Module.finrank ℝ E)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
              (coframeS (I := I) (M := M) g₀ x 2 e K))
            (k4aTuple (I := I) (M := M) g₁ x i (fun k => e (J k)) aa bb) =
          (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x)) *
            ∑ q : Fin n, g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x) *
              ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x) *
                Zc J p q := by
      intro bb aa
      refine Eq.trans (k4a_icg_refoldArgument_toModel (I := I) (M := M) g₀ V i x
        (coframeS (I := I) (M := M) g₀ x 2 e K)
        (fun k => k4aTuple (E := E) (I := I) (M := M) g₁ x i
          (fun k' => e (J k')) aa bb k)) ?_
      beta_reduce
      rw [k4aTuple_apply_fa (I := I) (M := M) g₁ x i (fun k' => e (J k')) aa bb
        ⟨i + 1, by omega⟩ (Or.inr rfl)]
      rw [k4aTuple_apply_fb (I := I) (M := M) g₁ x i (fun k' => e (J k')) aa bb
        ⟨i + 3, by omega⟩ (Or.inr rfl)]
      have hcof : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E),
            ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E)] =
          g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x) := by
        have h := coframeS_apply (I := I) (M := M) g₀ x 2 e K
          ![smoothOrthoFrame (I := I) g₁ x aa x, smoothOrthoFrame (I := I) g₁ x bb x]
        rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E)] =
            coframeS (I := I) (M := M) g₀ x 2 e K
              ![smoothOrthoFrame (I := I) g₁ x aa x,
                smoothOrthoFrame (I := I) g₁ x bb x] from rfl]
        rw [h, Fin.prod_univ_two]
        rfl
      rw [hcof]
      refine congrArg _ ?_
      refine Eq.trans (congrArg Zm (k4a_mixTuple_eq_update (I := I) (M := M) g₁ x i e J
        aa bb)) ?_
      conv_lhs => rw [show ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E) =
          ∑ q : Fin n, g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x) •
            ((e q : TangentSpace I x) : E) from hexp_fa bb]
      rw [k4a_toModel_update_sum Zm _ ⟨3 + i, by omega⟩ n
        (fun q => g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x))
        (fun q => ((e q : TangentSpace I x) : E))]
      refine Finset.sum_congr rfl fun q _ => ?_
      refine congrArg _ ?_
      rw [Function.update_comm hupdcomm]
      conv_lhs => rw [show ((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E) =
          ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x) •
            ((e p : TangentSpace I x) : E) from hexp_fa aa]
      rw [k4a_toModel_update_sum Zm _ ⟨2 + i, by omega⟩ n
        (fun p => g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x))
        (fun p => ((e p : TangentSpace I x) : E))]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine congrArg _ ?_
      rw [Function.update_comm (Ne.symm hupdcomm)]
      rw [k4a_update_update_eq_R (I := I) (M := M) x i e J p q]
    refine Eq.trans (Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun aa _ =>
      hterm bb aa) ?_
    refine Eq.trans (k4a_sum_reorg
      (fun aa => g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x))
      (fun bb => g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x))
      (fun q bb => g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x))
      (fun p aa => g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x))
      (fun p q => Zc J p q)) ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [k4a_frame_collapse (I := I) (M := M) g₀ g₁ x (e (K 1)) (e q)]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [k4a_frame_collapse (I := I) (M := M) g₀ g₁ x (e (K 0)) (e p)]
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) => Finset.sum_congr rfl
    (fun J (_ : J ∈ Finset.univ) => by rw [hcomp K J]))]
  have habs1 : ∀ (J : Fin (2 + i) → Fin n) (k0 : Fin n),
      (∑ k1 : Fin n, (∑ q : Fin n,
          g₀.inner x (e k1) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
        (1 / (1 - δ₀)) ^ 2 * ∑ q : Fin n,
          (∑ p : Fin n,
            g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 :=
    fun J k0 => k4a_W_absorption (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x e
      horth hpars (fun q => ∑ p : Fin n,
        g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q)
  have habs0 : ∀ (J : Fin (2 + i) → Fin n) (q : Fin n),
      (∑ k0 : Fin n, (∑ p : Fin n,
          g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
        (1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (Zc J p q) ^ 2 :=
    fun J q => k4a_W_absorption (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x e
      horth hpars (fun p => Zc J p q)
  have hd2_nn : (0 : ℝ) ≤ (1 / (1 - δ₀)) ^ 2 := sq_nonneg _
  have hKsplit : (∑ K : Fin 2 → Fin n, ∑ J : Fin (2 + i) → Fin n,
      (∑ q : Fin n,
        g₀.inner x (e (K 1)) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
          ∑ p : Fin n,
            g₀.inner x (e (K 0)) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) =
      ∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
        (∑ q : Fin n,
          g₀.inner x (e k1) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 := by
    refine Eq.trans Finset.sum_comm ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    calc (∑ K : Fin 2 → Fin n,
        (∑ q : Fin n,
          g₀.inner x (e (K 1)) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e (K 0)) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2)
        = ∑ pr : Fin n × Fin n,
            (∑ q : Fin n,
              g₀.inner x (e pr.2) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
                ∑ p : Fin n,
                  g₀.inner x (e pr.1) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) *
                    Zc J p q) ^ 2 :=
          Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun K => rfl)
      _ = ∑ k0 : Fin n, ∑ k1 : Fin n,
            (∑ q : Fin n,
              g₀.inner x (e k1) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
                ∑ p : Fin n,
                  g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) *
                    Zc J p q) ^ 2 := Fintype.sum_prod_type _
  rw [hKsplit]
  have hstep1 : (∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
      (∑ q : Fin n,
        g₀.inner x (e k1) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
          ∑ p : Fin n,
            g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
      (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
        ∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) := by
    calc (∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
        (∑ q : Fin n,
          g₀.inner x (e k1) (gInvRaisedEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2)
        ≤ ∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, (1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, (∑ p : Fin n,
              g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 :=
          Finset.sum_le_sum fun J _ => Finset.sum_le_sum fun k0 _ => habs1 J k0
      _ = ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ∑ k0 : Fin n, (∑ p : Fin n,
              g₀.inner x (e k0) (gInvRaisedEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) :=
          Finset.sum_congr rfl fun J _ =>
            Eq.trans (Finset.mul_sum _ _ _).symm
              (congrArg (fun t => (1 / (1 - δ₀)) ^ 2 * t) Finset.sum_comm)
      _ ≤ ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ((1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (Zc J p q) ^ 2)) := by
          refine Finset.sum_le_sum fun J _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ hd2_nn
          exact Finset.sum_le_sum fun q _ => habs0 J q
      _ = ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2)) :=
          Finset.sum_congr rfl fun J _ =>
            congrArg (fun t => (1 / (1 - δ₀)) ^ 2 * t) (Finset.mul_sum _ _ _).symm
      _ = (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
            ∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine le_trans hstep1 ?_
  have hbij : (∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) =
      ∑ R : Fin (4 + i) → Fin n,
        (Zm (fun t => ((e (R t) : TangentSpace I x) : E))) ^ 2 := by
    rw [show (∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) =
        ∑ tr : (Fin (2 + i) → Fin n) × Fin n × Fin n,
          (Zc tr.1 tr.2.2 tr.2.1) ^ 2 from by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun J _ =>
        (Fintype.sum_prod_type (fun y : Fin n × Fin n => (Zc J y.2 y.1) ^ 2)).symm]
    refine Fintype.sum_bijective
      (fun tr : (Fin (2 + i) → Fin n) × Fin n × Fin n => k4aR i tr.1 tr.2.2 tr.2.1) ?_ _ _
      (fun tr => by rw [hZc_def])
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun R => (fun j => R ⟨(j : ℕ), by have := j.isLt; omega⟩,
        R ⟨3 + i, by omega⟩, R ⟨2 + i, by omega⟩), ?_, ?_⟩
    · rintro ⟨J', qq, pp⟩
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext j
        refine Eq.trans (k4aR_apply_lt i J' pp qq ⟨(j : ℕ), by have := j.isLt; omega⟩
          j.isLt) ?_
        exact congrArg J' (Fin.ext rfl)
      · exact k4aR_apply_q i J' pp qq ⟨3 + i, by omega⟩
          (by change ¬(3 + i < 2 + i); omega) (by change ¬(3 + i = 2 + i); omega)
      · exact k4aR_apply_p i J' pp qq ⟨2 + i, by omega⟩ rfl
    · intro R
      funext t
      change k4aR i (fun j => R ⟨(j : ℕ), by have := j.isLt; omega⟩)
        (R ⟨2 + i, by omega⟩) (R ⟨3 + i, by omega⟩) t = R t
      by_cases hlt : (t : ℕ) < 2 + i
      · refine Eq.trans (k4aR_apply_lt i _ _ _ t hlt) ?_
        exact congrArg R (Fin.ext rfl)
      · by_cases heq2 : (t : ℕ) = 2 + i
        · refine Eq.trans (k4aR_apply_p i _ _ _ t heq2) ?_
          exact congrArg R (Fin.ext (by simpa using heq2.symm))
        · refine Eq.trans (k4aR_apply_q i _ _ _ t hlt heq2) ?_
          have heq3 : (t : ℕ) = 3 + i := by have := t.isLt; omega
          exact congrArg R (Fin.ext (by simpa using heq3.symm))
  rw [hbij]
  have hZmass : (∑ R : Fin (4 + i) → Fin n,
      (Zm (fun t => ((e (R t) : TangentSpace I x) : E))) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) := by
    rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) e hnE horth]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ R : Fin (4 + i) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (4 + i)
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) n e K R) ^ 2)]
    refine Finset.sum_congr rfl fun R _ => ?_
    refine congrArg (· ^ 2) ?_
    refine Eq.trans ?_ (fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ (4 + i) x
      (iteratedCovGrad (I := I) g₀ 0 4 i V) e default R).symm
    rfl
  rw [hZmass]
  have hVjets : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (symmS (I := I) (M := M) g₀ P))).toSection x) := by
          rw [hV_def]
          exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
            g₀ (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) i x
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i)
              (symmS (I := I) (M := M) g₀ P)).toSection x) :=
          rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 i
            (symmS (I := I) (M := M) g₀ P) x
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i) P).toSection x) :=
          rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + i) x
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) :=
          k4a_rfns_icg_order_congr (I := I) (M := M) g₀ 0 2
            (by omega : 2 + i = i + 2) P x
  calc (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x))
      ≤ (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVjets hd2_nn) hd2_nn
    _ = ((1 / (1 - δ₀)) ^ 2) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        ring

set_option linter.unusedVariables false in

theorem exists_rfns_icg_refoldKernelContractionMonomialField_leibnizResidual_window
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                σ)).toSection x
              - (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                  (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
                (iteratedCovGrad (I := I) g₀ 2 6 i
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (domDomCongrSection (I := I) g₀
                        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                        (iteratedCovGrad (I := I) g₀ 0 2 2
                          (symmS (I := I) (M := M) g₀ P))))))).toSection x) ≤
          K i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => (i : ℝ) * appCcGdiag (E := E) i *
      ∑ k ∈ Finset.range i, CPT (i - k) * fr ^ 2,
    fun i => mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
      (Finset.sum_nonneg fun k _ => mul_nonneg (hCPT_nn (i - k)) (by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound σ i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Xarg : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))))
    with hX_def
  have hsub : (iteratedCovGrad (I := I) g₀ 2 2 i
      (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
        σ)).toSection x
      - (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
          (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 6 i Xarg)).toSection x =
      ((∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (mvPairTraceOp (I := I) (M := M) g₀ g₁) i k)
          (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x) := by
    rw [refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) σ]
    rw [← hX_def]
    rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 6 2
      (mvPairTraceOp (I := I) (M := M) g₀ g₁) Xarg i]
    rw [show ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
          (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 6 i Xarg) +
        ∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
              (mvPairTraceOp (I := I) (M := M) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x) =
        (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i Xarg)).toSection x +
        (∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
              (mvPairTraceOp (I := I) (M := M) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x from by
      rw [SmoothCcTensor.toSection_add]
      rfl]
    rw [add_sub_cancel_left]
  rw [hsub]
  refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 6 2
    (mvPairTraceOp (I := I) (M := M) g₀ g₁) Xarg i x) ?_
  have hWb : ∀ k : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x) ≤
        fr ^ 2 * b (2 + k) := by
    intro k
    rw [hX_def]
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 sigmaE _ k x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))) =
        slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))))
        from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5 _ k x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 _ k x) hfr_nn) ?_
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) k x]
    rw [rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 k
      (symmS (I := I) (M := M) g₀ P) x]
    have hstep := rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + k) x
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + k)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + k)
              (symmS (I := I) (M := M) g₀ P)).toSection x))
        ≤ fr * (fr * b (2 + k)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep hfr_nn) hfr_nn
      _ = fr ^ 2 * b (2 + k) := by ring
  have hterm : ∀ k ∈ Finset.range i,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 6 2 (i - k)
            (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x) ≤
      (CPT (i - k) * fr ^ 2) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hker := hCPT g₁ P htie hδ_le hδ0 hbound (i - k) (i + 1) (by omega) x
    have harg := hWb k
    have hker_nn : (0 : ℝ) ≤ CPT (i - k) * Combinatorics.boundedFactorGridWindow b
        (i + 1) ((i - k) + 1) :=
      mul_nonneg (hCPT_nn (i - k))
        (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
    refine le_trans (mul_le_mul hker harg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + k) x _) hker_nn) ?_
    have habsorb : b (2 + k) * Combinatorics.boundedFactorGridWindow b (i + 1)
        ((i - k) + 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 1) (((i - k) + 1) + (2 + k)) :=
      Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb_nn
        (by omega) (by omega)
    calc (CPT (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1)) *
          (fr ^ 2 * b (2 + k))
        = (CPT (i - k) * fr ^ 2) *
            (b (2 + k) * Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1)) := by
          ring
      _ ≤ (CPT (i - k) * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (((i - k) + 1) + (2 + k)) :=
          mul_le_mul_of_nonneg_left habsorb
            (mul_nonneg (hCPT_nn (i - k)) (by positivity))
      _ = (CPT (i - k) * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          rw [show ((i - k) + 1) + (2 + k) = i + 3 from by omega]
  calc (i : ℝ) * appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 6 2 (i - k)
                (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x)
      ≤ (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (CPT (i - k) * fr ^ 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
          (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
    _ = ((i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i, CPT (i - k) * fr ^ 2) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        rw [← Finset.sum_mul]
        ring

end k4aRefoldCorner

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
