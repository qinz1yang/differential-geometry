import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder0KernelJetGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePairCore
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankReducingOperatorFieldGreenIBP
import DifferentialGeometry.Geometry.Metric.InnerExpansion

/-!
# Ricci connection-difference pairing at a closed edge

The order-zero Ricci connection-difference coefficient contains six terms
quadratic in the connection difference and two terms linear in its covariant
derivative.  The latter terms cannot be estimated pointwise at the initial
edge.  This file first exposes that algebraic split using only public tensor
operator APIs.  The derivative part is kept as a concrete field, so its
pairing can subsequently be lowered to the closed-edge formal partners and
integrated by parts.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-! ## Concrete kernel split -/

private def ricPerm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def ricPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def ricPerm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def ricPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def ricPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def ricPerm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def ricPerm3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

private def ricPerm2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

private def ricPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ricPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

set_option linter.unusedSectionVars false in
private theorem permCoeff_smooth (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(Real, Tensor0SBundle.TensorRSModel d d Real E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d Real E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) rho x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d Real E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d Real E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) rho x)
  intro Y
  have h := slotPermCLM_field_contMDiff (I := I) rho
    (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk'
    (Tensor0SBundle.Tensor0SModel d Real E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

/-- Smooth operator field which permutes all covariant output slots. -/
def permCoeff (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) : SmoothCcTensor g d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) rho x)
      contMDiff_toFun := permCoeff_smooth (I := I) (M := M) g rho }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private def ricQuad0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3201)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm102)
        (connDiffContrInsertionInnerField (I := I) g gm)))

private def ricQuad1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2301)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm102)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private def ricQuad2 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3102)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm120)
        (connDiffContrInsertionInnerField (I := I) g gm)))

private def ricQuad3 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1302)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (connDiffContrInsertionInnerField (I := I) g gm)))
    innerCoreInPerm10

private def ricQuad4 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1203)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (connDiffContrInsertionInnerField (I := I) g gm))

private def ricQuad5 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2103)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm120)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private def ricDer0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
    (permCoeff (I := I) (M := M) g ricPerm3012)
    (connDiffGradContrInsertionField (I := I) g gm)

private def ricDer1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2013)
      (connDiffGradContrInsertionField (I := I) g gm))
    innerCoreInPerm10

/-- The six connection-difference-quadratic arms of the order-zero Ricci
kernel. -/
def ricciAAKer (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ricQuad0 (I := I) (M := M) g gm +
    ricQuad1 (I := I) (M := M) g gm +
    ricQuad2 (I := I) (M := M) g gm +
    ricQuad3 (I := I) (M := M) g gm +
    ricQuad4 (I := I) (M := M) g gm +
    ricQuad5 (I := I) (M := M) g gm

/-- The signed two-arm part of the order-zero Ricci kernel which is linear in
the covariant derivative of the connection difference. -/
def ricciDAKer (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  -ricDer0 (I := I) (M := M) g gm -
    ricDer1 (I := I) (M := M) g gm

/-- Exact derivative/non-derivative split of the order-zero Ricci kernel. -/
theorem ricciKer_split (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder0KernelField (I := I) g gm =
      ricciAAKer (I := I) (M := M) g gm +
        ricciDAKer (I := I) (M := M) g gm := by
  have hraw :
      linearizedRicciConnDiffOrder0KernelField (I := I) g gm =
        ricciAAKer (I := I) (M := M) g gm -
          ricDer0 (I := I) (M := M) g gm -
          ricDer1 (I := I) (M := M) g gm := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    rfl
  rw [hraw, ricciDAKer]
  module

/-- Four-trace contraction of the quadratic kernel arms. -/
def ricciAAArm (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciAAKer (I := I) (M := M) g gm)

/-- Four-trace contraction of the derivative-only kernel arms. -/
def ricciDAArm (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciDAKer (I := I) (M := M) g gm)

/-- Exact split of the full order-zero Ricci connection-difference
coefficient into its quadratic and derivative-only parts. -/
theorem ricciCoeff_split (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g gm =
      ricciAAArm (I := I) (M := M) g gm +
        ricciDAArm (I := I) (M := M) g gm := by
  rw [linearizedRicciConnDiffOrder0CoeffField_eq_appCcRS,
    ricciKer_split, appCcRS_add_right]
  rfl

set_option linter.unusedSectionVars false in
private lemma ricPerm3012_eval (x : M) (D : Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) ricPerm3012 x D)
        ![a, b, c, d] =
      Tensor0SSpace.toModel D ![d, a, b, c] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

set_option linter.unusedSectionVars false in
private lemma ricPerm2013_eval (x : M) (D : Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) ricPerm2013 x D)
        ![a, b, c, d] =
      Tensor0SSpace.toModel D ![c, a, b, d] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

set_option linter.unusedSectionVars false in
private lemma ricPerm2_eval (x : M) (D : Tensor0SSpace 2 I x)
    (a b : TangentSpace I x) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) innerCoreInPerm10 x D)
        ![a, b] =
      Tensor0SSpace.toModel D ![b, a] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

/-- The derivative kernel consists of exactly the two expected contractions
of `covGrad connDiffSection` against its rank-two input. -/
theorem ricciDAKer_eval (g gm : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace 2 I x) (a b c d : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (ricciDAKer (I := I) (M := M) g gm).toSection x) T)
        ![a, b, c, d] =
      -Tensor0SSpace.toModel T
          ![rs13ContrVec (I := I) (M := M) x
              (show TensorRSSpace 1 3 I x from
                (covGrad (I := I) (M := M) g 1 2
                  (connDiffSection (I := I) gm g)).toSection x)
              ![a, b, c], d] -
        Tensor0SSpace.toModel T
          ![c, rs13ContrVec (I := I) (M := M) x
              (show TensorRSSpace 1 3 I x from
                (covGrad (I := I) (M := M) g 1 2
                  (connDiffSection (I := I) gm g)).toSection x)
              ![a, b, d]] := by
  let DA : TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g 1 2
      (connDiffSection (I := I) gm g)).toSection x
  change Tensor0SSpace.toModel
      (((-(slotPermCLM (I := I) ricPerm3012 x).comp
          (connContrCLM (I := I) 1 2 x DA) -
        (slotPermCLM (I := I) ricPerm2013 x).comp
          ((connContrCLM (I := I) 1 2 x DA).comp
            (slotPermCLM (I := I) innerCoreInPerm10 x))) T)
        ![a, b, c, d] = _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, Tensor0SSpace.toModel_sub,
    Tensor0SSpace.toModel_neg, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.neg_apply]
  rw [ricPerm3012_eval, ricPerm2013_eval]
  rw [connContr12_insert, connContr12_insert]
  rw [ricPerm2_eval]

/-- A single moving-metric trace is a `g`-orthonormal diagonal trace with
one relative inverse-metric insertion. -/
theorem ricTrace_eval (g gm : SmoothRiemannianMetric I M)
    (Z : SmoothCcTensor g 0 4) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z) x v =
      ∑ i : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4 Z x
          ![fullRaisedEndoField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x),
            smoothOrthoFrame (I := I) g x i x, v 0, v 1] := by
  classical
  rw [show ricciArmPrincipalCoeffPure (I := I) (M := M) g gm =
      mvDoubleTraceField (I := I) (M := M) g gm 2 from rfl]
  rw [pairTrace_refold (I := I) (M := M) g gm 2]
  rw [← appCc_assoc (I := I) (M := M) g 4 4 2]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply]
  rw [show ((show Tensor0SSpace 4 I x →L[Real] Tensor0SSpace 2 I x from
        (cometricDoubleTraceField (I := I) g 2).toSection x)
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
        (appCc (I := I) (M := M) g 4 4
          (slotInsertEndoCc (I := I) (M := M) g 3
            (fullRaisedEndoField (I := I) (M := M) g gm)) Z).toSection x)
        (unitTensor (I := I) (M := M) x))) =
      cometricDoubleTraceFib (I := I) g 2 x
        (slotInsertEndoFib (I := I) (M := M) 4 0 x
          (fullRaisedEndoField (I := I) (M := M) g gm x)
          ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
            Z.toSection x) (unitTensor (I := I) (M := M) x))) from by
      rw [cometricDoubleTraceField_toSection, appCc_toSection]
      rfl]
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotInsertEndoFib_apply_eval, Fin.update_cons_zero]
  rfl

/-! ## The genuine one-moving-trace flux -/

set_option linter.unusedSectionVars false in
private lemma ricUnit_sub (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A - B) x =
      unitModel (I := I) (M := M) g s A x -
        unitModel (I := I) (M := M) g s B x := by
  have h :
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          (A - B).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          A.toSection x) (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          B.toSection x) (unitTensor (I := I) (M := M) x) := by
    rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
      rw [SmoothCcTensor.toSection_sub]
      rfl]
    rfl
  rw [unitModel, unitModel, unitModel, h, Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
private lemma ricUnit_add (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A + B) x =
      unitModel (I := I) (M := M) g s A x +
        unitModel (I := I) (M := M) g s B x := by
  rw [unitModel, unitModel, unitModel,
    show (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (A + B).toSection x) =
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        A.toSection x) +
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        B.toSection x) from by
          rw [SmoothCcTensor.toSection_add]
          rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma ricUnit_smul (g : SmoothRiemannianMetric I M) (s : Nat)
    (c : Real) (A : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • A) x =
      c • unitModel (I := I) (M := M) g s A x := by
  have h :
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          (c • A).toSection x) (unitTensor (I := I) (M := M) x)) =
        c • ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          A.toSection x) (unitTensor (I := I) (M := M) x)) := by
    rw [show ((c • A).toSection x) = c • A.toSection x from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [unitModel, unitModel, h, Tensor0SSpace.toModel_smul]

/-- Rank-four flux left after the signed Ricci four-trace cancellation.  It
contains exactly one relative inverse-metric insertion. -/
def ricciDAFlux (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 W
  let P : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  P - domDomCongrSection (I := I) g ricPerm1203 P

/-- Component formula for `ricciDAFlux`.  In a `g`-orthonormal frame it is
`W[p,u] W(L v,r) - W[u,v] W(L p,r)`. -/
theorem ricciDAFlux_eval (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciDAFlux (I := I) (M := M) g gm W) x v =
      unitModel (I := I) (M := M) g 2 W x ![v 0, v 1] *
          unitModel (I := I) (M := M) g 2 W x
            ![fullRaisedEndoField (I := I) (M := M) g gm x (v 2), v 3] -
        unitModel (I := I) (M := M) g 2 W x ![v 1, v 2] *
          unitModel (I := I) (M := M) g 2 W x
            ![fullRaisedEndoField (I := I) (M := M) g gm x (v 0), v 3] := by
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 W
  let P : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  rw [ricciDAFlux, ricUnit_sub]
  change unitModel (I := I) (M := M) g 4 P x v -
      unitModel (I := I) (M := M) g 4
        (domDomCongrSection (I := I) g ricPerm1203 P) x v = _
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv : (fun i => v (ricPerm1203 i)) = ![v 1, v 2, v 0, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [P, pairProd4_eval, WR, pairSlot2_eval]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

/-! ## A slot-aligned carrier for the Green pairing -/

/-- Covariant derivative of the lowered connection difference, with slots
ordered as `[r,p,u,v]`.  Thus its component at those slots is
`g ((nabla_p A) u v) r`. -/
def ricciDAG (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
    (covGrad (I := I) (M := M) g 0 3
      (domDomCongrSection (I := I) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm)))

/-- The two-term Ricci derivative partner, ordered to pair directly with
`ricciDAG`.  At slots `[r,p,u,v]` it is
`W[p,u] W(L v,r) - W[u,v] W(L p,r)`. -/
def ricciDAPart (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g ricPerm3012.symm
    (ricciDAFlux (I := I) (M := M) g gm W)

/-- The Ricci DA flux is a difference of a rank-four product and one slot
permutation of that product, so every covariant-derivative fibre norm costs at
most the universal factor four.  This public estimate hides the internal
choice of component permutation. -/
theorem ricciFlux_rfns (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (j : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciDAFlux (I := I) (M := M) g gm W)).toSection x) ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (pairProd4 (I := I) (M := M) g W
            (pairSlot2 (I := I) (M := M) g
              (fullRaisedEndoField (I := I) (M := M) g gm) 0 W))).toSection x) := by
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 W
  let Q : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  rw [ricciDAFlux]
  change riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
      ((iteratedCovGrad (I := I) g 0 4 j
        (Q - domDomCongrSection (I := I) g ricPerm1203 Q)).toSection x) ≤ _
  rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]
  have hadd := riemannianFiberNormSq_sub_le
    (I := I) (M := M) g 0 (4 + j) x
    ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x)
    ((iteratedCovGrad (I := I) g 0 4 j
      (domDomCongrSection (I := I) g ricPerm1203 Q)).toSection x)
  have hperm :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g ricPerm1203 Q j x
  calc
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j
            (domDomCongrSection (I := I) g ricPerm1203 Q)).toSection x) := hadd
    _ = 4 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x) := by
      rw [hperm]
      ring
    _ = _ := by rfl

/-- The outer slot alignment in `ricciDAPart` preserves every covariant
derivative fibre norm.  This is the bound-facing interface which hides the
internal alignment permutation. -/
theorem ricciPart_rfns (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (j : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciDAPart (I := I) (M := M) g gm W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciDAFlux (I := I) (M := M) g gm W)).toSection x) := by
  rw [ricciDAPart]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g ricPerm3012.symm
      (ricciDAFlux (I := I) (M := M) g gm W) j x

/-- `ricciDAG` is just the first-two-slot swap of the covariant derivative
of the rotated lowered connection-difference tensor. -/
theorem ricciDAG_eval (g gm : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciDAG (I := I) (M := M) g gm) x v =
      unitModel (I := I) (M := M) g 4
        (covGrad (I := I) (M := M) g 0 3
          (domDomCongrSection (I := I) g (finRotate 3)
            (connDiffLoweredCc (I := I) g gm))) x
        ![v 1, v 0, v 2, v 3] := by
  rw [ricciDAG, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma ricLow_unitModel (g gm : SmoothRiemannianMetric I M)
    (x : M) :
    unitModel (I := I) (M := M) g 3
        (connDiffLoweredCc (I := I) g gm) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g gm x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (connDiffLoweredField (I := I) g gm x)
        (ContinuousMultilinearMap.constOfIsEmpty Real
          (fun _ : Fin 0 => TangentSpace I x) (1 : Real)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

private lemma ricLow_eval (g gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 3
        (connDiffLoweredCc (I := I) g gm) x m =
      g.inner x (PDE.DeTurck.connDiff (I := I) gm g x (m 0) (m 1))
        (m 2) := by
  rw [ricLow_unitModel]
  rfl

set_option linter.unusedSectionVars false in
private lemma ricInterior_eval (s : Nat) (x : M)
    (v : TangentSpace I x) (D : Tensor0SSpace (s + 1) I x)
    (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := Real) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := Real) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := Real) (E := E) s
        (show E from v) (Tensor0SSpace.toModel D) := rfl
  rw [h]
  rfl

private lemma ricCDual_coord
    (B : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (k : Fin (Module.finrank Real E)) :
    B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  exact congrArg (fun L : E →ₗ[Real] Real => LinearMap.toContinuousLinearMap L)
    (congrFun (Module.Basis.coe_dualBasis B) k)

set_option linter.unusedSectionVars false in
private lemma ricRS13_pair (x : M) (B : TensorRSSpace 1 3 I x)
    (beta : Tensor0SSpace 1 I x) (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
          beta) v =
      Tensor0SSpace.toModel beta
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) := by
  classical
  have hci : ∀ i : Fin (Module.finrank Real E),
      ((Module.finBasis Real E).cDualBasis i)
          (rs13ContrVec (I := I) (M := M) x B v) =
        (TensorRSSpace.toModel B
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := Real) (E := E)
            ((Module.finBasis Real E).cDualBasis i))) v := by
    intro i
    rw [rs13ContrVec, ricCDual_coord (Module.finBasis Real E) i]
    rw [map_sum]
    rw [show (∑ j : Fin (Module.finrank Real E),
        LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i)
          (((TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := Real) (E := E)
                ((Module.finBasis Real E).cDualBasis j))) v) •
            (Module.finBasis Real E) j)) =
        ∑ j : Fin (Module.finrank Real E),
          ((TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := Real) (E := E)
                ((Module.finBasis Real E).cDualBasis j))) v) *
            ((Module.finBasis Real E).repr
              ((Module.finBasis Real E) j) i) from
      Finset.sum_congr rfl (fun j _ => by
        rw [map_smul]
        rfl)]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.repr_self,
        show (Finsupp.single j (1 : Real)) i =
            if j = i then (1 : Real) else 0 from Finsupp.single_apply,
        mul_ite, mul_one, mul_zero])]
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp
    rw [ricCDual_coord (Module.finBasis Real E) i]
  have hexp : Tensor0SSpace.toModel beta =
      ∑ i : Fin (Module.finrank Real E),
        (Tensor0SSpace.toModel beta
          (Fin.cons ((Module.finBasis Real E) i) ![])) •
          Tensor0SBundle.model_covectorOfCLM (𝕜 := Real) (E := E)
            ((Module.finBasis Real E).cDualBasis i) := by
    refine ContinuousMultilinearMap.ext (fun w => ?_)
    rw [ContinuousMultilinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul,
        Tensor0SBundle.model_covectorOfCLM_apply])]
    rw [sum_cons_cDual_collapse (I := I) (M := M) beta ![] (w 0)]
    congr 1
    funext j
    fin_cases j
    rfl
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
        beta) =
      TensorRSSpace.toModel B (Tensor0SSpace.toModel beta) :=
    toModel_tensorRS_apply (I := I) 1 3 x B beta
  have hR : Tensor0SSpace.toModel beta
      (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
      ∑ i : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel beta
            (Fin.cons ((Module.finBasis Real E) i) ![]) *
          (TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := Real) (E := E)
              ((Module.finBasis Real E).cDualBasis i))) v := by
    rw [show Tensor0SSpace.toModel beta
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
      Tensor0SSpace.toModel beta
        (Fin.cons (rs13ContrVec (I := I) (M := M) x B v) ![]) from
      congrArg (fun w => Tensor0SSpace.toModel beta w)
        (funext (fun j => by fin_cases j; rfl))]
    rw [← sum_cons_cDual_collapse (I := I) (M := M) beta ![]
      (rs13ContrVec (I := I) (M := M) x B v)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hci i])
  rw [hL, hR]
  conv_lhs => rw [hexp]
  rw [map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul])

/-- Public realization of the connection difference by raising the first
slot of its lowered covariant tensor. -/
theorem connRaise_eq (g gm : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gm g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS :
      (show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 2 I x from
        connDiffFib (I := I) gm g x) om YZ =
      g.inner x u (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om
          (fun _ : Fin 1 =>
            PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)), ← hu]
  have hRHS :
      (show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := Real) (I := I)
            (1 + 1) x (inverseMetricSharpFib (I := I) g x om) D YZ :
          Real) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := Real) (I := I)
            (1 + 1) x (inverseMetricSharpFib (I := I) g x om) D) YZ from
      rfl]
    rw [ricInterior_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g 3
      (domDomCongrSection (I := I) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm)) x ![u, YZ 0, YZ 1] from by
    rw [hum]
    congr 1
    funext k
    fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
      ![YZ 0, YZ 1, u] from by
    funext i
    fin_cases i <;> simp [finRotate_succ_apply]]
  rw [ricLow_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g.symm x u
    (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1))]

/-- The covariant derivative consumed by the Ricci derivative kernel is the
first-slot raise of the slot-aligned lowered carrier `ricciDAG`. -/
theorem covConnRaise_eq (g gm : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g 1 2 (connDiffSection (I := I) gm g) =
      cometricRaiseSlot0Field (I := I) (M := M) g 2
        (ricciDAG (I := I) (M := M) g gm) := by
  rw [connRaise_eq,
    covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M)]
  rfl

/-- Pairing the vector reconstructed from the raised derivative tensor with
its lowering slot recovers the corresponding `ricciDAG` component. -/
theorem ricciDAG_pair (g gm : SmoothRiemannianMetric I M) (x : M)
    (r p u v : TangentSpace I x) :
    g.inner x
        (rs13ContrVec (I := I) (M := M) x
          (show TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g 1 2
              (connDiffSection (I := I) gm g)).toSection x)
          ![p, u, v]) r =
      unitModel (I := I) (M := M) g 4
        (ricciDAG (I := I) (M := M) g gm) x ![r, p, u, v] := by
  classical
  let D : Tensor0SSpace 4 I x :=
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
      (ricciDAG (I := I) (M := M) g gm).toSection x)
      (unitTensor (I := I) (M := M) x)
  let B : TensorRSSpace 1 3 I x :=
    cometricRaiseSlot0Fib (I := I) g 2 x D
  have hB :
      (show TensorRSSpace 1 3 I x from
        (covGrad (I := I) (M := M) g 1 2
          (connDiffSection (I := I) gm g)).toSection x) = B := by
    dsimp [B, D]
    rw [covConnRaise_eq (I := I) (M := M) g gm,
      cometricRaiseSlot0Field_toSection]
  rw [hB]
  let q : Fin 3 → E := ![p, u, v]
  let R : E := rs13ContrVec (I := I) (M := M) x B q
  change g.inner x R r = Tensor0SSpace.toModel D ![r, p, u, v]
  have hp := ricRS13_pair (I := I) (M := M) x B
    (g0FlatCLM (I := I) g x r) q
  have hleft :
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
          (g0FlatCLM (I := I) g x r)) q =
        Tensor0SSpace.toModel D ![r, p, u, v] := by
    dsimp [B]
    rw [cometricRaiseSlot0Fib_clm_apply,
      inverseMetricSharpFib_g0FlatCLM]
    rw [show (Tensor0SBundle.interior_product (𝕜 := Real) (I := I) 3 x r
          D q : Real) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := Real) (I := I) 3 x r D) q
        from rfl]
    rw [ricInterior_eval]
    dsimp [q]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hright :
      Tensor0SSpace.toModel (g0FlatCLM (I := I) g x r)
          (fun _ : Fin 1 => R) = g.inner x r R := by
    change (g0FlatCLM (I := I) g x r) (fun _ : Fin 1 => R) = _
    rw [show (g0FlatCLM (I := I) g x r) (fun _ : Fin 1 => R) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g x r) R
      from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM]
  rw [hleft] at hp
  change Tensor0SSpace.toModel D ![r, p, u, v] =
    Tensor0SSpace.toModel (g0FlatCLM (I := I) g x r)
      (fun _ : Fin 1 => R) at hp
  rw [hright] at hp
  rw [g.symm x R r, ← hp]

set_option linter.unusedSectionVars false in
private lemma ricL_self (g gm : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (fullRaisedEndoField (I := I) (M := M) g gm x v) w =
      g.inner x v
        (fullRaisedEndoField (I := I) (M := M) g gm x w) := by
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply]
  rw [inner_sharp_mixed (I := I) (M := M) g gm x
    (g0FlatCLM (I := I) g x v) w]
  rw [cotangentToDual_g0FlatCLM]

/-- Vector-valued component of the covariant derivative of the connection
difference. -/
def ricDAVec (g gm : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) : TangentSpace I x :=
  rs13ContrVec (I := I) (M := M) x
    (show TensorRSSpace 1 3 I x from
      (covGrad (I := I) (M := M) g 1 2
        (connDiffSection (I := I) gm g)).toSection x)
    ![a, b, c]

/-- Lowering `ricDAVec` in its output slot gives the corresponding
`ricciDAG` component. -/
theorem ricDAVec_pair (g gm : SmoothRiemannianMetric I M) (x : M)
    (r p u v : TangentSpace I x) :
    g.inner x (ricDAVec (I := I) (M := M) g gm x p u v) r =
      unitModel (I := I) (M := M) g 4
        (ricciDAG (I := I) (M := M) g gm) x ![r, p, u, v] := by
  simpa only [ricDAVec] using
    ricciDAG_pair (I := I) (M := M) g gm x r p u v

/-- Evaluation of the derivative-only kernel after applying it to a
covariant two-tensor. -/
theorem ricciDAKer_app (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g 4
        (appCc (I := I) (M := M) g 2 4
          (ricciDAKer (I := I) (M := M) g gm) W) x ![a, b, c, d] =
      -unitModel (I := I) (M := M) g 2 W x
          ![ricDAVec (I := I) (M := M) g gm x a b c, d] -
        unitModel (I := I) (M := M) g 2 W x
          ![c, ricDAVec (I := I) (M := M) g gm x a b d] := by
  rw [unitModel, appCc_toSection]
  simpa only [ricDAVec] using
    ricciDAKer_eval (I := I) (M := M) g gm x
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) a b c d

/-- The derivative of the connection difference remains symmetric in the
two connection-input slots. -/
theorem ricDAVec_symm (g gm : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    ricDAVec (I := I) (M := M) g gm x a b c =
      ricDAVec (I := I) (M := M) g gm x a c b := by
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x a,
      smoothExtensionTangent_contMDiff (I := I) x a⟩
  let Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x b,
      smoothExtensionTangent_contMDiff (I := I) x b⟩
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x c,
      smoothExtensionTangent_contMDiff (I := I) x c⟩
  have hX : X x = a := smoothExtensionTangent_eq (I := I) x a
  have hY : Y x = b := smoothExtensionTangent_eq (I := I) x b
  have hZ : Z x = c := smoothExtensionTangent_eq (I := I) x c
  have h1 := rs13ContrVec_covGrad_eq (I := I) (M := M) gm g X Y Z x
  have h2 := rs13ContrVec_covGrad_eq (I := I) (M := M) gm g X Z Y x
  change rs13ContrVec (I := I) (M := M) x _ ![a, b, c] =
    rs13ContrVec (I := I) (M := M) x _ ![a, c, b]
  rw [hX, hY, hZ] at h1 h2
  rw [h1, h2]
  exact covDerivConnDiff_symm23 (I := I) (M := M) gm g X Y Z x

set_option linter.unusedSectionVars false in
private lemma ricW_expand (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (y z : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x ![y, z] =
      ∑ i : Fin (Module.finrank Real E),
        g.inner x (smoothOrthoFrame (I := I) g x i x) y *
          unitModel (I := I) (M := M) g 2 W x
            ![smoothOrthoFrame (I := I) g x i x, z] := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hy := Geometry.Riemannian.expand_orthonormal
    (I := I) (M := M) g x hcard e horth y
  rw [unitModel_eq_ccTensorBilin_local, hy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, ← unitModel_eq_ccTensorBilin_local]
  rfl

private lemma ricSum_succ {A R : Type*} [Fintype A] [AddCommMonoid R]
    (s : Nat) (F : (Fin (s + 1) → A) → R) :
    (∑ J : Fin (s + 1) → A, F J) =
      ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
  classical
  calc
    (∑ J : Fin (s + 1) → A, F J) =
        ∑ p : A × (Fin s → A),
          F ((Fin.consEquiv (fun _ : Fin (s + 1) => A)) p) :=
      ((Fin.consEquiv (fun _ : Fin (s + 1) => A)).sum_comp F).symm
    _ = ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
      rw [Fintype.sum_prod_type]
      rfl

private lemma ricSum2 {A : Type*} [Fintype A]
    (F : (Fin 2 → A) → Real) :
    (∑ J : Fin 2 → A, F J) = ∑ a : A, ∑ b : A, F ![a, b] := by
  classical
  calc
    (∑ J : Fin 2 → A, F J) =
        ∑ p : A × A, F ((finTwoArrowEquiv A).symm p) :=
      ((finTwoArrowEquiv A).symm.sum_comp F).symm
    _ = ∑ a : A, ∑ b : A, F ![a, b] := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      funext k
      fin_cases k <;> rfl

private lemma ricSum4 {A : Type*} [Fintype A]
    (F : (Fin 4 → A) → Real) :
    (∑ J : Fin 4 → A, F J) =
      ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A,
        F ![a, b, c, d] := by
  classical
  rw [ricSum_succ (s := 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricSum_succ (s := 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ricSum_succ (s := 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ricSum_succ (s := 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · congr 1
    funext k
    fin_cases k <;> rfl
  · intro q _ hq
    exact absurd (Subsingleton.elim q (fun i : Fin 0 => i.elim0)) hq
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma ricSum4_comm
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ p : A × B, ∑ q : C × D, F p.1 p.2 q.1 q.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : C × D, ∑ p : A × B, F p.1 p.2 q.1 q.2 :=
      Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      simp only [Fintype.sum_prod_type]

private lemma ricSum3_cycle {A : Type*} [Fintype A]
    (F : A → A → A → Real) :
    (∑ a, ∑ b, ∑ c, F a b c) =
      ∑ a, ∑ b, ∑ c, F b c a := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, F a b c) =
        ∑ q : A × A, ∑ c, F q.1 q.2 c := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ c, ∑ q : A × A, F q.1 q.2 c := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ a, ∑ b, ∑ c, F b c a := by
      rfl

private lemma ricPair_alg {A : Type*} [Fintype A]
    (w h : A → A → Real) (d : A → A → A → A → Real) :
    (∑ u, ∑ v, w u v *
      (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) =
      ∑ r, ∑ p, ∑ u, ∑ v,
        (w p u * h v r - w u v * h p r) * d r p u v := by
  classical
  let P : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w u v * h p r * d r u v p
  let N : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w u v * h p r * d r p u v
  let F : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w p u * h v r * d r p u v
  have hL :
      (∑ u, ∑ v, w u v *
        (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) = P - N := by
    calc
      (∑ u, ∑ v, w u v *
          (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) =
          ∑ u, ∑ v, ∑ r, ∑ p,
            w u v * (h p r * (d r u v p - d r p u v)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ r, ∑ p, ∑ u, ∑ v,
          w u v * (h p r * (d r u v p - d r p u v)) :=
        ricSum4_comm (fun u v r p =>
          w u v * (h p r * (d r u v p - d r p u v)))
      _ = P - N := by
        dsimp only [P, N]
        have hterm : ∀ r p u v,
            w u v * (h p r * (d r u v p - d r p u v)) =
              w u v * h p r * d r u v p -
                w u v * h p r * d r p u v := by
          intros
          ring
        simp_rw [hterm, Finset.sum_sub_distrib]
  have hR :
      (∑ r, ∑ p, ∑ u, ∑ v,
        (w p u * h v r - w u v * h p r) * d r p u v) = F - N := by
    dsimp only [F, N]
    have hterm : ∀ r p u v,
        (w p u * h v r - w u v * h p r) * d r p u v =
          w p u * h v r * d r p u v -
            w u v * h p r * d r p u v := by
      intros
      ring
    simp_rw [hterm, Finset.sum_sub_distrib]
  have hFP : F = P := by
    dsimp only [F, P]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact ricSum3_cycle
      (fun p u v => w p u * h v r * d r p u v)
  rw [hL, hR, hFP]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma ricInner0 (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g.inner x (e a) (e b) =
      if a = b then (1 : Real) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (A.toFun x) (B.toFun x) =
      ∑ J : Fin s → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g s A x
            (fun k => (e (J k) : E)) *
          unitModel (I := I) (M := M) g s B x
            (fun k => (e (J k) : E)) := by
  classical
  rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  rw [tensorInnerPointwise_eq_sum_componentS_mul
    (I := I) (M := M) g 0 s x e bse rfl hbse horth
    (A.toSection x) (B.toSection x)]
  have hcomp : ∀ (T : SmoothCcTensor g 0 s)
      (K : Fin 0 → Fin (Module.finrank Real E))
      (J : Fin s → Fin (Module.finrank Real E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (T.toSection x) (Module.finrank Real E) e K J =
        unitModel (I := I) (M := M) g s T x
          (fun k => (e (J k) : E)) := by
    intro T K J
    rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s
        (T.toSection x) (Module.finrank Real E) e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          T.toSection x) (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => (e (J k) : E)) from rfl]
    rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
    rfl
  have hK : ∀ F : (Fin 0 → Fin (Module.finrank Real E)) → Real,
      (∑ K : Fin 0 → Fin (Module.finrank Real E), F K) =
        F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro q _ hq
      exact absurd (Subsingleton.elim q Fin.elim0) hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hK]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hcomp A Fin.elim0 J, hcomp B Fin.elim0 J]

set_option linter.unusedSectionVars false in
private lemma ricSmooth_basis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank Real E)) Real
        (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have horth : ∀ a b : Fin (Module.finrank Real E),
      g.inner x (e a) (e b) = if a = b then (1 : Real) else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent Real e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hz : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by
      rw [hsum]
      simp
    rw [map_sum] at hz
    have hpull : ∀ j ∈ fs,
        g.inner x (e k) (c j • e j) =
          c j * (if k = j then (1 : Real) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl hpull] at hz
    rw [Finset.sum_eq_single k
      (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun h => absurd hk h)] at hz
    rwa [if_pos rfl, mul_one] at hz
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_⟩
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma ricSwap_point (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 4) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 4 x (A.toFun x)
        ((domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) B).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) A).toFun x) (B.toFun x) := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  obtain ⟨bse, hbse0⟩ := ricSmooth_basis (I := I) (M := M) g x
  have hbse : ∀ i, bse i = e i := by
    simpa only [e] using hbse0
  have horth : ∀ a b, g.inner x (e a) (e b) =
      if a = b then (1 : Real) else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [ricInner0 (I := I) (M := M) g 4 A
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) B)
      x e bse hbse horth,
    ricInner0 (I := I) (M := M) g 4
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) A)
      B x e bse hbse horth]
  simp_rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1
  let tau : (Fin 4 → Fin (Module.finrank Real E)) ≃
      (Fin 4 → Fin (Module.finrank Real E)) :=
    Equiv.arrowCongr sigma.symm
      (Equiv.refl (Fin (Module.finrank Real E)))
  refine Fintype.sum_equiv tau
    (fun J =>
      unitModel (I := I) (M := M) g 4 A x (fun k => (e (J k) : E)) *
        unitModel (I := I) (M := M) g 4 B x
          (fun k => (e (J (sigma k)) : E)))
    (fun J =>
      unitModel (I := I) (M := M) g 4 A x
          (fun k => (e (J (sigma k)) : E)) *
        unitModel (I := I) (M := M) g 4 B x
          (fun k => (e (J k) : E)))
    (fun J => ?_)
  have htau : tau J = fun k => J (sigma k) := by
    funext k
    simp [tau, sigma, Equiv.arrowCongr]
  rw [htau]
  congr 1 <;> congr 1 <;> funext k <;> simp [sigma]

/-- Moving the first-two-slot swap from one rank-four covariant tensor to the
other leaves the global `L²` pairing unchanged. -/
theorem ricSwap_l2 (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 4) :
    tensorL2Inner (I := I) (M := M) g 0 4 A.toFun
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) B).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) A).toFun B.toFun := by
  classical
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact ricSwap_point (I := I) (M := M) g A B x

/-- Component formula for the slot-aligned Ricci derivative partner. -/
theorem ricciDAPart_eval (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciDAPart (I := I) (M := M) g gm W) x v =
      unitModel (I := I) (M := M) g 2 W x ![v 1, v 2] *
          unitModel (I := I) (M := M) g 2 W x
            ![fullRaisedEndoField (I := I) (M := M) g gm x (v 3), v 0] -
        unitModel (I := I) (M := M) g 2 W x ![v 2, v 3] *
          unitModel (I := I) (M := M) g 2 W x
            ![fullRaisedEndoField (I := I) (M := M) g gm x (v 1), v 0] := by
  rw [ricciDAPart, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv : (fun i => v (ricPerm3012.symm i)) =
      ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, ricciDAFlux_eval]

/-- The Ricci four-trace is the signed half-sum of four genuine single
moving-metric traces. -/
theorem ricFour_eval (g gm : SmoothRiemannianMetric I M)
    (Z : SmoothCcTensor g 0 4) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gm) Z) x v =
      (1 / 2 : Real) *
        (unitModel (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceArgPerm0231 Z)) x v +
          unitModel (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceArgPerm0321 Z)) x v -
          unitModel (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z) x v -
          unitModel (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceArgPerm2301 Z)) x v) := by
  let Z1 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceArgPerm0231 Z
  let Z2 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceArgPerm0321 Z
  let Z3 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceArgPerm2301 Z
  have h1 := reindexCoeffGen_appCc_eq (I := I) (M := M) g 4
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
    fourTraceArgPerm0231 Z Z1
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceArgPerm0231 Z y) x
  have h2 := reindexCoeffGen_appCc_eq (I := I) (M := M) g 4
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
    fourTraceArgPerm0321 Z Z2
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceArgPerm0321 Z y) x
  have h3 := reindexCoeffGen_appCc_eq (I := I) (M := M) g 4
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm)
    fourTraceArgPerm2301 Z Z3
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceArgPerm2301 Z y) x
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination]
  simp only [appCc_smul_left, appCc_add_left, appCc_sub_left]
  rw [ricUnit_smul, ricUnit_sub, ricUnit_sub, ricUnit_add]
  simp only [ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply,
    smul_eq_mul]
  change _ = (1 / 2 : Real) *
    (unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z1) x v +
      unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z2) x v -
      unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z) x v -
      unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g gm) Z3) x v)
  rw [h1, h2, h3]

/-- Pointwise eight-term expansion of the Ricci derivative arm before the
last-two-slot and formal-adjoint cancellations. -/
theorem ricciDAOut_eval (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      fullRaisedEndoField (I := I) (M := M) g gm x
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W) x v =
      (1 / 2 : Real) *
        ∑ i : Fin (Module.finrank Real E),
          (-unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x (L (e i)) (v 0) (v 1),
                e i] -
            unitModel (I := I) (M := M) g 2 W x
              ![v 1,
                ricDAVec (I := I) (M := M) g gm x (L (e i)) (v 0) (e i)] -
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x (L (e i)) (v 1) (v 0),
                e i] -
            unitModel (I := I) (M := M) g 2 W x
              ![v 0,
                ricDAVec (I := I) (M := M) g gm x (L (e i)) (v 1) (e i)] +
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x (L (e i)) (e i) (v 0),
                v 1] +
            unitModel (I := I) (M := M) g 2 W x
              ![v 0,
                ricDAVec (I := I) (M := M) g gm x (L (e i)) (e i) (v 1)] +
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x (v 0) (v 1) (L (e i)),
                e i] +
            unitModel (I := I) (M := M) g 2 W x
              ![L (e i),
                ricDAVec (I := I) (M := M) g gm x (v 0) (v 1) (e i)]) := by
  dsimp only
  rw [ricciDAArm, ← appCc_assoc (I := I) (M := M) g 2 4 2]
  rw [ricFour_eval]
  simp_rw [ricTrace_eval]
  simp_rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have h0231 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![fullRaisedEndoField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x),
            smoothOrthoFrame (I := I) g x i x, v 0, v 1] : Fin 4 → E)
          (fourTraceArgPerm0231 k)) =
        ![fullRaisedEndoField (I := I) (M := M) g gm x
            (smoothOrthoFrame (I := I) g x i x),
          v 0, v 1, smoothOrthoFrame (I := I) g x i x] := by
    intro i
    funext k
    fin_cases k <;> rfl
  have h0321 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![fullRaisedEndoField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x),
            smoothOrthoFrame (I := I) g x i x, v 0, v 1] : Fin 4 → E)
          (fourTraceArgPerm0321 k)) =
        ![fullRaisedEndoField (I := I) (M := M) g gm x
            (smoothOrthoFrame (I := I) g x i x),
          v 1, v 0, smoothOrthoFrame (I := I) g x i x] := by
    intro i
    funext k
    fin_cases k <;> rfl
  have h2301 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![fullRaisedEndoField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x),
            smoothOrthoFrame (I := I) g x i x, v 0, v 1] : Fin 4 → E)
          (fourTraceArgPerm2301 k)) =
        ![v 0, v 1,
          fullRaisedEndoField (I := I) (M := M) g gm x
            (smoothOrthoFrame (I := I) g x i x),
          smoothOrthoFrame (I := I) g x i x] := by
    intro i
    funext k
    fin_cases k <;> rfl
  simp_rw [h0231, h0321, h2301, ricciDAKer_app]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

set_option linter.unusedSectionVars false in
private lemma ricW_symm (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) (u v : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x ![u, v] =
      unitModel (I := I) (M := M) g 2 W x ![v, u] := by
  rw [unitModel_eq_ccTensorBilin_local,
    unitModel_eq_ccTensorBilin_local]
  exact hWsymm x u v

set_option linter.unusedSectionVars false in
private lemma ricW_D (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (p u v z : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x
        ![ricDAVec (I := I) (M := M) g gm x p u v, z] =
      ∑ r : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4
            (ricciDAG (I := I) (M := M) g gm) x
            ![smoothOrthoFrame (I := I) g x r x, p, u, v] *
          unitModel (I := I) (M := M) g 2 W x
            ![smoothOrthoFrame (I := I) g x r x, z] := by
  rw [ricW_expand]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [g.symm x (smoothOrthoFrame (I := I) g x r x)
      (ricDAVec (I := I) (M := M) g gm x p u v),
    ricDAVec_pair]

/-- After the connection-input and test-tensor symmetries, the pointwise
eight-term Ricci derivative output reduces to three terms. -/
theorem ricciDAOut_red (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) (v : Fin 2 → E) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      fullRaisedEndoField (I := I) (M := M) g gm x
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W) x v =
      (1 / 2 : Real) *
        ∑ i : Fin (Module.finrank Real E),
          (-2 * unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (L (e i)) (v 0) (v 1), e i] +
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (L (e i)), e i] +
            unitModel (I := I) (M := M) g 2 W x
              ![L (e i),
                ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (e i)]) := by
  dsimp only
  rw [ricciDAOut_eval]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ricDAVec_symm (I := I) (M := M) g gm x
      (fullRaisedEndoField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x)) (v 1) (v 0),
    ricDAVec_symm (I := I) (M := M) g gm x
      (fullRaisedEndoField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
      (smoothOrthoFrame (I := I) g x i x) (v 0),
    ricDAVec_symm (I := I) (M := M) g gm x
      (fullRaisedEndoField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
      (smoothOrthoFrame (I := I) g x i x) (v 1),
    ricW_symm (I := I) (M := M) g W hWsymm x
      (ricDAVec (I := I) (M := M) g gm x
        (fullRaisedEndoField (I := I) (M := M) g gm x
          (smoothOrthoFrame (I := I) g x i x)) (v 0)
          (smoothOrthoFrame (I := I) g x i x)) (v 1)]
  ring

set_option linter.unusedSectionVars false in
private lemma ricMove2 (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) (r u v : TangentSpace I x) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      fullRaisedEndoField (I := I) (M := M) g gm x
    (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![r, e p] *
          unitModel (I := I) (M := M) g 4
            (ricciDAG (I := I) (M := M) g gm) x
            ![r, L (e p), u, v]) =
      ∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![L (e p), r] *
          unitModel (I := I) (M := M) g 4
            (ricciDAG (I := I) (M := M) g gm) x
            ![r, e p, u, v] := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    fullRaisedEndoField (I := I) (M := M) g gm x
  let Wm := unitModel (I := I) (M := M) g 2 W x
  let Dm := unitModel (I := I) (M := M) g 4
    (ricciDAG (I := I) (M := M) g gm) x
  let Am : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    Wm.curryLeft r
  let Bm : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    (((Dm.domDomCongr fourTraceArgPerm2301).curryLeft u).curryLeft v).curryLeft r
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hkey := multilinear_slot0_pairing_self_adjoint
    (I := I) (M := M) g x L
    (ricL_self (I := I) (M := M) g gm x) e horth Am Bm
    (fun i : Fin 0 => i.elim0)
  have hAm (q : TangentSpace I x) : Am ![q] = Wm ![r, q] := by
    rfl
  have hBm (q : TangentSpace I x) : Bm ![q] = Dm ![r, q, u, v] := by
    simp only [Bm, ContinuousMultilinearMap.curryLeft_apply,
      ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext k
    fin_cases k <;> rfl
  change (∑ p : Fin (Module.finrank Real E),
      Am ![e p] * Bm ![L (e p)]) =
    ∑ p : Fin (Module.finrank Real E),
      Am ![L (e p)] * Bm ![e p] at hkey
  simp_rw [hAm, hBm] at hkey
  calc
    (∑ p : Fin (Module.finrank Real E),
        Wm ![r, e p] * Dm ![r, L (e p), u, v]) =
        ∑ p : Fin (Module.finrank Real E),
          Wm ![r, L (e p)] * Dm ![r, e p, u, v] := hkey
    _ = ∑ p : Fin (Module.finrank Real E),
        Wm ![L (e p), r] * Dm ![r, e p, u, v] := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ricW_symm (I := I) (M := M) g W hWsymm x r (L (e p))]

set_option linter.unusedSectionVars false in
private lemma ricMove4 (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) (r u v : TangentSpace I x) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      fullRaisedEndoField (I := I) (M := M) g gm x
    (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![r, e p] *
          unitModel (I := I) (M := M) g 4
            (ricciDAG (I := I) (M := M) g gm) x
            ![r, u, v, L (e p)]) =
      ∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![L (e p), r] *
          unitModel (I := I) (M := M) g 4
            (ricciDAG (I := I) (M := M) g gm) x
            ![r, u, v, e p] := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    fullRaisedEndoField (I := I) (M := M) g gm x
  let Wm := unitModel (I := I) (M := M) g 2 W x
  let Dm := unitModel (I := I) (M := M) g 4
    (ricciDAG (I := I) (M := M) g gm) x
  let Am : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    Wm.curryLeft r
  let Bm : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    (((Dm.curryLeft r).curryLeft u).curryLeft v)
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hkey := multilinear_slot0_pairing_self_adjoint
    (I := I) (M := M) g x L
    (ricL_self (I := I) (M := M) g gm x) e horth Am Bm
    (fun i : Fin 0 => i.elim0)
  have hAm (q : TangentSpace I x) : Am ![q] = Wm ![r, q] := by
    rfl
  have hBm (q : TangentSpace I x) : Bm ![q] = Dm ![r, u, v, q] := by
    rfl
  change (∑ p : Fin (Module.finrank Real E),
      Am ![e p] * Bm ![L (e p)]) =
    ∑ p : Fin (Module.finrank Real E),
      Am ![L (e p)] * Bm ![e p] at hkey
  simp_rw [hAm, hBm] at hkey
  calc
    (∑ p : Fin (Module.finrank Real E),
        Wm ![r, e p] * Dm ![r, u, v, L (e p)]) =
        ∑ p : Fin (Module.finrank Real E),
          Wm ![r, L (e p)] * Dm ![r, u, v, e p] := hkey
    _ = ∑ p : Fin (Module.finrank Real E),
        Wm ![L (e p), r] * Dm ![r, u, v, e p] := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ricW_symm (I := I) (M := M) g W hWsymm x r (L (e p))]

/-- Fully contracted pointwise formula for the Ricci derivative arm.  The
two surviving components are exactly the two arms of `ricciDAPart`. -/
theorem ricciDAOut_fin (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) (v : Fin 2 → E) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      fullRaisedEndoField (I := I) (M := M) g gm x
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W) x v =
      ∑ r : Fin (Module.finrank Real E),
        ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
            (unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] -
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, e p, v 0, v 1]) := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    fullRaisedEndoField (I := I) (M := M) g gm x
  have hA :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![ricDAVec (I := I) (M := M) g gm x
              (L (e p)) (v 0) (v 1), e p]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, e p, v 0, v 1] := by
    simp_rw [ricW_D (I := I) (M := M) g gm W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 4
              (ricciDAG (I := I) (M := M) g gm) x
              ![e r, L (e p), v 0, v 1] *
            unitModel (I := I) (M := M) g 2 W x ![e r, e p]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![e r, e p] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, L (e p), v 0, v 1] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      _ = ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
            unitModel (I := I) (M := M) g 4
              (ricciDAG (I := I) (M := M) g gm) x
              ![e r, e p, v 0, v 1] :=
        ricMove2 (I := I) (M := M) g gm W hWsymm x (e r) (v 0) (v 1)
  have hF :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![ricDAVec (I := I) (M := M) g gm x
              (v 0) (v 1) (L (e p)), e p]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] := by
    simp_rw [ricW_D (I := I) (M := M) g gm W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 4
              (ricciDAG (I := I) (M := M) g gm) x
              ![e r, v 0, v 1, L (e p)] *
            unitModel (I := I) (M := M) g 2 W x ![e r, e p]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![e r, e p] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, L (e p)] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      _ = ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
            unitModel (I := I) (M := M) g 4
              (ricciDAG (I := I) (M := M) g gm) x
              ![e r, v 0, v 1, e p] :=
        ricMove4 (I := I) (M := M) g gm W hWsymm x (e r) (v 0) (v 1)
  have hG :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![L (e p),
            ricDAVec (I := I) (M := M) g gm x
              (v 0) (v 1) (e p)]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] := by
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x
            ![L (e p),
              ricDAVec (I := I) (M := M) g gm x
                (v 0) (v 1) (e p)]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p), L (e p)] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact ricW_symm (I := I) (M := M) g W hWsymm x
          (L (e p))
          (ricDAVec (I := I) (M := M) g gm x (v 0) (v 1) (e p))
      _ = ∑ p : Fin (Module.finrank Real E),
          ∑ r : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] *
              unitModel (I := I) (M := M) g 2 W x ![e r, L (e p)] := by
        simp_rw [ricW_D (I := I) (M := M) g gm W]
      _ = ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] *
              unitModel (I := I) (M := M) g 2 W x ![e r, L (e p)] :=
        Finset.sum_comm
      _ = ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![L (e p), e r] *
              unitModel (I := I) (M := M) g 4
                (ricciDAG (I := I) (M := M) g gm) x
                ![e r, v 0, v 1, e p] := by
        refine Finset.sum_congr rfl fun r _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [ricW_symm (I := I) (M := M) g W hWsymm x
          (e r) (L (e p))]
        ring
  rw [ricciDAOut_red (I := I) (M := M) g gm W hWsymm x v]
  have hsplit :
      (∑ p : Fin (Module.finrank Real E),
          (-2 * unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (L (e p)) (v 0) (v 1), e p] +
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (L (e p)), e p] +
            unitModel (I := I) (M := M) g 2 W x
              ![L (e p),
                ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p)])) =
        -2 * (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x
            ![ricDAVec (I := I) (M := M) g gm x
                (L (e p)) (v 0) (v 1), e p]) +
          (∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (L (e p)), e p]) +
          (∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![L (e p),
                ricDAVec (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p)]) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hsplit, hA, hF, hG]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem ricDA_point (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x)
        ((appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((ricciDAPart (I := I) (M := M) g gm W).toFun x)
        ((ricciDAG (I := I) (M := M) g gm).toFun x) := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  obtain ⟨bse, hbse⟩ := ricSmooth_basis (I := I) (M := M) g x
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [ricInner0 (I := I) (M := M) g 2 W
      (appCc (I := I) (M := M) g 2 2
        (ricciDAArm (I := I) (M := M) g gm) W)
      x e bse hbse horth,
    ricInner0 (I := I) (M := M) g 4
      (ricciDAPart (I := I) (M := M) g gm W)
      (ricciDAG (I := I) (M := M) g gm)
      x e bse hbse horth,
    ricSum2, ricSum4]
  simp_rw [ricciDAOut_fin (I := I) (M := M) g gm W hWsymm,
    ricciDAPart_eval (I := I) (M := M) g gm W]
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    fullRaisedEndoField (I := I) (M := M) g gm x
  let w : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Real := fun a b =>
    unitModel (I := I) (M := M) g 2 W x ![e a, e b]
  let h : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Real := fun p r =>
    unitModel (I := I) (M := M) g 2 W x ![L (e p), e r]
  let d : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun r p u v =>
      unitModel (I := I) (M := M) g 4
        (ricciDAG (I := I) (M := M) g gm) x
        ![e r, e p, e u, e v]
  change (∑ u, ∑ v, w u v *
      (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) =
    ∑ r, ∑ p, ∑ u, ∑ v,
      (w p u * h v r - w u v * h p r) * d r p u v
  exact ricPair_alg w h d

/-- The derivative-only Ricci connection-difference arm pairs exactly with
the rank-four single-relative-trace partner. -/
theorem ricciDA_pair (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (ricciDAPart (I := I) (M := M) g gm W).toFun
        (ricciDAG (I := I) (M := M) g gm).toFun := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact ricDA_point (I := I) (M := M) g gm W hWsymm x

/-- Rotated lowered connection difference whose covariant derivative is the
unswapped carrier underlying `ricciDAG`. -/
def ricciDABase (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 3 :=
  domDomCongrSection (I := I) g (finRotate 3)
    (connDiffLoweredCc (I := I) g gm)

/-- Formal adjoint of the slot-aligned Ricci derivative partner. -/
def ricciDAAdj (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 3 :=
  covDivergence (I := I) (M := M) g 3
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciDAPart (I := I) (M := M) g gm W))

/-- Closed-manifold Green identity for the derivative-only Ricci
connection-difference arm.  The covariant derivative has been transferred
entirely to the explicit single-relative-trace partner. -/
theorem ricciDA_green (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W).toFun =
      -tensorL2Inner (I := I) (M := M) g 0 3
        (ricciDAAdj (I := I) (M := M) g gm W).toFun
        (ricciDABase (I := I) (M := M) g gm).toFun := by
  rw [ricciDA_pair (I := I) (M := M) g gm W hWsymm]
  change tensorL2Inner (I := I) (M := M) g 0 4
      (ricciDAPart (I := I) (M := M) g gm W).toFun
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
        (covGrad (I := I) (M := M) g 0 3
          (ricciDABase (I := I) (M := M) g gm))).toFun = _
  rw [ricSwap_l2 (I := I) (M := M) g
    (ricciDAPart (I := I) (M := M) g gm W)
    (covGrad (I := I) (M := M) g 0 3
      (ricciDABase (I := I) (M := M) g gm))]
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 4
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciDAPart (I := I) (M := M) g gm W)).toFun
    (covGrad (I := I) (M := M) g 0 3
      (ricciDABase (I := I) (M := M) g gm)).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g 3
    (ricciDABase (I := I) (M := M) g gm)
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciDAPart (I := I) (M := M) g gm W))]
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 3
    (ricciDABase (I := I) (M := M) g gm).toFun
    (ricciDAAdj (I := I) (M := M) g gm W).toFun]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
