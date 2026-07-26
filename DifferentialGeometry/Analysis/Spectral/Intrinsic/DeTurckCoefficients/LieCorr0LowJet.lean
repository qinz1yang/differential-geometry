import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance

/-!
# Low-jet refolds for the zeroth-order DeTurck correction

This file exposes the cancellation-compatible operator products behind the
zeroth-order DeTurck correction.  The first completed block is the fixed
curvature term: one moving inverse-metric trace acts on one fixed smooth
curvature operator.  Its moving trace has a pointwise antidiagonal-grid bound
at every covariant order.
-/

noncomputable section

-- Match `Tensor/RSTensor/Defs.lean` (and `LieCorr0Split`): section constructions
-- over the `(r,s)`-tensor bundle need the same reduced def-eq transparency to
-- synthesize the FiberBundle/VectorBundle stack. Elaboration-config only.
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Lowered connection-difference normal form -/

/-- The rank-three covariant tensor used by the `VB` and `AMix` fibres: the
connection difference from `gB` to `g₁`, lowered by the moving metric `g₁`,
but bundled over the frozen Sobolev background `g₀`. -/
def lc0KappaField (g₁ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ gB⟩

/-- Smooth compactly supported realization of the moving lowered connection
difference. -/
def lc0Kappa (g₀ g₁ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (lc0KappaField (I := I) (M := M) g₁ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem kappa_unit (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (lc0KappaField (I := I) (M := M) g₁ gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x m

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
theorem koszul_g1 (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS
    (I := I) (M := M) g₀ g₁ P htie x a b c]
  rfl

/-- Exact cancellation of the moving inverse metric in the self-background
lowered connection difference: after a fixed cyclic slot rotation it is the
linear Koszul covector built from one derivative of `P`. -/
theorem kappa_self (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ =
      domDomCongrSection (I := I) g₀ (finRotate 3).symm
        (koszulCovecCc (I := I) g₀ P) := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [kappa_unit (I := I) (M := M) g₀ g₁ g₀ x m]
  rw [domDomCongrSection_unitModel (I := I) g₀ (finRotate 3).symm
    (koszulCovecCc (I := I) g₀ P) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  rw [show (fun i => m ((finRotate 3).symm i)) = ![m 2, m 0, m 1] from by
    funext i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hτ0, hτ1, hτ2]]
  exact koszul_g1 (I := I) (M := M) g₀ g₁ P htie x (m 0) (m 1) (m 2)

/-- The part obtained by pairing a connection-difference vector with the
metric perturbation rather than with the frozen metric. -/
def lc0PbLowField (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

def lc0PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (lc0PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem pbLow_unit (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (lc0PbLowField (I := I) (M := M) g₀ P gA gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

private theorem unit_add0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m +
        unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      A.toSection x + B.toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

private theorem unit_sub0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A - B) x m =
      unitModel (I := I) (M := M) g₀ s A x m -
        unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      A.toSection x - B.toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

/-- Exact affine-background split of the lowered connection-difference
passenger.  The first term is the linear self-background Koszul tensor; the
remaining moving term is only `P` applied to the fixed connection difference. -/
theorem kappa_bg (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
        connDiffLoweredCc (I := I) g₀ gB +
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unit_add0 (I := I) (M := M) g₀ 3 _ _ x m,
    unit_sub0 (I := I) (M := M) g₀ 3 _ _ x m]
  rw [kappa_unit (I := I) (M := M) g₀ g₁ gB x m,
    kappa_unit (I := I) (M := M) g₀ g₁ g₀ x m,
    pbLow_unit (I := I) (M := M) g₀ P g₀ gB x m]
  rw [show unitModel (I := I) (M := M) g₀ 3
      (connDiffLoweredCc (I := I) g₀ gB) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gB g₀ x (m 0) (m 1)) (m 2) from by
    rw [unitModel]
    rw [show (connDiffLoweredCc (I := I) g₀ gB).toSection x
        (unitTensor (I := I) (M := M) x) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    rfl]
  have hanti : PDE.DeTurck.connDiff (I := I) gB g₀ x (m 0) (m 1) =
      -PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1) := by
    have h := PDE.DeTurck.connDiff_cocycle
      (I := I) gB g₀ g₀ x (m 0) (m 1)
    rw [PDE.DeTurck.connDiff_self] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [hanti, map_neg, ContinuousLinearMap.neg_apply, sub_neg_eq_add]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1)) (m 2)]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

private theorem ip_toModel (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s
        (show E from v) (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

/-- Raising and cyclically rotating `lc0PbLow` exposes it as the composition
of the fixed connection-difference operator with the `g₀`-raised symmetric
metric perturbation.  This is the exact normal form consumed by the `H2`
algebra estimate. -/
theorem pbLow_raise (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (connDiffSection (I := I) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [ip_toModel (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) x
          ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x)
          ((finRotate 3) i)) = ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [pbLow_unit (I := I) (M := M) g₀ P g₀ gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₀ gB).toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [connDiffSection_toSection]
    rw [connDiffFib_apply_eval (I := I) g₀ gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om) =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun _ : Fin 1 => (show E from
              PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)))) from by
      rw [ip_toModel (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _ _, ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from u)
          (fun _ : Fin 1 => (show E from
            PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2
          (symmS (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))
  rw [hLHS, hLHSval]
  exact hRHS.symm

/-- Pointwise jet-norm version of `pbLow_raise`. -/
theorem pbLow_rfns (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (appCcRS (I := I) (M := M) g₀ 1 1 2
            (connDiffSection (I := I) g₀ gB)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P g₀ gB))).toSection x) :=
          (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (appCcRS (I := I) (M := M) g₀ 1 1 2
              (connDiffSection (I := I) g₀ gB)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [pbLow_raise (I := I) (M := M) g₀ gB P]

/-- A moving cometric trace with a fixed permutation of its input slots. -/
def lc0Trace (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) : SmoothCcTensor g₀ (p + 2) p :=
  reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
    (pureTrace (I := I) (M := M) g₀ g₁ p) σ

/-- Fibre readout of `lc0Trace`: it is exactly the trace step used by the
canonical `lieCorr0` fibre formula. -/
theorem lc0Trace_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lc0Trace (I := I) (M := M) g₀ g₁ p σ).toSection x) =
      lieCorr0TraceStep (I := I) g₁ p σ x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lc0Trace (I := I) (M := M) g₀ g₁ p σ).toSection x) D) =
      reindexCoeffFibGen (I := I) (p + 2) p σ x
        (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
          (pureTrace (I := I) (M := M) g₀ g₁ p).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) (p + 2) p σ x _ D,
    pureTrace_toSection (I := I) (M := M) g₀ g₁ p x]
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply]
  congr 1

private lemma unitTensor_model (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

private lemma curry_zero (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀ =
      (Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀)) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    unitTensor_model (I := I) (M := M) x m, smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

private lemma clm_unit_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

private lemma slotLift_13 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) m =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => m 0) *
        Tensor0SSpace.toModel κ (Fin.tail m) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) =
        slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D
        from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D
      (m 0) (Fin.tail m)]
    rw [curry_zero (I := I) (M := M) x D (m 0)]
    rw [clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma slotLift_21 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 1) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hstep : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) =
      slotExtendFib (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D := rfl
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun _ : Fin 1 => m 2) := by
    rw [hstep]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D₁) =
        slotExtendFib (I := I) (M := M) g₀ 0 1 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x) D₁
        from rfl]
    rw [show (Fin.tail m : Fin 2 → E) =
        Fin.cons (m 1) (fun _ : Fin 1 => m 2) from by
      funext k; fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 1 x _ D₁
      (m 1) (fun _ : Fin 1 => m 2)]
    rw [curry_zero (I := I) (M := M) x D₁ (m 1)]
    rw [clm_unit_smul (I := I) (M := M) x 1 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1 <;> first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma slotLift_23 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) =
        slotExtendFib (I := I) (M := M) g₀ 1 4 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D
        from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D₁) =
        slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D₁
        from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k; fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [curry_zero (I := I) (M := M) x D₁ (m 1)]
    rw [clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1 <;> first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma slotLift_33 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) =
        slotExtendFib (I := I) (M := M) g₀ 2 5 x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D
        from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotLift_23 (I := I) (M := M) g₀ K x D₂, ← hκ,
      tensor0SProdKappaFib_apply (I := I) x κ D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma kappa_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      metricConnDiffLoweredFib (I := I) g₁ g₁ gB x := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (lc0KappaField (I := I) (M := M) g₁ gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

private lemma interior_model (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h₁ : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s
        (show E from v) (Tensor0SSpace.toModel D) := rfl
  rw [h₁]
  rfl

private lemma toModel_cons_sum (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h₁ : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0
          (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c *
          Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from
          (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul, zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha,
          ContinuousMultilinearMap.map_update_add, ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul, smul_eq_mul]
  have h₂ := hgen Finset.univ
  rw [h₁, h₂]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h₁ (u c)]

private lemma orthoFrame_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with he
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • e i) (e j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • e i) (e j) =
        c i * (if i = j then (1 : ℝ) else 0) := by
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
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hb
  have hb_coe : ∀ i, b i = e i := by
    intro i
    rw [hb]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = e i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      b.repr w j = g.inner x (e j) w := by
    intro w j
    conv_rhs => rw [← b.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (e j) (b.repr w i • b i) =
        b.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hb_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← b.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hb_coe i]

/-! ## Cancellation-compatible `VB` and `AMix` operator forms -/

/-- The moving-metric covector dual to the DeTurck vector field.  It is one
rank-one moving trace applied to the lowered connection difference. -/
def lc0VFlat (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 1 :=
  appCcRS (I := I) (M := M) g₀ 0 3 1
    (lc0Trace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
    (lc0Kappa (I := I) (M := M) g₀ g₁ gB)

/-- Permutation placing the traced DeTurck-vector slot in front of a
rank-two passenger. -/
def lc0IVPerm : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2

/-- Operator realizing insertion of the DeTurck vector field into a symmetric
rank-two passenger. -/
def lc0IV (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 1 :=
  appCcRS (I := I) (M := M) g₀ 2 3 1
    (lc0Trace (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB))

private lemma vflat_value (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (u : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
          (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => u) =
      g₁.inner x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Π b : M, TangentSpace I b) x) u := by
  have hfib : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0Trace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) from rfl]
    rw [ContinuousLinearMap.comp_apply, kappa_fiber (I := I) (M := M) g₀ g₁ gB x,
      lc0Trace_fiber (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _) x]
    rfl
  rw [hfib, cometricDoubleTraceFib_toModel (I := I) g₁ 1 x]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x))
    (fun _ : Fin 1 => u)]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (fun _ : Fin 1 => u))) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x
        (smoothOrthoFrame (I := I) g₁ x c x)
        (smoothOrthoFrame (I := I) g₁ x c x)) u := by
    intro c
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x]
    rfl
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  rw [PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gB x,
    map_sum, ContinuousLinearMap.sum_apply]

theorem iv_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0IV (I := I) (M := M) g₀ g₁ gB).toSection x) D =
    Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gB :
        Π b : M, TangentSpace I b) x) D := by
  classical
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x with hV
  set Vf : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) with hVf
  have hchain :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0IV (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      lieCorr0TraceStep (I := I) g₁ 1 lieCorr0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D) := by
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0IV (I := I) (M := M) g₀ g₁ gB).toSection x) D =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0Trace (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 1 2
              (lc0VFlat (I := I) (M := M) g₀ g₁ gB)).toSection x) D) from rfl]
    rw [slotLift_21 (I := I) (M := M) g₀
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB) x D, ← hVf]
    exact congrFun (congrArg DFunLike.coe
      (lc0Trace_fiber (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm x))
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D)
  rw [hchain]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  have hLHS : Tensor0SSpace.toModel
      (lieCorr0TraceStep (I := I) g₁ 1 lieCorr0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D)) w =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
          Tensor0SSpace.toModel Vf
            (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) := by
    rw [show lieCorr0TraceStep (I := I) g₁ 1 lieCorr0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D) =
        cometricDoubleTraceFib (I := I) g₁ 1 x
          (domDomCongrFibRank (I := I) 3 lieCorr0IVPerm x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D)) from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 1 x,
      modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (domDomCongrFibRank (I := I) 3 lieCorr0IVPerm x
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf D))) w]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [domDomCongrFibRank_apply (I := I) 3 lieCorr0IVPerm x,
      Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply,
      tensor0SProdKappaFib_apply (I := I) x Vf D,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · congr 1
      funext k
      fin_cases k <;> rfl
    · congr 1
      funext k
      fin_cases k <;> rfl
  rw [hLHS]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
        Tensor0SSpace.toModel Vf
          (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) =
      g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] := by
    intro c
    rw [hVf, vflat_value (I := I) (M := M) g₀ g₁ gB x
      ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E), ← hV]
    rw [g₁.symm x V (smoothOrthoFrame (I := I) g₁ x c x)]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hRHS : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from V) (fun k => (show E from w k))) :=
    interior_model (I := I) (M := M) 1 x V D w
  rw [hRHS]
  have hrepr := orthoFrame_repr (I := I) (M := M) g₁ x V
  have hexp : Tensor0SSpace.toModel D
      (Fin.cons (show E from V) (fun k => (show E from w k))) =
      ∑ c : Fin (Module.finrank ℝ E),
        g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V *
          Tensor0SSpace.toModel D
            (Fin.cons
              ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (fun k => (show E from w k))) := by
    have hsum := toModel_cons_sum (E := E) x (Tensor0SSpace.toModel D)
      (Module.finrank ℝ E)
      (fun c => g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V)
      (fun c => ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E))
      (fun k => (show E from w k))
    rw [← hsum]
    exact congrArg (fun t : TangentSpace I x =>
      Tensor0SSpace.toModel D
        (Fin.cons (show E from t) (fun k => (show E from w k)))) hrepr
  rw [hexp]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  congr 1
  funext k
  fin_cases k <;> rfl

/-! ## Cancellation-compatible insertion normal form -/

/-- Smooth section of the endomorphism appearing in the two insertion slots
of `lieCorr0InsertFib`. -/
def lc0NSec (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ⟨fun x : M => lieCorr0NEndo (I := I) g₀ g₁ gB x,
    lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ gB⟩

/-- Composition of insertion by the DeTurck vector field with the
moving-to-frozen connection difference. -/
def lc0CdV (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 1 :=
  appCcRS (I := I) (M := M) g₀ 1 2 1
    (lc0IV (I := I) (M := M) g₀ g₁ gB)
    (connDiffSection (I := I) g₁ g₀)

private lemma covec_model (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [cotangentToDual_apply]
  rw [show (om (fun _ : Fin 1 => (m 0 : TangentSpace I x)) : ℝ) =
      Tensor0SSpace.toModel om (fun _ : Fin 1 => m 0) from rfl]
  congr 1
  funext k
  rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]

private lemma cdv_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0CdV (I := I) (M := M) g₀ g₁ gB).toSection x) om =
    slotInsertEndoFib (I := I) (M := M) 1 0 x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Π b : M, TangentSpace I b) x)) om := by
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
      Π b : M, TangentSpace I b) x with hV
  have hstep :
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdV (I := I) (M := M) g₀ g₁ gB).toSection x) om =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V
        (connDiffFib (I := I) g₁ g₀ x om) := by
    rw [show
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdV (I := I) (M := M) g₀ g₁ gB).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0IV (I := I) (M := M) g₀ g₁ gB).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x) om) from rfl]
    rw [show
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om from rfl]
    exact iv_fiber (I := I) (M := M) g₀ g₁ gB x
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om)
  rw [hstep]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [interior_model (I := I) (M := M) 1 x V
    (connDiffFib (I := I) g₁ g₀ x om) w]
  rw [slotInsertEndoFib_apply_eval]
  have hLHS : Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
      (Fin.cons (show E from V) (fun k => (show E from w k))) =
      om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) := by
    rw [show Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
        (Fin.cons (show E from V) (fun k => (show E from w k))) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om)
          (Fin.cons V (fun k => w k)) from rfl]
    rw [connDiffFib_apply_eval (I := I) g₁ g₀ x om
      (Fin.cons V (fun k => w k))]
    congr 1
  rw [hLHS]
  rw [covec_model (I := I) (M := M) x om
    (Function.update (fun k => (show E from w k)) 0
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x V
        ((fun k => (show E from w k)) 0)))]
  rw [Function.update_self]
  exact (cotangentToDual_apply (I := I) om _).symm

/-- Two-slot insertion operator built from an arbitrary smooth tangent
endomorphism section. -/
def lc0InsForm (g₀ : SmoothRiemannianMetric I M)
    (N : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    SmoothCcTensor g₀ 2 2 :=
  slotInsertEndoCc (I := I) (M := M) g₀ 1 N +
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N))
      (Equiv.swap (0 : Fin 2) 1)

private lemma insForm_model (g₀ : SmoothRiemannianMetric I M)
    (N : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (D : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0InsForm (I := I) (M := M) g₀ N).toSection x) D) m =
      Tensor0SSpace.toModel D (Function.update m 0 (N x (m 0))) +
        Tensor0SSpace.toModel D (Function.update m 1 (N x (m 1))) := by
  have hsplit :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0InsForm (I := I) (M := M) g₀ N).toSection x) D =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
            (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1 N))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) := rfl
  rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  have hterm1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x) D) m =
      Tensor0SSpace.toModel D (Function.update m 0 (N x (m 0))) := by
    rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (N x) D from rfl]
    rw [slotInsertEndoFib_apply_eval]
  have hterm2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
            (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1 N))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel D (Function.update m 1 (N x (m 1))) := by
    rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
            (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1 N))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
            (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1 N)).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply (I := I) 2 2
      (Equiv.swap (0 : Fin 2) 1) x _ D]
    rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
          (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1 N)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D))) =
      rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
        ((slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D))) from rfl]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M)
      (Equiv.swap (0 : Fin 2) 1)
      ((slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D))) =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (N x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D))) from rfl]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x (N x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
    rw [Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    have harg :
        (fun k => Function.update
          (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          (N x ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
          ((Equiv.swap (0 : Fin 2) 1) k)) =
        Function.update m 1 (N x (m 1)) := by
      funext k
      have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 :=
        Equiv.swap_apply_left 0 1
      have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 :=
        Equiv.swap_apply_right 0 1
      simp only [Function.update_apply]
      rw [hswap0, Equiv.swap_apply_self]
      have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
        apply propext
        constructor
        · intro h
          have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
          rwa [Equiv.swap_apply_self, hswap0] at h2
        · intro h
          rw [h, hswap1]
      simp only [hcond]
    rw [harg]
  rw [hterm1, hterm2]

/-- The difference of the insertion endomorphisms is exactly the difference
of the two connection-after-vector-field compositions. -/
theorem nins_diff (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0
        (lc0NSec (I := I) (M := M) g₀ g₁ gB -
          lc0NSec (I := I) (M := M) g₀ g₁ g₀) =
      lc0CdV (I := I) (M := M) g₀ g₁ g₀ -
        lc0CdV (I := I) (M := M) g₀ g₁ gB := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  rw [SmoothCcTensor.toSection_sub, ContinuousLinearMap.sub_apply,
    cdv_fiber (I := I) (M := M) g₀ g₁ g₀ x om,
    cdv_fiber (I := I) (M := M) g₀ g₁ gB x om]
  simp only [slotInsertEndoCc_toSection]
  rw [show
    ((lc0NSec (I := I) (M := M) g₀ g₁ gB -
      lc0NSec (I := I) (M := M) g₀ g₁ g₀) x) =
      lieCorr0NEndo (I := I) g₀ g₁ gB x -
        lieCorr0NEndo (I := I) g₀ g₁ g₀ x from by
      rw [ContMDiffSection.coe_sub]; rfl]
  rw [nEndo_diff (I := I) (M := M) g₀ g₁ gB x,
    slotInsertEndoFib_sub_left, ContinuousLinearMap.sub_apply]

/-- Exact smooth-field normal form of the insertion background difference.
The leading base-background endomorphism has already cancelled inside the
single section difference on the right. -/
theorem insert_diff (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ gB -
        lc0Insert (I := I) (M := M) g₀ g₁ g₀ =
      lc0InsForm (I := I) (M := M) g₀
        (lc0NSec (I := I) (M := M) g₀ g₁ gB -
          lc0NSec (I := I) (M := M) g₀ g₁ g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [show
    ((lc0Insert (I := I) (M := M) g₀ g₁ gB -
      lc0Insert (I := I) (M := M) g₀ g₁ g₀).toSection x) =
      (lc0Insert (I := I) (M := M) g₀ g₁ gB).toSection x -
        (lc0Insert (I := I) (M := M) g₀ g₁ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  change Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ gB x D) m -
      Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ g₀ x D) m = _
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ gB x D m,
    lieCorr0InsertFib_toModel (I := I) g₀ g₁ g₀ x D m,
    insForm_model (I := I) (M := M) g₀
      (lc0NSec (I := I) (M := M) g₀ g₁ gB -
        lc0NSec (I := I) (M := M) g₀ g₁ g₀) x D m]
  rw [show
    ((lc0NSec (I := I) (M := M) g₀ g₁ gB -
      lc0NSec (I := I) (M := M) g₀ g₁ g₀) x) =
      lieCorr0NEndo (I := I) g₀ g₁ gB x -
        lieCorr0NEndo (I := I) g₀ g₁ g₀ x from by
      rw [ContMDiffSection.coe_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.map_update_sub,
    ContinuousMultilinearMap.map_update_sub]
  ring

/-- The lowered-connection background difference contains no self-background
top arm: it is a fixed coefficient minus the perturbative lower pairing. -/
theorem kappa_diff (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
        lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ gB -
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  rw [kappa_bg (I := I) (M := M) g₀ g₁ gB P htie]
  abel

/-- Iterated slot extension is linear in its passenger. -/
theorem slotIter_sub (g₀ : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g₀ r s) :
    slotExtendIter (I := I) (M := M) g₀ r s w (A - B) =
      slotExtendIter (I := I) (M := M) g₀ r s w A -
        slotExtendIter (I := I) (M := M) g₀ r s w B := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g₀ (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g₀ r s w (A - B)) = _
      rw [ih, slotExtend_sub]
      rfl

/-- The DeTurck-vector covector background difference is one common moving
trace applied to the lowered-connection background difference. -/
theorem vflat_diff (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0VFlat (I := I) (M := M) g₀ g₁ g₀ -
        lc0VFlat (I := I) (M := M) g₀ g₁ gB =
      appCcRS (I := I) (M := M) g₀ 0 3 1
        (lc0Trace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
          lc0Kappa (I := I) (M := M) g₀ g₁ gB) := by
  rw [appCcRS_sub_right]
  rfl

/-- The vector-insertion operator background difference is one common trace
applied to the slot extension of `vflat_diff`. -/
theorem iv_diff (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0IV (I := I) (M := M) g₀ g₁ g₀ -
        lc0IV (I := I) (M := M) g₀ g₁ gB =
      appCcRS (I := I) (M := M) g₀ 2 3 1
        (lc0Trace (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lc0VFlat (I := I) (M := M) g₀ g₁ g₀ -
            lc0VFlat (I := I) (M := M) g₀ g₁ gB)) := by
  rw [slotIter_sub, appCcRS_sub_right]
  rfl

/-- The connection-after-vector-field background difference is the common
connection-difference passenger acted on by `iv_diff`. -/
theorem cdv_diff (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0CdV (I := I) (M := M) g₀ g₁ g₀ -
        lc0CdV (I := I) (M := M) g₀ g₁ gB =
      appCcRS (I := I) (M := M) g₀ 1 2 1
        (lc0IV (I := I) (M := M) g₀ g₁ g₀ -
          lc0IV (I := I) (M := M) g₀ g₁ gB)
        (connDiffSection (I := I) g₁ g₀) := by
  rw [appCcRS_sub_left]
  rfl

/-- Nested operator-product normal form of the vector--bilinear correction. -/
def lc0VBForm (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2
    (lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
    (appCcRS (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IV (I := I) (M := M) g₀ g₁ g₀))

private lemma vbForm_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0VBForm (I := I) (M := M) g₀ g₁).toSection x) D =
    lieCorr0VBFib (I := I) g₀ g₁ x D := by
  have h₁ :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0VBForm (I := I) (M := M) g₀ g₁).toSection x) D =
      (2 : ℝ) •
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 1
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x)
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
              (lc0IV (I := I) (M := M) g₀ g₁ g₀).toSection x) D)) := rfl
  rw [h₁, iv_fiber (I := I) (M := M) g₀ g₁ g₀ x D]
  rw [slotLift_13 (I := I) (M := M) g₀
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) x _]
  rw [kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  have h₂ := lc0Trace_fiber (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm x
  rw [show
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
        (tensor0SProdKappaFib (I := I) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
              Π b : M, TangentSpace I b) x) D)) =
      lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        (tensor0SProdKappaFib (I := I) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
              Π b : M, TangentSpace I b) x) D)) from
    congrFun (congrArg DFunLike.coe h₂) _]
  rw [show lieCorr0VBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
              Π b : M, TangentSpace I b) x) D)) from by
    rw [lieCorr0VBFib, ContinuousLinearMap.smul_apply]
    rfl]

/-- Exact operator-product refold of the vector--bilinear correction. -/
theorem vb_refold (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0VB (I := I) (M := M) g₀ g₁ = lc0VBForm (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorr0VBFib (I := I) g₀ g₁ x D = _
  exact (vbForm_fiber (I := I) (M := M) g₀ g₁ x D).symm

/-- One unsymmetrized half of the nested mixed connection correction. -/
def lc0AMixHalf (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  appCcRS (I := I) (M := M) g₀ 2 4 2
    (lc0Trace (I := I) (M := M) g₀ g₁ 2 σlast)
    (appCcRS (I := I) (M := M) g₀ 2 6 4
      (lc0Trace (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (appCcRS (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB))
        (appCcRS (I := I) (M := M) g₀ 2 5 3
          (lc0Trace (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))

/-- Swap the two output slots after the last mixed trace. -/
def lc0SwapPerm : Equiv.Perm (Fin 4) :=
  ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

private lemma swap_trace (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) (Z : Tensor0SSpace 4 I x) :
    domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
      (lieCorr0TraceStep (I := I) g₁ 2 σ x Z) =
    lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapPerm * σ) x Z := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [domDomCongrFibRank_apply (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 σ x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 σ x Z) from rfl]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapPerm * σ) x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 (lc0SwapPerm * σ) x Z) from rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x,
    cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x),
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [domDomCongrFibRank_apply (I := I) 4 σ x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [domDomCongrFibRank_apply (I := I) 4 (lc0SwapPerm * σ) x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  have hpt : ∀ t : Fin 4,
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k)
          (fun j : Fin 2 => w ((Equiv.swap (0 : Fin 2) 1) j))) : Fin 4 → E) t =
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 4 → E) (lc0SwapPerm t) := by
    intro t
    fin_cases t <;> rfl
  rw [hpt (σ i)]
  rfl

/-- Symmetrized operator-product normal form of the mixed connection
correction. -/
def lc0AMixForm (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) •
    (lc0AMixHalf (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 +
      lc0AMixHalf (I := I) (M := M) g₀ g₁ gB
        (lc0SwapPerm * lieCorr0AMixPerm2))

private lemma amixHalf_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixHalf (I := I) (M := M) g₀ g₁ gB σlast).toSection x) D =
    lieCorr0TraceStep (I := I) g₁ 2 σlast x
      (lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D)))) := by
  have h₁ :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixHalf (I := I) (M := M) g₀ g₁ gB σlast).toSection x) D =
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Trace (I := I) (M := M) g₀ g₁ 2 σlast).toSection x)
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lc0Trace (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x)
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (lc0Kappa (I := I) (M := M) g₀ g₁ gB)).toSection x)
            ((show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
              (lc0Trace (I := I) (M := M) g₀ g₁ 3
                lieCorr0AMixPermQ).toSection x)
              ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
                (slotExtendIter (I := I) (M := M) g₀ 0 3 2
                  (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x) D))) := rfl
  rw [h₁]
  rw [slotLift_23 (I := I) (M := M) g₀
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) x D]
  rw [kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  rw [show
      (show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
        (lc0Trace (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ).toSection x)
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) =
      lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) from
    congrFun (congrArg DFunLike.coe
      (lc0Trace_fiber (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ x)) _]
  rw [slotLift_33 (I := I) (M := M) g₀
    (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x _]
  rw [kappa_fiber (I := I) (M := M) g₀ g₁ gB x]
  rw [show
      (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lc0Trace (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x)
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))) =
      lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))) from
    congrFun (congrArg DFunLike.coe
      (lc0Trace_fiber (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1 x)) _]
  exact congrFun (congrArg DFunLike.coe
    (lc0Trace_fiber (I := I) (M := M) g₀ g₁ 2 σlast x)) _

private lemma amixForm_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixForm (I := I) (M := M) g₀ g₁ gB).toSection x) D =
    lieCorr0AMixFib (I := I) g₀ g₁ gB x D := by
  have h₁ :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixForm (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      (2 : ℝ) •
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalf (I := I) (M := M) g₀ g₁ gB
            lieCorr0AMixPerm2).toSection x) D +
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalf (I := I) (M := M) g₀ g₁ gB
            (lc0SwapPerm * lieCorr0AMixPerm2)).toSection x) D) := rfl
  rw [h₁]
  rw [amixHalf_fiber (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 x D]
  rw [amixHalf_fiber (I := I) (M := M) g₀ g₁ gB
    (lc0SwapPerm * lieCorr0AMixPerm2) x D]
  rw [← swap_trace (I := I) (M := M) g₁ lieCorr0AMixPerm2 x _]
  rw [show lieCorr0AMixFib (I := I) g₀ g₁ gB x D =
      (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ gB x D +
        domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ gB x D)) from by
    rw [lieCorr0AMixFib, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]]
  rfl

/-- Exact operator-product refold of the mixed connection correction. -/
theorem amix_refold (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0AMix (I := I) (M := M) g₀ g₁ gB =
      lc0AMixForm (I := I) (M := M) g₀ g₁ gB := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorr0AMixFib (I := I) g₀ g₁ gB x D = _
  exact (amixForm_fiber (I := I) (M := M) g₀ g₁ gB x D).symm

private theorem riemRest_smooth (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝒘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM
          ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x))))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => (lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x)))
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x
      (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x)) hprod
  refine htr.congr (fun _ => rfl)

/-- The fixed-curvature passenger on which the moving final trace acts. -/
def lc0RiemRest (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from TensorRSSpace.ofCLM
          ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x))))
      contMDiff_toFun := riemRest_smooth (I := I) (M := M) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Exact operator-product refold of the fixed-curvature correction. -/
theorem riem_refold (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Riem (I := I) (M := M) g₀ g₁ =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2
        (lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
        (lc0RiemRest (I := I) (M := M) g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x) D = _
  rw [lc0Trace_fiber (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2 x]
  rfl

/-- Pointwise product-grid control of a moving rank-`(p + 2, p)` trace.

The fixed trace contributes bounded background jets, while every moving
factor is an inverse-metric-difference jet.  Keeping the passenger rank
explicit is essential for the nested rank-three and rank-four traces in the
low-regularity `AMix` normal form. -/
theorem trace_grid
    (p : ℕ) (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (lc0Trace (I := I) (M := M) g₀ g₁ p σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) k := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  let Φ : SmoothCcTensor g₀ (p + 2) p := cometricDoubleTraceField (I := I) g₀ p
  have hS_ex : ∀ m : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
        ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) ≤ S :=
    fun m => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ (p + 2) (p + m)
      (iteratedCovGrad (I := I) g₀ (p + 2) p m Φ)
  choose S hS_nn hS using hS_ex
  let fr : ℝ := Module.finrank ℝ E
  let CQ : ℕ → ℝ := fun i => appCcGdiag (E := E) i *
    ∑ m ∈ Finset.range (i + 1),
      S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l
  let C : ℕ → ℝ := fun i => 2 * CQ i + 2 * S i
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCQ : ∀ i, 0 ≤ CQ i := by
    intro i
    exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun m _ => mul_nonneg (hS_nn m)
        (Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hfr (p + 1)) (hCD_nn l)))
  refine ⟨C, fun i => by dsimp [C]; positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound σ i x
  let b : ℕ → ℝ := fun j =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
  let G : ℝ := ∑ k ∈ Finset.range (i + 1),
    Combinatorics.antidiagonalTupleGrid b k
  have hb : ∀ j, 0 ≤ b j := fun j =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hG_nn : 0 ≤ G := Finset.sum_nonneg fun k _ =>
    Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hG_one : (1 : ℝ) ≤ G := by
    calc
      (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
        (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ G := Finset.single_le_sum
        (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
        (Finset.mem_range.mpr (by omega))
  let W : SmoothCcTensor g₀ (p + 2) (p + 2) :=
    slotInsertEndoCc (I := I) (M := M) g₀ (p + 1)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁)
  have hW : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) ≤
        fr ^ (p + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
    intro l
    refine le_trans
      (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g₀ (p + 1)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hfr (p + 1))
    simpa only [b, Combinatorics.antidiagonalTupleGrid] using
      hCD g₁ P htie hδ_le hδ_nonneg hbound l x
  have hgrid_le : ∀ l, l < i + 1 →
      Combinatorics.antidiagonalTupleGrid b l ≤ G := by
    intro l hl
    exact Finset.single_le_sum
      (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
      (Finset.mem_range.mpr hl)
  have hcell : ∀ m ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) ≤
      (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G := by
    intro m hm
    have hmle : m ≤ i := by
      have := Finset.mem_range.mp hm
      omega
    have hsumW : (∑ l ∈ Finset.range (i + 1 - m),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - m),
          (fr ^ (p + 1) * CD l) * G := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hli : l < i + 1 := by
        have := Finset.mem_range.mp hl
        omega
      calc
        _ ≤ fr ^ (p + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := hW l
        _ ≤ fr ^ (p + 1) * (CD l * G) := by
          gcongr
          exact hgrid_le l hli
        _ = (fr ^ (p + 1) * CD l) * G := by ring
    have hsumW_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - m),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x _
    calc
      _ ≤ S m * ∑ l ∈ Finset.range (i + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) :=
        mul_le_mul_of_nonneg_right (hS m x) hsumW_nn
      _ ≤ S m * ∑ l ∈ Finset.range (i + 1 - m),
          (fr ^ (p + 1) * CD l) * G :=
        mul_le_mul_of_nonneg_left hsumW (hS_nn m)
      _ = (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G := by
        rw [Finset.sum_mul]
        ring
  have hQ :
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p i
            (appCcRS (I := I) (M := M) g₀ (p + 2) (p + 2) p Φ W)).toSection x) ≤
        CQ i * G := by
    refine le_trans
      (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i (p + 2) (p + 2) p Φ W x) ?_
    calc
      appCcGdiag (E := E) i * ∑ m ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
              ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - m),
              riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x)
          ≤ appCcGdiag (E := E) i * ∑ m ∈ Finset.range (i + 1),
              (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
          (appCcGdiag_nonneg (E := E) i)
      _ = CQ i * G := by
        rw [Finset.sum_mul]
        rfl
  have hfixed :
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p i Φ).toSection x) ≤
        S i * G := by
    exact (hS i x).trans (by nlinarith [hS_nn i, hG_one])
  rw [lc0Trace, rfns_iteratedCovGrad_reindexCoeffGen_eq
    (I := I) (M := M) g₀ (p + 2) p
      (pureTrace (I := I) (M := M) g₀ g₁ p) σ i x]
  rw [pureTrace_split (I := I) (M := M) g₀ g₁ p,
    iteratedCovGrad_add, SmoothCcTensor.toSection_add]
  refine le_trans
    (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (p + 2) (p + i) x _ _) ?_
  change 2 * _ + 2 * _ ≤ C i * G
  have hQ' := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 2)
  have hfixed' := mul_le_mul_of_nonneg_left hfixed (by norm_num : (0 : ℝ) ≤ 2)
  change _ ≤ (2 * CQ i + 2 * S i) * G
  linarith

/-- Rank-two specialization of `trace_grid`. -/
theorem trace2_grid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (lc0Trace (I := I) (M := M) g₀ g₁ 2 σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) k := by
  simpa only [Nat.reduceAdd] using trace_grid (I := I) (M := M) 2 g₀ hδ₀

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
