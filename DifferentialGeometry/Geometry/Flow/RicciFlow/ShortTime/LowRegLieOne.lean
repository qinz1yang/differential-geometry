import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound

/-!
# Low-regularity order-one DeTurck Lie coefficient

This file proves the dimension-three `H2` jet estimate for the concrete
order-one DeTurck Lie coefficient.  The proof first performs the exact
connection-difference cancellations in the lowered `kappa` arm.  Consequently
the third metric derivative occurs only once, while all inverse-metric and
other multiplicative factors are controlled by the lower `H2` radius.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev jet
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W : SmoothCcTensor g r s) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖iteratedCovGrad (I := I) g r s i W‖ ^ 2

private theorem low_grid_nonneg
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (k : ℕ) (x : M) :
    0 ≤ lowJetGrid (I := I) (M := M) g P k x := by
  unfold lowJetGrid
  exact Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun e _ =>
    Finset.prod_nonneg fun m _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g
        0 (2 + e m) x _

private theorem jet_add
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : jet (I := I) (M := M) g r s n A ≤ a ^ 2)
    (hB : jet (I := I) (M := M) g r s n B ≤ b ^ 2) :
    jet (I := I) (M := M) g r s n (A + B) ≤
      (2 * (a + b)) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s i (A + B)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s i B‖ ^ 2) := by
    intro i hi
    rw [iteratedCovGrad_add]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s i A)
      (iteratedCovGrad (I := I) g r s i B)
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g r s i A),
      norm_nonneg (iteratedCovGrad (I := I) g r s i B),
      norm_nonneg (iteratedCovGrad (I := I) g r s i A +
        iteratedCovGrad (I := I) g r s i B),
      sq_nonneg (‖iteratedCovGrad (I := I) g r s i A‖ -
        ‖iteratedCovGrad (I := I) g r s i B‖)]
  have hsum := Finset.sum_le_sum hterm
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  calc
    _ ≤ 2 * (jet (I := I) (M := M) g r s n A +
          jet (I := I) (M := M) g r s n B) := hsum
    _ ≤ 2 * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ ≤ (2 * (a + b)) ^ 2 := by
      nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha hb]

private theorem jet_sub
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : jet (I := I) (M := M) g r s n A ≤ a ^ 2)
    (hB : jet (I := I) (M := M) g r s n B ≤ b ^ 2) :
    jet (I := I) (M := M) g r s n (A - B) ≤
      (2 * (a + b)) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s i (A - B)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s i B‖ ^ 2) := by
    intro i hi
    rw [iteratedCovGrad_sub]
    have htri := norm_sub_le
      (iteratedCovGrad (I := I) g r s i A)
      (iteratedCovGrad (I := I) g r s i B)
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g r s i A),
      norm_nonneg (iteratedCovGrad (I := I) g r s i B),
      norm_nonneg (iteratedCovGrad (I := I) g r s i A -
        iteratedCovGrad (I := I) g r s i B),
      sq_nonneg (‖iteratedCovGrad (I := I) g r s i A‖ -
        ‖iteratedCovGrad (I := I) g r s i B‖)]
  have hsum := Finset.sum_le_sum hterm
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  calc
    _ ≤ 2 * (jet (I := I) (M := M) g r s n A +
          jet (I := I) (M := M) g r s n B) := hsum
    _ ≤ 2 * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ ≤ (2 * (a + b)) ^ 2 := by
      nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha hb]

private theorem jet_add_mul
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (L a b : ℝ)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : jet (I := I) (M := M) g r s n A ≤ (a * L) ^ 2)
    (hB : jet (I := I) (M := M) g r s n B ≤ (b * L) ^ 2) :
    jet (I := I) (M := M) g r s n (A + B) ≤
      ((2 * (a + b)) * L) ^ 2 := by
  have h := jet_add (I := I) (M := M) g r s n A B
    (a * L) (b * L) (mul_nonneg ha hL) (mul_nonneg hb hL) hA hB
  convert h using 1 <;> ring

private theorem jet_sub_mul
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (L a b : ℝ)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : jet (I := I) (M := M) g r s n A ≤ (a * L) ^ 2)
    (hB : jet (I := I) (M := M) g r s n B ≤ (b * L) ^ 2) :
    jet (I := I) (M := M) g r s n (A - B) ≤
      ((2 * (a + b)) * L) ^ 2 := by
  have h := jet_sub (I := I) (M := M) g r s n A B
    (a * L) (b * L) (mul_nonneg ha hL) (mul_nonneg hb hL) hA hB
  convert h using 1 <;> ring

private theorem norm_eq_of_sq_eq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have hs := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at hs

private theorem conn_norm_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (connDiffSection (I := I) g₁ g₀)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (connDiffLoweredCc (I := I) g₀ g₁)‖ := by
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 1 (2 + i),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 (3 + i)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      (connLow_rfns (I := I) (M := M) g₀ g₁ i x).symm)

private theorem unit_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - T) x =
      unitModel (I := I) (M := M) g s S x -
        unitModel (I := I) (M := M) g s T x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - T).toSection x = S.toSection x - T.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (S - T).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        S.toSection x) (unitTensor (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        T.toSection x) (unitTensor (I := I) (M := M) x) from by
        rw [hsec]
        rfl]
  rw [Tensor0SSpace.toModel_sub]

private theorem unit_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + T) x =
      unitModel (I := I) (M := M) g s S x +
        unitModel (I := I) (M := M) g s T x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + T).toSection x = S.toSection x + T.toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (S + T).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        S.toSection x) (unitTensor (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        T.toSection x) (unitTensor (I := I) (M := M) x) from by
        rw [hsec]
        rfl]
  rw [Tensor0SSpace.toModel_add]

private theorem conn_self_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g g x u v = 0 := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) g g g x u v
  have h' : PDE.DeTurck.connDiff (I := I) g g x u v +
      PDE.DeTurck.connDiff (I := I) g g x u v =
      PDE.DeTurck.connDiff (I := I) g g x u v + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

private theorem conn_antisymm
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      -PDE.DeTurck.connDiff (I := I) gB gA x u v := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gB gA gA x u v
  rw [conn_self_zero (I := I) (M := M) gA x u v] at h
  exact eq_neg_of_add_eq_zero_left h.symm

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffLoweredField) in
private theorem lie_kappa_unit
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) gB g₁ x
        (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  show Tensor0SSpace.toModel
      (((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB).toSection x)
        (unitTensor (I := I) (M := M) x)) m = _
  rw [show ((lieArm1LoweredBgKappa
      (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

private theorem lie_kappa_eq
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB =
      -(lc0Kappa (I := I) (M := M) g₀ g₁ gB) := by
  rw [show -(lc0Kappa (I := I) (M := M) g₀ g₁ gB) =
      lc0Kappa (I := I) (M := M) g₀ g₁ gB -
        (lc0Kappa (I := I) (M := M) g₀ g₁ gB +
          lc0Kappa (I := I) (M := M) g₀ g₁ gB) from by abel]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unit_sub (I := I) (M := M) g₀ 3, unit_add (I := I) (M := M) g₀ 3]
  rw [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply]
  rw [lie_kappa_unit (I := I) (M := M) g₀ g₁ gB x m,
    kappa_unit (I := I) (M := M) g₀ g₁ gB x m]
  rw [conn_antisymm (I := I) (M := M) gB g₁ x (m 0) (m 1),
    map_neg, ContinuousLinearMap.neg_apply]
  ring

private theorem raise_dom_normSq
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 3))
    (W : SmoothCcTensor g 0 3) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 2 i
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g σ W))‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 3 i W‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g 1
    (domDomCongrSection (I := I) g σ W) i x]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g σ W i x

private theorem toModel_single
    (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) =
      (fun _ : Fin 1 => (m 0 : E)) from by
        funext k
        fin_cases k
        rfl]
  rw [cotangentToDual_apply]
  rfl

private theorem inner_inv_endo
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w =
      g₀.inner x v w := by
  rw [gInvRaisedEndo_apply,
    inverseMetricSharpFib_inner (I := I) g₁ x
      (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x)
      (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x)
        (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

private theorem inner_inv_mixed
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om
        (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om
      (gInvRaisedEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om
        (gInvRaisedEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om
    (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [inner_inv_endo (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
private theorem sharp_eq_insert
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x)
        (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_single (I := I) (M := M) x om
    (Function.update m 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x)
      (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [inner_inv_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

private theorem fullRaised_split
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
      fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
          rw [ContMDiffSection.coe_add]
          rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show gInvDiffRaisedEndoField (I := I) g₀ g₁ x =
      gInvDiffRaisedEndo (I := I) g₀ g₁ x from rfl]
  rw [fullRaisedEndoField_apply,
    gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
private theorem insert_add
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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
          rw [SmoothCcTensor.toSection_add]
          rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

private theorem sharp_split
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
  rw [sharp_eq_insert (I := I) (M := M) g₀ g₁,
    fullRaised_split (I := I) (M := M) g₀ g₁,
    insert_add (I := I) (M := M) g₀ 0]

private theorem sharp_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R : ℝ), 0 ≤ R →
        jet (I := I) (M := M) g₀ 0 2 3 P ≤ R ^ 2 →
        jet (I := I) (M := M) g₀ 1 1 3
          (sharpFlatEndoCc (I := I) g₀ g₁) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hgrid⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨BD, hBD, hdiff⟩ :=
    h2_of_grid_low (I := I) (M := M) (r := 1) (s := 1)
      hDim g₀ C hC
  let Fix : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)
  let QF : ℝ := jet (I := I) (M := M) g₀ 1 1 3 Fix
  have hQF : 0 ≤ QF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let AF : ℝ := Real.sqrt QF
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hFix : jet (I := I) (M := M) g₀ 1 1 3 Fix ≤ AF ^ 2 := by
    change QF ≤ AF ^ 2
    rw [show AF ^ 2 = QF by simp only [AF, Real.sq_sqrt hQF]]
  let B : ℝ → ℝ := fun R => 2 * (BD R + AF)
  refine ⟨B, fun R hR =>
    mul_nonneg (by norm_num) (add_nonneg (hBD R hR) hAF), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  let Diff : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (gInvDiffRaisedEndoField (I := I) g₀ g₁)
  have hDiff : jet (I := I) (M := M) g₀ 1 1 3 Diff ≤
      (BD R) ^ 2 := by
    refine hdiff P Diff R hR hP ?_
    intro i hi x
    have hraw := hgrid g₁ P htie hδ_le hδ_nonneg hbound i x
    have himem : i ∈ Finset.range (i + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_self i)
    have hsingle : lowJetGrid (I := I) (M := M) g₀ P i x ≤
        ∑ k ∈ Finset.range (i + 1),
          lowJetGrid (I := I) (M := M) g₀ P k x :=
      Finset.single_le_sum
        (f := fun k => lowJetGrid (I := I) (M := M) g₀ P k x)
        (fun k _ => low_grid_nonneg (I := I) (M := M) g₀ P k x) himem
    exact hraw.trans (mul_le_mul_of_nonneg_left hsingle (hC i))
  rw [sharp_split (I := I) (M := M) g₀ g₁]
  simpa only [B, Diff, Fix] using
    jet_add (I := I) (M := M) g₀ 1 1 3 Diff Fix
      (BD R) AF (hBD R hR) hAF hDiff hFix

private theorem psi_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        jet (I := I) (M := M) g₀ 0 2 3 P ≤ R ^ 2 →
        jet (I := I) (M := M) g₀ 0 2 4 P ≤ A ^ 2 →
        jet (I := I) (M := M) g₀ 1 2 3
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨BP, hBP, hpb⟩ :=
    pbLow_h2 (I := I) (M := M) hDim g₀ gB
  obtain ⟨BS, hBS, hsharp⟩ :=
    sharp_h2 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨C, hC, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 1 1 2
  let Fix : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ gB
  let QF : ℝ := jet (I := I) (M := M) g₀ 0 3 3 Fix
  have hQF : 0 ≤ QF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let AF : ℝ := Real.sqrt QF
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hFix : jet (I := I) (M := M) g₀ 0 3 3 Fix ≤ AF ^ 2 := by
    change QF ≤ AF ^ 2
    rw [show AF ^ 2 = QF by simp only [AF, Real.sq_sqrt hQF]]
  let K0 : ℝ → ℝ := fun R => 4 * AF + 2 * BP R
  let K1 : ℝ → ℝ := fun _ => 16
  have hK0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K0 R := by
    intro R hR
    exact add_nonneg (mul_nonneg (by norm_num) hAF)
      (mul_nonneg (by norm_num) (hBP R hR))
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := by
    intro R hR
    norm_num [K1]
  let B0 : ℝ → ℝ := fun R => C * K0 R * BS R
  let B1 : ℝ → ℝ := fun R => C * K1 R * BS R
  refine ⟨B0, B1, fun R hR =>
    mul_nonneg (mul_nonneg hC (hK0 R hR)) (hBS R hR),
    fun R hR => mul_nonneg (mul_nonneg hC (hK1 R hR)) (hBS R hR), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  let Self : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let Pb : SmoothCcTensor g₀ 0 3 :=
    lc0PbLow (I := I) (M := M) g₀ P g₀ gB
  have hSelf : jet (I := I) (M := M) g₀ 0 3 3 Self ≤
      (4 * A) ^ 2 := by
    simpa only [Self] using
      kappaSelf_h2 (I := I) (M := M) g₀ g₁ P htie A hA hP3
  have hPb : jet (I := I) (M := M) g₀ 0 3 3 Pb ≤
      (BP R) ^ 2 := by
    simpa only [Pb] using hpb P R hR hP2
  have hSub := jet_sub (I := I) (M := M) g₀ 0 3 3 Self Fix
    (4 * A) AF (mul_nonneg (by norm_num) hA) hAF hSelf hFix
  have hKapRaw := jet_add (I := I) (M := M) g₀ 0 3 3
    (Self - Fix) Pb (2 * (4 * A + AF)) (BP R)
    (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) hA) hAF))
    (hBP R hR) hSub hPb
  have hKap : jet (I := I) (M := M) g₀ 0 3 3
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB) ≤
      (K0 R + K1 R * A) ^ 2 := by
    rw [kappa_bg (I := I) (M := M) g₀ g₁ gB P htie]
    convert hKapRaw using 1 <;>
      simp only [Self, Fix, Pb, K0, K1] <;> ring
  let Raised : SmoothCcTensor g₀ 1 2 :=
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB))
  have hRaised : jet (I := I) (M := M) g₀ 1 2 3 Raised ≤
      (K0 R + K1 R * A) ^ 2 := by
    calc
      _ = jet (I := I) (M := M) g₀ 0 3 3
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [Raised] using
          raise_dom_normSq (I := I) (M := M) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ gB) i
      _ = jet (I := I) (M := M) g₀ 0 3 3
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [lie_kappa_eq (I := I) (M := M) g₀ g₁ gB,
          iteratedCovGrad_neg, norm_neg]
      _ ≤ (K0 R + K1 R * A) ^ 2 := hKap
  have hSharp := hsharp g₁ P htie hδ_le hδ_nonneg hbound R hR hP2
  have hOut := happ Raised (sharpFlatEndoCc (I := I) g₀ g₁)
    (K0 R + K1 R * A) (BS R)
    (add_nonneg (hK0 R hR) (mul_nonneg (hK1 R hR) hA))
    (hBS R hR) hRaised hSharp
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ gB =
      appCcRS (I := I) (M := M) g₀ 1 1 2 Raised
        (sharpFlatEndoCc (I := I) g₀ g₁) := by
    rfl
  rw [hdef]
  have hfactor : C * (K0 R + K1 R * A) * BS R =
      B0 R + B1 R * A := by
    simp only [B0, B1]
    ring
  rw [← hfactor]
  exact hOut

private theorem traceHessian_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ =
      lc0Trace (I := I) (M := M) g₀ g₁ 2 traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [traceHessianCoeff_toSection, lc0Trace,
    reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, pureTrace_toSection,
    traceHessianFib, ContinuousLinearMap.comp_apply,
    domDomCongrFib_apply]

private theorem piece_h2_const
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
        (Ψ : SmoothCcTensor g₀ 1 2) (T Q : ℝ),
        0 ≤ T → 0 ≤ Q →
        jet (I := I) (M := M) g₀ 4 2 3
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ) ≤ T ^ 2 →
        jet (I := I) (M := M) g₀ 1 2 3 Ψ ≤ Q ^ 2 →
        jet (I := I) (M := M) g₀ 3 2 3
          (lieArm1Piece (I := I) (M := M) g₀ g₁ σ ρ Ψ) ≤
            (C * T *
              (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) * Q)) ^ 2 := by
  classical
  obtain ⟨C, hC, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 3 4 2
  refine ⟨C, hC, ?_⟩
  intro g₁ σ ρ Ψ T Q hT hQ hTrace hΨ
  let S : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSlot : jet (I := I) (M := M) g₀ 3 4 3
      (slotExtend (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)) ≤
      (S * Q) ^ 2 := by
    simpa only [S, slotExtendIter, Nat.reduceAdd] using
      slotIter_h2b (I := I) (M := M) g₀ 1 2 2 Ψ Q hΨ
  have hApp := happ
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ)
    (slotExtend (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))
    T (S * Q) hT (mul_nonneg hS hQ) hTrace hSlot
  calc
    _ = jet (I := I) (M := M) g₀ 3 2 3
        (appCcRS (I := I) (M := M) g₀ 3 4 2
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ)
          (slotExtend (I := I) (M := M) g₀ 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lieArm1Piece, iteratedCovGrad_reindexCoeffGen,
        norm_reindexCoeffGen_eq]
    _ ≤ (C * T * (S * Q)) ^ 2 := hApp
    _ = (C * T *
        (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) * Q)) ^ 2 := by
      rfl

/-- On a closed three-manifold, the concrete order-one DeTurck Lie
coefficient has a tame intrinsic `H2` bound.  Its lower coefficients depend
only on the perturbation `H2` radius, and the third metric derivative enters
affinely after the exact self-background connection cancellation. -/
theorem lie1_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Bc0, Bc1, hBc0, hBc1, hconn⟩ :=
    connLow_tame (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Bp0, Bp1, hBp0, hBp1, hpsi⟩ :=
    psi_h2_tame (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨C, hC, hpiece⟩ :=
    piece_h2_const (I := I) (M := M) hDim g₀
  let S : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  let FixCd : SmoothCcTensor g₀ 1 2 :=
    lieArm1FixCd (I := I) (M := M) g₀ gB
  let QF : ℝ := jet (I := I) (M := M) g₀ 1 2 3 FixCd
  have hQF : 0 ≤ QF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let AF : ℝ := Real.sqrt QF
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hFix : jet (I := I) (M := M) g₀ 1 2 3 FixCd ≤ AF ^ 2 := by
    change QF ≤ AF ^ 2
    rw [show AF ^ 2 = QF by simp only [AF, Real.sq_sqrt hQF]]
  let D0 : ℝ → ℝ := fun R => 2 * (Bc0 R + AF)
  let D1 : ℝ → ℝ := fun R => 2 * Bc1 R
  have hD0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D0 R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg (hBc0 R hR) hAF)
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := by
    intro R hR
    exact mul_nonneg (by norm_num) (hBc1 R hR)
  let C0 : ℝ → ℝ := fun R => C * Bt R * (S * Bc0 R)
  let C1 : ℝ → ℝ := fun R => C * Bt R * (S * Bc1 R)
  let P0 : ℝ → ℝ := fun R => C * Bt R * (S * Bp0 R)
  let P1 : ℝ → ℝ := fun R => C * Bt R * (S * Bp1 R)
  let G0 : ℝ → ℝ := fun R => C * Bt R * (S * D0 R)
  let G1 : ℝ → ℝ := fun R => C * Bt R * (S * D1 R)
  have hC0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ C0 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hBc0 R hR))
  have hC1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ C1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hBc1 R hR))
  have hP0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ P0 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hBp0 R hR))
  have hP1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ P1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hBp1 R hR))
  have hG0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ G0 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hD0 R hR))
  have hG1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ G1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC (hBt R hR))
      (mul_nonneg hS (hD1 R hR))
  let B0 : ℝ → ℝ := fun R => 8 * G0 R + 746 * C0 R + 384 * P0 R
  let B1 : ℝ → ℝ := fun R => 8 * G1 R + 746 * C1 R + 384 * P1 R
  refine ⟨B0, B1, fun R hR => by
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (hG0 R hR))
        (mul_nonneg (by norm_num) (hC0 R hR)))
      (mul_nonneg (by norm_num) (hP0 R hR)), fun R hR => by
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (hG1 R hR))
        (mul_nonneg (by norm_num) (hC1 R hR)))
      (mul_nonneg (by norm_num) (hP1 R hR)), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  have hTraceH : jet (I := I) (M := M) g₀ 4 2 3
      (traceHessianCoeff (I := I) (M := M) g₀ g₁) ≤ (Bt R) ^ 2 := by
    rw [traceHessian_eq (I := I) (M := M) g₀ g₁]
    exact htrace g₁ P htie hδ_le hδ_nonneg hbound
      traceHessianSlotPerm R hR hP2
  have hTrace : ∀ σ : Equiv.Perm (Fin 4),
      jet (I := I) (M := M) g₀ 4 2 3
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ) ≤
          (Bt R) ^ 2 := by
    intro σ
    calc
      _ = jet (I := I) (M := M) g₀ 4 2 3
          (traceHessianCoeff (I := I) (M := M) g₀ g₁) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lieArm1_normSq_icg_dLTC_eq
          (I := I) (M := M) g₀ g₁ σ i
      _ ≤ (Bt R) ^ 2 := hTraceH
  let Qc : ℝ := Bc0 R + Bc1 R * A
  have hQc : 0 ≤ Qc :=
    add_nonneg (hBc0 R hR) (mul_nonneg (hBc1 R hR) hA)
  have hConnLow := hconn g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 hP3
  have hConn : jet (I := I) (M := M) g₀ 1 2 3
      (connDiffSection (I := I) g₁ g₀) ≤ Qc ^ 2 := by
    calc
      _ = jet (I := I) (M := M) g₀ 0 3 3
          (connDiffLoweredCc (I := I) g₀ g₁) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [conn_norm_eq (I := I) (M := M) g₀ g₁ i]
      _ ≤ Qc ^ 2 := hConnLow
  let Qp : ℝ := Bp0 R + Bp1 R * A
  have hQp : 0 ≤ Qp :=
    add_nonneg (hBp0 R hR) (mul_nonneg (hBp1 R hR) hA)
  have hPsi : jet (I := I) (M := M) g₀ 1 2 3
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB) ≤ Qp ^ 2 :=
    hpsi g₁ P htie hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  let Qg : ℝ := D0 R + D1 R * A
  have hQg : 0 ≤ Qg :=
    add_nonneg (hD0 R hR) (mul_nonneg (hD1 R hR) hA)
  have hBgRaw := jet_add (I := I) (M := M) g₀ 1 2 3
    (connDiffSection (I := I) g₁ g₀) FixCd Qc AF
    hQc hAF hConn hFix
  have hBg : jet (I := I) (M := M) g₀ 1 2 3
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ gB) ≤ Qg ^ 2 := by
    rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀ g₁ gB]
    convert hBgRaw using 1 <;> simp only [Qg, D0, D1, Qc, FixCd] <;> ring
  let Ac : ℝ := C0 R + C1 R * A
  let Ap : ℝ := P0 R + P1 R * A
  let Ag : ℝ := G0 R + G1 R * A
  have hAc : 0 ≤ Ac :=
    add_nonneg (hC0 R hR) (mul_nonneg (hC1 R hR) hA)
  have hAp : 0 ≤ Ap :=
    add_nonneg (hP0 R hR) (mul_nonneg (hP1 R hR) hA)
  have hAg : 0 ≤ Ag :=
    add_nonneg (hG0 R hR) (mul_nonneg (hG1 R hR) hA)
  have hPc : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      jet (I := I) (M := M) g₀ 3 2 3
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ ρ
          (connDiffSection (I := I) g₁ g₀)) ≤ Ac ^ 2 := by
    intro σ ρ
    have h := hpiece g₁ σ ρ (connDiffSection (I := I) g₁ g₀)
      (Bt R) Qc (hBt R hR) hQc (hTrace σ) hConn
    convert h using 1 <;> simp only [Ac, C0, C1, S, Qc] <;> ring
  have hPp : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      jet (I := I) (M := M) g₀ 3 2 3
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB)) ≤ Ap ^ 2 := by
    intro σ ρ
    have h := hpiece g₁ σ ρ
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB)
      (Bt R) Qp (hBt R hR) hQp (hTrace σ) hPsi
    convert h using 1 <;> simp only [Ap, P0, P1, S, Qp] <;> ring
  have hPg : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      jet (I := I) (M := M) g₀ 3 2 3
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ gB)) ≤ Ag ^ 2 := by
    intro σ ρ
    have h := hpiece g₁ σ ρ
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ gB)
      (Bt R) Qg (hBt R hR) hQg (hTrace σ) hBg
    convert h using 1 <;> simp only [Ag, G0, G1, S, Qg] <;> ring
  let Z0 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ gB)
  let Z1 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z2 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA
      (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB)
  let Z3 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z4 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)
  let Z5 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4))
      lieArm1RhoSlot1 (connDiffSection (I := I) g₁ g₀)
  let Z6 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z7 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z8 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap
      (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ gB)
  let Z9 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z10 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)
  let Z11 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)
  let Z12 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap
      (Equiv.refl (Fin 3)) (connDiffSection (I := I) g₁ g₀)
  let Z13 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4))
      lieArm1RhoSlot0 (connDiffSection (I := I) g₁ g₀)
  have hZ0 : jet (I := I) (M := M) g₀ 3 2 3 Z0 ≤ Ag ^ 2 :=
    hPg lieArm1SigmaC lieArm1RhoSlot0
  have hZ1 : jet (I := I) (M := M) g₀ 3 2 3 Z1 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaA (Equiv.refl (Fin 3))
  have hZ2 : jet (I := I) (M := M) g₀ 3 2 3 Z2 ≤ Ap ^ 2 :=
    hPp lieArm1SigmaA (Equiv.refl (Fin 3))
  have hZ3 : jet (I := I) (M := M) g₀ 3 2 3 Z3 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaC (Equiv.refl (Fin 3))
  have hZ4 : jet (I := I) (M := M) g₀ 3 2 3 Z4 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaD lieArm1RhoSlot0
  have hZ5 : jet (I := I) (M := M) g₀ 3 2 3 Z5 ≤ Ac ^ 2 :=
    hPc (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have hZ6 : jet (I := I) (M := M) g₀ 3 2 3 Z6 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaF (Equiv.refl (Fin 3))
  have hZ7 : jet (I := I) (M := M) g₀ 3 2 3 Z7 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have hZ8 : jet (I := I) (M := M) g₀ 3 2 3 Z8 ≤ Ap ^ 2 :=
    hPp lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have hZ9 : jet (I := I) (M := M) g₀ 3 2 3 Z9 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have hZ10 : jet (I := I) (M := M) g₀ 3 2 3 Z10 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaDSwap lieArm1RhoSlot0
  have hZ11 : jet (I := I) (M := M) g₀ 3 2 3 Z11 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaESwap lieArm1RhoSlot1
  have hZ12 : jet (I := I) (M := M) g₀ 3 2 3 Z12 ≤ Ac ^ 2 :=
    hPc lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have hZ13 : jet (I := I) (M := M) g₀ 3 2 3 Z13 ≤ Ac ^ 2 :=
    hPc (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  let Q2 : ℝ := 2 * (Ac + Ap)
  let Q3 : ℝ := 2 * (Q2 + Ac)
  let Q4 : ℝ := 2 * (Q3 + Ac)
  let Q5 : ℝ := 2 * (Q4 + Ac)
  let Q6 : ℝ := 2 * (Q5 + Ac)
  have hQ2 : 0 ≤ Q2 := mul_nonneg (by norm_num) (add_nonneg hAc hAp)
  have hQ3 : 0 ≤ Q3 := mul_nonneg (by norm_num) (add_nonneg hQ2 hAc)
  have hQ4 : 0 ≤ Q4 := mul_nonneg (by norm_num) (add_nonneg hQ3 hAc)
  have hQ5 : 0 ≤ Q5 := mul_nonneg (by norm_num) (add_nonneg hQ4 hAc)
  have hQ6 : 0 ≤ Q6 := mul_nonneg (by norm_num) (add_nonneg hQ5 hAc)
  have hB12 := jet_add (I := I) (M := M) g₀ 3 2 3 Z1 Z2
    Ac Ap hAc hAp hZ1 hZ2
  have hB123 := jet_sub (I := I) (M := M) g₀ 3 2 3 (Z1 + Z2) Z3
    Q2 Ac hQ2 hAc (by simpa only [Q2] using hB12) hZ3
  have hB1234 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z1 + Z2 - Z3) Z4 Q3 Ac hQ3 hAc
    (by simpa only [Q3] using hB123) hZ4
  have hB12345 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z1 + Z2 - Z3 - Z4) Z5 Q4 Ac hQ4 hAc
    (by simpa only [Q4] using hB1234) hZ5
  have hBlock1 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z1 + Z2 - Z3 - Z4 - Z5) Z6 Q5 Ac hQ5 hAc
    (by simpa only [Q5] using hB12345) hZ6
  have hB78 := jet_add (I := I) (M := M) g₀ 3 2 3 Z7 Z8
    Ac Ap hAc hAp hZ7 hZ8
  have hB789 := jet_sub (I := I) (M := M) g₀ 3 2 3 (Z7 + Z8) Z9
    Q2 Ac hQ2 hAc (by simpa only [Q2] using hB78) hZ9
  have hB78910 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z7 + Z8 - Z9) Z10 Q3 Ac hQ3 hAc
    (by simpa only [Q3] using hB789) hZ10
  have hB7891011 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z7 + Z8 - Z9 - Z10) Z11 Q4 Ac hQ4 hAc
    (by simpa only [Q4] using hB78910) hZ11
  have hBlock2 := jet_sub (I := I) (M := M) g₀ 3 2 3
    (Z7 + Z8 - Z9 - Z10 - Z11) Z12 Q5 Ac hQ5 hAc
    (by simpa only [Q5] using hB7891011) hZ12
  let Q7 : ℝ := 2 * (Ag + Q6)
  let Q8 : ℝ := 2 * (Q7 + Q6)
  let Q9 : ℝ := 2 * (Q8 + Ac)
  have hQ7 : 0 ≤ Q7 := mul_nonneg (by norm_num) (add_nonneg hAg hQ6)
  have hQ8 : 0 ≤ Q8 := mul_nonneg (by norm_num) (add_nonneg hQ7 hQ6)
  have hQ9 : 0 ≤ Q9 := mul_nonneg (by norm_num) (add_nonneg hQ8 hAc)
  have hOuter1 := jet_add (I := I) (M := M) g₀ 3 2 3 Z0
    (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) Ag Q6 hAg hQ6 hZ0
    (by simpa only [Q6] using hBlock1)
  have hOuter2 := jet_add (I := I) (M := M) g₀ 3 2 3
    (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6))
    (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) Q7 Q6 hQ7 hQ6
    (by simpa only [Q7] using hOuter1)
    (by simpa only [Q6] using hBlock2)
  have hAll := jet_add (I := I) (M := M) g₀ 3 2 3
    (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
      (Z7 + Z8 - Z9 - Z10 - Z11 - Z12)) Z13
    Q8 Ac hQ8 hAc (by simpa only [Q8] using hOuter2) hZ13
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum
    (I := I) (M := M) g₀ g₁ gB]
  change jet (I := I) (M := M) g₀ 3 2 3
      (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
        (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13) ≤
    (B0 R + B1 R * A) ^ 2
  have hfactor : Q9 = B0 R + B1 R * A := by
    simp only [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q2,
      Ac, Ap, Ag, B0, B1]
    ring
  rw [← hfactor]
  simpa only [Q9] using hAll

/-- One-parameter compatibility wrapper around `lie1_h2_tame`. -/
theorem lie1_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, htame⟩ :=
    lie1_h2_tame (I := I) (M := M) hDim g₀ gB hδ₀
  let B : ℝ → ℝ := fun A => B0 A + B1 A * A
  refine ⟨B, fun A hA =>
    add_nonneg (hB0 A hA) (mul_nonneg (hB1 A hA) hA), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP3
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP3
  simpa only [B] using htame g₁ P htie hδ_le hδ_nonneg hbound
    A A hA hA hP2 hP3

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
