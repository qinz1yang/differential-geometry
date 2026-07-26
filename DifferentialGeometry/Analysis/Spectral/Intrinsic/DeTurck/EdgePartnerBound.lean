import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound

/-!
# Closed-edge formal-partner bounds

The top refold coefficient cannot be differentiated as an arbitrary
coefficient: that loses the sharp zero at the diagonal.  This file estimates
the explicit formal partner from `EdgeRefoldPairing`.  Every differentiated
monomial keeps one undifferentiated metric difference, hence gains the small
`C0` radius needed by the closed-edge energy argument.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private lemma edge_symm_eq (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g S x u w = ccTensorBilin (I := I) g S x w u) :
    symmS (I := I) (M := M) g S = S := by
  have hswap : domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
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
  have htwo : S + S = (2 : Real) • S := (two_smul Real S).symm
  rw [symmS, hswap, htwo, smul_smul,
    show (1 / 2 : Real) * 2 = 1 by norm_num, one_smul]

private theorem edge_full_split
    (g gm : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g gm =
      gInvDiffRaisedEndoField (I := I) g gm +
        fullRaisedEndoField (I := I) (M := M) g g := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g gm +
      fullRaisedEndoField (I := I) (M := M) g g) x) =
      gInvDiffRaisedEndoField (I := I) g gm x +
        fullRaisedEndoField (I := I) (M := M) g g x from by
          rw [ContMDiffSection.coe_add]
          rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show gInvDiffRaisedEndoField (I := I) g gm x =
      gInvDiffRaisedEndo (I := I) g gm x from rfl]
  rw [fullRaisedEndoField_apply,
    gInvRaisedEndo_eq_diff_add_id (I := I) g gm x v]
  rw [show gInvRaisedEndo (I := I) g g x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
private theorem edge_insert_add
    (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g s A +
        slotInsertEndoCc (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g s A +
      slotInsertEndoCc (I := I) (M := M) g s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g s B).toSection x from by
          rw [SmoothCcTensor.toSection_add]
          rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

private lemma edge_endo_id_zero (g : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g)
        (fullRaisedEndoField (I := I) (M := M) g g) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g
    (fullRaisedEndoField (I := I) (M := M) g g) Y x v
  have hLambda : (fun y : M =>
      (fullRaisedEndoField (I := I) (M := M) g g y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_self,
      ContinuousLinearMap.id_apply]
  rw [hLeib, hLambda]
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_self,
    ContinuousLinearMap.id_apply, sub_self]

set_option backward.isDefEq.respectTransparency false in
private lemma edge_cov_insert_id (g : SmoothRiemannianMetric I M) (s : Nat) :
    covGrad (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s
          (fullRaisedEndoField (I := I) (M := M) g g)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1)
    (slotInsertEndoCc (I := I) (M := M) g s
      (fullRaisedEndoField (I := I) (M := M) g g)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s
    (fullRaisedEndoField (I := I) (M := M) g g) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g)
        (fullRaisedEndoField (I := I) (M := M) g g) x (m 0)) =
      (0 : TangentSpace I x →L[Real] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact edge_endo_id_zero (I := I) (M := M) g Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (0 : TangentSpace I x →L[Real] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[Real] TangentSpace I x) =
        (0 : Real) • (0 : TangentSpace I x →L[Real] TangentSpace I x) from
      (zero_smul Real _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem edge_cov_full_eq
    (g gm : SmoothRiemannianMetric I M) (s : Nat) :
    covGrad (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s
          (fullRaisedEndoField (I := I) (M := M) g gm)) =
      covGrad (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s
          (gInvDiffRaisedEndoField (I := I) g gm)) := by
  rw [edge_full_split (I := I) (M := M) g gm,
    edge_insert_add (I := I) (M := M) g s, covGrad_add,
    edge_cov_insert_id (I := I) (M := M) g s, add_zero]

/-- The first derivative of a relative inverse-metric insertion is uniformly
linear in the first derivative of the metric difference. -/
theorem edgeFull_one (g : SmoothRiemannianMetric I M) :
    ∃ A : Real, 0 ≤ A ∧
      ∀ (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g T y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 3 x
              ((covGrad (I := I) (M := M) g 2 2
                (slotInsertEndoCc (I := I) (M := M) g 1
                  (fullRaisedEndoField (I := I) (M := M) g gm))).toSection x) ≤
            A * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  classical
  obtain ⟨C, hC, hgrid⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g (show (1 / 2 : Real) < 1 by norm_num)
  refine ⟨C 1, hC 1, ?_⟩
  intro gm T htie delta hdelta hdelta0 hbound x
  rw [edge_cov_full_eq (I := I) (M := M) g gm 1]
  have h := hgrid gm T htie hdelta hdelta0 hbound 1 x
  simpa [Finset.sum_range_succ, Finset.sum_range_one] using h

/-- A relative inverse-metric insertion is uniformly bounded on the half
operator ball. -/
theorem edgeFull_zero
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g T y v w)
    {delta : Real} (hdelta : delta ≤ 1 / 2) (hdelta0 : 0 ≤ delta)
    (hbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        ((slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x) ≤
      (2 * (Module.finrank Real E : Real)) ^ 2 := by
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta (by norm_num)
  have hraw := riemannianFiberNormSq_gInvSlotEndo_le
    (I := I) (M := M) g gm
    (ccTensorBilinSymm (I := I) g T) htie hdelta_lt hdelta0 hbound x
  have hden : 0 < 1 - delta := by linarith
  have hfrac : 1 / (1 - delta) ≤ (2 : Real) := by
    rw [div_le_iff₀ hden]
    linarith
  have hfrac0 : 0 ≤ 1 / (1 - delta) := by positivity
  have hd : 0 ≤ (Module.finrank Real E : Real) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hfrac hd
  change riemannianFiberNormSq (I := I) (M := M) g 2 2 x
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (gInvSlotEndo (I := I) g gm x)) ≤ _
  refine hraw.trans ?_
  nlinarith [mul_nonneg hd hfrac0]

private lemma edge_app_le (g : SmoothRiemannianMetric I M)
    (r s : Nat) (Phi : SmoothCcTensor g r s)
    (W : SmoothCcTensor g 0 r) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((appCc (I := I) (M := M) g r s Phi W).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x (Phi.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  rw [appCc_toSection]
  exact riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 0 r s x (Phi.toSection x) (W.toSection x)

/-- Applying one relative inverse-metric slot map is uniformly bounded in
fibre norm on the half ball. -/
theorem edgeSlot_zero
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g T y v w)
    {delta : Real} (hdelta : delta ≤ 1 / 2) (hdelta0 : 0 ≤ delta)
    (hbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (j : Fin 2) (S : SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((edgeSlot2 (I := I) (M := M) g
          (fullRaisedEndoField (I := I) (M := M) g gm) j S).toSection x) ≤
      (2 * (Module.finrank Real E : Real)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) := by
  let P : SmoothCcTensor g 0 2 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S
  let Phi : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gm)
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) j)
    (appCc (I := I) (M := M) g 2 2 Phi P) 0 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((edgeSlot2 (I := I) (M := M) g
            (fullRaisedEndoField (I := I) (M := M) g gm) j S).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((appCc (I := I) (M := M) g 2 2 Phi P).toSection x) := by
    simpa only [edgeSlot2, Phi, P, iteratedCovGrad_zero] using hout
  rw [hout']
  have happ := edge_app_le (I := I) (M := M) g 2 2 Phi P x
  have hphi := edgeFull_zero (I := I) (M := M) g gm T htie hdelta hdelta0 hbound x
  have hp := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) j) S 0 x
  have hp' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) := by
    simpa only [P, iteratedCovGrad_zero] using hp
  calc
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g 2 2 x (Phi.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) := happ
    _ ≤ (2 * (Module.finrank Real E : Real)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) :=
      mul_le_mul_of_nonneg_right hphi
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
    _ = _ := by rw [hp']

/-- The exact product rule for one raised slot has no zeroth-order additive
error: its derivative is controlled by `nabla T * S + nabla S`. -/
theorem edgeSlot_one (g : SmoothRiemannianMetric I M) :
    ∃ K : Real, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g T y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        ∀ (j : Fin 2) (S : SmoothCcTensor g 0 2) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2
                (edgeSlot2 (I := I) (M := M) g
                  (fullRaisedEndoField (I := I) (M := M) g gm) j S)).toSection x) ≤
            K *
              (riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                    ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (S.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                  ((covGrad (I := I) (M := M) g 0 2 S).toSection x)) := by
  classical
  obtain ⟨A, hA0, hA⟩ := edgeFull_one (I := I) (M := M) g
  let F : Real := (2 * (Module.finrank Real E : Real)) ^ 2
  let K : Real := 2 * (A + F)
  have hF0 : 0 ≤ F := sq_nonneg _
  have hK0 : 0 ≤ K := mul_nonneg (by norm_num) (add_nonneg hA0 hF0)
  refine ⟨K, hK0, ?_⟩
  intro gm T htie delta hdelta hdelta0 hbound j S x
  let P : SmoothCcTensor g 0 2 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S
  let Phi : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gm)
  let U : SmoothCcTensor g 0 3 :=
    appCc (I := I) (M := M) g 2 3
      (covGrad (I := I) (M := M) g 2 2 Phi) P
  let V : SmoothCcTensor g 0 3 :=
    appCc (I := I) (M := M) g 3 3
      (slotExtend (I := I) (M := M) g 2 2 Phi)
      (covGrad (I := I) (M := M) g 0 2 P)
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) j)
    (appCc (I := I) (M := M) g 2 2 Phi P) 1 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2
            (edgeSlot2 (I := I) (M := M) g
              (fullRaisedEndoField (I := I) (M := M) g gm) j S)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2
            (appCc (I := I) (M := M) g 2 2 Phi P)).toSection x) := by
    simpa only [edgeSlot2, Phi, P, iteratedCovGrad_succ,
      iteratedCovGrad_zero] using hout
  rw [hout']
  have hprod : covGrad (I := I) (M := M) g 0 2
      (appCc (I := I) (M := M) g 2 2 Phi P) = U + V := by
    simpa only [U, V] using
      covGrad_appCc_eq (I := I) (M := M) g 2 2 Phi P
  rw [hprod]
  have hadd := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 0 3 x (U.toSection x) (V.toSection x)
  have hpa := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) j) S 0 x
  have hp0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) := by
    simpa only [P, iteratedCovGrad_zero] using hpa
  have hpb := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) j) S 1 x
  have hp1 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 P).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGrad (I := I) (M := M) g 0 2 S).toSection x) := by
    simpa only [P, iteratedCovGrad_succ, iteratedCovGrad_zero] using hpb
  have hphi0 : riemannianFiberNormSq (I := I) (M := M) g 2 2 x
      (Phi.toSection x) ≤ F := by
    simpa only [Phi, F] using
      edgeFull_zero (I := I) (M := M) g gm T htie hdelta hdelta0 hbound x
  have hphi1 : riemannianFiberNormSq (I := I) (M := M) g 2 3 x
      ((covGrad (I := I) (M := M) g 2 2 Phi).toSection x) ≤
      A * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
    simpa only [Phi] using hA gm T htie hdelta hdelta0 hbound x
  have hU : riemannianFiberNormSq (I := I) (M := M) g 0 3 x (U.toSection x) ≤
      A * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) := by
    refine (edge_app_le (I := I) (M := M) g 2 3
      (covGrad (I := I) (M := M) g 2 2 Phi) P x).trans ?_
    rw [hp0]
    exact mul_le_mul_of_nonneg_right hphi1
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
  have hV : riemannianFiberNormSq (I := I) (M := M) g 0 3 x (V.toSection x) ≤
      F * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGrad (I := I) (M := M) g 0 2 S).toSection x) := by
    refine (riemannianFiberNormSq_appCc_slotExtend_le
      (I := I) (M := M) g 2 2 Phi
      (covGrad (I := I) (M := M) g 0 2 P) x).trans ?_
    rw [hp1]
    exact mul_le_mul_of_nonneg_right hphi0
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _)
  let X : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) *
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x)
  let Y : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 S).toSection x)
  have hX0 : 0 ≤ X := mul_nonneg
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
  have hY0 : 0 ≤ Y := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  calc
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x (U.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x (V.toSection x) := hadd
    _ ≤ 2 * (A * X) + 2 * (F * Y) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (by simpa only [X] using hU) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [Y] using hV) (by norm_num))
    _ ≤ K * (X + Y) := by
      dsimp only [K]
      nlinarith
    _ = _ := by rfl

/-- Applying the relative inverse metric in both tensor slots preserves the
`C0` smallness and costs only a uniform multiple of the first derivative. -/
theorem edgeRaise_gen (g : SmoothRiemannianMetric I M) :
    ∃ Z D : Real, 0 ≤ Z ∧ 0 ≤ D ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              ((edgeRaise2 (I := I) (M := M) g gm T).toSection x) ≤
              Z * delta ^ 2 ∧
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2
                (edgeRaise2 (I := I) (M := M) g gm T)).toSection x) ≤
              D * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  classical
  obtain ⟨K, hK0, hK⟩ := edgeSlot_one (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let F : Real := (2 * d) ^ 2
  let D0 : Real := K * (d ^ 2 + 1)
  let Z : Real := F ^ 2 * d ^ 2
  let D : Real := K * (F * d ^ 2 + D0)
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hF0 : 0 ≤ F := sq_nonneg _
  have hD00 : 0 ≤ D0 := mul_nonneg hK0 (by positivity)
  have hZ0 : 0 ≤ Z := mul_nonneg (sq_nonneg F) (sq_nonneg d)
  have hD0 : 0 ≤ D := mul_nonneg hK0
    (add_nonneg (mul_nonneg hF0 (sq_nonneg d)) hD00)
  refine ⟨Z, D, hZ0, hD0, ?_⟩
  intro gm P T hTsymm htie delta hdelta hdelta0 hPbound hTbound hgrad x
  let T0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (T.toSection x)
  let T1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)
  let P1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
  let S0 : SmoothCcTensor g 0 2 :=
    edgeSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 T
  have hsymm : symmS (I := I) (M := M) g T = T :=
    edge_symm_eq (I := I) (M := M) g T hTsymm
  have hT0 := symmC0_rfns_le (I := I) (M := M) g T hdelta0 hTbound x
  rw [hsymm] at hT0
  have hT0' : T0 ≤ d ^ 2 * delta ^ 2 := by
    simpa only [T0, d] using hT0
  have hdsq : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg delta]
  have hT0coarse : T0 ≤ d ^ 2 := by
    calc
      T0 ≤ d ^ 2 * delta ^ 2 := hT0'
      _ ≤ d ^ 2 * 1 := mul_le_mul_of_nonneg_left hdsq (sq_nonneg d)
      _ = d ^ 2 := mul_one _
  have hT00 : 0 ≤ T0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hT10 : 0 ≤ T1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hP1T1 : P1 ≤ T1 := by simpa only [P1, T1] using hgrad x
  have hS00 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (S0.toSection x) ≤ F * T0 := by
    simpa only [S0, F, d, T0] using
      edgeSlot_zero (I := I) (M := M) g gm P htie hdelta hdelta0 hPbound 0 T x
  have hS01raw := hK gm P htie hdelta hdelta0 hPbound 0 T x
  have hS01 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 S0).toSection x) ≤ D0 * T1 := by
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGrad (I := I) (M := M) g 0 2 S0).toSection x) ≤
        K * (P1 * T0 + T1) := by
      simpa only [S0, P1, T0, T1, iteratedCovGrad_succ,
        iteratedCovGrad_zero] using hS01raw
    calc
      _ ≤ K * (P1 * T0 + T1) := hraw
      _ ≤ K * (T1 * T0 + T1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ T1) hK0
        exact mul_le_mul_of_nonneg_right hP1T1 hT00
      _ ≤ K * (T1 * d ^ 2 + T1) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        exact add_le_add_right (mul_le_mul_of_nonneg_left hT0coarse hT10) T1
      _ = D0 * T1 := by simp only [D0]; ring
  have hR0 := edgeSlot_zero (I := I) (M := M) g gm P htie
    hdelta hdelta0 hPbound 1 S0 x
  have hR1 := hK gm P htie hdelta hdelta0 hPbound 1 S0 x
  have hR0' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      ((edgeRaise2 (I := I) (M := M) g gm T).toSection x) ≤ Z * delta ^ 2 := by
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((edgeRaise2 (I := I) (M := M) g gm T).toSection x) ≤
        F * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (S0.toSection x) := by
      simpa only [edgeRaise2, S0, F, d] using hR0
    calc
      _ ≤ F * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (S0.toSection x) := hraw
      _ ≤ F * (F * T0) := mul_le_mul_of_nonneg_left hS00 hF0
      _ ≤ F * (F * (d ^ 2 * delta ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hT0' hF0) hF0
      _ = Z * delta ^ 2 := by simp only [Z]; ring
  have hR1' : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2
        (edgeRaise2 (I := I) (M := M) g gm T)).toSection x) ≤ D * T1 := by
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGrad (I := I) (M := M) g 0 2
          (edgeRaise2 (I := I) (M := M) g gm T)).toSection x) ≤
        K * (P1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (S0.toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 S0).toSection x)) := by
      simpa only [edgeRaise2, S0, P1, T1, iteratedCovGrad_succ,
        iteratedCovGrad_zero] using hR1
    calc
      _ ≤ K * (P1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (S0.toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 S0).toSection x)) := hraw
      _ ≤ K * (T1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (S0.toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 S0).toSection x)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) hK0
        exact mul_le_mul_of_nonneg_right hP1T1
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
      _ ≤ K * (T1 * (F * T0) + D0 * T1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ hS01) hK0
        exact mul_le_mul_of_nonneg_left hS00 hT10
      _ ≤ K * (T1 * (F * d ^ 2) + D0 * T1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ (D0 * T1)) hK0
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hT0coarse hF0) hT10
      _ = D * T1 := by simp only [D]; ring
  exact ⟨hR0', by simpa only [T1] using hR1'⟩

/-- Diagonal specialization of `edgeRaise_gen`. -/
theorem edgeRaise_bds (g : SmoothRiemannianMetric I M) :
    ∃ Z D : Real, 0 ≤ Z ∧ 0 ≤ D ∧
      ∀ (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g T y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              ((edgeRaise2 (I := I) (M := M) g gm T).toSection x) ≤
              Z * delta ^ 2 ∧
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2
                (edgeRaise2 (I := I) (M := M) g gm T)).toSection x) ≤
              D * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  obtain ⟨Z, D, hZ, hD, h⟩ := edgeRaise_gen (I := I) (M := M) g
  refine ⟨Z, D, hZ, hD, ?_⟩
  intro gm T hTsymm htie delta hdelta hdelta0 hbound x
  exact h gm T T hTsymm htie hdelta hdelta0 hbound hbound
    (fun _ => le_rfl) x

private lemma edge_extend2_one (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 5 x
        ((covGrad (I := I) (M := M) g 2 4
          (slotExtendIter (I := I) (M := M) g 0 2 2 T)).toSection x) =
      (Module.finrank Real E : Real) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T).toSection x) := by
  change riemannianFiberNormSq (I := I) (M := M) g 2 5 x
      ((covGrad (I := I) (M := M) g 2 4
        (slotExtend (I := I) (M := M) g 1 3
          (slotExtend (I := I) (M := M) g 0 2 T))).toSection x) = _
  rw [rfns_covGrad_slotExtend_scale (I := I) (M := M) g 1 3
    (slotExtend (I := I) (M := M) g 0 2 T) x]
  rw [rfns_covGrad_slotExtend_scale (I := I) (M := M) g 0 2 T x]
  ring

/-- One explicit Palatini formal partner has the sharp differentiated bound
`O(delta^2) * |nabla T|^2`. -/
theorem edgePartner_gen (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)) →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 5 x
              ((covGrad (I := I) (M := M) g 0 4
                (edgePairPartner (I := I) (M := M) g gm T sigma)).toSection x) ≤
            C * delta ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  classical
  obtain ⟨Z, D, hZ0, hD0, hraise⟩ := edgeRaise_gen (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let C : Real := 2 * (d ^ 2 * Z + d ^ 4 * D)
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg (sq_nonneg d) hZ0)
      (mul_nonneg (by positivity) hD0))
  refine ⟨C, hC0, ?_⟩
  intro gm P T hTsymm htie delta hdelta hdelta0 hPbound hTbound hgrad sigma x
  let A : SmoothCcTensor g 0 2 :=
    edgeRaise2 (I := I) (M := M) g gm T
  let Phi : SmoothCcTensor g 2 4 :=
    slotExtendIter (I := I) (M := M) g 0 2 2 T
  let U : SmoothCcTensor g 0 5 :=
    appCc (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) A
  let V : SmoothCcTensor g 0 5 :=
    appCc (I := I) (M := M) g 3 5
      (slotExtend (I := I) (M := M) g 2 4 Phi)
      (covGrad (I := I) (M := M) g 0 2 A)
  let T0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (T.toSection x)
  let T1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)
  have hsymm : symmS (I := I) (M := M) g T = T :=
    edge_symm_eq (I := I) (M := M) g T hTsymm
  have hT0raw := symmC0_rfns_le (I := I) (M := M) g T hdelta0 hTbound x
  rw [hsymm] at hT0raw
  have hT0 : T0 ≤ d ^ 2 * delta ^ 2 := by
    simpa only [T0, d] using hT0raw
  have hT10 : 0 ≤ T1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  obtain ⟨hA0, hA1⟩ := hraise gm P T hTsymm htie hdelta hdelta0
    hPbound hTbound hgrad x
  have hA0' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (A.toSection x) ≤ Z * delta ^ 2 := by simpa only [A] using hA0
  have hA1' : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 A).toSection x) ≤ D * T1 := by
    simpa only [A, T1] using hA1
  have hPhi0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (Phi.toSection x) = d ^ 2 * T0 := by
    simpa only [Phi, d] using
      rfns_slotExtendIter_eq (I := I) (M := M) g 0 2 2 T x
  have hPhi1 : riemannianFiberNormSq (I := I) (M := M) g 2 5 x
      ((covGrad (I := I) (M := M) g 2 4 Phi).toSection x) = d ^ 2 * T1 := by
    simpa only [Phi, d, T1, iteratedCovGrad_succ, iteratedCovGrad_zero] using
      edge_extend2_one (I := I) (M := M) g T x
  have hprod : covGrad (I := I) (M := M) g 0 4
      (edgeProd4 (I := I) (M := M) g A T) = U + V := by
    simpa only [edgeProd4, Phi, U, V] using
      covGrad_appCc_eq (I := I) (M := M) g 2 4 Phi A
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g sigma.symm
    (edgeProd4 (I := I) (M := M) g A T) 1 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (edgePairPartner (I := I) (M := M) g gm T sigma)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (edgeProd4 (I := I) (M := M) g A T)).toSection x) := by
    simpa only [edgePairPartner, A, iteratedCovGrad_succ,
      iteratedCovGrad_zero] using hout
  rw [hout', hprod]
  have hadd := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 0 5 x (U.toSection x) (V.toSection x)
  have hU : riemannianFiberNormSq (I := I) (M := M) g 0 5 x (U.toSection x) ≤
      d ^ 2 * Z * delta ^ 2 * T1 := by
    refine (edge_app_le (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) A x).trans ?_
    rw [hPhi1]
    calc
      d ^ 2 * T1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (A.toSection x) ≤ d ^ 2 * T1 * (Z * delta ^ 2) :=
        mul_le_mul_of_nonneg_left hA0' (mul_nonneg (sq_nonneg d) hT10)
      _ = d ^ 2 * Z * delta ^ 2 * T1 := by ring
  have hV : riemannianFiberNormSq (I := I) (M := M) g 0 5 x (V.toSection x) ≤
      d ^ 4 * D * delta ^ 2 * T1 := by
    refine (riemannianFiberNormSq_appCc_slotExtend_le
      (I := I) (M := M) g 2 4 Phi
      (covGrad (I := I) (M := M) g 0 2 A) x).trans ?_
    rw [hPhi0]
    calc
      d ^ 2 * T0 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 A).toSection x) ≤
          d ^ 2 * T0 * (D * T1) :=
        mul_le_mul_of_nonneg_left hA1'
          (mul_nonneg (sq_nonneg d)
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _))
      _ ≤ d ^ 2 * (d ^ 2 * delta ^ 2) * (D * T1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hT0 (sq_nonneg d))
          (mul_nonneg hD0 hT10)
      _ = d ^ 4 * D * delta ^ 2 * T1 := by ring
  calc
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x (U.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x (V.toSection x) := hadd
    _ ≤ 2 * (d ^ 2 * Z * delta ^ 2 * T1) +
        2 * (d ^ 4 * D * delta ^ 2 * T1) :=
      add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num))
        (mul_le_mul_of_nonneg_left hV (by norm_num))
    _ = C * delta ^ 2 * T1 := by simp only [C]; ring
    _ = _ := by rfl

/-- One explicit Palatini formal partner is pointwise quadratic in the metric
difference.  The estimate is stated relative to the undifferentiated tensor so
that its integral can be paired with `edgePartner_gen` in the divergence
bound. -/
theorem edgePartner_zero (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)) →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 4 x
              ((edgePairPartner (I := I) (M := M) g gm T sigma).toSection x) ≤
            C * delta ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (T.toSection x) := by
  classical
  obtain ⟨Z, D, hZ0, hD0, hraise⟩ := edgeRaise_gen (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let C : Real := d ^ 2 * Z
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg d) hZ0
  refine ⟨C, hC0, ?_⟩
  intro gm P T hTsymm htie delta hdelta hdelta0 hPbound hTbound hgrad sigma x
  let A : SmoothCcTensor g 0 2 :=
    edgeRaise2 (I := I) (M := M) g gm T
  let Phi : SmoothCcTensor g 2 4 :=
    slotExtendIter (I := I) (M := M) g 0 2 2 T
  obtain ⟨hA0, _hA1⟩ := hraise gm P T hTsymm htie hdelta hdelta0
    hPbound hTbound hgrad x
  have hA0' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (A.toSection x) ≤ Z * delta ^ 2 := by
    simpa only [A] using hA0
  have hPhi0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (Phi.toSection x) = d ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) := by
    simpa only [Phi, d] using
      rfns_slotExtendIter_eq (I := I) (M := M) g 0 2 2 T x
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g sigma.symm
    (edgeProd4 (I := I) (M := M) g A T) 0 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((edgePairPartner (I := I) (M := M) g gm T sigma).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((edgeProd4 (I := I) (M := M) g A T).toSection x) := by
    simpa only [edgePairPartner, A, iteratedCovGrad_zero] using hout
  rw [hout']
  refine (edge_app_le (I := I) (M := M) g 2 4 Phi A x).trans ?_
  rw [hPhi0]
  calc
    d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (A.toSection x) ≤
        d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) * (Z * delta ^ 2) :=
      mul_le_mul_of_nonneg_left hA0'
        (mul_nonneg (sq_nonneg d)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _))
    _ = C * delta ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) := by simp only [C]; ring

/-- Diagonal specialization of `edgePartner_gen`. -/
theorem edgePartner_one (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g T y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 5 x
              ((covGrad (I := I) (M := M) g 0 4
                (edgePairPartner (I := I) (M := M) g gm T sigma)).toSection x) ≤
            C * delta ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  obtain ⟨C, hC, h⟩ := edgePartner_gen (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro gm T hTsymm htie delta hdelta hdelta0 hbound sigma x
  exact h gm T T hTsymm htie hdelta hdelta0 hbound hbound
    (fun _ => le_rfl) sigma x

private lemma edge_bound_mono (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {a b : Real} (hab : a ≤ b)
    (ha : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) a) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) b := by
  intro x v w
  exact (ha x v w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-- The complete top formal partner is pointwise quadratic in the metric
difference on the realized segment. -/
theorem edgeTop_zero (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        {delta : Real}, 0 ≤ delta → delta ≤ 1 / 2 →
        (hdelta : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta) →
        (hdeltaZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) →
        ∀ (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 0 4 x
                ((edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
                  qA qB q epsilon s).toSection x) ≤
              C * delta ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                  (T.toSection x) := by
  classical
  obtain ⟨Cp, hCp0, hp⟩ := edgePartner_zero (I := I) (M := M) g
  let C : Real := 52 * Cp
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) hCp0
  refine ⟨C, hC0, ?_⟩
  intro T hTsymm delta hdelta0 hdelta_half hdelta hdeltaZ
    qA qB q epsilon hepsilon s hs x
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half (by norm_num)
  have hsSmall : s ∈ realizedSmallSet (δ := delta) (δ' := delta) :=
    Icc_subset_realizedSmallSet hdelta_lt hdelta_lt hs
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hdelta hdeltaZ s
  let P : SmoothCcTensor g 0 2 := s • T
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    have hpath := realizedFam_inner_of_mem (I := I) (M := M)
      g T 0 hdelta hdeltaZ hsSmall y v w
    simpa only [gm, P, convexPerturbation, smul_zero, zero_add] using hpath
  have hsabs : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs2 : s ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - s) * (1 + s) :=
      mul_nonneg (sub_nonneg.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hPraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s T hdelta
  have hrad : |s| * delta ≤ delta := by
    have hprod : 0 ≤ (1 - |s|) * delta :=
      mul_nonneg (sub_nonneg.mpr hsabs) hdelta0
    nlinarith
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta := by
    exact edge_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hgrad : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection y) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection y) := by
    intro y
    rw [show iteratedCovGrad (I := I) g 0 2 1 P =
        s • iteratedCovGrad (I := I) g 0 2 1 T from by
      simp only [P, iteratedCovGrad_smul]]
    rw [SmoothCcTensor.toSection_smul, riemannianFiberNormSq_smul]
    exact mul_le_of_le_one_left
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 y _) hs2
  let T0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (T.toSection x)
  let B : Real := Cp * delta ^ 2 * T0
  have hT00 : 0 ≤ T0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hB0 : 0 ≤ B := mul_nonneg
    (mul_nonneg hCp0 (sq_nonneg delta)) hT00
  let N : SmoothCcTensor g 0 4 → Real := fun Q =>
    riemannianFiberNormSq (I := I) (M := M) g 0 4 x (Q.toSection x)
  have hpair : ∀ sigma : Equiv.Perm (Fin 4),
      N (edgePairPartner (I := I) (M := M) g gm T sigma) ≤ B := by
    intro sigma
    simpa only [N, B, T0, gm] using hp gm P T hTsymm htie
      hdelta_half hdelta0 hPbound hdelta hgrad sigma x
  have hNadd : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q + R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [SmoothCcTensor.toSection_add]
    exact riemannianFiberNormSq_add_le
      (I := I) (M := M) g 0 4 x _ _
  have hNsub : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q - R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [SmoothCcTensor.toSection_sub]
    exact riemannianFiberNormSq_sub_le
      (I := I) (M := M) g 0 4 x _ _
  have hNsmul : ∀ (a : Real) (Q : SmoothCcTensor g 0 4),
      N (a • Q) = a ^ 2 * N Q := by
    intro a Q
    dsimp only [N]
    rw [SmoothCcTensor.toSection_smul, riemannianFiberNormSq_smul]
  have hkernel : ∀ qq : Fin 4 → Equiv.Perm (Fin 4),
      N (edgeKernelPartner (I := I) (M := M) g gm T qq) ≤ 4 * B := by
    intro qq
    let Q0 := edgePairPartner (I := I) (M := M) g gm T (qq 0)
    let Q1 := edgePairPartner (I := I) (M := M) g gm T (qq 1)
    let Q2 := edgePairPartner (I := I) (M := M) g gm T (qq 2)
    let Q3 := edgePairPartner (I := I) (M := M) g gm T (qq 3)
    have h01 : N (Q0 + Q1) ≤ 4 * B := by
      calc
        N (Q0 + Q1) ≤ 2 * N Q0 + 2 * N Q1 := hNadd Q0 Q1
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (qq 0)) (by norm_num))
          (mul_le_mul_of_nonneg_left (hpair (qq 1)) (by norm_num))
        _ = 4 * B := by ring
    have h23 : N (Q2 + Q3) ≤ 4 * B := by
      calc
        N (Q2 + Q3) ≤ 2 * N Q2 + 2 * N Q3 := hNadd Q2 Q3
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (qq 2)) (by norm_num))
          (mul_le_mul_of_nonneg_left (hpair (qq 3)) (by norm_num))
        _ = 4 * B := by ring
    have hdiff : N ((Q0 + Q1) - (Q2 + Q3)) ≤ 16 * B := by
      calc
        N ((Q0 + Q1) - (Q2 + Q3)) ≤
            2 * N (Q0 + Q1) + 2 * N (Q2 + Q3) := hNsub _ _
        _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
          (mul_le_mul_of_nonneg_left h01 (by norm_num))
          (mul_le_mul_of_nonneg_left h23 (by norm_num))
        _ = 16 * B := by ring
    have heq : Q0 + Q1 - Q2 - Q3 = (Q0 + Q1) - (Q2 + Q3) := by abel
    rw [edgeKernelPartner]
    change N ((1 / 2 : Real) • (Q0 + Q1 - Q2 - Q3)) ≤ _
    rw [hNsmul, heq]
    norm_num
    linarith
  have hriem : N (edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ
      qA qB s) ≤ 4 * B := by
    let KA := edgeKernelPartner (I := I) (M := M) g gm T qA
    let KB := edgeKernelPartner (I := I) (M := M) g gm T qB
    have hab : N (KA + KB) ≤ 16 * B := by
      calc
        N (KA + KB) ≤ 2 * N KA + 2 * N KB := hNadd KA KB
        _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
          (mul_le_mul_of_nonneg_left (hkernel qA) (by norm_num))
          (mul_le_mul_of_nonneg_left (hkernel qB) (by norm_num))
        _ = 16 * B := by ring
    rw [edgeRiemPartner]
    change N (s • ((1 / 2 : Real) • (KA + KB))) ≤ _
    rw [hNsmul, hNsmul]
    norm_num
    nlinarith
  have hlieTerm : ∀ i : Fin 3,
      N (epsilon i • ((1 / 2 : Real) •
        (edgePairPartner (I := I) (M := M) g gm T (q i) +
          edgePairPartner (I := I) (M := M) g gm T
            ((q i).trans (Equiv.swap (0 : Fin 4) 1))))) ≤ B := by
    intro i
    let QA := edgePairPartner (I := I) (M := M) g gm T (q i)
    let QB := edgePairPartner (I := I) (M := M) g gm T
      ((q i).trans (Equiv.swap (0 : Fin 4) 1))
    have hab : N (QA + QB) ≤ 4 * B := by
      calc
        N (QA + QB) ≤ 2 * N QA + 2 * N QB := hNadd QA QB
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (q i)) (by norm_num))
          (mul_le_mul_of_nonneg_left
            (hpair ((q i).trans (Equiv.swap (0 : Fin 4) 1))) (by norm_num))
        _ = 4 * B := by ring
    have heps2 : (epsilon i) ^ 2 ≤ 1 := by
      have hi := (abs_le.mp (hepsilon i))
      have hprod : 0 ≤ (1 - epsilon i) * (1 + epsilon i) :=
        mul_nonneg (sub_nonneg.mpr hi.2) (by linarith [hi.1])
      nlinarith
    change N (epsilon i • ((1 / 2 : Real) • (QA + QB))) ≤ B
    rw [hNsmul, hNsmul]
    norm_num
    nlinarith
  have hlie : N (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ
      q epsilon s) ≤ 10 * B := by
    let L0 : SmoothCcTensor g 0 4 := epsilon 0 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 0) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 0).trans (Equiv.swap (0 : Fin 4) 1))))
    let L1 : SmoothCcTensor g 0 4 := epsilon 1 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 1) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 1).trans (Equiv.swap (0 : Fin 4) 1))))
    let L2 : SmoothCcTensor g 0 4 := epsilon 2 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 2) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 2).trans (Equiv.swap (0 : Fin 4) 1))))
    have h01 : N (L0 + L1) ≤ 4 * B := by
      calc
        N (L0 + L1) ≤ 2 * N L0 + 2 * N L1 := hNadd L0 L1
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (by simpa only [L0] using hlieTerm 0) (by norm_num))
          (mul_le_mul_of_nonneg_left (by simpa only [L1] using hlieTerm 1) (by norm_num))
        _ = 4 * B := by ring
    have h012 : N (L0 + L1 + L2) ≤ 10 * B := by
      calc
        N (L0 + L1 + L2) ≤ 2 * N (L0 + L1) + 2 * N L2 := hNadd _ _
        _ ≤ 2 * (4 * B) + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left h01 (by norm_num))
          (mul_le_mul_of_nonneg_left (by simpa only [L2] using hlieTerm 2) (by norm_num))
        _ = 10 * B := by ring
    rw [edgeLiePartner, Fin.sum_univ_three]
    change N (s • (L0 + L1 + L2)) ≤ _
    rw [hNsmul]
    exact (mul_le_mul_of_nonneg_left h012 (sq_nonneg s)).trans (by
      nlinarith)
  have htop : N (edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
      qA qB q epsilon s) ≤ 52 * B := by
    rw [edgeTopPartner]
    have hadd := hNadd
      ((2 : Real) • edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ qA qB s)
      (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
    rw [hNsmul] at hadd
    norm_num at hadd
    calc
      _ ≤ 2 * (4 * N (edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ
            qA qB s)) +
          2 * N (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ
            q epsilon s) := hadd
      _ ≤ 2 * (4 * (4 * B)) + 2 * (10 * B) := add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hriem (by norm_num)) (by norm_num))
        (mul_le_mul_of_nonneg_left hlie (by norm_num))
      _ = 52 * B := by ring
  simpa only [N, B, C, T0] using htop

/-- The complete top formal partner returned by the refold package retains a
small undifferentiated metric difference after one covariant derivative. -/
theorem edgeTop_one (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        {delta : Real}, 0 ≤ delta → delta ≤ 1 / 2 →
        (hdelta : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta) →
        (hdeltaZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) →
        ∀ (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 0 5 x
                ((covGrad (I := I) (M := M) g 0 4
                  (edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
                    qA qB q epsilon s)).toSection x) ≤
              C * delta ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                  ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
  classical
  obtain ⟨Cp, hCp0, hp⟩ := edgePartner_gen (I := I) (M := M) g
  let C : Real := 52 * Cp
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) hCp0
  refine ⟨C, hC0, ?_⟩
  intro T hTsymm delta hdelta0 hdelta_half hdelta hdeltaZ
    qA qB q epsilon hepsilon s hs x
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half (by norm_num)
  have hsSmall : s ∈ realizedSmallSet (δ := delta) (δ' := delta) :=
    Icc_subset_realizedSmallSet hdelta_lt hdelta_lt hs
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hdelta hdeltaZ s
  let P : SmoothCcTensor g 0 2 := s • T
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    have hpath := realizedFam_inner_of_mem (I := I) (M := M)
      g T 0 hdelta hdeltaZ hsSmall y v w
    simpa only [gm, P, convexPerturbation, smul_zero, zero_add] using hpath
  have hsabs : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs2 : s ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - s) * (1 + s) :=
      mul_nonneg (sub_nonneg.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hPraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s T hdelta
  have hrad : |s| * delta ≤ delta := by
    have hprod : 0 ≤ (1 - |s|) * delta :=
      mul_nonneg (sub_nonneg.mpr hsabs) hdelta0
    nlinarith
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta := by
    exact edge_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hgrad : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection y) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection y) := by
    intro y
    rw [show iteratedCovGrad (I := I) g 0 2 1 P =
        s • iteratedCovGrad (I := I) g 0 2 1 T from by
      simp only [P, iteratedCovGrad_smul]]
    rw [SmoothCcTensor.toSection_smul, riemannianFiberNormSq_smul]
    exact mul_le_of_le_one_left
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 y _) hs2
  let T1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x)
  let B : Real := Cp * delta ^ 2 * T1
  have hT10 : 0 ≤ T1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hB0 : 0 ≤ B := mul_nonneg
    (mul_nonneg hCp0 (sq_nonneg delta)) hT10
  let N : SmoothCcTensor g 0 4 → Real := fun Q =>
    riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      ((covGrad (I := I) (M := M) g 0 4 Q).toSection x)
  have hpair : ∀ sigma : Equiv.Perm (Fin 4),
      N (edgePairPartner (I := I) (M := M) g gm T sigma) ≤ B := by
    intro sigma
    simpa only [N, B, T1, gm] using hp gm P T hTsymm htie
      hdelta_half hdelta0 hPbound hdelta hgrad sigma x
  have hNadd : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q + R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [covGrad_add, SmoothCcTensor.toSection_add]
    exact riemannianFiberNormSq_add_le
      (I := I) (M := M) g 0 5 x _ _
  have hNsub : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q - R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [covGrad_sub, SmoothCcTensor.toSection_sub]
    exact riemannianFiberNormSq_sub_le
      (I := I) (M := M) g 0 5 x _ _
  have hNsmul : ∀ (a : Real) (Q : SmoothCcTensor g 0 4),
      N (a • Q) = a ^ 2 * N Q := by
    intro a Q
    dsimp only [N]
    rw [covGrad_smul, SmoothCcTensor.toSection_smul,
      riemannianFiberNormSq_smul]
  have hkernel : ∀ qq : Fin 4 → Equiv.Perm (Fin 4),
      N (edgeKernelPartner (I := I) (M := M) g gm T qq) ≤ 4 * B := by
    intro qq
    let Q0 := edgePairPartner (I := I) (M := M) g gm T (qq 0)
    let Q1 := edgePairPartner (I := I) (M := M) g gm T (qq 1)
    let Q2 := edgePairPartner (I := I) (M := M) g gm T (qq 2)
    let Q3 := edgePairPartner (I := I) (M := M) g gm T (qq 3)
    have h01 : N (Q0 + Q1) ≤ 4 * B := by
      calc
        N (Q0 + Q1) ≤ 2 * N Q0 + 2 * N Q1 := hNadd Q0 Q1
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (qq 0)) (by norm_num))
          (mul_le_mul_of_nonneg_left (hpair (qq 1)) (by norm_num))
        _ = 4 * B := by ring
    have h23 : N (Q2 + Q3) ≤ 4 * B := by
      calc
        N (Q2 + Q3) ≤ 2 * N Q2 + 2 * N Q3 := hNadd Q2 Q3
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (qq 2)) (by norm_num))
          (mul_le_mul_of_nonneg_left (hpair (qq 3)) (by norm_num))
        _ = 4 * B := by ring
    have hdiff : N ((Q0 + Q1) - (Q2 + Q3)) ≤ 16 * B := by
      calc
        N ((Q0 + Q1) - (Q2 + Q3)) ≤
            2 * N (Q0 + Q1) + 2 * N (Q2 + Q3) := hNsub _ _
        _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
          (mul_le_mul_of_nonneg_left h01 (by norm_num))
          (mul_le_mul_of_nonneg_left h23 (by norm_num))
        _ = 16 * B := by ring
    have heq : Q0 + Q1 - Q2 - Q3 = (Q0 + Q1) - (Q2 + Q3) := by abel
    rw [edgeKernelPartner]
    change N ((1 / 2 : Real) • (Q0 + Q1 - Q2 - Q3)) ≤ _
    rw [hNsmul, heq]
    norm_num
    linarith
  have hriem : N (edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ
      qA qB s) ≤ 4 * B := by
    let KA := edgeKernelPartner (I := I) (M := M) g gm T qA
    let KB := edgeKernelPartner (I := I) (M := M) g gm T qB
    have hab : N (KA + KB) ≤ 16 * B := by
      calc
        N (KA + KB) ≤ 2 * N KA + 2 * N KB := hNadd KA KB
        _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
          (mul_le_mul_of_nonneg_left (hkernel qA) (by norm_num))
          (mul_le_mul_of_nonneg_left (hkernel qB) (by norm_num))
        _ = 16 * B := by ring
    rw [edgeRiemPartner]
    change N (s • ((1 / 2 : Real) • (KA + KB))) ≤ _
    rw [hNsmul, hNsmul]
    norm_num
    nlinarith
  have hlieTerm : ∀ i : Fin 3,
      N (epsilon i • ((1 / 2 : Real) •
        (edgePairPartner (I := I) (M := M) g gm T (q i) +
          edgePairPartner (I := I) (M := M) g gm T
            ((q i).trans (Equiv.swap (0 : Fin 4) 1))))) ≤ B := by
    intro i
    let QA := edgePairPartner (I := I) (M := M) g gm T (q i)
    let QB := edgePairPartner (I := I) (M := M) g gm T
      ((q i).trans (Equiv.swap (0 : Fin 4) 1))
    have hab : N (QA + QB) ≤ 4 * B := by
      calc
        N (QA + QB) ≤ 2 * N QA + 2 * N QB := hNadd QA QB
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (hpair (q i)) (by norm_num))
          (mul_le_mul_of_nonneg_left
            (hpair ((q i).trans (Equiv.swap (0 : Fin 4) 1))) (by norm_num))
        _ = 4 * B := by ring
    have heps2 : (epsilon i) ^ 2 ≤ 1 := by
      have hi := (abs_le.mp (hepsilon i))
      have hprod : 0 ≤ (1 - epsilon i) * (1 + epsilon i) :=
        mul_nonneg (sub_nonneg.mpr hi.2) (by linarith [hi.1])
      nlinarith
    change N (epsilon i • ((1 / 2 : Real) • (QA + QB))) ≤ B
    rw [hNsmul, hNsmul]
    norm_num
    nlinarith
  have hlie : N (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ
      q epsilon s) ≤ 10 * B := by
    let L0 : SmoothCcTensor g 0 4 := epsilon 0 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 0) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 0).trans (Equiv.swap (0 : Fin 4) 1))))
    let L1 : SmoothCcTensor g 0 4 := epsilon 1 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 1) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 1).trans (Equiv.swap (0 : Fin 4) 1))))
    let L2 : SmoothCcTensor g 0 4 := epsilon 2 • ((1 / 2 : Real) •
      (edgePairPartner (I := I) (M := M) g gm T (q 2) +
        edgePairPartner (I := I) (M := M) g gm T
          ((q 2).trans (Equiv.swap (0 : Fin 4) 1))))
    have h01 : N (L0 + L1) ≤ 4 * B := by
      calc
        N (L0 + L1) ≤ 2 * N L0 + 2 * N L1 := hNadd L0 L1
        _ ≤ 2 * B + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left (by simpa only [L0] using hlieTerm 0) (by norm_num))
          (mul_le_mul_of_nonneg_left (by simpa only [L1] using hlieTerm 1) (by norm_num))
        _ = 4 * B := by ring
    have h012 : N (L0 + L1 + L2) ≤ 10 * B := by
      calc
        N (L0 + L1 + L2) ≤ 2 * N (L0 + L1) + 2 * N L2 := hNadd _ _
        _ ≤ 2 * (4 * B) + 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left h01 (by norm_num))
          (mul_le_mul_of_nonneg_left (by simpa only [L2] using hlieTerm 2) (by norm_num))
        _ = 10 * B := by ring
    rw [edgeLiePartner, Fin.sum_univ_three]
    change N (s • (L0 + L1 + L2)) ≤ _
    rw [hNsmul]
    exact (mul_le_mul_of_nonneg_left h012 (sq_nonneg s)).trans (by
      nlinarith)
  have htop : N (edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
      qA qB q epsilon s) ≤ 52 * B := by
    rw [edgeTopPartner]
    have hadd := hNadd
      ((2 : Real) • edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ qA qB s)
      (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
    rw [hNsmul] at hadd
    norm_num at hadd
    calc
      _ ≤ 2 * (4 * N (edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ
            qA qB s)) +
          2 * N (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ
            q epsilon s) := hadd
      _ ≤ 2 * (4 * (4 * B)) + 2 * (10 * B) := add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hriem (by norm_num)) (by norm_num))
        (mul_le_mul_of_nonneg_left hlie (by norm_num))
      _ = 52 * B := by ring
  simpa only [N, B, C, T1] using htop

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
