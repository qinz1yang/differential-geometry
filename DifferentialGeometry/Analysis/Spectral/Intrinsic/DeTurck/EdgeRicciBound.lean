import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePartnerBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRicciPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound

/-!
# Closed-edge bounds for the derivative Ricci arm

The order-zero Ricci connection-difference coefficient contains a covariant
derivative of the connection difference.  Estimating that coefficient before
pairing would therefore ask for a second derivative of the metric difference.
`EdgeRicciPairing` instead transfers the derivative to a rank-four partner
which contains only one relative inverse-metric trace.  This file proves the
sharp zeroth- and first-derivative bounds for that partner and converts the
Green identity into a closed-edge energy estimate.

The small factor below comes from the undifferentiated symmetric tensor `W`.
The metric defining the relative inverse is allowed to be `g + P`, with only
`|nabla P| <= |nabla W|`; this is the form needed on the genuine segment
`P = s W`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Tensor0SBundle
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

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private lemma ric_symm_eq (g : SmoothRiemannianMetric I M)
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

private lemma ric_app_le (g : SmoothRiemannianMetric I M)
    (r s : Nat) (Phi : SmoothCcTensor g r s)
    (W : SmoothCcTensor g 0 r) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((appCc (I := I) (M := M) g r s Phi W).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (Phi.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 r x
          (W.toSection x) := by
  rw [appCc_toSection]
  exact riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 0 r s x (Phi.toSection x) (W.toSection x)

private lemma ric_extend2_one (g : SmoothRiemannianMetric I M)
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

private lemma ric_perm_rfns (g : SmoothRiemannianMetric I M)
    {s : Nat} (Q : SmoothCcTensor g 0 s) (sigma : Equiv.Perm (Fin s))
    (j : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j
          (domDomCongrSection (I := I) g sigma Q)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j Q).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g sigma Q j x

private theorem ric_l2_of_rfns
    (g : SmoothRiemannianMetric I M) (ra sa rb sb : Nat)
    (A : SmoothCcTensor g ra sa) (B : SmoothCcTensor g rb sb)
    {c : Real} (hc : 0 ≤ c)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g ra sa x
          (A.toSection x) ≤
        c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g rb sb x
          (B.toSection x)) :
    ‖A‖ ≤ c * ‖B‖ := by
  have hint : Integrable
      (fun x => c ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g rb sb x
          (B.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g rb sb B).const_mul (c ^ 2)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g ra sa A _ hint hpt
  rw [integral_const_mul,
    ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g rb sb B,
    DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm]
    at hsq
  have hright : 0 ≤ c * ‖B‖ := mul_nonneg hc (norm_nonneg B)
  nlinarith [norm_nonneg A]

private theorem ric_perm_norm_le
    (g : SmoothRiemannianMetric I M) {s : Nat}
    (Q : SmoothCcTensor g 0 s) (sigma : Equiv.Perm (Fin s)) (j : Nat) :
    ‖iteratedCovGrad (I := I) g 0 s j
        (domDomCongrSection (I := I) g sigma Q)‖ ≤
      ‖iteratedCovGrad (I := I) g 0 s j Q‖ := by
  apply ric_l2_of_rfns (I := I) (M := M) g 0 (s + j) 0 (s + j)
    (iteratedCovGrad (I := I) g 0 s j
      (domDomCongrSection (I := I) g sigma Q))
    (iteratedCovGrad (I := I) g 0 s j Q) (by norm_num)
  intro x
  simpa only [one_pow, one_mul] using
    (ric_perm_rfns (I := I) (M := M) g Q sigma j x).le

/-! ## Pointwise partner bounds -/

/-- The single-relative-trace Ricci partner and its first covariant
derivative retain the sharp squared small factor.  No derivative above
`nabla W` occurs. -/
theorem ricciPart_bds (g : SmoothRiemannianMetric I M) :
    ∃ C0 C1 : Real, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (htie : ∀ (y : M) (u v : TangentSpace I y),
          gm.inner y u v = g.inner y u v +
            ccTensorBilinSymm (I := I) g P y u v)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x)) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 4 x
              ((ricciDAPart (I := I) (M := M) g gm W).toSection x) ≤
              C0 * delta ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                  (W.toSection x) ∧
            riemannianFiberNormSq (I := I) (M := M) g 0 5 x
              ((covGrad (I := I) (M := M) g 0 4
                (ricciDAPart (I := I) (M := M) g gm W)).toSection x) ≤
              C1 * delta ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                  ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) := by
  classical
  obtain ⟨K, hK0, hslot1⟩ := edgeSlot_one (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let F : Real := (2 * d) ^ 2
  let D0 : Real := K * (d ^ 2 + 1)
  let C0 : Real := 4 * d ^ 4 * F
  let C1 : Real := 8 * d ^ 4 * (D0 + F)
  have hF0 : 0 ≤ F := sq_nonneg _
  have hD00 : 0 ≤ D0 := mul_nonneg hK0 (by positivity)
  have hC00 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hF0
  have hC10 : 0 ≤ C1 := by
    dsimp only [C1]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (add_nonneg hD00 hF0)
  refine ⟨C0, C1, hC00, hC10, ?_⟩
  intro gm P W hWsymm htie delta hdelta hdelta0 hPbound hWbound hgrad x
  let W0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (W.toSection x)
  let W1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x)
  let P1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
  let WR : SmoothCcTensor g 0 2 :=
    edgeSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 W
  let Phi : SmoothCcTensor g 2 4 :=
    slotExtendIter (I := I) (M := M) g 0 2 2 WR
  let Q : SmoothCcTensor g 0 4 :=
    edgeProd4 (I := I) (M := M) g W WR
  let U : SmoothCcTensor g 0 5 :=
    appCc (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) W
  let V : SmoothCcTensor g 0 5 :=
    appCc (I := I) (M := M) g 3 5
      (slotExtend (I := I) (M := M) g 2 4 Phi)
      (covGrad (I := I) (M := M) g 0 2 W)
  have hWfix : symmS (I := I) (M := M) g W = W :=
    ric_symm_eq (I := I) (M := M) g W hWsymm
  have hW0raw := symmC0_rfns_le
    (I := I) (M := M) g W hdelta0 hWbound x
  rw [hWfix] at hW0raw
  have hW0 : W0 ≤ d ^ 2 * delta ^ 2 := by
    simpa only [W0, d] using hW0raw
  have hdeltaOne : delta ≤ 1 := hdelta.trans (by norm_num)
  have hdeltaFac : 0 ≤ (1 - delta) * (1 + delta) :=
    mul_nonneg (sub_nonneg.mpr hdeltaOne) (by linarith [hdelta0])
  have hdeltaSq : delta ^ 2 ≤ 1 := by nlinarith
  have hW0coarse : W0 ≤ d ^ 2 := by
    calc
      W0 ≤ d ^ 2 * delta ^ 2 := hW0
      _ ≤ d ^ 2 * 1 := mul_le_mul_of_nonneg_left hdeltaSq (sq_nonneg d)
      _ = d ^ 2 := mul_one _
  have hW00 : 0 ≤ W0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hW10 : 0 ≤ W1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hP1W1 : P1 ≤ W1 := by
    simpa only [P1, W1] using hgrad x
  have hWR0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (WR.toSection x) ≤ F * W0 := by
    simpa only [WR, F, d, W0] using
      edgeSlot_zero (I := I) (M := M) g gm P htie hdelta hdelta0
        hPbound 0 W x
  have hWR1raw := hslot1 gm P htie hdelta hdelta0 hPbound 0 W x
  have hWR1 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 WR).toSection x) ≤
        D0 * W1 := by
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGrad (I := I) (M := M) g 0 2 WR).toSection x) ≤
          K * (P1 * W0 + W1) := by
      simpa only [WR, P1, W0, W1, iteratedCovGrad_succ,
        iteratedCovGrad_zero] using hWR1raw
    calc
      _ ≤ K * (P1 * W0 + W1) := hraw
      _ ≤ K * (W1 * W0 + W1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ W1) hK0
        exact mul_le_mul_of_nonneg_right hP1W1 hW00
      _ ≤ K * (W1 * d ^ 2 + W1) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hW0coarse hW10) W1
      _ = D0 * W1 := by simp only [D0]; ring
  have hPhi0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (Phi.toSection x) = d ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (WR.toSection x) := by
    simpa only [Phi, d] using
      rfns_slotExtendIter_eq (I := I) (M := M) g 0 2 2 WR x
  have hPhi1 : riemannianFiberNormSq (I := I) (M := M) g 2 5 x
      ((covGrad (I := I) (M := M) g 2 4 Phi).toSection x) =
        d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 WR).toSection x) := by
    simpa only [Phi, d] using
      ric_extend2_one (I := I) (M := M) g WR x
  have hQ0 : riemannianFiberNormSq (I := I) (M := M) g 0 4 x
      (Q.toSection x) ≤ d ^ 4 * F * delta ^ 2 * W0 := by
    have happ := ric_app_le (I := I) (M := M) g 2 4 Phi W x
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 0 4 x
        (Q.toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g 2 4 x
              (Phi.toSection x) * W0 := by
      simpa only [Q, edgeProd4, Phi, W0] using happ
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 2 4 x
            (Phi.toSection x) * W0 := hraw
      _ = (d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (WR.toSection x)) * W0 := by rw [hPhi0]
      _ ≤ (d ^ 2 * (F * W0)) * W0 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWR0 (sq_nonneg d)) hW00
      _ ≤ (d ^ 2 * (F * (d ^ 2 * delta ^ 2))) * W0 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hW0 hF0) (sq_nonneg d)) hW00
      _ = d ^ 4 * F * delta ^ 2 * W0 := by ring
  have hprod : covGrad (I := I) (M := M) g 0 4 Q = U + V := by
    change covGrad (I := I) (M := M) g 0 4
        (appCc (I := I) (M := M) g 2 4 Phi W) =
      appCc (I := I) (M := M) g 2 5
          (covGrad (I := I) (M := M) g 2 4 Phi) W +
        appCc (I := I) (M := M) g 3 5
          (slotExtend (I := I) (M := M) g 2 4 Phi)
          (covGrad (I := I) (M := M) g 0 2 W)
    exact covGrad_appCc_eq (I := I) (M := M) g 2 4 Phi W
  have hU : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      (U.toSection x) ≤ d ^ 4 * D0 * delta ^ 2 * W1 := by
    refine (ric_app_le (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) W x).trans ?_
    rw [hPhi1]
    calc
      d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 WR).toSection x) * W0 ≤
          d ^ 2 * (D0 * W1) * W0 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWR1 (sq_nonneg d)) hW00
      _ ≤ d ^ 2 * (D0 * W1) * (d ^ 2 * delta ^ 2) :=
        mul_le_mul_of_nonneg_left hW0
          (mul_nonneg (sq_nonneg d) (mul_nonneg hD00 hW10))
      _ = d ^ 4 * D0 * delta ^ 2 * W1 := by ring
  have hV : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      (V.toSection x) ≤ d ^ 4 * F * delta ^ 2 * W1 := by
    refine (riemannianFiberNormSq_appCc_slotExtend_le
      (I := I) (M := M) g 2 4 Phi
      (covGrad (I := I) (M := M) g 0 2 W) x).trans ?_
    rw [hPhi0]
    calc
      d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (WR.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 W).toSection x) ≤
          d ^ 2 * (F * W0) * W1 := by
        simpa only [W1, iteratedCovGrad_succ, iteratedCovGrad_zero] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hWR0 (sq_nonneg d)) hW10
      _ ≤ d ^ 2 * (F * (d ^ 2 * delta ^ 2)) * W1 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hW0 hF0) (sq_nonneg d)) hW10
      _ = d ^ 4 * F * delta ^ 2 * W1 := by ring
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      ((covGrad (I := I) (M := M) g 0 4 Q).toSection x) ≤
        2 * d ^ 4 * (D0 + F) * delta ^ 2 * W1 := by
    rw [hprod, SmoothCcTensor.toSection_add]
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 0 5 x (U.toSection x) (V.toSection x)
    calc
      _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x
            (U.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x
            (V.toSection x) := hadd
      _ ≤ 2 * (d ^ 4 * D0 * delta ^ 2 * W1) +
          2 * (d ^ 4 * F * delta ^ 2 * W1) :=
        add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num))
          (mul_le_mul_of_nonneg_left hV (by norm_num))
      _ = 2 * d ^ 4 * (D0 + F) * delta ^ 2 * W1 := by ring
  have hFlux0 : riemannianFiberNormSq (I := I) (M := M) g 0 4 x
      ((ricciDAFlux (I := I) (M := M) g gm W).toSection x) ≤
        C0 * delta ^ 2 * W0 := by
    have hsub := ricciFlux_rfns (I := I) (M := M) g gm W 0 x
    simp only [iteratedCovGrad_zero] at hsub
    have hq := mul_le_mul_of_nonneg_left hQ0 (by norm_num : (0 : Real) ≤ 4)
    calc
      _ ≤ 4 * riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          (Q.toSection x) := by simpa only [Q, WR] using hsub
      _ ≤ 4 * (d ^ 4 * F * delta ^ 2 * W0) := hq
      _ = C0 * delta ^ 2 * W0 := by simp only [C0]; ring
  have hFlux1 : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      ((covGrad (I := I) (M := M) g 0 4
        (ricciDAFlux (I := I) (M := M) g gm W)).toSection x) ≤
        C1 * delta ^ 2 * W1 := by
    have hsub := ricciFlux_rfns (I := I) (M := M) g gm W 1 x
    simp only [iteratedCovGrad_succ, iteratedCovGrad_zero] at hsub
    have hq := mul_le_mul_of_nonneg_left hQ1 (by norm_num : (0 : Real) ≤ 4)
    calc
      _ ≤ 4 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4 Q).toSection x) := by
        simpa only [Q, WR] using hsub
      _ ≤ 4 * (2 * d ^ 4 * (D0 + F) * delta ^ 2 * W1) := hq
      _ = C1 * delta ^ 2 * W1 := by simp only [C1]; ring
  constructor
  · calc
      riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((ricciDAPart (I := I) (M := M) g gm W).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((ricciDAFlux (I := I) (M := M) g gm W).toSection x) := by
            simpa only [iteratedCovGrad_zero] using
              ricciPart_rfns (I := I) (M := M) g gm W 0 x
      _ ≤ C0 * delta ^ 2 * W0 := hFlux0
      _ = _ := by rfl
  · calc
      riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (ricciDAPart (I := I) (M := M) g gm W)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (ricciDAFlux (I := I) (M := M) g gm W)).toSection x) := by
            simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using
              ricciPart_rfns (I := I) (M := M) g gm W 1 x
      _ ≤ C1 * delta ^ 2 * W1 := hFlux1
      _ = _ := by rfl

/-! ## The undifferentiated connection-difference carrier -/

/-- The rotated lowered connection difference in `ricciDA_green` is bounded
in `L2` by one derivative of the metric perturbation. -/
theorem ricciBase_l2 (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
        (htie : ∀ (y : M) (u v : TangentSpace I y),
          gm.inner y u v = g.inner y u v +
            ccTensorBilinSymm (I := I) g P y u v)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        ‖ricciDABase (I := I) (M := M) g gm‖ ≤
          C * ‖iteratedCovGrad (I := I) g 0 2 1 P‖ := by
  obtain ⟨C, hC0, hconn⟩ :=
    connDiffSection_riemannianFiberNormSq_le_iteratedCovGrad_of_lt_one
      (I := I) (M := M) g (δ₀ := 1 / 2)
        (show (0 : Real) ≤ 1 / 2 by norm_num)
        (show (1 / 2 : Real) < 1 by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro gm P htie delta hdelta hdelta0 hPbound
  apply ric_l2_of_rfns (I := I) (M := M) g 0 3 0 3
    (ricciDABase (I := I) (M := M) g gm)
    (iteratedCovGrad (I := I) g 0 2 1 P) hC0
  intro x
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => TensorRSSpace 0 3 I y) :=
    tensorRS_riemannianBundle (I := I) (M := M) g 0 3
  have hraw := hconn gm P hdelta hdelta0 htie hPbound x
  have hbase :
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((ricciDABase (I := I) (M := M) g gm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((connDiffLoweredCc (I := I) g gm).toSection x) := by
    simpa only [ricciDABase, iteratedCovGrad_zero] using
      ric_perm_rfns (I := I) (M := M) g
        (connDiffLoweredCc (I := I) g gm) (finRotate 3) 0 x
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((ricciDABase (I := I) (M := M) g gm).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((connDiffLoweredCc (I := I) g gm).toSection x) := hbase
    _ = riemannianFiberNormSq (I := I) (M := M) g 1 2 x
        ((connDiffSection (I := I) gm g).toSection x) := by
      simpa only [iteratedCovGrad_zero, Nat.add_zero] using
        connLow_rfns (I := I) (M := M) g gm 0 x
    _ ≤ C ^ 2 *
        ‖((iteratedCovGrad (I := I) g 0 2 1 P).toSection x :
          TensorRSSpace 0 3 I x)‖ ^ 2 := hraw
    _ = C ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) := by
      have hn := riemannianFiberNormSq_eq_bundle_norm_sq'
        (I := I) (M := M) g 0 3 x
        ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
      exact congrArg (fun z : Real => C ^ 2 * z) hn.symm

private lemma ric_bound_mono
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {a b : Real} (hab : a ≤ b)
    (ha : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) a) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) b := by
  intro x u v
  exact (ha x u v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-! ## Absorption on the genuine slope segment -/

/-- The exact derivative-only Ricci order-zero term on the realized segment
costs at most one eighth of the Dirichlet energy, plus a fixed multiple of the
`L2` energy.  The factor `-2` is the coefficient with which this arm occurs
inside `edgeRate0`. -/
theorem ricciDA_path_le [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    ∃ delta0 K : Real,
      0 < delta0 ∧ delta0 < 1 / 2 ∧ 0 ≤ K ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        {delta s : Real}, 0 ≤ delta → delta ≤ delta0 →
        (hWbound : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        s ∈ Set.Icc (0 : Real) 1 →
        (-2 : Real) *
            (⟦W, appCc (I := I) (M := M) g 2 2
              (ricciDAArm (I := I) (M := M) g
                (edgeMetric (I := I) (M := M) g W hWbound s)) W⟧_Real : Real) ≤
          (1 / 8 : Real) *
              ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
            K * ‖W‖ ^ 2 := by
  classical
  obtain ⟨C0, C1, hC00, hC10, hpart⟩ :=
    ricciPart_bds (I := I) (M := M) g
  obtain ⟨Cb, hCb0, hbase⟩ := ricciBase_l2 (I := I) (M := M) g
  obtain ⟨Kd, hKd0, hdiv⟩ :=
    exists_iteratedCovGrad_covDivergence_l2_le
      (I := I) (M := M) g 3
  let A0 : Real := Kd 0 * Real.sqrt C0
  let A1 : Real := Kd 0 * Real.sqrt C1
  let G : Real := 2 * Cb * A0
  let Hc : Real := 2 * Cb * A1
  let delta0 : Real := 1 / (16 * (1 + Hc))
  let K : Real := 4 * G ^ 2
  have hA00 : 0 ≤ A0 := mul_nonneg (hKd0 0) (Real.sqrt_nonneg _)
  have hA10 : 0 ≤ A1 := mul_nonneg (hKd0 0) (Real.sqrt_nonneg _)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact mul_nonneg (mul_nonneg (by norm_num) hCb0) hA00
  have hHc0 : 0 ≤ Hc := by
    dsimp only [Hc]
    exact mul_nonneg (mul_nonneg (by norm_num) hCb0) hA10
  have hden : 0 < 16 * (1 + Hc) :=
    mul_pos (by norm_num) (by linarith)
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact one_div_pos.mpr hden
  have hdelta0half : delta0 < 1 / 2 := by
    dsimp only [delta0]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num) (sq_nonneg G)
  refine ⟨delta0, K, hdelta0, hdelta0half, hK0, ?_⟩
  intro W hWsymm delta s hdelta0' hdeltaCap hWbound hs
  let P : SmoothCcTensor g 0 2 := s • W
  let gm : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g W hWbound s
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  let R : SmoothCcTensor g 0 4 :=
    ricciDAPart (I := I) (M := M) g gm W
  let S : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) R
  let Base : SmoothCcTensor g 0 3 :=
    ricciDABase (I := I) (M := M) g gm
  let Adj : SmoothCcTensor g 0 3 :=
    covDivergence (I := I) (M := M) g 3 S
  have hdeltaHalf : delta ≤ 1 / 2 :=
    hdeltaCap.trans hdelta0half.le
  have hdeltaLt : delta < 1 :=
    lt_of_le_of_lt hdeltaHalf (by norm_num)
  have hsSmall : s ∈ realizedSmallSet (δ := delta) (δ' := 0) :=
    Icc_subset_realizedSmallSet hdeltaLt (by norm_num) hs
  have htie : ∀ (y : M) (u v : TangentSpace I y),
      gm.inner y u v = g.inner y u v +
        ccTensorBilinSymm (I := I) g P y u v := by
    intro y u v
    have hpath := realizedFam_inner_of_mem (I := I) (M := M)
      g W 0 hWbound (edgeZeroBound (I := I) (M := M) g)
      hsSmall y u v
    simpa only [gm, edgeMetric, P, convexPerturbation, smul_zero,
      zero_add] using hpath
  have hsabs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - s) * (1 + s) :=
      mul_nonneg (sub_nonneg.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hPraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s W hWbound
  have hrad : |s| * delta ≤ delta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsabs) hdelta0']
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta :=
    ric_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hgrad : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection y) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 W).toSection y) := by
    intro y
    rw [show iteratedCovGrad (I := I) g 0 2 1 P =
        s • iteratedCovGrad (I := I) g 0 2 1 W from by
      simp only [P, iteratedCovGrad_smul]]
    rw [SmoothCcTensor.toSection_smul, riemannianFiberNormSq_smul]
    exact mul_le_of_le_one_left
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 y _) hs2
  have hPnorm : ‖iteratedCovGrad (I := I) g 0 2 1 P‖ = s * ‖D‖ := by
    simp only [P, iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1, D]
  have hpt := hpart gm P W hWsymm htie hdeltaHalf hdelta0'
    hPbound hWbound hgrad
  have hR0 : ‖R‖ ≤ Real.sqrt C0 * delta * ‖W‖ := by
    apply ric_l2_of_rfns (I := I) (M := M) g 0 4 0 2 R W
      (mul_nonneg (Real.sqrt_nonneg _) hdelta0')
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          (R.toSection x) ≤
        C0 * delta ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (W.toSection x) := by
        simpa only [R] using (hpt x).1
      _ = (Real.sqrt C0 * delta) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (W.toSection x) := by
        rw [mul_pow, Real.sq_sqrt hC00]
  have hR1 : ‖covGrad (I := I) (M := M) g 0 4 R‖ ≤
      Real.sqrt C1 * delta * ‖D‖ := by
    apply ric_l2_of_rfns (I := I) (M := M) g 0 5 0 3
      (covGrad (I := I) (M := M) g 0 4 R) D
      (mul_nonneg (Real.sqrt_nonneg _) hdelta0')
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4 R).toSection x) ≤
        C1 * delta ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) := by
        simpa only [R, D] using (hpt x).2
      _ = (Real.sqrt C1 * delta) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) := by
        rw [mul_pow, Real.sq_sqrt hC10]
  have hS0 : ‖S‖ ≤ ‖R‖ := by
    simpa only [S, iteratedCovGrad_zero] using
      ric_perm_norm_le (I := I) (M := M) g R
        (Equiv.swap (0 : Fin 4) 1) 0
  have hS1 : ‖covGrad (I := I) (M := M) g 0 4 S‖ ≤
      ‖covGrad (I := I) (M := M) g 0 4 R‖ := by
    simpa only [S, iteratedCovGrad_succ, iteratedCovGrad_zero] using
      ric_perm_norm_le (I := I) (M := M) g R
        (Equiv.swap (0 : Fin 4) 1) 1
  have hsum :
      (∑ k ∈ Finset.range (0 + 2),
          ‖iteratedCovGrad (I := I) g 0 4 k S‖) =
        ‖S‖ + ‖covGrad (I := I) (M := M) g 0 4 S‖ := by
    norm_num [Finset.sum_range_succ]
  have hAdj0 : ‖Adj‖ ≤
      Kd 0 * (‖S‖ + ‖covGrad (I := I) (M := M) g 0 4 S‖) := by
    have h := hdiv 0 S
    simp only [iteratedCovGrad_zero] at h
    rw [hsum] at h
    simpa only [Adj] using h
  have hAdj1 : ‖Adj‖ ≤
      A0 * delta * ‖W‖ + A1 * delta * ‖D‖ := by
    calc
      ‖Adj‖ ≤ Kd 0 *
          (‖S‖ + ‖covGrad (I := I) (M := M) g 0 4 S‖) := hAdj0
      _ ≤ Kd 0 * (‖R‖ +
          ‖covGrad (I := I) (M := M) g 0 4 R‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hS0 hS1) (hKd0 0)
      _ ≤ Kd 0 * ((Real.sqrt C0 * delta * ‖W‖) +
          (Real.sqrt C1 * delta * ‖D‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hR0 hR1) (hKd0 0)
      _ = A0 * delta * ‖W‖ + A1 * delta * ‖D‖ := by
        dsimp only [A0, A1]
        ring
  have hBase0 : ‖Base‖ ≤ Cb * ‖D‖ := by
    have hraw := hbase gm P htie hdeltaHalf hdelta0' hPbound
    calc
      ‖Base‖ ≤ Cb *
          ‖iteratedCovGrad (I := I) g 0 2 1 P‖ := by
        simpa only [Base] using hraw
      _ = Cb * (s * ‖D‖) := by rw [hPnorm]
      _ ≤ Cb * (1 * ‖D‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg D)) hCb0
      _ = Cb * ‖D‖ := by ring
  have hgreen :
      (⟦W, appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W⟧_Real : Real) =
        -⟦Adj, Base⟧_Real := by
    change tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g gm) W).toFun =
      -tensorL2Inner (I := I) (M := M) g 0 3 Adj.toFun Base.toFun
    simpa only [Adj, S, R, Base, ricciDAAdj] using
      ricciDA_green (I := I) (M := M) g gm W hWsymm
  have hAdjRhs0 : 0 ≤
      A0 * delta * ‖W‖ + A1 * delta * ‖D‖ :=
    add_nonneg
      (mul_nonneg (mul_nonneg hA00 hdelta0') (norm_nonneg W))
      (mul_nonneg (mul_nonneg hA10 hdelta0') (norm_nonneg D))
  have hprod : ‖Adj‖ * ‖Base‖ ≤
      (A0 * delta * ‖W‖ + A1 * delta * ‖D‖) *
        (Cb * ‖D‖) :=
    mul_le_mul hAdj1 hBase0 (norm_nonneg Base) hAdjRhs0
  have hpair :
      (-2 : Real) *
          (⟦W, appCc (I := I) (M := M) g 2 2
            (ricciDAArm (I := I) (M := M) g gm) W⟧_Real : Real) ≤
        G * delta * ‖W‖ * ‖D‖ +
          Hc * delta * ‖D‖ ^ 2 := by
    calc
      (-2 : Real) *
          (⟦W, appCc (I := I) (M := M) g 2 2
            (ricciDAArm (I := I) (M := M) g gm) W⟧_Real : Real) =
        2 * ⟦Adj, Base⟧_Real := by rw [hgreen]; ring
      _ ≤ 2 * |⟦Adj, Base⟧_Real| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ ≤ 2 * (‖Adj‖ * ‖Base‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm Adj Base)
          (by norm_num)
      _ ≤ 2 * ((A0 * delta * ‖W‖ + A1 * delta * ‖D‖) *
          (Cb * ‖D‖)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = G * delta * ‖W‖ * ‖D‖ +
          Hc * delta * ‖D‖ ^ 2 := by
        dsimp only [G, Hc]
        ring
  have hHdelta : Hc * delta ≤ 1 / 16 := by
    calc
      Hc * delta ≤ Hc * delta0 :=
        mul_le_mul_of_nonneg_left hdeltaCap hHc0
      _ = Hc / (16 * (1 + Hc)) := by
        dsimp only [delta0]
        ring
      _ ≤ 1 / 16 := by
        apply (div_le_iff₀ hden).2
        nlinarith
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hdeltaFac : 0 ≤ (1 - delta) * (1 + delta) :=
    mul_nonneg (sub_nonneg.mpr hdeltaOne) (by linarith [hdelta0'])
  have hdeltaSq : delta ^ 2 ≤ 1 := by nlinarith
  have hcross : G * delta * ‖W‖ * ‖D‖ ≤
      (1 / 16 : Real) * ‖D‖ ^ 2 +
        4 * G ^ 2 * delta ^ 2 * ‖W‖ ^ 2 := by
    nlinarith [sq_nonneg (‖D‖ - 8 * (G * delta * ‖W‖))]
  have hgradTerm : Hc * delta * ‖D‖ ^ 2 ≤
      (1 / 16 : Real) * ‖D‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hHdelta (sq_nonneg ‖D‖)
  have hzeroTerm : 4 * G ^ 2 * delta ^ 2 * ‖W‖ ^ 2 ≤
      K * ‖W‖ ^ 2 := by
    dsimp only [K]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg ‖W‖)
    calc
      4 * G ^ 2 * delta ^ 2 ≤ 4 * G ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hdeltaSq (by positivity)
      _ = 4 * G ^ 2 := by ring
  dsimp only [gm, D] at hpair hcross hgradTerm ⊢
  calc
    (-2 : Real) *
        (⟦W, appCc (I := I) (M := M) g 2 2
          (ricciDAArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hWbound s)) W⟧_Real : Real) ≤
      G * delta * ‖W‖ *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ +
        Hc * delta * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := hpair
    _ ≤ ((1 / 16 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        4 * G ^ 2 * delta ^ 2 * ‖W‖ ^ 2) +
          (1 / 16 : Real) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 :=
      add_le_add hcross hgradTerm
    _ ≤ (1 / 8 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        K * ‖W‖ ^ 2 := by linarith

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
