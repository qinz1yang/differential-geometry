import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePartnerBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder0KernelJetGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound

/-!
# Closed-edge bound for the order-one Ricci arm

The order-one connection-difference coefficient is linear in the connection
difference.  At the closed edge this is exactly the structure needed for an
`O(delta) * ||nabla W||^2` energy bound: the coefficient contributes one
factor of `nabla P`, its input is `nabla W`, and the outer pairing contributes
the small undifferentiated `W`.

The canonical order-one tame-envelope file proves the relevant five-arm
kernel expansion only as a private implementation lemma.  This file reproves
that finite algebra locally, exports the pointwise kernel and coefficient
bounds needed at the energy boundary, and then specializes to the genuine
segment `P = s W`.  No `H2` or higher jet of the edge tensor is used.
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

private lemma one_symm_eq (g : SmoothRiemannianMetric I M)
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

/-! ## The five-arm kernel split -/

private def oneOut0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def oneOut0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def oneOut2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def oneOut1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def oneOut1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def oneIn102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def oneIn120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private theorem onePerm_smooth
    (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝒘(Real, Tensor0SBundle.TensorRSModel d d Real E)) ∞
      (fun x : M => TotalSpace.mk'
        (Tensor0SBundle.TensorRSModel d d Real E)
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
  have h := slotPermCLM_field_contMDiff
    (I := I) rho (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk'
    (Tensor0SBundle.Tensor0SModel d Real E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

private def onePerm
    (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) : SmoothCcTensor g d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) rho x)
      contMDiff_toFun := onePerm_smooth (I := I) (M := M) g rho }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private def oneArm0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 4 :=
  reindexCoeffGen (I := I) (M := M) g 3 4
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g oneOut0312)
      (connDiffContrInsertionField (I := I) g gm)) oneIn102

private def oneArm1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 4 :=
  reindexCoeffGen (I := I) (M := M) g 3 4
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g oneOut0213)
      (connDiffContrInsertionField (I := I) g gm)) oneIn120

private def oneArm2 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 4 4
    (onePerm (I := I) (M := M) g oneOut2301)
    (connDiffContrInsertionField (I := I) g gm)

private def oneArm3 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 4 :=
  reindexCoeffGen (I := I) (M := M) g 3 4
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g oneOut1302)
      (connDiffContrInsertionField (I := I) g gm)) oneIn102

private def oneArm4 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 4 :=
  reindexCoeffGen (I := I) (M := M) g 3 4
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g oneOut1203)
      (connDiffContrInsertionField (I := I) g gm)) oneIn120

private theorem oneKer_split
    (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g gm =
      -(oneArm0 (I := I) (M := M) g gm +
        oneArm1 (I := I) (M := M) g gm +
        oneArm2 (I := I) (M := M) g gm +
        oneArm3 (I := I) (M := M) g gm +
        oneArm4 (I := I) (M := M) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem oneArm_rfns
    (g gm : SmoothRiemannianMetric I M)
    (sigma : Equiv.Perm (Fin 4)) (q : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (appCcRS (I := I) (M := M) g 3 4 4
            (onePerm (I := I) (M := M) g sigma)
            (connDiffContrInsertionField (I := I) g gm))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (connDiffContrInsertionField (I := I) g gm)).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g 3 4 sigma
    (connDiffContrInsertionField (I := I) g gm)
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g sigma)
      (connDiffContrInsertionField (I := I) g gm))
    (fun y d => ?_) q x
  have hy :
      (show Tensor0SBundle.Tensor0SSpace 3 I y →L[Real]
          Tensor0SBundle.Tensor0SSpace 4 I y from
        (appCcRS (I := I) (M := M) g 3 4 4
          (onePerm (I := I) (M := M) g sigma)
          (connDiffContrInsertionField (I := I) g gm)).toSection y) d =
        slotPermCLM (I := I) sigma y
          ((show Tensor0SBundle.Tensor0SSpace 3 I y →L[Real]
              Tensor0SBundle.Tensor0SSpace 4 I y from
            (connDiffContrInsertionField (I := I) g gm).toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

private theorem oneFull_rfns
    (g gm : SmoothRiemannianMetric I M)
    (sigma : Equiv.Perm (Fin 4)) (rho : Equiv.Perm (Fin 3))
    (q : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (appCcRS (I := I) (M := M) g 3 4 4
              (onePerm (I := I) (M := M) g sigma)
              (connDiffContrInsertionField (I := I) g gm)) rho)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (connDiffContrInsertionField (I := I) g gm)).toSection x) := by
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq
    (I := I) (M := M) g 3 4
    (appCcRS (I := I) (M := M) g 3 4 4
      (onePerm (I := I) (M := M) g sigma)
      (connDiffContrInsertionField (I := I) g gm)) rho q x]
  exact oneArm_rfns (I := I) (M := M) g gm sigma q x

private theorem one_rfns_neg
    (g : SmoothRiemannianMetric I M) (r s : Nat)
    (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul Real
    (TensorRSSpace.toModel (𝕜 := Real) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

/-- The order-one Ricci kernel is a five-term isometric reindexing of the
twice-slot-extended connection difference. -/
theorem ricci1Ker_rfns
    (g gm : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        ((linearizedRicciConnDiffOrder1KernelField (I := I) g gm).toSection x) ≤
      46 * riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        ((connDiffContrInsertionField (I := I) g gm).toSection x) := by
  let Q : Real := riemannianFiberNormSq (I := I) (M := M) g 3 4 x
    ((connDiffContrInsertionField (I := I) g gm).toSection x)
  let A0 := (oneArm0 (I := I) (M := M) g gm).toSection x
  let A1 := (oneArm1 (I := I) (M := M) g gm).toSection x
  let A2 := (oneArm2 (I := I) (M := M) g gm).toSection x
  let A3 := (oneArm3 (I := I) (M := M) g gm).toSection x
  let A4 := (oneArm4 (I := I) (M := M) g gm).toSection x
  have h0 : riemannianFiberNormSq (I := I) (M := M) g 3 4 x A0 = Q := by
    simpa only [A0, oneArm0, Q, iteratedCovGrad_zero, Nat.add_zero] using
      oneFull_rfns (I := I) (M := M) g gm oneOut0312 oneIn102 0 x
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 3 4 x A1 = Q := by
    simpa only [A1, oneArm1, Q, iteratedCovGrad_zero, Nat.add_zero] using
      oneFull_rfns (I := I) (M := M) g gm oneOut0213 oneIn120 0 x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g 3 4 x A2 = Q := by
    simpa only [A2, oneArm2, Q, iteratedCovGrad_zero, Nat.add_zero] using
      oneArm_rfns (I := I) (M := M) g gm oneOut2301 0 x
  have h3 : riemannianFiberNormSq (I := I) (M := M) g 3 4 x A3 = Q := by
    simpa only [A3, oneArm3, Q, iteratedCovGrad_zero, Nat.add_zero] using
      oneFull_rfns (I := I) (M := M) g gm oneOut1302 oneIn102 0 x
  have h4 : riemannianFiberNormSq (I := I) (M := M) g 3 4 x A4 = Q := by
    simpa only [A4, oneArm4, Q, iteratedCovGrad_zero, Nat.add_zero] using
      oneFull_rfns (I := I) (M := M) g gm oneOut1203 oneIn120 0 x
  have h01 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 3 4 x A0 A1
  have h012 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 3 4 x (A0 + A1) A2
  have h0123 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 3 4 x (A0 + A1 + A2) A3
  have h01234 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 3 4 x (A0 + A1 + A2 + A3) A4
  have hsum : riemannianFiberNormSq (I := I) (M := M) g 3 4 x
      (A0 + A1 + A2 + A3 + A4) ≤ 46 * Q := by
    have h01' : riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        (A0 + A1) ≤ 4 * Q := by linarith
    have h012' : riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        (A0 + A1 + A2) ≤ 10 * Q := by linarith
    have h0123' : riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        (A0 + A1 + A2 + A3) ≤ 22 * Q := by linarith
    linarith
  rw [oneKer_split (I := I) (M := M) g gm,
    SmoothCcTensor.toSection_neg]
  change riemannianFiberNormSq (I := I) (M := M) g 3 4 x
      (-(A0 + A1 + A2 + A3 + A4)) ≤ 46 * Q
  rw [one_rfns_neg (I := I) (M := M) g 3 4 x]
  exact hsum

/-! ## Pointwise coefficient bound -/

private theorem one_insert_rfns
    (g gm : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 4 x
        ((connDiffContrInsertionField (I := I) g gm).toSection x) ≤
      (Module.finrank Real E : Real) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
          ((connDiffSection (I := I) gm g).toSection x) := by
  let A := connDiffSection (I := I) gm g
  let B := slotExtend (I := I) (M := M) g 1 2 A
  have h0 :
      riemannianFiberNormSq (I := I) (M := M) g 3 4 x
          ((connDiffContrInsertionField (I := I) g gm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 3 4 x
          ((slotExtend (I := I) (M := M) g 2 3 B).toSection x) := by
    rw [connDiffContrInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gm]
    simpa only [A, B, iteratedCovGrad_zero, Nat.add_zero] using
      rfns_iteratedCovGrad_reindexCoeffGen_eq
        (I := I) (M := M) g 3 4
        (slotExtend (I := I) (M := M) g 2 3 B) coreInPerm201 0 x
  have houter := rfns_iteratedCovGrad_slotExtend_le
    (I := I) (M := M) g 2 3 B 0 x
  have hinner := rfns_iteratedCovGrad_slotExtend_le
    (I := I) (M := M) g 1 2 A 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero] at houter hinner
  rw [h0]
  calc
    _ ≤ (Module.finrank Real E : Real) *
        riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          (B.toSection x) := houter
    _ ≤ (Module.finrank Real E : Real) *
        ((Module.finrank Real E : Real) *
          riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            (A.toSection x)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (Module.finrank Real E : Real) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
          ((connDiffSection (I := I) gm g).toSection x) := by
      simp only [A]
      ring

/-- The order-one Ricci coefficient is pointwise linear in the first
covariant derivative of the metric perturbation. -/
theorem ricci1Coeff_rfns (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
        (htie : ∀ (y : M) (u v : TangentSpace I y),
          gm.inner y u v = g.inner y u v +
            ccTensorBilinSymm (I := I) g P y u v)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
              ((linearizedRicciConnDiffOrder1CoeffField
                (I := I) (M := M) g gm).toSection x) ≤
            C ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) := by
  classical
  obtain ⟨Ct, hCt0, htrace⟩ :=
    rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g (show (1 / 2 : Real) < 1 by norm_num)
  obtain ⟨Ca, hCa0, hconn⟩ :=
    connDiffSection_riemannianFiberNormSq_le_iteratedCovGrad_of_lt_one
      (I := I) (M := M) g (δ₀ := 1 / 2)
        (show (0 : Real) ≤ 1 / 2 by norm_num)
        (show (1 / 2 : Real) < 1 by norm_num)
  let d : Real := Module.finrank Real E
  let K : Real := Ct 0 * (46 * d ^ 2 * Ca ^ 2)
  have hK0 : 0 ≤ K := by
    dsimp only [K, d]
    exact mul_nonneg (hCt0 0) (by positivity)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro gm P htie delta hdelta hdelta0 hPbound x
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => TensorRSSpace 0 3 I y) :=
    tensorRS_riemannianBundle (I := I) (M := M) g 0 3
  let P1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
  let Ac : Real := riemannianFiberNormSq (I := I) (M := M) g 1 2 x
    ((connDiffSection (I := I) gm g).toSection x)
  let Ai : Real := riemannianFiberNormSq (I := I) (M := M) g 3 4 x
    ((connDiffContrInsertionField (I := I) g gm).toSection x)
  let Kr : Real := riemannianFiberNormSq (I := I) (M := M) g 3 4 x
    ((linearizedRicciConnDiffOrder1KernelField (I := I) g gm).toSection x)
  let Tr : Real := riemannianFiberNormSq (I := I) (M := M) g 4 2 x
    ((ricciCometricFourTraceCastG0 (I := I) g gm).toSection x)
  have hAc : Ac ≤ Ca ^ 2 * P1 := by
    have hraw := hconn gm P hdelta hdelta0 htie hPbound x
    calc
      Ac ≤ Ca ^ 2 *
          ‖((iteratedCovGrad (I := I) g 0 2 1 P).toSection x :
            TensorRSSpace 0 3 I x)‖ ^ 2 := by
        simpa only [Ac] using hraw
      _ = Ca ^ 2 * P1 := by
        have hn := riemannianFiberNormSq_eq_bundle_norm_sq'
          (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
        exact congrArg (fun z : Real => Ca ^ 2 * z) hn.symm
  have hAi : Ai ≤ d ^ 2 * Ac := by
    simpa only [Ai, Ac, d] using
      one_insert_rfns (I := I) (M := M) g gm x
  have hKr : Kr ≤ 46 * Ai := by
    simpa only [Kr, Ai] using ricci1Ker_rfns (I := I) (M := M) g gm x
  have hTr : Tr ≤ Ct 0 := by
    have hraw := htrace gm P htie hdelta hdelta0 hPbound 0 x
    simpa only [Tr, iteratedCovGrad_zero, Nat.add_zero,
      Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero,
      mul_one] using hraw
  have hcomp := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 3 4 2 x
    ((ricciCometricFourTraceCastG0 (I := I) g gm).toSection x)
    ((linearizedRicciConnDiffOrder1KernelField (I := I) g gm).toSection x)
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS,
    appCcRS_toSection]
  calc
    _ ≤ Tr * Kr := by simpa only [Tr, Kr] using hcomp
    _ ≤ Tr * (46 * Ai) :=
      mul_le_mul_of_nonneg_left hKr
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 2 x _)
    _ ≤ Tr * (46 * (d ^ 2 * Ac)) := by
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hAi (by norm_num)) ?_
      exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 2 x _
    _ ≤ (Ct 0) * (46 * (d ^ 2 * Ac)) := by
      exact mul_le_mul_of_nonneg_right hTr
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg d)
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g 1 2 x _)))
    _ ≤ (Ct 0) * (46 * (d ^ 2 * (Ca ^ 2 * P1))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hAc (sq_nonneg d)) (by norm_num))
        (hCt0 0)
    _ = K * P1 := by
      simp only [K]
      ring
    _ = (Real.sqrt K) ^ 2 * P1 := by rw [Real.sq_sqrt hK0]

/-! ## Energy pairing on the genuine segment -/

private theorem onePair_point
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (F : SmoothCcTensor g 3 2)
    {C delta : Real} (hC0 : 0 ≤ C) (hdelta0 : 0 ≤ delta)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (W.toSection x) ≤
        (Module.finrank Real E : Real) ^ 2 * delta ^ 2)
    (hF : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (F.toSection x) ≤
        C ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x))
    (x : M) :
    |tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x)
        ((appCc (I := I) (M := M) g 3 2 F
          (iteratedCovGrad (I := I) g 0 2 1 W)).toFun x)| ≤
      (Module.finrank Real E : Real) * C * delta *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) := by
  classical
  let S := W.toSection x
  let D := (iteratedCovGrad (I := I) g 0 2 1 W).toSection x
  let U := (appCc (I := I) (M := M) g 3 2 F
    (iteratedCovGrad (I := I) g 0 2 1 W)).toSection x
  let d : Real := Module.finrank Real E
  let q : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x D
  have hq0 : 0 ≤ q := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x D
  have hS0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x S ≤
      d ^ 2 * delta ^ 2 := by simpa only [S, d] using hW x
  have hU0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤
      C ^ 2 * q ^ 2 := by
    have happ : riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤
        riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (F.toSection x) * q := by
      dsimp only [U, q, D]
      rw [appCc_toSection]
      exact riemannianFiberNormSq_comp_le_mul
        (I := I) (M := M) g 3 2 x _ _
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (F.toSection x) * q := happ
      _ ≤ (C ^ 2 * q) * q :=
        mul_le_mul_of_nonneg_right (by simpa only [q, D] using hF x) hq0
      _ = C ^ 2 * q ^ 2 := by ring
  have hcs := tensorInnerPointwise_sq_le_mul
    (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)
  have hcs' :
      (tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)) ^ 2 ≤
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x S *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x U := by
    simpa only [riemannianFiberNormSq_eq_tensorInnerPointwise] using hcs
  have hprod :
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤
        (d * C * delta * q) ^ 2 := by
    calc
      _ ≤ (d ^ 2 * delta ^ 2) * (C ^ 2 * q ^ 2) :=
        mul_le_mul hS0 hU0
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x U)
          (by positivity)
      _ = (d * C * delta * q) ^ 2 := by ring
  have hsq := hcs'.trans hprod
  have hrhs0 : 0 ≤ d * C * delta * q := by positivity
  change |tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)| ≤
    d * C * delta * q
  nlinarith [sq_abs (tensorInnerPointwise (I := I) (M := M) g 0 2 x
    (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)),
    abs_nonneg (tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U))]

private lemma one_bound_mono
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

/-- On the genuine closed-edge segment, the order-one Ricci term costs at
most one eighth of the Dirichlet energy. -/
theorem ricci1_path_le (g : SmoothRiemannianMetric I M) :
    ∃ delta0 : Real, 0 < delta0 ∧ delta0 < 1 / 2 ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        {delta s : Real}, 0 ≤ delta → delta ≤ delta0 →
        (hWbound : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        s ∈ Set.Icc (0 : Real) 1 →
        (-2 : Real) * tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (appCc (I := I) (M := M) g 3 2
              (linearizedRicciConnDiffOrder1CoeffField
                (I := I) (M := M) g
                (edgeMetric (I := I) (M := M) g W hWbound s))
              (iteratedCovGrad (I := I) g 0 2 1 W)).toFun ≤
          (1 / 8 : Real) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := by
  classical
  obtain ⟨C0, hC00, hcoeff⟩ := ricci1Coeff_rfns (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let C : Real := d * C0
  let delta0 : Real := 1 / (16 * (1 + C))
  have hC : 0 ≤ C := mul_nonneg (by positivity) hC00
  have hden : 0 < 16 * (1 + C) := by positivity
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact one_div_pos.mpr hden
  have hdelta0half : delta0 < 1 / 2 := by
    dsimp only [delta0]
    apply (div_lt_iff₀ hden).2
    nlinarith
  refine ⟨delta0, hdelta0, hdelta0half, ?_⟩
  intro W hWsymm delta s hdelta0' hdeltaCap hWbound hs
  let P : SmoothCcTensor g 0 2 := s • W
  let gm : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g W hWbound s
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  let F : SmoothCcTensor g 3 2 :=
    linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g gm
  let U : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 3 2 F D
  let mu := riemannianVolumeMeasure (I := I) (M := M) g
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
    one_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hgrad : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection y) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 3 y
          (D.toSection y) := by
    intro y
    rw [show iteratedCovGrad (I := I) g 0 2 1 P = s • D from by
      simp only [P, D, iteratedCovGrad_smul]]
    rw [SmoothCcTensor.toSection_smul, riemannianFiberNormSq_smul]
    exact mul_le_of_le_one_left
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 y _) hs2
  have hFraw := hcoeff gm P htie hdeltaHalf hdelta0' hPbound
  have hF : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (F.toSection x) ≤
        C0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (D.toSection x) := by
    intro x
    calc
      _ ≤ C0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) := by
        simpa only [F, gm] using hFraw x
      _ ≤ C0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (D.toSection x) := mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg C0)
  have hWfix : symmS (I := I) (M := M) g W = W :=
    one_symm_eq (I := I) (M := M) g W hWsymm
  have hWpt := symmC0_rfns_le
    (I := I) (M := M) g W hdelta0' hWbound
  rw [hWfix] at hWpt
  have hpt : ∀ x : M,
      |tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x) (U.toFun x)| ≤
      C * delta * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        (D.toSection x) := by
    intro x
    have h := onePair_point (I := I) (M := M) g W F hC00 hdelta0'
      hWpt hF x
    simpa only [U, D, C, d] using h
  have hcross :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) W U
  have hsqint := integrable_riemannianFiberNormSq_toSection
    (I := I) (M := M) g 0 3 D
  have hrhsint : Integrable
      (fun x => C * delta *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (D.toSection x)) mu := hsqint.const_mul (C * delta)
  have habs :
      |tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U.toFun| ≤
        C * delta * ‖D‖ ^ 2 := by
    unfold tensorL2Inner
    calc
      |∫ x, tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (W.toFun x) (U.toFun x) ∂mu| ≤
        ∫ x, |tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (W.toFun x) (U.toFun x)| ∂mu := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * delta *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ∂mu := integral_mono hcross.abs hrhsint hpt
      _ = C * delta * ∫ x,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ∂mu := by rw [integral_const_mul]
      _ = C * delta * ‖D‖ ^ 2 := by
        have hnorm :=
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
            (I := I) (M := M) g 0 3 D
        simpa only [SmoothCcTensor.norm_def] using
          congrArg (fun z : Real => C * delta * z) hnorm.symm
  have hsmall : 2 * C * delta ≤ 1 / 8 := by
    calc
      2 * C * delta ≤ 2 * C * delta0 :=
        mul_le_mul_of_nonneg_left hdeltaCap (mul_nonneg (by norm_num) hC)
      _ = C / (8 * (1 + C)) := by
        dsimp only [delta0]
        ring
      _ ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : Real) < 8 * (1 + C))).2
        nlinarith
  dsimp only [U, F, gm, D] at habs ⊢
  calc
    (-2 : Real) * tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 3 2
          (linearizedRicciConnDiffOrder1CoeffField
            (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hWbound s))
          (iteratedCovGrad (I := I) g 0 2 1 W)).toFun ≤
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 3 2
          (linearizedRicciConnDiffOrder1CoeffField
            (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hWbound s))
          (iteratedCovGrad (I := I) g 0 2 1 W)).toFun| := by
        nlinarith [le_abs_self (tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (appCc (I := I) (M := M) g 3 2
            (linearizedRicciConnDiffOrder1CoeffField
              (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hWbound s))
            (iteratedCovGrad (I := I) g 0 2 1 W)).toFun)]
    _ ≤ 2 * (C * delta *
        ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = (2 * C * delta) *
        ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := by ring
    _ ≤ (1 / 8 : Real) *
        ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
