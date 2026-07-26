import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePartnerBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRicciPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound

/-!
# Closed-edge bound for the quadratic Ricci arm

The order-zero Ricci connection-difference coefficient splits into a part
quadratic in the connection difference and a derivative part.  The latter is
handled by `EdgeRicciBound`.  This file treats the quadratic part directly.

On the genuine segment `g + s W`, the connection difference is pointwise
linear in `nabla (s W)`.  Consequently the quadratic coefficient is bounded
by `|nabla W|^2`; the energy pairing supplies two undifferentiated copies of
`W`, hence a shrinkable `delta^2 |nabla W|^2` contribution.  The final theorem
accepts an arbitrary positive energy budget.
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

private lemma aa_symm_eq (g : SmoothRiemannianMetric I M)
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

/-! ## Local names for the six public-kernel arms -/

private def aaPerm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def aaPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def aaPerm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def aaPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def aaPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def aaPerm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def aaPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def aaPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private def aaQuad0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm3201)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g aaPerm102)
        (connDiffContrInsertionInnerField (I := I) g gm)))

private def aaQuad1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm2301)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g aaPerm102)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private def aaQuad2 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm3102)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g aaPerm120)
        (connDiffContrInsertionInnerField (I := I) g gm)))

private def aaQuad3 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm1302)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (connDiffContrInsertionInnerField (I := I) g gm)))
    innerCoreInPerm10

private def aaQuad4 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm1203)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (connDiffContrInsertionInnerField (I := I) g gm))

private def aaQuad5 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g aaPerm2103)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g aaPerm120)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private theorem aaKer_split (g gm : SmoothRiemannianMetric I M) :
    ricciAAKer (I := I) (M := M) g gm =
      aaQuad0 (I := I) (M := M) g gm +
        aaQuad1 (I := I) (M := M) g gm +
        aaQuad2 (I := I) (M := M) g gm +
        aaQuad3 (I := I) (M := M) g gm +
        aaQuad4 (I := I) (M := M) g gm +
        aaQuad5 (I := I) (M := M) g gm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem aa_out_rfns
    (g : SmoothRiemannianMetric I M) {r d : Nat}
    (rho : Equiv.Perm (Fin d)) (Q : SmoothCcTensor g r d) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r d x
        ((appCcRS (I := I) (M := M) g r d d
          (permCoeff (I := I) (M := M) g rho) Q).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r d x
        (Q.toSection x) := by
  have h := rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r d rho Q
    (appCcRS (I := I) (M := M) g r d d
      (permCoeff (I := I) (M := M) g rho) Q)
    (fun y q => by
      have hy : (show Tensor0SSpace r I y →L[Real] Tensor0SSpace d I y from
          (appCcRS (I := I) (M := M) g r d d
            (permCoeff (I := I) (M := M) g rho) Q).toSection y) q =
        slotPermCLM (I := I) rho y
          ((show Tensor0SSpace r I y →L[Real] Tensor0SSpace d I y from
            Q.toSection y) q) := rfl
      rw [hy, slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]) 0 x
  simpa only [iteratedCovGrad_zero, Nat.add_zero] using h

private theorem aa_in_rfns
    (g : SmoothRiemannianMetric I M) {r s : Nat}
    (Q : SmoothCcTensor g r s) (rho : Equiv.Perm (Fin r)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        ((reindexCoeffGen (I := I) (M := M) g r s Q rho).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (Q.toSection x) := by
  simpa only [iteratedCovGrad_zero, Nat.add_zero] using
    rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g r s Q rho 0 x

private theorem aa_inner_le
    (g gm : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 3 x
        ((connDiffContrInsertionInnerField (I := I) g gm).toSection x) ≤
      (Module.finrank Real E : Real) *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
          ((connDiffSection (I := I) gm g).toSection x) := by
  let A := connDiffSection (I := I) gm g
  have h0 :
      riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          ((connDiffContrInsertionInnerField (I := I) g gm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          ((slotExtend (I := I) (M := M) g 1 2 A).toSection x) := by
    rw [connDiffContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gm]
    exact aa_in_rfns (I := I) (M := M) g
      (slotExtend (I := I) (M := M) g 1 2 A) innerCoreInPerm10 x
  rw [h0]
  simpa only [A, iteratedCovGrad_zero, Nat.add_zero] using
    rfns_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g 1 2 A 0 x

private theorem aa_outer_le
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
    exact aa_in_rfns (I := I) (M := M) g
      (slotExtend (I := I) (M := M) g 2 3 B) coreInPerm201 x
  have hout := rfns_iteratedCovGrad_slotExtend_le
    (I := I) (M := M) g 2 3 B 0 x
  have hin := rfns_iteratedCovGrad_slotExtend_le
    (I := I) (M := M) g 1 2 A 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero] at hout hin
  rw [h0]
  calc
    _ ≤ (Module.finrank Real E : Real) *
        riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          (B.toSection x) := hout
    _ ≤ (Module.finrank Real E : Real) *
        ((Module.finrank Real E : Real) *
          riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            (A.toSection x)) :=
      mul_le_mul_of_nonneg_left hin (by positivity)
    _ = (Module.finrank Real E : Real) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
          ((connDiffSection (I := I) gm g).toSection x) := by
      simp only [A]
      ring

private theorem aa_mid_le
    (g gm : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 2 3)
    (hQ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          (Q.toSection x) ≤
        (Module.finrank Real E : Real) *
          riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            ((connDiffSection (I := I) gm g).toSection x))
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        ((appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gm) Q).toSection x) ≤
      (Module.finrank Real E : Real) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            ((connDiffSection (I := I) gm g).toSection x) ^ 2 := by
  let d : Real := Module.finrank Real E
  let A : Real := riemannianFiberNormSq (I := I) (M := M) g 1 2 x
    ((connDiffSection (I := I) gm g).toSection x)
  have hA0 : 0 ≤ A := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 1 2 x _
  have hout : riemannianFiberNormSq (I := I) (M := M) g 3 4 x
      ((connDiffContrInsertionField (I := I) g gm).toSection x) ≤
      d ^ 2 * A := by
    simpa only [d, A] using aa_outer_le (I := I) (M := M) g gm x
  have hin : riemannianFiberNormSq (I := I) (M := M) g 2 3 x
      (Q.toSection x) ≤ d * A := by
    simpa only [d, A] using hQ x
  rw [appCcRS_toSection]
  calc
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g 3 4 x
          ((connDiffContrInsertionField (I := I) g gm).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 2 3 x
          (Q.toSection x) :=
      riemannianFiberNormSq_compRS_le_mul
        (I := I) (M := M) g 2 3 4 x _ _
    _ ≤ (d ^ 2 * A) * (d * A) :=
      mul_le_mul hout hin
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 2 3 x _)
        (mul_nonneg (sq_nonneg d) hA0)
    _ = (Module.finrank Real E : Real) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            ((connDiffSection (I := I) gm g).toSection x) ^ 2 := by
      simp only [d, A]
      ring

private theorem aa_quad_le
    (g gm : SmoothRiemannianMetric I M)
    (rho : Equiv.Perm (Fin 3)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        ((appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gm)
          (appCcRS (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g rho)
            (connDiffContrInsertionInnerField (I := I) g gm))).toSection x) ≤
      (Module.finrank Real E : Real) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            ((connDiffSection (I := I) gm g).toSection x) ^ 2 := by
  apply aa_mid_le (I := I) (M := M) g gm _ _ x
  intro y
  rw [aa_out_rfns (I := I) (M := M) g rho
    (connDiffContrInsertionInnerField (I := I) g gm) y]
  exact aa_inner_le (I := I) (M := M) g gm y

/-! ## Quadratic-kernel and coefficient bounds -/

/-- The six quadratic Ricci arms are bounded by the square of the
connection-difference fibre norm. -/
theorem ricciAAKer_rfns
    (g gm : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        ((ricciAAKer (I := I) (M := M) g gm).toSection x) ≤
      94 * (Module.finrank Real E : Real) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g 1 2 x
            ((connDiffSection (I := I) gm g).toSection x) ^ 2 := by
  let Q : Real := (Module.finrank Real E : Real) ^ 3 *
    riemannianFiberNormSq (I := I) (M := M) g 1 2 x
      ((connDiffSection (I := I) gm g).toSection x) ^ 2
  let A0 := (aaQuad0 (I := I) (M := M) g gm).toSection x
  let A1 := (aaQuad1 (I := I) (M := M) g gm).toSection x
  let A2 := (aaQuad2 (I := I) (M := M) g gm).toSection x
  let A3 := (aaQuad3 (I := I) (M := M) g gm).toSection x
  let A4 := (aaQuad4 (I := I) (M := M) g gm).toSection x
  let A5 := (aaQuad5 (I := I) (M := M) g gm).toSection x
  have hplain := aa_mid_le (I := I) (M := M) g gm
    (connDiffContrInsertionInnerField (I := I) g gm)
    (aa_inner_le (I := I) (M := M) g gm) x
  have h0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A0 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A0 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm)
            (appCcRS (I := I) (M := M) g 2 3 3
              (permCoeff (I := I) (M := M) g aaPerm102)
              (connDiffContrInsertionInnerField (I := I) g gm))).toSection x) by
          exact aa_out_rfns (I := I) (M := M) g aaPerm3201 _ x]
    simpa only [Q] using aa_quad_le (I := I) (M := M) g gm aaPerm102 x
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A1 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A1 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 4 4
            (permCoeff (I := I) (M := M) g aaPerm2301)
            (appCcRS (I := I) (M := M) g 2 3 4
              (connDiffContrInsertionField (I := I) g gm)
              (appCcRS (I := I) (M := M) g 2 3 3
                (permCoeff (I := I) (M := M) g aaPerm102)
                (connDiffContrInsertionInnerField (I := I) g gm)))).toSection x) by
          exact aa_in_rfns (I := I) (M := M) g _ innerCoreInPerm10 x]
    rw [aa_out_rfns (I := I) (M := M) g aaPerm2301]
    simpa only [Q] using aa_quad_le (I := I) (M := M) g gm aaPerm102 x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A2 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A2 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm)
            (appCcRS (I := I) (M := M) g 2 3 3
              (permCoeff (I := I) (M := M) g aaPerm120)
              (connDiffContrInsertionInnerField (I := I) g gm))).toSection x) by
          exact aa_out_rfns (I := I) (M := M) g aaPerm3102 _ x]
    simpa only [Q] using aa_quad_le (I := I) (M := M) g gm aaPerm120 x
  have h3 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A3 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A3 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 4 4
            (permCoeff (I := I) (M := M) g aaPerm1302)
            (appCcRS (I := I) (M := M) g 2 3 4
              (connDiffContrInsertionField (I := I) g gm)
              (connDiffContrInsertionInnerField (I := I) g gm))).toSection x) by
          exact aa_in_rfns (I := I) (M := M) g _ innerCoreInPerm10 x]
    rw [aa_out_rfns (I := I) (M := M) g aaPerm1302]
    simpa only [Q] using hplain
  have h4 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A4 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A4 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm)
            (connDiffContrInsertionInnerField (I := I) g gm)).toSection x) by
          exact aa_out_rfns (I := I) (M := M) g aaPerm1203 _ x]
    simpa only [Q] using hplain
  have h5 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x A5 ≤ Q := by
    rw [show riemannianFiberNormSq (I := I) (M := M) g 2 4 x A5 =
        riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((appCcRS (I := I) (M := M) g 2 4 4
            (permCoeff (I := I) (M := M) g aaPerm2103)
            (appCcRS (I := I) (M := M) g 2 3 4
              (connDiffContrInsertionField (I := I) g gm)
              (appCcRS (I := I) (M := M) g 2 3 3
                (permCoeff (I := I) (M := M) g aaPerm120)
                (connDiffContrInsertionInnerField (I := I) g gm)))).toSection x) by
          exact aa_in_rfns (I := I) (M := M) g _ innerCoreInPerm10 x]
    rw [aa_out_rfns (I := I) (M := M) g aaPerm2103]
    simpa only [Q] using aa_quad_le (I := I) (M := M) g gm aaPerm120 x
  have h01 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 2 4 x A0 A1
  have h012 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 2 4 x (A0 + A1) A2
  have h0123 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 2 4 x (A0 + A1 + A2) A3
  have h01234 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 2 4 x (A0 + A1 + A2 + A3) A4
  have h012345 := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 2 4 x (A0 + A1 + A2 + A3 + A4) A5
  have hsum : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (A0 + A1 + A2 + A3 + A4 + A5) ≤ 94 * Q := by
    have h01' : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        (A0 + A1) ≤ 4 * Q := by linarith
    have h012' : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        (A0 + A1 + A2) ≤ 10 * Q := by linarith
    have h0123' : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        (A0 + A1 + A2 + A3) ≤ 22 * Q := by linarith
    have h01234' : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
        (A0 + A1 + A2 + A3 + A4) ≤ 46 * Q := by linarith
    linarith
  rw [aaKer_split (I := I) (M := M) g gm]
  change riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (A0 + A1 + A2 + A3 + A4 + A5) ≤ _
  simpa only [Q, mul_assoc] using hsum

/-- The quadratic Ricci coefficient is pointwise quadratic in the first
covariant derivative of the metric perturbation. -/
theorem ricciAACoeff_rfns (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
        (htie : ∀ (y : M) (u v : TangentSpace I y),
          gm.inner y u v = g.inner y u v +
            ccTensorBilinSymm (I := I) g P y u v)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) delta →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
              ((ricciAAArm (I := I) (M := M) g gm).toSection x) ≤
            C ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) ^ 2 := by
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
  let K : Real := Ct 0 * (94 * d ^ 3 * Ca ^ 4)
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
  let Kr : Real := riemannianFiberNormSq (I := I) (M := M) g 2 4 x
    ((ricciAAKer (I := I) (M := M) g gm).toSection x)
  let Tr : Real := riemannianFiberNormSq (I := I) (M := M) g 4 2 x
    ((ricciCometricFourTraceCastG0 (I := I) g gm).toSection x)
  have hP10 : 0 ≤ P1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hAc0 : 0 ≤ Ac := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 1 2 x _
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
  have hAcSq : Ac ^ 2 ≤ (Ca ^ 2 * P1) ^ 2 := by
    nlinarith [sq_nonneg Ac, sq_nonneg (Ca ^ 2 * P1)]
  have hKr : Kr ≤ 94 * d ^ 3 * Ac ^ 2 := by
    simpa only [Kr, Ac, d, mul_assoc] using
      ricciAAKer_rfns (I := I) (M := M) g gm x
  have hTr : Tr ≤ Ct 0 := by
    have hraw := htrace gm P htie hdelta hdelta0 hPbound 0 x
    simpa only [Tr, iteratedCovGrad_zero, Nat.add_zero,
      Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero,
      mul_one] using hraw
  have hcomp := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 2 4 2 x
    ((ricciCometricFourTraceCastG0 (I := I) g gm).toSection x)
    ((ricciAAKer (I := I) (M := M) g gm).toSection x)
  rw [ricciAAArm, appCcRS_toSection]
  calc
    _ ≤ Tr * Kr := by simpa only [Tr, Kr] using hcomp
    _ ≤ Tr * (94 * d ^ 3 * Ac ^ 2) :=
      mul_le_mul_of_nonneg_left hKr
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 2 x _)
    _ ≤ (Ct 0) * (94 * d ^ 3 * Ac ^ 2) := by
      exact mul_le_mul_of_nonneg_right hTr
        (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (sq_nonneg Ac))
    _ ≤ (Ct 0) * (94 * d ^ 3 * (Ca ^ 2 * P1) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hAcSq
          (mul_nonneg (by norm_num) (by positivity))) (hCt0 0)
    _ = K * P1 ^ 2 := by
      simp only [K]
      ring
    _ = (Real.sqrt K) ^ 2 * P1 ^ 2 := by rw [Real.sq_sqrt hK0]

/-! ## Arbitrarily small energy pairing on the genuine segment -/

private theorem aa_pair_point
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (F : SmoothCcTensor g 2 2)
    {C delta : Real} (hC0 : 0 ≤ C) (hdelta0 : 0 ≤ delta)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (W.toSection x) ≤
        (Module.finrank Real E : Real) ^ 2 * delta ^ 2)
    (hF : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          (F.toSection x) ≤
        C ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) ^ 2)
    (x : M) :
    |tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x)
        ((appCc (I := I) (M := M) g 2 2 F W).toFun x)| ≤
      (Module.finrank Real E : Real) ^ 2 * C * delta ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) := by
  classical
  let S := W.toSection x
  let U := (appCc (I := I) (M := M) g 2 2 F W).toSection x
  let d : Real := Module.finrank Real E
  let p : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x S
  let q : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x)
  let B : Real := d ^ 2 * delta ^ 2
  let R : Real := C ^ 2 * q ^ 2
  have hp0 : 0 ≤ p := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x S
  have hq0 : 0 ≤ q := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hp : p ≤ B := by simpa only [p, B, S, d] using hW x
  have hU : riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤ R * p := by
    have happ : riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤
        riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          (F.toSection x) * p := by
      dsimp only [U, p]
      rw [appCc_toSection]
      exact riemannianFiberNormSq_comp_le_mul
        (I := I) (M := M) g 2 2 x _ _
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          (F.toSection x) * p := happ
      _ ≤ (C ^ 2 * q ^ 2) * p :=
        mul_le_mul_of_nonneg_right (by simpa only [q] using hF x) hp0
      _ = R * p := by rfl
  have hcs := tensorInnerPointwise_sq_le_mul
    (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)
  have hcs' :
      (tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)) ^ 2 ≤
          p * riemannianFiberNormSq (I := I) (M := M) g 0 2 x U := by
    simpa only [p, riemannianFiberNormSq_eq_tensorInnerPointwise] using hcs
  have hprod : p * riemannianFiberNormSq (I := I) (M := M) g 0 2 x U ≤
      (d ^ 2 * C * delta ^ 2 * q) ^ 2 := by
    calc
      _ ≤ p * (R * p) := mul_le_mul_of_nonneg_left hU hp0
      _ ≤ B * (R * B) :=
        mul_le_mul hp (mul_le_mul_of_nonneg_left hp hR0)
          (mul_nonneg hR0 hp0) hB0
      _ = (d ^ 2 * C * delta ^ 2 * q) ^ 2 := by
        simp only [B, R]
        ring
  have hsq := hcs'.trans hprod
  have hrhs0 : 0 ≤ d ^ 2 * C * delta ^ 2 * q := by positivity
  change |tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)| ≤
    d ^ 2 * C * delta ^ 2 * q
  nlinarith [sq_abs (tensorInnerPointwise (I := I) (M := M) g 0 2 x
    (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)),
    abs_nonneg (tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U))]

private lemma aa_bound_mono
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

/-- On the genuine closed-edge segment, the quadratic Ricci term fits into
any prescribed positive Dirichlet-energy budget after shrinking the carrier
`C0` radius. -/
theorem ricciAA_path_le (g : SmoothRiemannianMetric I M)
    {eta : Real} (heta : 0 < eta) :
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
            (appCc (I := I) (M := M) g 2 2
              (ricciAAArm (I := I) (M := M) g
                (edgeMetric (I := I) (M := M) g W hWbound s)) W).toFun ≤
          eta * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := by
  classical
  obtain ⟨C0, hC00, hcoeff⟩ := ricciAACoeff_rfns (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let C : Real := d ^ 2 * C0
  let den : Real := 4 * (1 + eta) * (1 + C)
  let delta0 : Real := eta / den
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg d) hC00
  have hden : 0 < den := by
    dsimp only [den]
    positivity
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact div_pos heta hden
  have hdelta0half : delta0 < 1 / 2 := by
    dsimp only [delta0]
    apply (div_lt_iff₀ hden).2
    dsimp only [den]
    nlinarith [mul_nonneg (le_of_lt heta) hC]
  have htwoC : 2 * C ≤ den := by
    dsimp only [den]
    nlinarith [mul_nonneg (le_of_lt heta) hC]
  have hbudget0 : 2 * C * delta0 ≤ eta := by
    dsimp only [delta0]
    rw [show 2 * C * (eta / den) = (2 * C * eta) / den by ring]
    apply (div_le_iff₀ hden).2
    calc
      2 * C * eta ≤ den * eta :=
        mul_le_mul_of_nonneg_right htwoC (le_of_lt heta)
      _ = eta * den := by ring
  refine ⟨delta0, hdelta0, hdelta0half, ?_⟩
  intro W hWsymm delta s hdelta0' hdeltaCap hWbound hs
  let P : SmoothCcTensor g 0 2 := s • W
  let gm : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g W hWbound s
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  let F : SmoothCcTensor g 2 2 := ricciAAArm (I := I) (M := M) g gm
  let U : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 F W
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
    aa_bound_mono (I := I) (M := M) g P hrad
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
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          (F.toSection x) ≤
        C0 ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ^ 2 := by
    intro x
    let qP : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
    let qD : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      (D.toSection x)
    have hqP0 : 0 ≤ qP := riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 3 x _
    have hqD0 : 0 ≤ qD := riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 3 x _
    have hq : qP ≤ qD := by simpa only [qP, qD] using hgrad x
    have hq2 : qP ^ 2 ≤ qD ^ 2 := by nlinarith
    calc
      _ ≤ C0 ^ 2 * qP ^ 2 := by
        simpa only [F, gm, qP] using hFraw x
      _ ≤ C0 ^ 2 * qD ^ 2 :=
        mul_le_mul_of_nonneg_left hq2 (sq_nonneg C0)
      _ = C0 ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ^ 2 := by rfl
  have hWfix : symmS (I := I) (M := M) g W = W :=
    aa_symm_eq (I := I) (M := M) g W hWsymm
  have hWpt := symmC0_rfns_le
    (I := I) (M := M) g W hdelta0' hWbound
  rw [hWfix] at hWpt
  have hpt : ∀ x : M,
      |tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x) (U.toFun x)| ≤
      C * delta ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (D.toSection x) := by
    intro x
    have h := aa_pair_point (I := I) (M := M) g W F hC00 hdelta0'
      hWpt hF x
    simpa only [U, D, C, d, mul_assoc] using h
  have hcross :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) W U
  have hsqint := integrable_riemannianFiberNormSq_toSection
    (I := I) (M := M) g 0 3 D
  have hrhsint : Integrable
      (fun x => C * delta ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (D.toSection x)) mu := hsqint.const_mul (C * delta ^ 2)
  have habs :
      |tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U.toFun| ≤
        C * delta ^ 2 * ‖D‖ ^ 2 := by
    unfold tensorL2Inner
    calc
      |∫ x, tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (W.toFun x) (U.toFun x) ∂mu| ≤
        ∫ x, |tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (W.toFun x) (U.toFun x)| ∂mu := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * delta ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ∂mu := integral_mono hcross.abs hrhsint hpt
      _ = C * delta ^ 2 * ∫ x,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (D.toSection x) ∂mu := by rw [integral_const_mul]
      _ = C * delta ^ 2 * ‖D‖ ^ 2 := by
        have hnorm :=
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
            (I := I) (M := M) g 0 3 D
        simpa only [SmoothCcTensor.norm_def] using
          congrArg (fun z : Real => C * delta ^ 2 * z) hnorm.symm
  have hdeltaOne : delta ≤ 1 :=
    hdeltaHalf.trans (by norm_num)
  have hdeltaSq : delta ^ 2 ≤ delta := by
    nlinarith [mul_nonneg hdelta0' (sub_nonneg.mpr hdeltaOne)]
  have hsmall : 2 * C * delta ^ 2 ≤ eta := by
    calc
      2 * C * delta ^ 2 ≤ 2 * C * delta :=
        mul_le_mul_of_nonneg_left hdeltaSq (mul_nonneg (by norm_num) hC)
      _ ≤ 2 * C * delta0 :=
        mul_le_mul_of_nonneg_left hdeltaCap (mul_nonneg (by norm_num) hC)
      _ ≤ eta := hbudget0
  dsimp only [U, F, gm, D] at habs ⊢
  calc
    (-2 : Real) * tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 2 2
          (ricciAAArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hWbound s)) W).toFun ≤
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (appCc (I := I) (M := M) g 2 2
          (ricciAAArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hWbound s)) W).toFun| := by
        nlinarith [le_abs_self (tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (appCc (I := I) (M := M) g 2 2
            (ricciAAArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hWbound s)) W).toFun)]
    _ ≤ 2 * (C * delta ^ 2 *
        ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = (2 * C * delta ^ 2) *
        ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := by ring
    _ ≤ eta * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
