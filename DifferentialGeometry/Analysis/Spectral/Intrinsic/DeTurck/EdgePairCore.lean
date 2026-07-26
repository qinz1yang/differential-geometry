import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence

/-!
# Acyclic closed-edge pairing core

This file isolates the three algebraic APIs needed by the Ricci closed-edge
pairing argument: moving double-trace refolding, insertion into a covariant
rank-two slot, and the rank-four product carrier.  It deliberately avoids the
later lower-pairing and refold-pairing modules so downstream Ricci estimates
can depend on these identities without an import cycle.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
private lemma pair_cons_sum {n : Nat}
    (Zm : Tensor0SModel (n + 1) Real E) (d : Nat) (t : Fin d → Real)
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
        rw [show (0 : E) = ((0 : Real) • (0 : E)) from (zero_smul Real (0 : E)).symm]
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
private lemma pair_cons2_sum {n : Nat}
    (Zm : Tensor0SModel (n + 2) Real E) (aa : E) (d : Nat)
    (t : Fin d → Real) (u : Fin d → E) (rest : Fin n → E) :
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
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1
          (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c *
          Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : Real) • (0 : E)) from (zero_smul Real (0 : E)).symm]
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
private lemma pair_frame_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank Real E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  haveI : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))⟩⟩
  set B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent Real B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) =
        c i * (if i = j then (1 : Real) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : Real) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank Real E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank Real E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : Real) else 0) := by
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
/-- A moving-metric double trace is a fixed-background trace after inserting
the relative inverse-metric endomorphism in the first contracted slot. -/
theorem pairTrace_refold (g gm : SmoothRiemannianMetric I M) (s : Nat) :
    mvDoubleTraceField (I := I) (M := M) g gm s =
      appCcRS (I := I) (M := M) g (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g s)
        (slotInsertEndoCc (I := I) (M := M) g (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g gm)) := by
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
      ((show Tensor0SSpace (s + 2) I x →L[Real] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g gm s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[Real] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g gm s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) gm s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) gm s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) gm x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[Real] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g s)
          (slotInsertEndoCc (I := I) (M := M) g (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g gm))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g gm x
              (smoothOrthoFrame (I := I) g x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[Real] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g s)
          (slotInsertEndoCc (I := I) (M := M) g (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g gm))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g gm x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g gm x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank Real E),
      (show E from gInvRaisedEndo (I := I) g gm x
        (smoothOrthoFrame (I := I) g x a x)) =
        ∑ c : Fin (Module.finrank Real E),
          g.inner x (smoothOrthoFrame (I := I) g x a x)
              (smoothOrthoFrame (I := I) gm x c x) •
            (smoothOrthoFrame (I := I) gm x c x : E) := by
    intro a
    have h1 := pair_frame_repr (I := I) (M := M) gm x
      (gInvRaisedEndo (I := I) g gm x (smoothOrthoFrame (I := I) g x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g gm x
        (smoothOrthoFrame (I := I) g x a x)) =
        gInvRaisedEndo (I := I) g gm x
          (smoothOrthoFrame (I := I) g x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [gm.symm x (smoothOrthoFrame (I := I) gm x c x)
      (gInvRaisedEndo (I := I) g gm x (smoothOrthoFrame (I := I) g x a x))]
    rw [show gm.inner x
        (gInvRaisedEndo (I := I) g gm x (smoothOrthoFrame (I := I) g x a x))
        (smoothOrthoFrame (I := I) gm x c x) =
        g.inner x (smoothOrthoFrame (I := I) g x a x)
          (smoothOrthoFrame (I := I) gm x c x) from by
      rw [gInvRaisedEndo_apply]
      rw [inverseMetricSharpFib_inner (I := I) gm x
        (g0FlatCLM (I := I) g x (smoothOrthoFrame (I := I) g x a x))
        (smoothOrthoFrame (I := I) gm x c x)]
      rw [show cotangentToDualLinear (I := I) (x := x)
          (g0FlatCLM (I := I) g x (smoothOrthoFrame (I := I) g x a x))
          (smoothOrthoFrame (I := I) gm x c x) =
          cotangentToDual (I := I) (x := x)
            (g0FlatCLM (I := I) g x (smoothOrthoFrame (I := I) g x a x))
            (smoothOrthoFrame (I := I) gm x c x) from rfl]
      rw [cotangentToDual_g0FlatCLM]]
  symm
  calc (∑ a : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g gm x
              (smoothOrthoFrame (I := I) g x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) mm))) =
      ∑ a : Fin (Module.finrank Real E), ∑ c : Fin (Module.finrank Real E),
        g.inner x (smoothOrthoFrame (I := I) g x a x)
            (smoothOrthoFrame (I := I) gm x c x) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact pair_cons_sum (E := E) (Tensor0SSpace.toModel Z)
          (Module.finrank Real E)
          (fun c => g.inner x (smoothOrthoFrame (I := I) g x a x)
            (smoothOrthoFrame (I := I) gm x c x))
          (fun c => (smoothOrthoFrame (I := I) gm x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank Real E), ∑ a : Fin (Module.finrank Real E),
        g.inner x (smoothOrthoFrame (I := I) g x a x)
            (smoothOrthoFrame (I := I) gm x c x) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := pair_cons2_sum (E := E) (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
          (Module.finrank Real E)
          (fun a => g.inner x (smoothOrthoFrame (I := I) g x a x)
            (smoothOrthoFrame (I := I) gm x c x))
          (fun a => (smoothOrthoFrame (I := I) g x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := pair_frame_repr (I := I) (M := M) g x
          (smoothOrthoFrame (I := I) gm x c x)
        rw [show (∑ a : Fin (Module.finrank Real E),
            g.inner x (smoothOrthoFrame (I := I) g x a x)
              (smoothOrthoFrame (I := I) gm x c x) •
              (smoothOrthoFrame (I := I) g x a x : E)) =
            ((∑ a : Fin (Module.finrank Real E),
              g.inner x (smoothOrthoFrame (I := I) g x a x)
                (smoothOrthoFrame (I := I) gm x c x) •
                smoothOrthoFrame (I := I) g x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

/-- Insert a smooth tangent endomorphism into one of the two covariant slots
of a rank-two tensor. -/
def pairSlot2 (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j)
    (appCc (I := I) (M := M) g 2 2
      (slotInsertEndoCc (I := I) (M := M) g 1 Λ)
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S))

/-- Covariant tensor product with the first factor occupying slots `0,1`. -/
def pairProd4 (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  appCc (I := I) (M := M) g 2 4
    (slotExtendIter (I := I) (M := M) g 0 2 2 B) A

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- Evaluation of `pairSlot2`: the chosen covariant slot is read through the
given endomorphism. -/
theorem pairSlot2_eval (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (pairSlot2 (I := I) (M := M) g Λ j S) x v =
      unitModel (I := I) (M := M) g 2 S x
        (Function.update v j (Λ x (v j))) := by
  classical
  rw [pairSlot2, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S) x from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases j <;> fin_cases k <;> simp [Equiv.swap_apply_def]

private lemma pair_extend_cons
    (g : SmoothRiemannianMetric I M) (r s : Nat)
    (Φ : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : TangentSpace I x)
    (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[Real]
            Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s Φ).toSection x) D)
        (Fin.cons (show E from v0) vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
          Φ.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := Real) r x D v0)) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[Real]
      Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s Φ).toSection x) D) =
      slotExtendFib (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
          Φ.toSection x) D from rfl]
  exact slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
      Φ.toSection x) D (show E from v0) vs

set_option linter.unusedSectionVars false in
private lemma pair_rank0_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  have hunit : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
      (1 : Real) := rfl
  rw [hunit, mul_one]
  congr 1
  funext i
  exact i.elim0

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma pair_extend2_eval (g : SmoothRiemannianMetric I M)
    (B : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 2 B).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g 2 B x ![u 2, u 3] := by
  have hu : (fun k : Fin 4 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1) ![(u 2 : E), (u 3 : E)]) := by
    funext k
    fin_cases k <;> rfl
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 2 B).toSection x) D) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtendIter (I := I) (M := M) g 0 2 1 B)).toSection x) D)
        (fun k : Fin 4 => (u k : E)) from rfl]
  rw [hu]
  rw [pair_extend_cons (I := I) (M := M) g 1 3
    (slotExtendIter (I := I) (M := M) g 0 2 1 B) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 1 B).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0))) =
      ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g 0 2 B).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0))) from rfl]
  rw [pair_extend_cons (I := I) (M := M) g 0 2 B x
    (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := Real) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0)) (u 1)
      with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0))
      (v0 := (u 1 : E)) (vs := fun i : Fin 0 => i.elim0)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := D) (v0 := (u 0 : E))
      (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))]
    congr 1
  have hdecomp := pair_rank0_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  rfl

/-- The rank-four product carrier evaluates as the product of its first and
last pair of covariant components. -/
theorem pairProd4_eval (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (pairProd4 (I := I) (M := M) g A B) x v =
      unitModel (I := I) (M := M) g 2 A x ![v 0, v 1] *
        unitModel (I := I) (M := M) g 2 B x ![v 2, v 3] := by
  rw [unitModel, pairProd4, appCc_toSection, ContinuousLinearMap.comp_apply]
  rw [pair_extend2_eval (I := I) (M := M) g B x]
  rfl

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
