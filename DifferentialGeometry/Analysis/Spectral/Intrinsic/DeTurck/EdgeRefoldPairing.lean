import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeLowerPairing

/-!
# Closed-edge Ricci--DeTurck refold pairing

The closed-edge slope split leaves one genuinely nonlinear lower arm.  Its
order-zero coefficient contains a derivative of the connection difference,
so estimating that coefficient before pairing would require an inadmissible
spatial derivative bound for the arbitrary edge solution.

This file performs the exact algebraic refold first.  The public Palatini and
DeTurck refold identities turn the dangerous part into

* the Ricci half-combination, whose low-order structure is handled jointly;
* a uniformly bounded order-zero family;
* an explicit lower residual and the genuine first-gradient arm; and
* a second-order coefficient which is pointwise `O(delta)`.

The final theorem also records the resulting Hilbert-space pairing identity,
so later energy estimates consume an actual full right-hand-side pairing and
not an uninstantiated symbolic decomposition.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The Ricci order-zero combination left after adding and subtracting one
Riemann coefficient.  It is the low-order Palatini residual; the complementary
Riemann coefficient is the one combined with the DeTurck covariant-derivative
arm below. -/
def edgeRicciHalf (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g g₁ +
    (1 / 2 : Real) •
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g g₁

/-- The explicit zeroth-order remainder after the covariant-derivative part of
the DeTurck coefficient has been refolded.  It contains no derivative of the
connection difference hidden inside `deTurckLieCoeffField`. -/
def edgeFold0 (g g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  ((deTurckLieEndoArmField (I := I) (M := M) g g₁ g_bg +
      lieCorr0Field (I := I) (M := M) g g₁ g_bg) +
    phiMetCurvCoeff (I := I) g g_bg g₁) -
      edgeCarry0 (I := I) (M := M) g g_bg

/-- The complete nonlinear refold arm at one slope parameter. -/
def edgeRefoldArm (g g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (C₀ : SmoothCcTensor g 2 2)
    (C₂ : SmoothCcTensor g 4 2) : SmoothCcTensor g 0 2 :=
  (-2 : Real) • appCc (I := I) (M := M) g 2 2
      (edgeRicciHalf (I := I) (M := M) g g₁) W +
    appCc (I := I) (M := M) g 2 2 C₀ W +
    appCc (I := I) (M := M) g 2 2
      (edgeFold0 (I := I) (M := M) g g₁ g_bg) W +
    appCc (I := I) (M := M) g 3 2
      (edgeQuad1 (I := I) (M := M) g g₁ g_bg)
      (iteratedCovGrad (I := I) g 0 2 1 W) +
    appCc (I := I) (M := M) g 4 2 C₂
      (iteratedCovGrad (I := I) g 0 2 2 W)

/-- The zero endpoint obeys any nonnegative fibre-operator bound. -/
theorem edgeZeroBoundAt (g : SmoothRiemannianMetric I M) {delta : Real}
    (hdelta : 0 ≤ delta) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0, ccTensorBilinSymm_smul]
  simp only [zero_mul, abs_zero]
  exact mul_nonneg (mul_nonneg hdelta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- On the genuine segment, the path using the sharp zero bound and the path
using the same radius at both endpoints are the same metric.  This bridge lets
the equal-radius public refold packages feed the exact closed-edge slope split.
-/
theorem edgeMetric_bal
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    {s : Real} (hs : s ∈ Set.Icc (0 : Real) 1) :
    edgeMetric (I := I) (M := M) g W hdelta s =
      realizedFam (I := I) g W 0 hdelta hdeltaZ s := by
  have hs0 : s ∈ realizedSmallSet (δ := delta) (δ' := 0) :=
    Icc_subset_realizedSmallSet hdelta_lt (by norm_num) hs
  have hsdelta : s ∈ realizedSmallSet (δ := delta) (δ' := delta) :=
    Icc_subset_realizedSmallSet hdelta_lt hdelta_lt hs
  apply riemannianMetric_eq_of_inner
  intro x v w
  change
    (realizedFam (I := I) g W 0 hdelta
        (edgeZeroBound (I := I) (M := M) g) s).inner x v w =
      (realizedFam (I := I) g W 0 hdelta hdeltaZ s).inner x v w
  rw [realizedFam_inner_of_mem (I := I) g W 0 hdelta
      (edgeZeroBound (I := I) (M := M) g) hs0 x v w,
    realizedFam_inner_of_mem (I := I) g W 0 hdelta hdeltaZ hsdelta x v w]

private lemma edge_rank0_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

private lemma edge_cons_sum (x : M) {n : Nat}
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

private lemma edge_cons2_sum (x : M) {n : Nat}
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

private lemma edge_frame_repr (g : SmoothRiemannianMetric I M) (x : M)
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
theorem edgeMvTrace (g gm : SmoothRiemannianMetric I M) (s : Nat) :
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
    have h1 := edge_frame_repr (I := I) (M := M) gm x
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
        exact edge_cons_sum (E := E) x (Tensor0SSpace.toModel Z)
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
        have hsum := edge_cons2_sum (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) gm x c x : TangentSpace I x) : E)
          (Module.finrank Real E)
          (fun a => g.inner x (smoothOrthoFrame (I := I) g x a x)
            (smoothOrthoFrame (I := I) gm x c x))
          (fun a => (smoothOrthoFrame (I := I) g x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := edge_frame_repr (I := I) (M := M) g x
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

private lemma edge_sum4_comm
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ p : A × B, ∑ q : C × D, F p.1 p.2 q.1 q.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ q : C × D, ∑ p : A × B, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
          simp only [Fintype.sum_prod_type]

private lemma edge_bitrace_move
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (S Z : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : Real) else 0) :
    (∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
        S (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x) *
          Z (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x)) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        S (gInvRaisedEndo (I := I) g gm x (e i))
            (gInvRaisedEndo (I := I) g gm x (e j)) * Z (e i) (e j) := by
  classical
  let f : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) gm x a x
  let c : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i a => g.inner x (e i) (f a)
  have hf : ∀ a b, gm.inner x (f a) (f b) = if a = b then (1 : Real) else 0 := by
    intro a b
    exact smoothOrthoFrame_orthonormal_at_center (I := I) gm x a b
  have hraise : ∀ i, gInvRaisedEndo (I := I) g gm x (e i) =
      ∑ a, c i a • f a := by
    intro i
    have hrep := orthonormal_tangent_expansion (I := I) (M := M) gm x f hf
      (gInvRaisedEndo (I := I) g gm x (e i))
    rw [← hrep]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [gm.symm x (f a) (gInvRaisedEndo (I := I) g gm x (e i))]
    change gm.inner x (gInvRaisedEndo (I := I) g gm x (e i)) (f a) = c i a
    rw [gInvRaisedEndo_apply]
    rw [inverseMetricSharpFib_inner (I := I) gm x
      (g0FlatCLM (I := I) g x (e i)) (f a)]
    rw [show cotangentToDualLinear (I := I) (x := x)
        (g0FlatCLM (I := I) g x (e i)) (f a) =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x (e i)) (f a) from rfl]
    rw [cotangentToDual_g0FlatCLM]
  have hframe : ∀ a, f a = ∑ i, c i a • e i := by
    intro a
    exact (orthonormal_tangent_expansion (I := I) (M := M) g x e he (f a)).symm
  have hS : ∀ i j,
      S (gInvRaisedEndo (I := I) g gm x (e i))
          (gInvRaisedEndo (I := I) g gm x (e j)) =
        ∑ a, ∑ b, (c i a * c j b) * S (f a) (f b) := by
    intro i j
    rw [hraise i, hraise j, map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hZ : ∀ a b, Z (f a) (f b) =
      ∑ i, ∑ j, (c i a * c j b) * Z (e i) (e j) := by
    intro a b
    rw [hframe a, hframe b, map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc
    (∑ a, ∑ b, S (f a) (f b) * Z (f a) (f b)) =
        ∑ a, ∑ b, ∑ i, ∑ j,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hZ a b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) :=
      edge_sum4_comm (fun a b i j =>
        (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)))
    _ = ∑ i, ∑ j,
        S (gInvRaisedEndo (I := I) g gm x (e i))
            (gInvRaisedEndo (I := I) g gm x (e j)) * Z (e i) (e j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS i j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring

/-- Insert a smooth tangent endomorphism into one of the two covariant slots
of a rank-two tensor. -/
def edgeSlot2 (g : SmoothRiemannianMetric I M)
    (Lambda : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j)
    (appCc (I := I) (M := M) g 2 2
      (slotInsertEndoCc (I := I) (M := M) g 1 Lambda)
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S))

/-- Apply the relative inverse-metric endomorphism in both slots. -/
def edgeRaise2 (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  edgeSlot2 (I := I) (M := M) g
    (fullRaisedEndoField (I := I) (M := M) g gm) 1
    (edgeSlot2 (I := I) (M := M) g
      (fullRaisedEndoField (I := I) (M := M) g gm) 0 S)

/-- Covariant tensor product with the first factor occupying slots `0,1`. -/
def edgeProd4 (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  appCc (I := I) (M := M) g 2 4
    (slotExtendIter (I := I) (M := M) g 0 2 2 B) A

/-- Formal rank-four partner of one moving Palatini pair-trace monomial. -/
def edgePairPartner (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (sigma : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g sigma.symm
    (edgeProd4 (I := I) (M := M) g
      (edgeRaise2 (I := I) (M := M) g gm S) S)

/-- The public moving-metric pair trace, arranged so that applying it to a
rank-two tensor reproduces one Palatini refold monomial.  Keeping this field
explicit is what later allows the second derivative to be moved by Green's
identity before any pointwise estimate is taken. -/
def edgePairMono (g gm : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 6 2
    (mvPairTraceOp (I := I) (M := M) g gm)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
/-- One moving pair-trace action is exactly one Palatini refold monomial.

This is the public-API reconstruction of the algebraic identity needed by the
closed-edge energy argument.  In particular it uses `mvPairTraceOp`, rather
than relying on the private pair-trace implementation in the coefficient
refold file. -/
theorem edgeMonoRefold (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    appCc (I := I) (M := M) g 2 2
        (edgePairMono (I := I) (M := M) g gm G σ) S =
      appCc (I := I) (M := M) g 4 2
        (curvatureRefoldMonomialCoeffField (I := I) (M := M) g gm
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ) G := by
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
  rw [edge_rank0_decomp (I := I) (M := M) x t]
  simp only [map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g gm
    (domDomCongrSection (I := I) g
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
    ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x)) v]
  rw [show ((show Tensor0SSpace 4 I x →L[Real] Tensor0SSpace 2 I x from
      (curvatureRefoldMonomialCoeffField (I := I) (M := M) g gm
        (ccTensorUnitValueSection (I := I) (M := M) g S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ).toSection x)
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x))) =
    curvatureRefoldMonomialBiContrFib (I := I) (M := M) gm
      (ccTensorUnitValueSection (I := I) (M := M) g S) σ x
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) from rfl]
  rw [curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg₂ (· * ·) rfl ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) =
    unitModel (I := I) (M := M) g 4 G x from rfl]
  refine congrArg _ ?_
  funext i
  rw [Equiv.trans_apply]
  generalize σ i = k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- Evaluation of `edgeSlot2`: the chosen covariant slot is read through the
given endomorphism. -/
theorem edgeSlot2_eval (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (edgeSlot2 (I := I) (M := M) g Λ j S) x v =
      unitModel (I := I) (M := M) g 2 S x
        (Function.update v j (Λ x (v j))) := by
  classical
  rw [edgeSlot2, domDomCongrSection_unitModel,
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

/-- Both relative inverse-metric insertions in `edgeRaise2` are visible on
the two covariant arguments. -/
theorem edgeRaise2_eval (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (edgeRaise2 (I := I) (M := M) g gm S) x v =
      unitModel (I := I) (M := M) g 2 S x
        (fun k => fullRaisedEndoField (I := I) (M := M) g gm x (v k)) := by
  classical
  rw [edgeRaise2, edgeSlot2_eval, edgeSlot2_eval]
  congr 1
  funext k
  fin_cases k <;> rfl

private lemma edge_extend_cons
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

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma edge_extend2_eval (g : SmoothRiemannianMetric I M)
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
  rw [edge_extend_cons (I := I) (M := M) g 1 3
    (slotExtendIter (I := I) (M := M) g 0 2 1 B) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 1 B).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0))) =
      ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g 0 2 B).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := Real) 1 x D (u 0))) from rfl]
  rw [edge_extend_cons (I := I) (M := M) g 0 2 B x
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
    funext k
    fin_cases k <;> rfl
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  rfl

/-- The rank-four product carrier evaluates as the product of its first and
last pair of covariant components. -/
theorem edgeProd4_eval (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (edgeProd4 (I := I) (M := M) g A B) x v =
      unitModel (I := I) (M := M) g 2 A x ![v 0, v 1] *
        unitModel (I := I) (M := M) g 2 B x ![v 2, v 3] := by
  rw [unitModel, edgeProd4, appCc_toSection, ContinuousLinearMap.comp_apply]
  rw [edge_extend2_eval (I := I) (M := M) g B x]
  rfl

/-- Component formula for the formal rank-four partner of one monomial. -/
theorem edgePartner_eval (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4))
    (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (edgePairPartner (I := I) (M := M) g gm S σ) x v =
      unitModel (I := I) (M := M) g 2 S x
          ![fullRaisedEndoField (I := I) (M := M) g gm x (v (σ.symm 0)),
            fullRaisedEndoField (I := I) (M := M) g gm x (v (σ.symm 1))] *
        unitModel (I := I) (M := M) g 2 S x
          ![v (σ.symm 2), v (σ.symm 3)] := by
  rw [edgePairPartner, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply, edgeProd4_eval,
    edgeRaise2_eval]
  congr 2 <;> funext k <;> fin_cases k <;> rfl

/-- Pointwise component formula for one public pair-trace monomial. -/
theorem edgeMono_eval (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (edgePairMono (I := I) (M := M) g gm G σ) S) x v =
      ∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 S x
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g 4 G x
            (fun i => (Fin.cons
              (smoothOrthoFrame (I := I) gm x a x : E)
              (Fin.cons (smoothOrthoFrame (I := I) gm x b x : E) v) :
                Fin 4 → E) (σ i)) := by
  rw [edgeMonoRefold (I := I) (M := M) g gm S G σ]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (curvatureRefoldMonomialBiContrFib (I := I) (M := M) gm
        (ccTensorUnitValueSection (I := I) (M := M) g S) σ x
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
          G.toSection x) (unitTensor (I := I) (M := M) x))) v = _
  rw [curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  rfl

private def edgeEvalCLM (s : Nat) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[Real] Real :=
  haveI : FiniteDimensional Real (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

private lemma edgeEvalCLM_apply (s : Nat) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    edgeEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel D v := rfl

/-- A curried scalar reading of the first two slots of a covariant tensor. -/
private def edgeFeedCLM (s : Nat) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  haveI : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (edgeEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := Real) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := Real) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

private lemma edgeFeedCLM_apply (s : Nat) (x : M)
    (G : Tensor0SSpace (s + 2) I x) (v : Fin s → E)
    (p q : TangentSpace I x) :
    edgeFeedCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [edgeFeedCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, edgeEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (𝕜 := Real) (I := I) (M := M) (s + 1) x G p)
      (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

private lemma edge_sum_succ {A R : Type*} [Fintype A] [AddCommMonoid R]
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

private lemma edge_sum2 {A : Type*} [Fintype A] (F : (Fin 2 → A) → Real) :
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

private lemma edge_sum4 {A : Type*} [Fintype A] (F : (Fin 4 → A) → Real) :
    (∑ J : Fin 4 → A, F J) =
      ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A, F ![a, b, c, d] := by
  classical
  rw [edge_sum_succ (s := 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [edge_sum_succ (s := 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [edge_sum_succ (s := 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [edge_sum_succ (s := 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · congr 1
    funext k
    fin_cases k <;> rfl
  · intro q _ hq
    exact absurd (Subsingleton.elim q (fun i : Fin 0 => i.elim0)) hq
  · intro h
    exact absurd (Finset.mem_univ _) h

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma edge_inner0 (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g.inner x (e a) (e b) = if a = b then (1 : Real) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x (A.toFun x) (B.toFun x) =
      ∑ J : Fin s → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g s A x (fun k => (e (J k) : E)) *
          unitModel (I := I) (M := M) g s B x (fun k => (e (J k) : E)) := by
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
      (∑ K : Fin 0 → Fin (Module.finrank Real E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro q _ hq
      exact absurd (Subsingleton.elim q Fin.elim0) hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hK]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hcomp A Fin.elim0 J, hcomp B Fin.elim0 J]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem edgePair_point (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x (S.toFun x)
        ((appCc (I := I) (M := M) g 2 2
          (edgePairMono (I := I) (M := M) g gm G σ) S).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((edgePairPartner (I := I) (M := M) g gm S σ).toFun x) (G.toFun x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) g x
  rw [edge_inner0 (I := I) (M := M) g 2 S
      (appCc (I := I) (M := M) g 2 2
        (edgePairMono (I := I) (M := M) g gm G σ) S) x e bse hbse horth,
    edge_inner0 (I := I) (M := M) g 4
      (edgePairPartner (I := I) (M := M) g gm S σ) G x e bse hbse horth,
    edge_sum2]
  have hmove : ∀ i j : Fin (Module.finrank Real E),
      (∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 S x
              ![(smoothOrthoFrame (I := I) gm x a x : E),
                (smoothOrthoFrame (I := I) gm x b x : E)] *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons
                (smoothOrthoFrame (I := I) gm x a x : E)
                (Fin.cons (smoothOrthoFrame (I := I) gm x b x : E)
                  ![(e i : E), (e j : E)]) : Fin 4 → E) (σ k))) =
        ∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 S x
              ![gInvRaisedEndo (I := I) g gm x (e a),
                gInvRaisedEndo (I := I) g gm x (e b)] *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons (e a : E)
                (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
                (σ k)) := by
    intro i j
    let Sx : Tensor0SSpace 2 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from S.toSection x)
        (unitTensor (I := I) (M := M) x)
    let Gx : Tensor0SSpace 4 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)
    have hm := edge_bitrace_move (I := I) (M := M) g gm x
      (edgeFeedCLM (I := I) (M := M) 0 x Sx ![])
      (edgeFeedCLM (I := I) (M := M) 2 x
        (slotPerm4Fib (I := I) (M := M) x σ Gx) ![(e i : E), (e j : E)])
      e horth
    simpa only [edgeFeedCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply, Sx, Gx, unitModel] using hm
  calc
    (∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
          unitModel (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 2 2
              (edgePairMono (I := I) (M := M) g gm G σ) S) x
            ![(e i : E), (e j : E)]) =
      ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 S x
                ![(smoothOrthoFrame (I := I) gm x a x : E),
                  (smoothOrthoFrame (I := I) gm x b x : E)] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons
                  (smoothOrthoFrame (I := I) gm x a x : E)
                  (Fin.cons (smoothOrthoFrame (I := I) gm x b x : E)
                    ![(e i : E), (e j : E)]) : Fin 4 → E) (σ k)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [edgeMono_eval (I := I) (M := M) g gm S G σ x]
    _ = ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 S x
                ![gInvRaisedEndo (I := I) g gm x (e a),
                  gInvRaisedEndo (I := I) g gm x (e b)] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (e a : E)
                  (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
                  (σ k))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hmove i j]
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        (unitModel (I := I) (M := M) g 2 S x
              ![gInvRaisedEndo (I := I) g gm x (e a),
                gInvRaisedEndo (I := I) g gm x (e b)] *
            unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)]) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => (Fin.cons (e a : E)
              (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
              (σ k)) := by
        rw [show (∑ i, ∑ j,
            unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
              (∑ a, ∑ b,
                unitModel (I := I) (M := M) g 2 S x
                    ![gInvRaisedEndo (I := I) g gm x (e a),
                      gInvRaisedEndo (I := I) g gm x (e b)] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (e a : E)
                      (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
                      (σ k))) =
            ∑ i, ∑ j, ∑ a, ∑ b,
              unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
                (unitModel (I := I) (M := M) g 2 S x
                    ![gInvRaisedEndo (I := I) g gm x (e a),
                      gInvRaisedEndo (I := I) g gm x (e b)] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (e a : E)
                      (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
                      (σ k))) from by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]]
        rw [edge_sum4_comm (fun i j a b =>
          unitModel (I := I) (M := M) g 2 S x ![(e i : E), (e j : E)] *
            (unitModel (I := I) (M := M) g 2 S x
                ![gInvRaisedEndo (I := I) g gm x (e a),
                  gInvRaisedEndo (I := I) g gm x (e b)] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (e a : E)
                  (Fin.cons (e b : E) ![(e i : E), (e j : E)]) : Fin 4 → E)
                  (σ k)))]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ K : Fin 4 → Fin (Module.finrank Real E),
        (unitModel (I := I) (M := M) g 2 S x
              ![gInvRaisedEndo (I := I) g gm x (e (K 0)),
                gInvRaisedEndo (I := I) g gm x (e (K 1))] *
            unitModel (I := I) (M := M) g 2 S x
              ![(e (K 2) : E), (e (K 3) : E)]) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => (e (K (σ k)) : E)) := by
        rw [edge_sum4]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rfl
    _ = ∑ J : Fin 4 → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4
            (edgePairPartner (I := I) (M := M) g gm S σ) x
            (fun k => (e (J k) : E)) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => (e (J k) : E)) := by
        refine Fintype.sum_equiv
          (Equiv.arrowCongr σ.symm
            (Equiv.refl (Fin (Module.finrank Real E))))
          (fun K =>
            (unitModel (I := I) (M := M) g 2 S x
                  ![gInvRaisedEndo (I := I) g gm x (e (K 0)),
                    gInvRaisedEndo (I := I) g gm x (e (K 1))] *
                unitModel (I := I) (M := M) g 2 S x
                  ![(e (K 2) : E), (e (K 3) : E)]) *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (e (K (σ k)) : E)))
          (fun J =>
            unitModel (I := I) (M := M) g 4
                (edgePairPartner (I := I) (M := M) g gm S σ) x
                (fun k => (e (J k) : E)) *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (e (J k) : E)))
          (fun K => ?_)
        have heqv :
            (Equiv.arrowCongr σ.symm
              (Equiv.refl (Fin (Module.finrank Real E)))) K =
              (fun k => K (σ k)) := by
          funext k
          simp [Equiv.arrowCongr]
        rw [heqv, edgePartner_eval]
        simp only [Equiv.apply_symm_apply]
        rfl

set_option linter.unusedSectionVars false in
/-- Exact global formal-partner identity for one moving Palatini pair-trace
monomial.  This is the Green-ready replacement for estimating the rank-four
coefficient and `nabla² S` separately. -/
theorem edgePair_l2 (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    tensorL2Inner (I := I) (M := M) g 0 2 S.toFun
        (appCc (I := I) (M := M) g 2 2
          (edgePairMono (I := I) (M := M) g gm G σ) S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (edgePairPartner (I := I) (M := M) g gm S σ).toFun G.toFun := by
  classical
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact edgePair_point (I := I) (M := M) g gm S G σ x

/-- Inner-product form of `edgePair_l2`, convenient for finite linear
combinations of refold monomials. -/
theorem edgePair_inner (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    (⟪S, appCc (I := I) (M := M) g 2 2
        (edgePairMono (I := I) (M := M) g gm G σ) S⟫_Real : Real) =
      ⟪edgePairPartner (I := I) (M := M) g gm S σ, G⟫_Real := by
  rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  exact edgePair_l2 (I := I) (M := M) g gm S G σ

/-- Pair-trace form of the DeTurck part of the second-order refold family. -/
def edgeLiePairFam (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
    (edgePairMono (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) (q i)
      + edgePairMono (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

/-- Rank-four formal partner of the DeTurck second-order pair family. -/
def edgeLiePartner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 0 4 :=
  s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
    (edgePairPartner (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T (q i) +
      edgePairPartner (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

/-- The DeTurck second-order action is exactly the application of its
rank-two pair-trace form to the metric difference. -/
theorem edgeLiePair_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    appCc (I := I) (M := M) g 2 2
        (edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ q epsilon s) T =
      appCc (I := I) (M := M) g 4 2
        (deTurckLieCovDerivRefoldC2Family
          (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [edgeLiePairFam, deTurckLieCovDerivRefoldC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_smul_left, appCc_add_left]
  rw [edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 0),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 1),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 2),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

/-- Pair-trace form of one four-monomial Palatini kernel. -/
def edgeKernelPair (g gm : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) (q : Fin 4 → Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 2 2 :=
  (1 / 2 : Real) •
    (edgePairMono (I := I) (M := M) g gm G (q 0) +
      edgePairMono (I := I) (M := M) g gm G (q 1) -
      edgePairMono (I := I) (M := M) g gm G (q 2) -
      edgePairMono (I := I) (M := M) g gm G (q 3))

/-- Rank-four formal partner of one four-monomial Palatini kernel. -/
def edgeKernelPartner (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (q : Fin 4 → Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 0 4 :=
  (1 / 2 : Real) •
    (edgePairPartner (I := I) (M := M) g gm S (q 0) +
      edgePairPartner (I := I) (M := M) g gm S (q 1) -
      edgePairPartner (I := I) (M := M) g gm S (q 2) -
      edgePairPartner (I := I) (M := M) g gm S (q 3))

/-- Applying a Palatini kernel pair field to its weight reproduces the
corresponding rank-four kernel coefficient acting on the chosen input. -/
theorem edgeKernel_apply (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (q : Fin 4 → Equiv.Perm (Fin 4)) :
    appCc (I := I) (M := M) g 2 2
        (edgeKernelPair (I := I) (M := M) g gm G q) S =
      appCc (I := I) (M := M) g 4 2
        (curvatureRefoldKernelCoeffField (I := I) (M := M) g gm
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S)
          (q 0) (q 1) (q 2) (q 3)) G := by
  rw [edgeKernelPair, curvatureRefoldKernelCoeffField]
  simp only [appCc_smul_left, appCc_add_left, appCc_sub_left]
  rw [edgeMonoRefold (I := I) (M := M) g gm S G (q 0),
    edgeMonoRefold (I := I) (M := M) g gm S G (q 1),
    edgeMonoRefold (I := I) (M := M) g gm S G (q 2),
    edgeMonoRefold (I := I) (M := M) g gm S G (q 3)]

/-- Pair-trace form of the Riemann--Palatini second-order refold family. -/
def edgeRiemPairFam (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    SmoothCcTensor g 2 2 :=
  s • ((1 / 2 : Real) •
    (edgeKernelPair (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) qA +
      edgeKernelPair (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) qB))

/-- Rank-four formal partner of the Riemann--Palatini pair family. -/
def edgeRiemPartner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    SmoothCcTensor g 0 4 :=
  s • ((1 / 2 : Real) •
    (edgeKernelPartner (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T qA +
      edgeKernelPartner (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T qB))

/-- The Riemann--Palatini second-order action is exactly the application of
its rank-two pair-trace form to the metric difference. -/
theorem edgeRiemPair_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    appCc (I := I) (M := M) g 2 2
        (edgeRiemPairFam (I := I) (M := M) g T hdelta hdeltaZ qA qB s) T =
      appCc (I := I) (M := M) g 4 2
        (riemannPalatiniRefoldC2Family
          (I := I) (M := M) g T hdelta hdeltaZ qA qB s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [edgeRiemPairFam, riemannPalatiniRefoldC2Family]
  simp only [appCc_smul_left, appCc_add_left]
  rw [edgeKernel_apply (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) qA,
    edgeKernel_apply (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) qB]

/-- The pair-trace field for the complete top coefficient returned by the
closed-edge refold package. -/
def edgeTopPair (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  (2 : Real) • edgeRiemPairFam (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
    edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ q epsilon s

/-- Rank-four formal partner of the complete top refold coefficient. -/
def edgeTopPartner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 0 4 :=
  (2 : Real) •
      edgeRiemPartner (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
    edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ q epsilon s

/-- Exact action identity for the complete top refold coefficient. -/
theorem edgeTopPair_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ qA qB q epsilon s) T =
      appCc (I := I) (M := M) g 4 2
        ((2 : Real) • riemannPalatiniRefoldC2Family
            (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
          deTurckLieCovDerivRefoldC2Family
            (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [edgeTopPair]
  simp only [appCc_add_left, appCc_smul_left]
  rw [edgeRiemPair_apply (I := I) (M := M) g T hdelta hdeltaZ qA qB s,
    edgeLiePair_apply (I := I) (M := M) g T hdelta hdeltaZ q epsilon s]

set_option maxHeartbeats 12800000 in
/-- Exact formal-partner identity for the complete top coefficient returned by
the Riemann--DeTurck refold. -/
theorem edgeTop_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T⟫_Real : Real) =
      ⟪edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s,
        iteratedCovGrad (I := I) g 0 2 2 T⟫_Real := by
  rw [edgeTopPair, edgeTopPartner, edgeRiemPairFam, edgeRiemPartner,
    edgeKernelPair, edgeKernelPartner, edgeLiePairFam, edgeLiePartner,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_add_left, appCc_sub_left, appCc_smul_left,
    real_inner_add_left, real_inner_add_right, real_inner_sub_left,
    real_inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp_rw [edgePair_inner (I := I) (M := M) g]
  module

/-- Green form of the complete top refold pairing.  All second derivatives of
`T` have been moved onto the explicit formal partner before any estimate is
taken. -/
theorem edgeTop_green
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T⟫_Real : Real) =
      -⟪covDivergence (I := I) (M := M) g 3
          (edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
            qA qB q epsilon s),
        iteratedCovGrad (I := I) g 0 2 1 T⟫_Real := by
  let P : SmoothCcTensor g 0 4 :=
    edgeTopPartner (I := I) (M := M) g T hdelta hdeltaZ
      qA qB q epsilon s
  let T₁ : SmoothCcTensor g 0 3 := iteratedCovGrad (I := I) g 0 2 1 T
  have hjet : iteratedCovGrad (I := I) g 0 2 2 T =
      covGrad (I := I) (M := M) g 0 3 T₁ := by
    rw [T₁]
    exact (iteratedCovGrad_succ g 0 2 1 T).symm
  have hgreen :
      (⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_Real : Real) =
        -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_Real := by
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 3 T₁ P
  calc
    (⟪T, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T⟫_Real : Real) =
        ⟪P, iteratedCovGrad (I := I) g 0 2 2 T⟫_Real := by
      exact edgeTop_inner (I := I) (M := M) g T hdelta hdeltaZ
        qA qB q epsilon s
    _ = ⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_Real := by
      rw [hjet, real_inner_comm]
    _ = -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_Real := hgreen
    _ = -⟪covDivergence (I := I) (M := M) g 3 P, T₁⟫_Real := by
      rw [real_inner_comm]

/-- Exact full nonlinear refold on the closed-edge segment.

No Sobolev or derivative bound is assumed: for the fixed smooth tensor `W`, a
finite jet radius is constructed internally only to instantiate the public
exact refold packages.  The returned top coefficient has an explicit
pointwise `O(delta)` bound.  The order-zero refold family is uniformly bounded
on the whole segment, while `edgeRicciHalf`, `edgeFold0`, and `edgeQuad1` stay
visible for the subsequent low-edge joint estimate. -/
theorem exists_edgeRefold
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g W x v w = ccTensorBilin (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B₀ : Real, 0 ≤ B₀ ∧
      ∃ (C₀ : Real → SmoothCcTensor g 2 2)
        (C₂ : Real → SmoothCcTensor g 4 2),
        (∀ s ∈ Set.Icc (0 : Real) 1,
          edgeQuadArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W =
            (-2 : Real) • appCc (I := I) (M := M) g 2 2
                (edgeRicciHalf (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s)) W +
              appCc (I := I) (M := M) g 2 2 (C₀ s) W +
              appCc (I := I) (M := M) g 2 2
                (edgeFold0 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
              appCc (I := I) (M := M) g 3 2
                (edgeQuad1 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
                (iteratedCovGrad (I := I) g 0 2 1 W) +
              appCc (I := I) (M := M) g 4 2 (C₂ s)
                (iteratedCovGrad (I := I) g 0 2 2 W)) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C₀ s).toSection x) ≤ B₀ ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((C₂ s).toSection x) ≤
            2 * (max (8 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta))) 0) ^ 2 +
              2 * (max (3 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta) ^ 2)) 0) ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1,
          (⟪W, edgeQuadArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W⟫_Real : Real) =
            (-2 : Real) *
                ⟪W, appCc (I := I) (M := M) g 2 2
                  (edgeRicciHalf (I := I) (M := M) g
                    (edgeMetric (I := I) (M := M) g W hdelta s)) W⟫_Real +
              ⟪W, appCc (I := I) (M := M) g 2 2 (C₀ s) W⟫_Real +
              ⟪W, appCc (I := I) (M := M) g 2 2
                (edgeFold0 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W⟫_Real +
              ⟪W, appCc (I := I) (M := M) g 3 2
                (edgeQuad1 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
                (iteratedCovGrad (I := I) g 0 2 1 W)⟫_Real +
              ⟪W, appCc (I := I) (M := M) g 4 2 (C₂ s)
                (iteratedCovGrad (I := I) g 0 2 2 W)⟫_Real) := by
  classical
  let a : Nat := 2 * Module.finrank Real E + 10
  let R : Real := ∑ j ∈ Finset.range (a + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j W‖
  have ha : 2 * Module.finrank Real E + 10 ≤ a := by rfl
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg fun j _ => norm_nonneg _
  have hball : ∀ j : Nat, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g 0 2 j W‖ ≤ R := by
    intro j hj
    exact Finset.single_le_sum
      (f := fun k => ‖iteratedCovGrad (I := I) g 0 2 k W‖)
      (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hhalf_lt : (1 / 2 : Real) < 1 := by norm_num
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half hhalf_lt
  let hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta :=
    edgeZeroBoundAt (I := I) (M := M) g hdelta_nn
  obtain ⟨LambdaR, hLambdaR, KR, hKR, qA, qB, hq, hRmain⟩ :=
    exists_riemannPalatini_refold_identity_data (I := I) (M := M)
      g a ha hR hhalf_lt
  obtain ⟨LambdaD, hLambdaD, KD, hKD, q, epsilon, hepsilon, hDmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M)
      g g_bg a ha hR hhalf_lt
  obtain ⟨C0R, hjR, hidR, hsupR, henvR⟩ :=
    hRmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨C0D, hjD, hidD, hsupD, henvD⟩ :=
    hDmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨K2D, hK2D, hDcap⟩ :=
    exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow
      (I := I) (M := M) g a ha hR hhalf_lt q epsilon hepsilon
  obtain ⟨hj2D, hsup2D, henv2D⟩ :=
    hDcap W hdelta_half hdelta hdeltaZ hball
  have hsup2R := riemannPalatiniRefoldC2Family_rfns_le
    (I := I) (M := M) g W hdelta_lt hdelta_half hdelta hdeltaZ qA qB hq
  let C₀ : Real → SmoothCcTensor g 2 2 := fun s => C0R s + C0D s
  let C₂ : Real → SmoothCcTensor g 4 2 := fun s =>
    (2 : Real) •
        riemannPalatiniRefoldC2Family (I := I) (M := M) g W hdelta hdeltaZ qA qB s +
      deTurckLieCovDerivRefoldC2Family
        (I := I) (M := M) g W hdelta hdeltaZ q epsilon s
  have hnormal : ∀ s ∈ Set.Icc (0 : Real) 1,
      edgeQuadArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W =
        (-2 : Real) • appCc (I := I) (M := M) g 2 2
            (edgeRicciHalf (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s)) W +
          appCc (I := I) (M := M) g 2 2 (C₀ s) W +
          appCc (I := I) (M := M) g 2 2
            (edgeFold0 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
          appCc (I := I) (M := M) g 3 2
            (edgeQuad1 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          appCc (I := I) (M := M) g 4 2 (C₂ s)
            (iteratedCovGrad (I := I) g 0 2 2 W) := by
    intro s hs
    have hmetric := edgeMetric_bal (I := I) (M := M) g W hdelta_lt hdelta hdeltaZ hs
    have hriem := hidR s hs
    have hlie := hidD s hs
    simp only [iteratedCovGrad_zero] at hriem hlie
    rw [hmetric]
    simp only [edgeQuadArm, edgeLowerArm, edgeQuad0,
      deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      appCc_add_left, appCc_sub_left, appCc_smul_left]
    rw [hriem, hlie]
    simp only [edgeRicciHalf, edgeFold0, C₀, C₂,
      appCc_add_left, appCc_sub_left, appCc_smul_left]
    module
  have hBsq : 0 ≤ 2 * LambdaR ^ 2 + 2 * LambdaD ^ 2 := by positivity
  refine ⟨Real.sqrt (2 * LambdaR ^ 2 + 2 * LambdaD ^ 2), Real.sqrt_nonneg _,
    C₀, C₂, ?_, ?_, ?_, ?_⟩
  · exact hnormal
  · intro s hs x
    dsimp only [C₀]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 2 2 x ((C0R s).toSection x) ((C0D s).toSection x)
    have hR0 := hsupR s hs x
    have hD0 := hsupD s hs x
    rw [Real.sq_sqrt hBsq]
    linarith
  · intro s hs x
    dsimp only [C₂]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
      (((2 : Real) •
        riemannPalatiniRefoldC2Family
          (I := I) (M := M) g W hdelta hdeltaZ qA qB s).toSection x)
      ((deTurckLieCovDerivRefoldC2Family
        (I := I) (M := M) g W hdelta hdeltaZ q epsilon s).toSection x)
    have hR2 := hsup2R s hs x
    have hD2 := hsup2D s hs x
    linarith
  · intro s hs
    have hid := hnormal s hs
    rw [hid]
    simp only [real_inner_add_right, real_inner_smul_right]

/-- Consumer-shaped full slope normal form.  This composes the closed-edge
three-arm cancellation with `exists_edgeRefold`; no residual coefficient or
pairing identity is supplied as a hypothesis. -/
theorem exists_edgeSlopeRef
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g W x v w = ccTensorBilin (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B₀ : Real, 0 ≤ B₀ ∧
      ∃ (C₀ : Real → SmoothCcTensor g 2 2)
        (C₂ : Real → SmoothCcTensor g 4 2),
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C₀ s).toSection x) ≤ B₀ ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((C₂ s).toSection x) ≤
            2 * (max (8 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta))) 0) ^ 2 +
              2 * (max (3 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta) ^ 2)) 0) ^ 2) ∧
        ∀ (x : M) (v w : TangentSpace I x) {s : Real},
          s ∈ Set.Ioo (0 : Real) 1 →
          DeTurckCoefficients.rhsSumSlope (I := I) g g_bg W 0
              (lt_of_le_of_lt hdelta_half (by norm_num : (1 / 2 : Real) < 1)) hdelta
              (show (0 : Real) < 1 by norm_num)
              (edgeZeroBound (I := I) (M := M) g) x v w s =
            unitModel (I := I) (M := M) g 2
              ((rawTensorConnLapSmooth (I := I) g 0 2 W +
                  deTurckPrincipalCometricArm (I := I) (M := M) g
                    (edgeMetric (I := I) (M := M) g W hdelta s) W) +
                (edgeCarryArm (I := I) (M := M) g g_bg W +
                  edgeRefoldArm (I := I) (M := M) g
                    (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W
                    (C₀ s) (C₂ s))) x ![v, w] := by
  obtain ⟨B₀, hB₀, C₀, C₂, hquad, hC₀, hC₂, hpair⟩ :=
    exists_edgeRefold (I := I) (M := M) g g_bg W hWsymm hdelta_nn hdelta_half hdelta
  refine ⟨B₀, hB₀, C₀, C₂, hC₀, hC₂, ?_⟩
  intro x v w s hs
  have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hslope := edgeSlope_split (I := I) (M := M) g g_bg W hWsymm
    (lt_of_le_of_lt hdelta_half (by norm_num : (1 / 2 : Real) < 1)) hdelta x v w hs
  rw [hslope, hquad s hscc]
  rfl

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
