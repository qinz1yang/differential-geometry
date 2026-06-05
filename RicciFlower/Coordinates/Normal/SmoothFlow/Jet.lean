import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.MeanValue
import RicciFlower.Analysis.ODE.FlowCInfinity
import RicciFlower.Coordinates.Normal.Flow

/-!
# Smooth-flow finite jet layer

This module contains the formal and finite-prefix jet API used by the
normal-coordinate smooth-flow infrastructure.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Filter
open scoped Manifold ContDiff Topology Uniformity
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

abbrev ModelPhase := E × E

abbrev ModelLin := ModelPhase (E := E) →L[Real] ModelPhase (E := E)

/-- Flat state space for the first augmented variational equation. -/
abbrev VarPhase := ModelPhase (E := E) × ModelLin (E := E)

/-- Linear maps on the flat augmented variational state space. -/
abbrev VarLin := VarPhase (E := E) →L[Real] VarPhase (E := E)

/-- Formal Taylor jet of a model-phase map at one initial phase. -/
abbrev ModelJet := FormalMultilinearSeries Real
  (ModelPhase (E := E)) (ModelPhase (E := E))

/-- The `n`th coefficient type in a model-phase jet. -/
abbrev ModelJetCoeff (n : Nat) :=
  ContinuousMultilinearMap Real
    (fun _ : Fin n => ModelPhase (E := E)) (ModelPhase (E := E))

/-- Finite prefix of a model-phase jet through order `N`.

This is the finite normed state space needed for smooth finite-jet ODEs.  The
full `ModelJet` remains a `FormalMultilinearSeries`; `ModelJetPrefix N`
packages the coefficients that a finite-order argument can actually use. -/
abbrev ModelJetPrefix (N : Nat) :=
  (k : Fin (N + 1)) -> ModelJetCoeff (E := E) k.1

/-- Zeroth coefficient of a formal model-phase jet. -/
def jetBase (J : ModelJet (E := E)) : ModelPhase (E := E) :=
  (J 0).curry0

/-- Taylor jet in the initial phase of a model flow at a fixed time. -/
def flowJet
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelJet (E := E) :=
  ftaylorSeries Real (fun z' : ModelPhase (E := E) => Φ z' t) z

/-- Initial Taylor jet of the identity flow. -/
def idJet (z : ModelPhase (E := E)) : ModelJet (E := E) :=
  ftaylorSeries Real (fun z' : ModelPhase (E := E) => z') z

/-- Faà di Bruno right-hand side for the formal Taylor jet of `z' = F z`. -/
def jetRHS
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) : ModelJet (E := E) :=
  (ftaylorSeries Real F (jetBase (E := E) J)).taylorComp J

/-- Specialized jet right-hand side for the fixed-chart model spray. -/
def sprayJetRHS
    (g : SmoothRiemannianMetric I M) (x : M)
    (J : ModelJet (E := E)) : ModelJet (E := E) :=
  jetRHS (E := E) (modelSpray (I := I) g x) J

namespace ModelJet

/-- Truncate a full formal model jet at order `N`, keeping coefficients
`0, ..., N` and setting all higher coefficients to zero.  The current
`ModelJet` API uses full `FormalMultilinearSeries`; finite order is carried by
predicates such as `IsFlowJetUpTo`, so truncation is an operation on full
series rather than a separate indexed jet type. -/
def trunc (N : Nat) (J : ModelJet (E := E)) : ModelJet (E := E) :=
  fun n => if n <= N then J n else 0

@[simp] theorem trunc_coeff_of_le
    (N n : Nat) (J : ModelJet (E := E)) (hn : n <= N) :
    trunc (E := E) N J n = J n := by
  simp [trunc, hn]

@[simp] theorem trunc_coeff_of_not_le
    (N n : Nat) (J : ModelJet (E := E)) (hn : ¬ n <= N) :
    trunc (E := E) N J n = 0 := by
  simp [trunc, hn]

theorem trunc_coeff_eq_of_le
    {N n : Nat} {J K : ModelJet (E := E)}
    (hJK : ∀ k, k <= n -> J k = K k) (hn : n <= N) :
    trunc (E := E) N J n = K n := by
  rw [trunc_coeff_of_le (E := E) N n J hn, hJK n le_rfl]

@[simp] theorem trunc_trunc
    (N : Nat) (J : ModelJet (E := E)) :
    trunc (E := E) N (trunc (E := E) N J) = trunc (E := E) N J := by
  apply FormalMultilinearSeries.ext
  intro n
  by_cases hn : n <= N
  · simp [hn]
  · simp [hn]

end ModelJet

namespace ModelJetPrefix

/-- Zeroth coefficient of a finite model jet prefix. -/
def base (N : Nat) (P : ModelJetPrefix (E := E) N) : ModelPhase (E := E) :=
  (P ⟨0, Nat.succ_pos N⟩).curry0

/-- Take the finite prefix of a full formal model jet. -/
def ofJet (N : Nat) (J : ModelJet (E := E)) : ModelJetPrefix (E := E) N :=
  fun k => J k.1

/-- Extend a finite jet prefix to a full formal model jet by filling higher
orders with zero. -/
def toJet (N : Nat) (P : ModelJetPrefix (E := E) N) : ModelJet (E := E) :=
  fun n => if h : n <= N then P ⟨n, Nat.lt_succ_of_le h⟩ else 0

@[simp] theorem ofJet_apply
    (N : Nat) (J : ModelJet (E := E)) (k : Fin (N + 1)) :
    ofJet (E := E) N J k = J k.1 := rfl

@[simp] theorem base_ofJet
    (N : Nat) (J : ModelJet (E := E)) :
    base (E := E) N (ofJet (E := E) N J) = jetBase (E := E) J := rfl

@[simp] theorem base_toJet
    (N : Nat) (P : ModelJetPrefix (E := E) N) :
    jetBase (E := E) (toJet (E := E) N P) = base (E := E) N P := by
  simp [base, jetBase, toJet]

theorem coeff_contDiffAt
    {n : WithTop ℕ∞} (N : Nat) (P : ModelJetPrefix (E := E) N)
    (k : Fin (N + 1)) :
    ContDiffAt Real n (fun Q : ModelJetPrefix (E := E) N => Q k) P :=
  contDiffAt_pi.mp (contDiffAt_id (𝕜 := Real) (n := n) (x := P)) k

theorem base_contDiffAt
    {n : WithTop ℕ∞} (N : Nat) (P : ModelJetPrefix (E := E) N) :
    ContDiffAt Real n (base (E := E) N) P := by
  haveI : FiniteDimensional Real (ModelJetCoeff (E := E) 0) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let L :
      ModelJetCoeff (E := E) 0 →L[Real] ModelPhase (E := E) :=
    (continuousMultilinearCurryFin0 Real
      (ModelPhase (E := E)) (ModelPhase (E := E))).toContinuousLinearMap
  simpa [base, L] using
    ((coeff_contDiffAt (E := E) (n := n) N P ⟨0, Nat.succ_pos N⟩).continuousLinearMap_comp L)

@[simp] theorem toJet_coeff_of_le
    (N n : Nat) (P : ModelJetPrefix (E := E) N) (hn : n <= N) :
    toJet (E := E) N P n = P ⟨n, Nat.lt_succ_of_le hn⟩ := by
  simp [toJet, hn]

@[simp] theorem toJet_coeff_of_not_le
    (N n : Nat) (P : ModelJetPrefix (E := E) N) (hn : ¬ n <= N) :
    toJet (E := E) N P n = 0 := by
  simp [toJet, hn]

@[simp] theorem toJet_ofJet
    (N : Nat) (J : ModelJet (E := E)) :
    toJet (E := E) N (ofJet (E := E) N J) =
      ModelJet.trunc (E := E) N J := by
  apply FormalMultilinearSeries.ext
  intro n
  by_cases hn : n <= N
  · simp [hn]
  · simp [hn]

@[simp] theorem ofJet_toJet
    (N : Nat) (P : ModelJetPrefix (E := E) N) :
    ofJet (E := E) N (toJet (E := E) N P) = P := by
  funext k
  simp [toJet, Nat.lt_succ_iff.mp k.2]

/-- Drop the top coefficient of a finite jet prefix. -/
def trunc (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) :
    ModelJetPrefix (E := E) N :=
  fun k => P k.castSucc

@[simp] theorem trunc_apply
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) (k : Fin (N + 1)) :
    trunc (E := E) N P k = P k.castSucc := rfl

@[simp] theorem base_trunc
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) :
    base (E := E) N (trunc (E := E) N P) =
      base (E := E) (N + 1) P := rfl

@[simp] theorem trunc_ofJet
    (N : Nat) (J : ModelJet (E := E)) :
    trunc (E := E) N (ofJet (E := E) (N + 1) J) =
      ofJet (E := E) N J := by
  funext k
  rfl

@[simp] theorem toJet_trunc
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) :
    toJet (E := E) N (trunc (E := E) N P) =
      ModelJet.trunc (E := E) N (toJet (E := E) (N + 1) P) := by
  apply FormalMultilinearSeries.ext
  intro n
  by_cases hn : n <= N
  · have hn' : n <= N + 1 := le_trans hn (Nat.le_succ N)
    simp [toJet, trunc, ModelJet.trunc, hn, hn']
  · simp [toJet, ModelJet.trunc, hn]

/-- The shifted top coefficients of an `(N+1)`-prefix, curried as a linear map
from the initial variation to the `N`-prefix.  This is the finite-state
replacement for "the derivative of an `N`-jet is the next coefficient". -/
noncomputable def shiftedDeriv
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) :
    ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N :=
  ContinuousLinearMap.pi fun k =>
    (P ⟨k.1 + 1, by
      exact Nat.succ_lt_succ k.2⟩).curryLeft

@[simp] theorem shiftedDeriv_apply
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1))
    (h : ModelPhase (E := E)) (k : Fin (N + 1)) :
    shiftedDeriv (E := E) N P h k =
      (P ⟨k.1 + 1, by
        exact Nat.succ_lt_succ k.2⟩).curryLeft h := by
  rfl

end ModelJetPrefix

/-- Finite Taylor-jet prefix of a model flow at a fixed time. -/
def flowJetPrefix
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real) : ModelJetPrefix (E := E) N :=
  ModelJetPrefix.ofJet (E := E) N (flowJet (E := E) Φ z t)

/-- Finite Taylor-jet prefix of the identity flow. -/
def idJetPrefix (N : Nat) (z : ModelPhase (E := E)) : ModelJetPrefix (E := E) N :=
  ModelJetPrefix.ofJet (E := E) N (idJet (E := E) z)

@[simp] theorem flowJet_base
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    jetBase (E := E) (flowJet (E := E) Φ z t) = Φ z t := by
  simp [jetBase, flowJet, ftaylorSeries]

@[simp] theorem flowJetPrefix_base
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real) :
    ModelJetPrefix.base (E := E) N (flowJetPrefix (E := E) Φ N z t) = Φ z t := by
  simp [flowJetPrefix]

@[simp] theorem flowJetPrefix_apply
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real) (k : Fin (N + 1)) :
    flowJetPrefix (E := E) Φ N z t k =
      flowJet (E := E) Φ z t k.1 := rfl

@[simp] theorem idJet_base (z : ModelPhase (E := E)) :
    jetBase (E := E) (idJet (E := E) z) = z := by
  simp [jetBase, idJet, ftaylorSeries]

@[simp] theorem idJetPrefix_base
    (N : Nat) (z : ModelPhase (E := E)) :
    ModelJetPrefix.base (E := E) N (idJetPrefix (E := E) N z) = z := by
  simp [idJetPrefix]

@[simp] theorem idJetPrefix_apply
    (N : Nat) (z : ModelPhase (E := E)) (k : Fin (N + 1)) :
    idJetPrefix (E := E) N z k = idJet (E := E) z k.1 := rfl

@[simp] theorem flowJetPrefix_trunc
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real) :
    ModelJetPrefix.trunc (E := E) N (flowJetPrefix (E := E) Φ (N + 1) z t) =
      flowJetPrefix (E := E) Φ N z t := by
  funext k
  rfl

@[simp] theorem idJetPrefix_trunc
    (N : Nat) (z : ModelPhase (E := E)) :
    ModelJetPrefix.trunc (E := E) N (idJetPrefix (E := E) (N + 1) z) =
      idJetPrefix (E := E) N z := by
  funext k
  rfl

set_option linter.flexible false in
@[simp] theorem jetRHS_base
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    jetBase (E := E) (jetRHS (E := E) F J) = F (jetBase (E := E) J) := by
  simp [jetBase, jetRHS, FormalMultilinearSeries.taylorComp, ftaylorSeries]
  exact iteratedFDeriv_zero_apply (𝕜 := Real) (f := F) (x := (J 0) ![])
    ((OrderedFinpartition.atomic 0).applyOrderedFinpartition (fun m => J 1) ![])

@[simp] theorem flowJet_zero
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    flowJet (E := E) Φ z t 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E)) (Φ z t) := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simp [flowJet, ftaylorSeries]

@[simp] theorem idJet_zero (z : ModelPhase (E := E)) :
    idJet (E := E) z 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E)) z := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simp [idJet, ftaylorSeries]

@[simp] theorem idJet_two (z : ModelPhase (E := E)) :
    idJet (E := E) z 2 = 0 := by
  have hzero :
      iteratedFDeriv Real 2
        (fun z' : ModelPhase (E := E) => z') z = 0 := by
    apply ContinuousMultilinearMap.ext
    intro m
    rw [iteratedFDeriv_two_apply]
    have hfd :
        fderiv Real (fun z' : ModelPhase (E := E) => z') =
          fun _ : ModelPhase (E := E) =>
            ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
      funext y
      simp
    rw [hfd]
    simp
  simpa [idJet, ftaylorSeries] using hzero

/-- All identity-jet coefficients of order at least two vanish. -/
theorem idJet_succ2_zero
    (z : ModelPhase (E := E)) (m : Nat) :
    idJet (E := E) z (Nat.succ (Nat.succ m)) = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  have hfd :
      (fun y : ModelPhase (E := E) =>
          fderiv Real (fun z' : ModelPhase (E := E) => z') y) =
        fun _ : ModelPhase (E := E) =>
          ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
    funext y
    simp
  rw [idJet, ftaylorSeries, iteratedFDeriv_succ_apply_right, hfd]
  have hconst :
      iteratedFDeriv Real (m + 1)
        (fun _ : ModelPhase (E := E) =>
          ContinuousLinearMap.id Real (ModelPhase (E := E))) z = 0 := by
    simpa [Nat.succ_eq_add_one] using congrFun
      (iteratedFDeriv_const_of_ne
        (𝕜 := Real) (E := ModelPhase (E := E)) (F := ModelLin (E := E))
        (n := Nat.succ m) (Nat.succ_ne_zero m)
        (ContinuousLinearMap.id Real (ModelPhase (E := E)))) z
  rw [hconst]
  simp

@[simp] theorem idJet_high_zero
    (z : ModelPhase (E := E)) {n : Nat} (hn : 2 <= n) :
    idJet (E := E) z n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hnm : 2 + m = Nat.succ (Nat.succ m) := by omega
  rw [hnm]
  exact idJet_succ2_zero (E := E) z m

@[simp] theorem ModelJet.trunc_idJet
    (N : Nat) (hN : 1 <= N) (z : ModelPhase (E := E)) :
    ModelJet.trunc (E := E) N (idJet (E := E) z) = idJet (E := E) z := by
  apply FormalMultilinearSeries.ext
  intro n
  by_cases hn : n <= N
  · simp [hn]
  · have hlt : 1 < n := lt_of_le_of_lt hN (Nat.lt_of_not_ge hn)
    have h2 : 2 <= n := Nat.succ_le_of_lt hlt
    simp [ModelJet.trunc, hn, idJet_high_zero (E := E) z h2]

@[simp] theorem jetRHS_zero
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    jetRHS (E := E) F J 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E))
        (F (jetBase (E := E) J)) := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simpa [jetBase] using jetRHS_base (E := E) F J

/-- Low-order coefficients of the Faà di Bruno jet RHS only depend on the
same low-order coefficients of the input jet. -/
theorem jetRHS_trunc_coeff_of_le
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) {N n : Nat} (hn : n <= N) :
    jetRHS (E := E) F (ModelJet.trunc (E := E) N J) n =
      jetRHS (E := E) F J n := by
  have hbase :
      jetBase (E := E) (ModelJet.trunc (E := E) N J) =
        jetBase (E := E) J := by
    simp [jetBase, ModelJet.trunc]
  simp only [jetRHS, FormalMultilinearSeries.taylorComp]
  rw [hbase]
  apply Finset.sum_congr rfl
  intro c _hc
  apply ContinuousMultilinearMap.ext
  intro v
  have hpart : ∀ m, c.partSize m <= N := fun m =>
    le_trans (c.partSize_le m) hn
  simp [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ModelJet.trunc, hpart]

/-- The `n`th Faà di Bruno RHS coefficient only depends on the input jet
coefficients of order at most `n`. -/
theorem jetRHS_coeff_congr_of_le
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    {J K : ModelJet (E := E)} {n : Nat}
    (hJK : ∀ k, k <= n -> J k = K k) :
    jetRHS (E := E) F J n = jetRHS (E := E) F K n := by
  have hbase : jetBase (E := E) J = jetBase (E := E) K := by
    simp [jetBase, hJK 0 (Nat.zero_le n)]
  simp only [jetRHS, FormalMultilinearSeries.taylorComp]
  rw [hbase]
  apply Finset.sum_congr rfl
  intro c _hc
  apply ContinuousMultilinearMap.ext
  intro v
  simp [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    hJK, c.partSize_le]

/-- Truncation commutes with the Faà di Bruno RHS at the retained orders. -/
theorem jetRHS_trunc
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) (N : Nat) :
    ModelJet.trunc (E := E) N
        (jetRHS (E := E) F (ModelJet.trunc (E := E) N J)) =
      ModelJet.trunc (E := E) N (jetRHS (E := E) F J) := by
  apply FormalMultilinearSeries.ext
  intro n
  by_cases hn : n <= N
  · simp [hn, jetRHS_trunc_coeff_of_le (E := E) F J hn]
  · simp [hn]

/-- Finite-prefix version of the Faà di Bruno jet RHS. -/
def jetRHSPrefix
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N) : ModelJetPrefix (E := E) N :=
  ModelJetPrefix.ofJet (E := E) N
    (jetRHS (E := E) F (ModelJetPrefix.toJet (E := E) N P))

/-- Finite-prefix jet RHS for the fixed-chart model spray. -/
def sprayJetRHSPrefix
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N) : ModelJetPrefix (E := E) N :=
  jetRHSPrefix (E := E) (modelSpray (I := I) g x) N P

@[simp] theorem jetRHSPrefix_apply
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N) (k : Fin (N + 1)) :
    jetRHSPrefix (E := E) F N P k =
      jetRHS (E := E) F (ModelJetPrefix.toJet (E := E) N P) k.1 := rfl

@[simp] theorem jetRHSPrefix_base
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N) :
    ModelJetPrefix.base (E := E) N (jetRHSPrefix (E := E) F N P) =
      F (ModelJetPrefix.base (E := E) N P) := by
  simp [ModelJetPrefix.base, jetRHSPrefix]

@[simp] theorem sprayJetRHSPrefix_base
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N) :
    ModelJetPrefix.base (E := E) N
        (sprayJetRHSPrefix (I := I) g x N P) =
      modelSpray (I := I) g x (ModelJetPrefix.base (E := E) N P) := by
  simp [sprayJetRHSPrefix]

/-- The finite-prefix RHS agrees with the full RHS on finite prefixes. -/
theorem jetRHSPrefix_ofJet
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (J : ModelJet (E := E)) :
    jetRHSPrefix (E := E) F N (ModelJetPrefix.ofJet (E := E) N J) =
      ModelJetPrefix.ofJet (E := E) N (jetRHS (E := E) F J) := by
  funext k
  have hk : k.1 <= N := Nat.lt_succ_iff.mp k.2
  simp [jetRHSPrefix, jetRHS_trunc_coeff_of_le (E := E) F J hk]

theorem jetRHSPrefix_trunc
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) (N + 1)) :
    ModelJetPrefix.trunc (E := E) N (jetRHSPrefix (E := E) F (N + 1) P) =
      jetRHSPrefix (E := E) F N (ModelJetPrefix.trunc (E := E) N P) := by
  funext k
  have hkN : k.1 <= N := Nat.lt_succ_iff.mp k.2
  exact
    jetRHS_coeff_congr_of_le (E := E) F
      (J := ModelJetPrefix.toJet (E := E) (N + 1) P)
      (K := ModelJetPrefix.toJet (E := E) N (ModelJetPrefix.trunc (E := E) N P))
      (n := k.1)
      (by
        intro m hm
        have hmN : m <= N := le_trans hm hkN
        have hmN' : m <= N + 1 := le_trans hmN (Nat.le_succ N)
        simp [ModelJetPrefix.toJet, ModelJetPrefix.trunc, hmN, hmN'])

private theorem jetRHSPrefix_flowJetPrefix_coeff_eq_taylorComp
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real)
    (k : Fin (N + 1)) :
    jetRHSPrefix (E := E) F N
        (flowJetPrefix (E := E) Φ N z t) k =
      ((ftaylorSeries Real F (Φ z t)).taylorComp
        (flowJet (E := E) Φ z t)) k.1 := by
  have hk : k.1 <= N := Nat.lt_succ_iff.mp k.2
  simpa [jetRHSPrefix, flowJetPrefix, jetRHS, flowJet_base] using
    jetRHS_trunc_coeff_of_le (E := E) F
      (flowJet (E := E) Φ z t) hk

private theorem jetRHSPrefix_flowJetPrefix_shiftedDeriv_apply
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z h : ModelPhase (E := E)) (t : Real)
    (k : Fin (N + 1)) :
    ModelJetPrefix.shiftedDeriv (E := E) N
        (jetRHSPrefix (E := E) F (N + 1)
          (flowJetPrefix (E := E) Φ (N + 1) z t)) h k =
      (((ftaylorSeries Real F (Φ z t)).taylorComp
        (flowJet (E := E) Φ z t)) (k.1 + 1)).curryLeft h := by
  rw [ModelJetPrefix.shiftedDeriv_apply]
  exact congrArg
    (fun A : ModelJetCoeff (E := E) (k.1 + 1) => A.curryLeft h)
    (jetRHSPrefix_flowJetPrefix_coeff_eq_taylorComp
      (E := E) F Φ (N + 1) z t
      ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩)

private theorem jetRHSPrefix_term_contDiffAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    {N n : Nat} (P : ModelJetPrefix (E := E) N)
    (c : OrderedFinpartition n) (hn : n <= N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (fun Q : ModelJetPrefix (E := E) N =>
        (ftaylorSeries Real F (ModelJetPrefix.base (E := E) N Q)).compAlongOrderedFinpartition
          (ModelJetPrefix.toJet (E := E) N Q) c) P := by
  let B := c.compAlongOrderedFinpartitionL Real
    (ModelPhase (E := E)) (ModelPhase (E := E)) (ModelPhase (E := E))
  have hFder :
      ContDiffAt Real ∞
        (fun y : ModelPhase (E := E) =>
          iteratedFDeriv Real c.length F y)
        (ModelJetPrefix.base (E := E) N P) :=
    hF.iteratedFDeriv_right (m := ∞) (i := c.length) (by
      have htop_add :
          ((⊤ : ℕ∞) : WithTop ℕ∞) + (c.length : WithTop ℕ∞) =
            ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        induction c.length with
        | zero => simp
        | succ m ih =>
            rw [Nat.cast_succ, ← add_assoc, ih, ENat.coe_top_add_one]
      change ((⊤ : ℕ∞) : WithTop ℕ∞) + (c.length : WithTop ℕ∞) <=
        ((⊤ : ℕ∞) : WithTop ℕ∞)
      rw [htop_add])
  have hq :
      ContDiffAt Real ∞
        (fun Q : ModelJetPrefix (E := E) N =>
          iteratedFDeriv Real c.length F (ModelJetPrefix.base (E := E) N Q)) P :=
    hFder.comp P (ModelJetPrefix.base_contDiffAt (E := E) (n := ∞) N P)
  have hp :
      ContDiffAt Real ∞
        (fun Q : ModelJetPrefix (E := E) N =>
          fun i : Fin c.length => ModelJetPrefix.toJet (E := E) N Q (c.partSize i)) P := by
    rw [contDiffAt_pi]
    intro i
    have hpart : c.partSize i <= N := le_trans (c.partSize_le i) hn
    simpa [ModelJetPrefix.toJet, hpart] using
      ModelJetPrefix.coeff_contDiffAt (E := E) (n := ∞) N P
        ⟨c.partSize i, Nat.lt_succ_of_le hpart⟩
  have hpair : ContDiffAt Real ∞
      (fun Q : ModelJetPrefix (E := E) N =>
        (iteratedFDeriv Real c.length F (ModelJetPrefix.base (E := E) N Q),
          fun i : Fin c.length => ModelJetPrefix.toJet (E := E) N Q (c.partSize i))) P :=
    hq.prodMk hp
  have hB :
      ContDiffAt Real ∞
        (fun p :
          (ModelPhase (E := E) [×c.length]→L[Real] ModelPhase (E := E)) ×
            ((i : Fin c.length) -> ModelJetCoeff (E := E) (c.partSize i)) =>
          B p.1 p.2)
        ((iteratedFDeriv Real c.length F (ModelJetPrefix.base (E := E) N P)),
          fun i : Fin c.length => ModelJetPrefix.toJet (E := E) N P (c.partSize i)) :=
    B.analyticAt_uncurry_of_multilinear.contDiffAt
  simpa [B, ftaylorSeries, Function.comp_def] using hB.comp P hpair

theorem jetRHSPrefix_zero_contDiffAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (fun Q : ModelJetPrefix (E := E) N =>
        jetRHSPrefix (E := E) F N Q ⟨0, Nat.succ_pos N⟩) P := by
  let L :
      ModelPhase (E := E) →L[Real] ModelJetCoeff (E := E) 0 :=
    (continuousMultilinearCurryFin0 Real
      (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
  have hcomp :
      ContDiffAt Real ∞
        (fun Q : ModelJetPrefix (E := E) N =>
          L (F (ModelJetPrefix.base (E := E) N Q))) P :=
    (hF.comp P (ModelJetPrefix.base_contDiffAt (E := E) (n := ∞) N P)).continuousLinearMap_comp L
  simpa [jetRHSPrefix, ModelJetPrefix.base_toJet, L] using hcomp

theorem jetRHSPrefix_contDiffAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞ (jetRHSPrefix (E := E) F N) P := by
  rw [contDiffAt_pi]
  intro k
  have hk : k.1 <= N := Nat.lt_succ_iff.mp k.2
  change ContDiffAt Real ∞
    (fun Q : ModelJetPrefix (E := E) N =>
      ∑ c : OrderedFinpartition k.1,
        (ftaylorSeries Real F (ModelJetPrefix.base (E := E) N Q)).compAlongOrderedFinpartition
          (ModelJetPrefix.toJet (E := E) N Q) c) P
  apply ContDiffAt.sum
  intro c _hc
  exact jetRHSPrefix_term_contDiffAt (E := E) F P c hk hF

theorem sprayJetRHSPrefix_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (hztarget :
      ModelJetPrefix.base (E := E) N P ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc :
      (phaseOfModel (I := I) x (ModelJetPrefix.base (E := E) N P)).proj ∈
        (extChartAt I x).source) :
    ContDiffAt Real ∞
      (jetRHSPrefix (E := E) (modelSpray (I := I) g x) N) P :=
  jetRHSPrefix_contDiffAt (E := E) (modelSpray (I := I) g x) N P
    (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- The first jet coefficient recovers the Frechet derivative. -/
theorem flowJet_one
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) {A : ModelLin (E := E)}
    (hA : HasFDerivAt (fun z' : ModelPhase (E := E) => Φ z' t) A z) :
    continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))
        (flowJet (E := E) Φ z t 1) =
      A := by
  apply ContinuousLinearMap.ext
  intro h
  rw [continuousMultilinearCurryFin1_apply]
  simp [flowJet, ftaylorSeries, hA.fderiv]

/-- Each coefficient of the identity jet depends smoothly on the base point.
Only the zeroth coefficient varies; the first is constant and all higher
coefficients vanish. -/
theorem idJet_coeff_contDiffAt
    (n : Nat) (z : ModelPhase (E := E)) :
    ContDiffAt Real ∞ (fun y : ModelPhase (E := E) => idJet (E := E) y n) z := by
  rcases Nat.lt_trichotomy n 1 with hn | hn | hn
  · have hn0 : n = 0 := by omega
    subst n
    let L : ModelPhase (E := E) →L[Real] ModelJetCoeff (E := E) 0 :=
      (continuousMultilinearCurryFin0 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
    simpa [L] using L.contDiff.contDiffAt (x := z)
  · subst n
    let C : ModelJetCoeff (E := E) 1 :=
      (continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))).symm
          (ContinuousLinearMap.id Real (ModelPhase (E := E)))
    have hconst : ContDiffAt Real ∞ (fun _ : ModelPhase (E := E) => C) z :=
      contDiffAt_const
    have hC : (fun y : ModelPhase (E := E) => idJet (E := E) y 1) =
        fun _ : ModelPhase (E := E) => C := by
      funext y
      apply (continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))).injective
      apply ContinuousLinearMap.ext
      intro h
      simp [C, idJet, ftaylorSeries, continuousMultilinearCurryFin1_apply]
    simpa [hC] using hconst
  · have hn2 : 2 <= n := by omega
    have hzero : (fun y : ModelPhase (E := E) => idJet (E := E) y n) =
        fun _ : ModelPhase (E := E) => 0 := by
      funext y
      simp [idJet_high_zero (E := E) y hn2]
    simpa [hzero] using
      (contDiffAt_const :
        ContDiffAt Real ∞
          (fun _ : ModelPhase (E := E) => (0 : ModelJetCoeff (E := E) n)) z)

theorem idJetPrefix_contDiffAt
    (N : Nat) (z : ModelPhase (E := E)) :
    ContDiffAt Real ∞ (idJetPrefix (E := E) N) z := by
  rw [contDiffAt_pi]
  intro k
  simpa [idJetPrefix] using idJet_coeff_contDiffAt (E := E) k.1 z

/-- If a fixed-time flow endpoint has a Taylor series through order `N + 1`,
then the derivative of its finite `N`-jet prefix is given by the shifted
coefficient prefix. -/
theorem flowJetPrefix_hasFDerivAt_of_hasFTaylor
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real)
    (hp :
      HasFTaylorSeriesUpTo (𝕜 := Real) (N + 1 : Nat)
        (fun y : ModelPhase (E := E) => Φ y t)
        (fun y : ModelPhase (E := E) => flowJet (E := E) Φ y t)) :
    HasFDerivAt
      (fun y : ModelPhase (E := E) => flowJetPrefix (E := E) Φ N y t)
      (ModelJetPrefix.shiftedDeriv (E := E) N
        (flowJetPrefix (E := E) Φ (N + 1) z t))
      z := by
  apply hasFDerivAt_pi''
  intro k
  have hk : k.1 < (N + 1 : WithTop ℕ∞) := by
    exact_mod_cast k.2
  exact hp.fderiv k.1 hk z

/-- Faa di Bruno bridge for the finite jet-prefix RHS along an actual fixed
time Taylor jet: differentiating the `N`-prefix RHS gives the shifted
`(N+1)`-prefix RHS. -/
theorem jetRHSPrefix_flowJetPrefix_hasFDerivAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real)
    (hF :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        F
        (fun y : ModelPhase (E := E) => ftaylorSeries Real F y)
        Set.univ)
    (hΦ :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        (fun y : ModelPhase (E := E) => Φ y t)
        (fun y : ModelPhase (E := E) => flowJet (E := E) Φ y t)
        Set.univ) :
    HasFDerivAt
      (fun y : ModelPhase (E := E) =>
        jetRHSPrefix (E := E) F N
          (flowJetPrefix (E := E) Φ N y t))
      (ModelJetPrefix.shiftedDeriv (E := E) N
        (jetRHSPrefix (E := E) F (N + 1)
          (flowJetPrefix (E := E) Φ (N + 1) z t)))
      z := by
  have hcomp :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        (fun y : ModelPhase (E := E) => F (Φ y t))
        (fun y : ModelPhase (E := E) =>
          (ftaylorSeries Real F (Φ y t)).taylorComp
            (flowJet (E := E) Φ y t))
        Set.univ := by
    simpa [Function.comp_def] using hF.comp hΦ (Set.mapsTo_univ _ _)
  apply hasFDerivAt_pi''
  intro k
  have hk : k.1 < (N + 1 : WithTop ℕ∞) := by
    exact_mod_cast k.2
  have hderiv :=
    (hasFTaylorSeriesUpToOn_univ_iff.mp hcomp).fderiv k.1 hk z
  have hfun :
      (fun y : ModelPhase (E := E) =>
        jetRHSPrefix (E := E) F N
          (flowJetPrefix (E := E) Φ N y t) k)
      =
      (fun y : ModelPhase (E := E) =>
        ((ftaylorSeries Real F (Φ y t)).taylorComp
          (flowJet (E := E) Φ y t)) k.1) := by
    funext y
    exact jetRHSPrefix_flowJetPrefix_coeff_eq_taylorComp
      (E := E) F Φ N y t k
  have hderiv_eq :
      ((ContinuousLinearMap.proj k).comp
          (ModelJetPrefix.shiftedDeriv (E := E) N
            (jetRHSPrefix (E := E) F (N + 1)
              (flowJetPrefix (E := E) Φ (N + 1) z t))))
        =
        (((ftaylorSeries Real F (Φ z t)).taylorComp
          (flowJet (E := E) Φ z t)) (k.1 + 1)).curryLeft := by
    apply ContinuousLinearMap.ext
    intro h
    exact jetRHSPrefix_flowJetPrefix_shiftedDeriv_apply
      (E := E) F Φ N z h t k
  rw [hderiv_eq]
  exact hderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrFun hfun y)

/-- The second jet coefficient is the second iterated Frechet derivative. -/
theorem flowJet_two_apply
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real)
    (m : Fin 2 -> ModelPhase (E := E)) :
    flowJet (E := E) Φ z t 2 m =
      fderiv Real (fderiv Real (fun z' : ModelPhase (E := E) => Φ z' t)) z
        (m 0) (m 1) := by
  simp [flowJet, ftaylorSeries, iteratedFDeriv_two_apply]

set_option linter.flexible false in
/-- First jet coefficient of the Faà di Bruno RHS. -/
theorem jetRHS_one
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))
        (jetRHS (E := E) F J 1) =
      (fderiv Real F (jetBase (E := E) J)).comp
        (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E)) (J 1)) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [continuousMultilinearCurryFin1_apply, ContinuousLinearMap.comp_apply,
    continuousMultilinearCurryFin1_apply]
  simp [jetRHS, jetBase, FormalMultilinearSeries.taylorComp, ftaylorSeries]
  have hiter :=
    iteratedFDeriv_one_apply (𝕜 := Real) (f := F) (x := (J 0) ![])
      (m := (OrderedFinpartition.atomic 1).applyOrderedFinpartition (fun m => J 1) ![h])
  refine hiter.trans ?_
  apply congrArg (fderiv Real F ((J 0) ![]))
  change J 1
      (![h] ∘ (OrderedFinpartition.atomic 1).emb
        ⟨0, by simp [OrderedFinpartition.atomic]⟩) =
    J 1 ![h]
  apply congrArg (J 1)
  funext i
  fin_cases i
  rfl

/-- Finite-prefix jet ODE target.  Unlike `IsFlowJetUpTo`, this predicate
lives in the finite normed state space `ModelJetPrefix N`. -/
def IsFlowJetPrefix
    (N : Nat)
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJetPrefix (E := E) N)
    (T : Set Real) : Prop :=
  (∀ z t, t ∈ T -> ModelJetPrefix.base (E := E) N (J z t) = Φ z t) ∧
    (∀ z, J z 0 = idJetPrefix (E := E) N z) ∧
      ∀ k : Fin (N + 1), ∀ z t, t ∈ T ->
        HasDerivWithinAt (fun τ : Real => J z τ k)
          (jetRHSPrefix (E := E) F N (J z t) k) T t

/-- Finite-prefix jet ODE target specialized to the fixed-chart model spray. -/
def IsModelJetPrefix
    (N : Nat)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJetPrefix (E := E) N)
    (T : Set Real) : Prop :=
  IsFlowJetPrefix (E := E) N (modelSpray (I := I) g x) Φ J T

/-- Finite-order jet ODE target.  A future induction should construct `J`
from the model flow and prove this predicate for every finite `N`. -/
def IsFlowJetUpTo
    (N : Nat)
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJet (E := E))
    (T : Set Real) : Prop :=
  (∀ z t, t ∈ T -> jetBase (E := E) (J z t) = Φ z t) ∧
    (∀ z, J z 0 = idJet (E := E) z) ∧
      ∀ n ≤ N, ∀ z t, t ∈ T ->
        HasDerivWithinAt (fun τ : Real => J z τ n)
          (jetRHS (E := E) F (J z t) n) T t

/-- Finite-order jet ODE target specialized to the fixed-chart model spray. -/
def IsModelFlowJetUpTo
    (N : Nat)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJet (E := E))
    (T : Set Real) : Prop :=
  IsFlowJetUpTo (E := E) N (modelSpray (I := I) g x) Φ J T

namespace IsFlowJetPrefix

/-- A full-series finite-order jet ODE target induces the corresponding
finite-prefix ODE target. -/
theorem of_full
    {N : Nat}
    {F : ModelPhase (E := E) -> ModelPhase (E := E)}
    {Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E)}
    {J : ModelPhase (E := E) -> Real -> ModelJet (E := E)}
    {T : Set Real}
    (h : IsFlowJetUpTo (E := E) N F Φ J T) :
    IsFlowJetPrefix (E := E) N F Φ
      (fun z t => ModelJetPrefix.ofJet (E := E) N (J z t)) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t ht
    simpa using h.1 z t ht
  · intro z
    simpa [idJetPrefix] using congrArg (ModelJetPrefix.ofJet (E := E) N) (h.2.1 z)
  · intro k z t ht
    have hk : k.1 <= N := Nat.lt_succ_iff.mp k.2
    have hderiv := h.2.2 k.1 hk z t ht
    simpa [jetRHSPrefix, jetRHS_trunc_coeff_of_le (E := E) F (J z t) hk] using hderiv

/-- A successor finite-prefix jet ODE target restricts to the previous finite
prefix by dropping the top coefficient. -/
theorem of_succ
    {N : Nat}
    {F : ModelPhase (E := E) -> ModelPhase (E := E)}
    {Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E)}
    {J : ModelPhase (E := E) -> Real -> ModelJetPrefix (E := E) (N + 1)}
    {T : Set Real}
    (h : IsFlowJetPrefix (E := E) (N + 1) F Φ J T) :
    IsFlowJetPrefix (E := E) N F Φ
      (fun z t => ModelJetPrefix.trunc (E := E) N (J z t)) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t ht
    simpa using h.1 z t ht
  · intro z
    simpa using congrArg (ModelJetPrefix.trunc (E := E) N) (h.2.1 z)
  · intro k z t ht
    have hderiv := h.2.2 k.castSucc z t ht
    have hkN : k.1 <= N := Nat.lt_succ_iff.mp k.2
    have hcoeff :
        jetRHS (E := E) F
            (ModelJet.trunc (E := E) N
              (ModelJetPrefix.toJet (E := E) (N + 1) (J z t))) k.1 =
          jetRHS (E := E) F
            (ModelJetPrefix.toJet (E := E) (N + 1) (J z t)) k.1 :=
      jetRHS_trunc_coeff_of_le (E := E) F
        (ModelJetPrefix.toJet (E := E) (N + 1) (J z t)) hkN
    simpa [jetRHSPrefix, ModelJetPrefix.toJet_trunc, hcoeff]
      using hderiv

end IsFlowJetPrefix

/-- Finite-order jet ODE targets are monotone in the jet order. -/
theorem IsFlowJetUpTo.of_le
    {N N' : Nat}
    {F : ModelPhase (E := E) -> ModelPhase (E := E)}
    {Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E)}
    {J : ModelPhase (E := E) -> Real -> ModelJet (E := E)}
    {T : Set Real}
    (h : IsFlowJetUpTo (E := E) N F Φ J T) (hN' : N' ≤ N) :
    IsFlowJetUpTo (E := E) N' F Φ J T := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro n hn z t ht
  exact h.2.2 n (le_trans hn hN') z t ht

/-- Successor step for the finite-order jet ODE target.  After order `N` is
known, the only new obligation for order `N + 1` is the ODE for the next
coefficient. -/
theorem IsFlowJetUpTo.succ
    {N : Nat}
    {F : ModelPhase (E := E) -> ModelPhase (E := E)}
    {Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E)}
    {J : ModelPhase (E := E) -> Real -> ModelJet (E := E)}
    {T : Set Real}
    (h : IsFlowJetUpTo (E := E) N F Φ J T)
    (hnext :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (fun τ : Real => J z τ (Nat.succ N))
          (jetRHS (E := E) F (J z t) (Nat.succ N)) T t) :
    IsFlowJetUpTo (E := E) (Nat.succ N) F Φ J T := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro n hn z t ht
  by_cases hnN : n ≤ N
  · exact h.2.2 n hnN z t ht
  · have hn_eq : n = Nat.succ N := by
      exact le_antisymm hn (Nat.succ_le_of_lt (Nat.lt_of_not_ge hnN))
    subst n
    exact hnext z t ht

/-- Induction principle for constructing finite-order jet ODE data.  This is
the high-order setup: the future analytic work is exactly to produce the
successor coefficient equation. -/
theorem flowJetUpTo_ind
    {F : ModelPhase (E := E) -> ModelPhase (E := E)}
    {Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E)}
    {J : ModelPhase (E := E) -> Real -> ModelJet (E := E)}
    {T : Set Real}
    (h0 : IsFlowJetUpTo (E := E) 0 F Φ J T)
    (hstep :
      ∀ N : Nat,
        IsFlowJetUpTo (E := E) N F Φ J T ->
          ∀ z : ModelPhase (E := E), ∀ t ∈ T,
            HasDerivWithinAt (fun τ : Real => J z τ (Nat.succ N))
              (jetRHS (E := E) F (J z t) (Nat.succ N)) T t) :
    ∀ N : Nat, IsFlowJetUpTo (E := E) N F Φ J T := by
  intro N
  induction N with
  | zero => exact h0
  | succ N ih =>
      exact IsFlowJetUpTo.succ (E := E) ih (hstep N ih)

/-- Zeroth-order case of the jet ODE: it is just the original flow equation. -/
theorem flowJetUpTo_zero
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    {T : Set Real}
    (hzero : ∀ z : ModelPhase (E := E), Φ z 0 = z)
    (hderiv :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (Φ z) (F (Φ z t)) T t) :
    IsFlowJetUpTo (E := E) 0 F Φ
      (fun z t => flowJet (E := E) Φ z t) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t _ht
    simp
  · intro z
    apply FormalMultilinearSeries.ext
    intro n
    simp [flowJet, idJet, hzero]
  · intro n hn z t ht
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    let L :
        ModelPhase (E := E) →L[Real]
          ContinuousMultilinearMap Real
            (fun _ : Fin 0 => ModelPhase (E := E)) (ModelPhase (E := E)) :=
      (continuousMultilinearCurryFin0 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
    have hcomp :
        HasDerivWithinAt (fun τ : Real => L (Φ z τ))
          (L (F (Φ z t))) T t :=
      L.hasFDerivAt.comp_hasDerivWithinAt t (hderiv z t ht)
    simpa [L] using hcomp

/-- First-order jet ODE bridge from a Frechet-derivative field satisfying the
variational equation. -/
theorem flowJetUpTo_one
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (A : ModelPhase (E := E) -> Real -> ModelLin (E := E))
    {T : Set Real}
    (hzero : ∀ z : ModelPhase (E := E), Φ z 0 = z)
    (hderiv :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (Φ z) (F (Φ z t)) T t)
    (hF :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasFDerivAt (fun z' : ModelPhase (E := E) => Φ z' t) (A z t) z)
    (hA :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (A z)
          ((fderiv Real F (Φ z t)).comp (A z t)) T t) :
    IsFlowJetUpTo (E := E) 1 F Φ
      (fun z t => flowJet (E := E) Φ z t) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t _ht
    simp
  · intro z
    apply FormalMultilinearSeries.ext
    intro n
    simp [flowJet, idJet, hzero]
  · intro n hn z t ht
    interval_cases n
    · exact (flowJetUpTo_zero (E := E) F Φ hzero hderiv).2.2 0 le_rfl z t ht
    · let L :
          ModelLin (E := E) →L[Real]
            ContinuousMultilinearMap Real
              (fun _ : Fin 1 => ModelPhase (E := E)) (ModelPhase (E := E)) :=
        (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
      have hcomp :
          HasDerivWithinAt (fun τ : Real => L (A z τ))
            (L ((fderiv Real F (Φ z t)).comp (A z t))) T t :=
        L.hasFDerivAt.comp_hasDerivWithinAt t (hA z t ht)
      have hfun :
          ∀ τ ∈ T,
            flowJet (E := E) Φ z τ 1 = L (A z τ) := by
        intro τ hτ
        apply (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).injective
        simp [L, flowJet_one (E := E) Φ z τ (hF z τ hτ)]
      have hrhs :
          jetRHS (E := E) F (flowJet (E := E) Φ z t) 1 =
            L ((fderiv Real F (Φ z t)).comp (A z t)) := by
        apply (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).injective
        rw [jetRHS_one]
        simp [L, flowJet_one (E := E) Φ z t (hF z t ht)]
      exact (hcomp.congr hfun (hfun t ht)).congr_deriv hrhs.symm


end Coordinates
end RicciFlower
