import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.MeanValue
import RicciFlower.Analysis.ODE.FlowCInfinity
import RicciFlower.Coordinates.Normal.Flow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smooth dependence for the fixed-chart model flow

This file starts the variational-equation route toward smooth dependence of the
fixed-chart geodesic model flow on its initial phase.
-/

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

/-- The coefficient of the forcing term in `gronwallBound 0 K ε t`. -/
private def gronwallCoeff (K t : Real) : Real :=
  if K = 0 then t else (Real.exp (K * t) - 1) / K

private theorem gronwallBound_zero_eq_mul (K ε t : Real) :
    gronwallBound 0 K ε t = ε * gronwallCoeff K t := by
  by_cases hK : K = 0
  · subst K
    simp [gronwallBound, gronwallCoeff]
  · simp [gronwallBound, gronwallCoeff, hK, div_eq_mul_inv]
    ring

/-- If the Taylor-residual coefficient tends to zero, then the corresponding
Gronwall forcing term is little-o in the perturbation. -/
private theorem gronwall_forcing_isLittleO
    {X : Type*} [NormedAddCommGroup X] {l : Filter X}
    {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0)) :
    (fun h : X => gronwallBound 0 B (C h * (L * ‖h‖)) T)
      =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hsmall : ∀ᶠ h in l, |C h| ≤ c / A := by
    have hAbs : Tendsto (fun h : X => |C h|) l (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : Real)).comp hC
    have hball :=
      hAbs.eventually (Metric.ball_mem_nhds (0 : Real) (div_pos hc hApos))
    filter_upwards [hball] with h hh
    have hlt : |C h| < c / A := by
      simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg (C h))] using hh
    exact le_of_lt hlt
  filter_upwards [hsmall] with h hh
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hdiv_nonneg : 0 ≤ c / A := by positivity
  have hcoef :
      (c / A) * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      (c / A) * (|L| * |gronwallCoeff B T|)
          ≤ (c / A) * A := by
            exact mul_le_mul_of_nonneg_left hP_le_A hdiv_nonneg
      _ = c := by
        field_simp [ne_of_gt hApos]
  calc
    ‖gronwallBound 0 B (C h * (L * ‖h‖)) T‖
        = |C h| * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          rw [gronwallBound_zero_eq_mul]
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hnorm]
          ring
    _ ≤ (c / A) * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hh hP_nonneg) hnorm
    _ ≤ c * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hcoef hnorm

/-- Turn a Gronwall forcing bound with a vanishing coefficient into a little-o
estimate for a vector-valued error. -/
private theorem isLittleO_of_gronwall_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0))
    (hbound : ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  have hg :=
    gronwall_forcing_isLittleO (X := X) (l := l)
      (C := C) (B := B) (L := L) (T := T) hC
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hbound, hg.bound hc] with h hf hg'
  exact hf.trans ((le_abs_self _).trans hg')

/-- A variant of `isLittleO_of_gronwall_bound` avoiding a chosen residual
coefficient: an eventual Gronwall bound with every positive constant is enough. -/
private theorem isLittleO_of_gronwall_bound_eventually
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {B L T : Real}
    (hbound : ∀ η > 0, ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  let η : Real := c / A
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hη_nonneg : 0 ≤ η := le_of_lt hηpos
  have hcoef : η * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      η * (|L| * |gronwallCoeff B T|) ≤ η * A := by
        exact mul_le_mul_of_nonneg_left hP_le_A hη_nonneg
      _ = c := by
        dsimp [η, A]
        field_simp [ne_of_gt hApos]
  filter_upwards [hbound η hηpos] with h hf
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hgr :
      ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖
        = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
    rw [gronwallBound_zero_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη_nonneg,
      abs_of_nonneg hnorm]
    ring
  calc
    ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T := hf
    _ ≤ ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖ := le_abs_self _
    _ = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := hgr
    _ ≤ c * ‖h‖ := by
      exact mul_le_mul_of_nonneg_right hcoef hnorm

section GenericC1Flow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]

/-- Error between a flow endpoint at `z + h` and the first-order variational
approximation at `z`.  This is the model-independent core of the C1
flow-dependence proof. -/
def flowError
    (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) : X :=
  Φ (z + h) t - Φ z t - A z t h

/-- Raw right-hand side of the model-independent variational error equation. -/
def flowErrorRHS
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) : X :=
  F (Φ (z + h) t) - F (Φ z t) -
    fderiv Real F (Φ z t) (A z t h)

/-- Taylor-residual part of the model-independent variational error equation. -/
def flowTaylorRem
    (F : X -> X) (Φ : X -> Real -> X)
    (z h : X) (t : Real) : X :=
  F (Φ (z + h) t) - F (Φ z t) -
    fderiv Real F (Φ z t) (Φ (z + h) t - Φ z t)

/-- Generic augmented vector field for a parameterized first variational
equation of `z' = F z`.  The second component is a linear map from an external
parameter space into the state space. -/
def paramVariationalRHS
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) : X × (P →L[Real] X) :=
  (F p.1, (fderiv Real F p.1).comp p.2)

@[simp] theorem paramVariationalRHS_fst
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) :
    (paramVariationalRHS F p).1 = F p.1 := rfl

@[simp] theorem paramVariationalRHS_snd
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) :
    (paramVariationalRHS F p).2 = (fderiv Real F p.1).comp p.2 := rfl

/-- Smoothness of the generic parameterized variational RHS follows from
smoothness of the base RHS. -/
theorem paramVariationalRHS_contDiffAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    {F : X -> X} {z : X} {A : P →L[Real] X}
    (hF : ContDiffAt Real ∞ F z) :
    ContDiffAt Real ∞ (paramVariationalRHS (P := P) F) (z, A) := by
  let L := P →L[Real] X
  let p0 : X × L := (z, A)
  have hF' :
      ContDiffAt Real ∞ (fun p : X × L => F p.1) p0 := by
    exact hF.comp p0 contDiffAt_fst
  have hDF0 : ContDiffAt Real ∞ (fderiv Real F) z := by
    exact hF.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
  have hDF :
      ContDiffAt Real ∞ (fun p : X × L => fderiv Real F p.1) p0 := by
    exact hDF0.comp p0 contDiffAt_fst
  have hA : ContDiffAt Real ∞ (fun p : X × L => p.2) p0 :=
    contDiffAt_snd
  have hcomp :
      ContDiffAt Real ∞
        (fun p : X × L => (fderiv Real F p.1).comp p.2) p0 := by
    exact hDF.clm_comp hA
  simpa [paramVariationalRHS, p0, L] using hF'.prodMk hcomp

/-- Generic augmented vector field for the first variational equation of
`z' = F z` with parameter space equal to the state space. -/
def variationalRHS
    (F : X -> X) (p : X × (X →L[Real] X)) : X × (X →L[Real] X) :=
  paramVariationalRHS (P := X) F p

@[simp] theorem variationalRHS_fst
    (F : X -> X) (p : X × (X →L[Real] X)) :
    (variationalRHS F p).1 = F p.1 := rfl

@[simp] theorem variationalRHS_snd
    (F : X -> X) (p : X × (X →L[Real] X)) :
    (variationalRHS F p).2 = (fderiv Real F p.1).comp p.2 := rfl

/-- Smoothness of the generic augmented variational RHS follows from
smoothness of the base RHS. -/
theorem variationalRHS_contDiffAt
    {F : X -> X} {z : X} {A : X →L[Real] X}
    (hF : ContDiffAt Real ∞ F z) :
    ContDiffAt Real ∞ (variationalRHS F) (z, A) :=
  paramVariationalRHS_contDiffAt (P := X) hF

/-- Base endpoint of a controlled augmented variational flow. -/
def controlledBaseEndpoint
    (Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X))
    (b : Real) (z : X) : X :=
  (Ψ (z, ContinuousLinearMap.id Real X) b).1

/-- Linear endpoint of a controlled augmented variational flow. -/
def controlledDerivEndpoint
    (Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X))
    (b : Real) (z : X) : X →L[Real] X :=
  (Ψ (z, ContinuousLinearMap.id Real X) b).2

/-- The base component of a generic augmented flow solves the original ODE. -/
theorem controlledBase_hasDerivWithinAt
    {F : X -> X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {z : X} {s : Set Real} {t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real X))
        (variationalRHS F (Ψ (z, ContinuousLinearMap.id Real X) t)) s t) :
    HasDerivWithinAt
      (controlledBaseEndpoint Ψ · z)
      (F (controlledBaseEndpoint Ψ t z)) s t := by
  let L := X →L[Real] X
  let A : L := ContinuousLinearMap.id Real X
  have hfst :
      HasFDerivWithinAt (fun q : X × L => q.1)
        (ContinuousLinearMap.fst Real X L) Set.univ
        (Ψ (z, A) t) :=
    (hasFDerivAt_fst (𝕜 := Real) (E := X) (F := L)
      (p := Ψ (z, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (z, A)) s Set.univ := by
    intro y hy
    trivial
  have hcomp := hfst.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, controlledBaseEndpoint, variationalRHS, L, A]
    using hcomp

/-- The linear component of a generic augmented flow solves the variational
equation. -/
theorem controlledDeriv_hasDerivWithinAt
    {F : X -> X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {z : X} {s : Set Real} {t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real X))
        (variationalRHS F (Ψ (z, ContinuousLinearMap.id Real X) t)) s t) :
    HasDerivWithinAt
      (controlledDerivEndpoint Ψ · z)
      ((fderiv Real F (controlledBaseEndpoint Ψ t z)).comp
        (controlledDerivEndpoint Ψ t z)) s t := by
  let L := X →L[Real] X
  let A : L := ContinuousLinearMap.id Real X
  have hsnd :
      HasFDerivWithinAt (fun q : X × L => q.2)
        (ContinuousLinearMap.snd Real X L) Set.univ
        (Ψ (z, A) t) :=
    (hasFDerivAt_snd (𝕜 := Real) (E := X) (F := L)
      (p := Ψ (z, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (z, A)) s Set.univ := by
    intro y hy
    trivial
  have hcomp := hsnd.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, controlledBaseEndpoint, controlledDerivEndpoint,
    variationalRHS, L, A] using hcomp

/-- Pointwise Taylor-residual estimate for a generic vector field on a convex
set. -/
theorem flowTaylorRem_norm_le
    {F : X -> X} {Φ : X -> Real -> X}
    (z h : X) (t : Real)
    {s : Set X} (hs : Convex Real s)
    (hFdiff : ∀ q ∈ s, DifferentiableAt Real F q)
    (hz : Φ z t ∈ s)
    (hzh : Φ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real F u - fderiv Real F (Φ z t)‖ ≤ C) :
    ‖flowTaylorRem F Φ z h t‖ ≤ C * ‖Φ (z + h) t - Φ z t‖ := by
  have hCalc :
      ‖F (Φ (z + h) t) - F (Φ z t) -
          (fderiv Real F (Φ z t)) ((Φ (z + h) t) - Φ z t)‖
        ≤ C * ‖(Φ (z + h) t) - Φ z t‖ := by
    refine hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := F) (f' := fun q => fderiv Real F q)
      (φ := fderiv Real F (Φ z t)) ?_ ?_ hz hzh
    · intro q hq
      exact ((hFdiff q hq).hasFDerivAt).hasFDerivWithinAt
    · intro q hq
      exact hD q hq
  simpa [flowTaylorRem] using hCalc

/-- Lipschitz dependence of an augmented flow controls separation of its base
endpoints. -/
theorem controlledBase_dist_le_of_lipschitz
    {x0 z h : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {t : Real}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hz :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r)
    (hzh :
      (z + h, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r) :
    dist (controlledBaseEndpoint Ψ t (z + h))
      (controlledBaseEndpoint Ψ t z) ≤ (L' : Real) * ‖h‖ := by
  let L := X →L[Real] X
  let idLin : L := ContinuousLinearMap.id Real X
  let pzh : X × L := (z + h, idLin)
  let pz : X × L := (z, idLin)
  have hdist := hLip.dist_le_mul pzh hzh pz hz
  have hfst :
      dist (controlledBaseEndpoint Ψ t (z + h))
        (controlledBaseEndpoint Ψ t z) ≤ dist (Ψ pzh t) (Ψ pz t) := by
    change dist (Ψ pzh t).1 (Ψ pz t).1 ≤ dist (Ψ pzh t) (Ψ pz t)
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hpdist : dist pzh pz = ‖h‖ := by
    have hzdist : dist (z + h) z = ‖h‖ := by
      rw [dist_eq_norm]
      have hsub : z + h - z = h := by
        abel
      rw [hsub]
    simp [pzh, pz, idLin, dist_prod_same_right, hzdist]
  exact hfst.trans (by simpa [hpdist] using hdist)

/-- Uniform continuity of `D F` in a tube around a compact base trajectory. -/
theorem fderiv_uniform_tube
    {F : X -> X} {K : Set Real} (hK : IsCompact K)
    {γ : Real -> X}
    (hγ : ContinuousOn γ K)
    (hDcont : ∀ y ∈ γ '' K, ContinuousAt (fderiv Real F) y) :
    ∀ c > 0, ∃ δ > 0, ∀ t ∈ K, ∀ u : X,
      dist u (γ t) < δ ->
        ‖fderiv Real F u - fderiv Real F (γ t)‖ ≤ c := by
  intro c hc
  let D : X -> (X →L[Real] X) := fderiv Real F
  have hcomp : IsCompact (γ '' K) :=
    hK.image_of_continuousOn hγ
  have hU :
      {p : X × X |
        p.1 ∈ γ '' K ->
          (D p.1, D p.2) ∈
            {q : (X →L[Real] X) × (X →L[Real] X) |
              dist q.1 q.2 < c}} ∈ 𝓤 X :=
    hcomp.uniformContinuousAt_of_continuousAt D hDcont
      (Metric.dist_mem_uniformity hc)
  rcases Metric.mem_uniformity_dist.mp hU with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu
  have hpair :
      ((γ t, u) : X × X) ∈
        {p : X × X |
          p.1 ∈ γ '' K ->
            (D p.1, D p.2) ∈
              {q : (X →L[Real] X) × (X →L[Real] X) |
                dist q.1 q.2 < c}} :=
    hδsub (by simpa [dist_comm] using hu)
  have hγmem : γ t ∈ γ '' K := ⟨t, ht, rfl⟩
  have hdist : dist (D (γ t)) (D u) < c := hpair hγmem
  have hnorm : ‖D u - D (γ t)‖ < c := by
    have hdist' : dist (D u) (D (γ t)) < c := by
      simpa [dist_comm] using hdist
    simpa [D, dist_eq_norm] using hdist'
  simpa [D] using le_of_lt hnorm

/-- The derivative of a vector field is bounded along a compact continuous
base trajectory if it is continuous along that trajectory. -/
theorem fderiv_bound_on_base
    {F : X -> X} {γ : Real -> X} {b : Real}
    (hγ : ContinuousOn γ (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ γ '' Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y) :
    ∃ B : Real, ∀ t ∈ Set.Icc (0 : Real) b,
      ‖fderiv Real F (γ t)‖ ≤ B := by
  have hDF :
      ContinuousOn (fun t : Real => fderiv Real F (γ t))
        (Set.Icc (0 : Real) b) := by
    intro t ht
    exact (hDcont (γ t) ⟨t, ht, rfl⟩).comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  exact isCompact_Icc.exists_bound_of_continuousOn hDF

/-- Lipschitz control of an augmented flow turns uniform continuity of `D F`
around the base trajectory into a derivative-difference estimate on trajectory
segments. -/
theorem controlled_fderiv_segment_small_of_lipschitz
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {b : Real}
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∃ ρ > 0, ∀ h : X,
      (L' : Real) * ‖h‖ < ρ ->
      (z + h, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (controlledBaseEndpoint Ψ t z)
          (controlledBaseEndpoint Ψ t (z + h)),
        ‖fderiv Real F u -
          fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ :=
    fderiv_uniform_tube (F := F)
      (K := Set.Icc (0 : Real) b) isCompact_Icc
      (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont η hη
  refine ⟨ρ, hρ, ?_⟩
  intro h hsmall hzh0 t ht u hu
  have htcc : t ∈ Set.Icc (0 : Real) b :=
    Set.Ico_subset_Icc_self ht
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) hz0 hzh0
  have hudist :
      dist u (controlledBaseEndpoint Ψ t z) <
        ρ := by
    have hball :
        u ∈ Metric.closedBall (controlledBaseEndpoint Ψ t z)
          (dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h))) :=
      segment_subset_closedBall_left
        (controlledBaseEndpoint Ψ t z)
        (controlledBaseEndpoint Ψ t (z + h)) hu
    have hudist_le :
        dist u (controlledBaseEndpoint Ψ t z) ≤
          dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h)) := by
      simpa [Metric.mem_closedBall] using hball
    have hsep' :
        dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h)) ≤
          (L' : Real) * ‖h‖ := by
      simpa [dist_comm] using hsep
    exact lt_of_le_of_lt (hudist_le.trans hsep') hsmall
  exact hρsmall t htcc u hudist

/-- The previous segment estimate gives the Taylor-residual forcing estimate
needed by the generic controlled C1 theorem. -/
theorem controlledTaylorRem_eventually_of_lipschitz
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {b : Real}
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * ((L' : Real) * ‖h‖) := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  have hz0 :
      (z, idLin) ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [idLin] using hzopen)
  have hDsmall :=
    controlled_fderiv_segment_small_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hbase hDcont hLip (by simpa [idLin] using hz0)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ := hDsmall η hη
  have hmul_cont :
      Continuous (fun h : X => (L' : Real) * ‖h‖) :=
    continuous_const.mul continuous_norm
  have hsmall_eventually :
      ∀ᶠ h : X in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
    have hball :=
      (hmul_cont.continuousAt (x := (0 : X))).eventually
        (Metric.ball_mem_nhds ((L' : Real) * ‖(0 : X)‖) hρ)
    filter_upwards [hball] with h hh
    have habs : |(L' : Real) * ‖h‖| < ρ := by
      simpa [Real.dist_eq] using hh
    exact (abs_lt.1 habs).2
  filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
  intro t ht
  let s : Set X :=
    segment Real (controlledBaseEndpoint Ψ t z)
      (controlledBaseEndpoint Ψ t (z + h))
  have hD : ∀ u ∈ s,
      ‖fderiv Real F u -
        fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
    intro u hu
    exact hρsmall h hsmall (by simpa [idLin] using hzh0) t ht u hu
  have hTaylor :=
    flowTaylorRem_norm_le
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (z := z) (h := h) (t := t)
      (s := s) (convex_segment _ _)
      (fun q _hq => hFdiff q)
      (left_mem_segment Real _ _)
      (right_mem_segment Real _ _)
      hD
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) (by simpa [idLin] using hz0)
      (by simpa [idLin] using hzh0)
  rw [dist_eq_norm] at hsep
  exact hTaylor.trans
    (mul_le_mul_of_nonneg_left hsep (le_of_lt hη))

/-- Controlled-ball variant of the Taylor-residual forcing estimate.  This is
the form needed for local vector fields: differentiability is only required on
the controlled ball that contains the relevant trajectory segments. -/
theorem controlledTaylorRem_eventually_of_lipschitz_on_ball
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {b : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * ((L' : Real) * ‖h‖) := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  have hz0 :
      (z, idLin) ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [idLin] using hzopen)
  have hbase_mem :
      ∀ t ∈ Set.Icc (0 : Real) b,
        controlledBaseEndpoint Ψ t z ∈ Metric.closedBall x0 (a : Real) := by
    intro t _ht
    have hp := hbound (z, idLin) (by simpa [idLin] using hz0) t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  have hDcont_img :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hDcont _ (hbase_mem t ht)
  have hDsmall :=
    controlled_fderiv_segment_small_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hbase hDcont_img hLip (by simpa [idLin] using hz0)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ := hDsmall η hη
  have hmul_cont :
      Continuous (fun h : X => (L' : Real) * ‖h‖) :=
    continuous_const.mul continuous_norm
  have hsmall_eventually :
      ∀ᶠ h : X in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
    have hball :=
      (hmul_cont.continuousAt (x := (0 : X))).eventually
        (Metric.ball_mem_nhds ((L' : Real) * ‖(0 : X)‖) hρ)
    filter_upwards [hball] with h hh
    have habs : |(L' : Real) * ‖h‖| < ρ := by
      simpa [Real.dist_eq] using hh
    exact (abs_lt.1 habs).2
  filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
  intro t ht
  have htcc : t ∈ Set.Icc (0 : Real) b :=
    Set.Ico_subset_Icc_self ht
  have hzh_mem :
      controlledBaseEndpoint Ψ t (z + h) ∈
        Metric.closedBall x0 (a : Real) := by
    have hp := hbound (z + h, idLin) (by simpa [idLin] using hzh0) t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  let s : Set X :=
    segment Real (controlledBaseEndpoint Ψ t z)
      (controlledBaseEndpoint Ψ t (z + h))
  have hseg_sub : s ⊆ Metric.closedBall x0 (a : Real) := by
    exact (convex_closedBall x0 (a : Real)).segment_subset
      (hbase_mem t htcc) hzh_mem
  have hD : ∀ u ∈ s,
      ‖fderiv Real F u -
        fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
    intro u hu
    exact hρsmall h hsmall (by simpa [idLin] using hzh0) t ht u hu
  have hTaylor :=
    flowTaylorRem_norm_le
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (z := z) (h := h) (t := t)
      (s := s) (convex_segment _ _)
      (fun q hq => hFdiff q (hseg_sub hq))
      (left_mem_segment Real _ _)
      (right_mem_segment Real _ _)
      hD
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) (by simpa [idLin] using hz0)
      (by simpa [idLin] using hzh0)
  rw [dist_eq_norm] at hsep
  exact hTaylor.trans
    (mul_le_mul_of_nonneg_left hsep (le_of_lt hη))

theorem flowErrorRHS_eq_taylorRem_add
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) :
    flowErrorRHS F Φ A z h t =
      flowTaylorRem F Φ z h t +
        fderiv Real F (Φ z t) (flowError Φ A z h t) := by
  simp only [flowErrorRHS, flowTaylorRem, flowError]
  simp only [map_sub]
  abel

/-- Gronwall-ready pointwise estimate for the generic variational-error RHS. -/
theorem flowErrorRHS_norm_le
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) {B ε : Real}
    (hB : ‖fderiv Real F (Φ z t)‖ ≤ B)
    (hRem : ‖flowTaylorRem F Φ z h t‖ ≤ ε) :
    ‖flowErrorRHS F Φ A z h t‖ ≤ B * ‖flowError Φ A z h t‖ + ε := by
  let D := fderiv Real F (Φ z t)
  have hLin0 : ‖D (flowError Φ A z h t)‖ ≤ ‖D‖ * ‖flowError Φ A z h t‖ :=
    D.le_opNorm _
  have hLin : ‖D (flowError Φ A z h t)‖ ≤
      B * ‖flowError Φ A z h t‖ := by
    exact hLin0.trans
      (mul_le_mul_of_nonneg_right (by simpa [D] using hB) (norm_nonneg _))
  rw [flowErrorRHS_eq_taylorRem_add]
  calc
    ‖flowTaylorRem F Φ z h t + D (flowError Φ A z h t)‖
        ≤ ‖D (flowError Φ A z h t)‖ + ‖flowTaylorRem F Φ z h t‖ := by
          simpa [add_comm] using
            norm_add_le (flowTaylorRem F Φ z h t) (D (flowError Φ A z h t))
    _ ≤ B * ‖flowError Φ A z h t‖ + ε := add_le_add hLin hRem

/-- If the variational approximation error is little-o in the initial
perturbation, then the variational linear map is the Frechet derivative of the
fixed-time flow endpoint. -/
theorem flow_hasFDerivAt_of_error
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {t : Real}
    (herr : (fun h : X => flowError Φ A z h t) =o[𝓝 0] (fun h : X => h)) :
    HasFDerivAt (fun z' : X => Φ z' t) (A z t) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa [flowError] using herr

/-- Fixed-time C1 dependence from an eventual Gronwall bound with a vanishing
Taylor-residual coefficient. -/
theorem flow_hasFDerivAt_of_gronwall
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {t B L T : Real} {C : X -> Real}
    (hC : Tendsto C (𝓝 0) (𝓝 0))
    (hbound : ∀ᶠ h in 𝓝 (0 : X),
      ‖flowError Φ A z h t‖ ≤ gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    HasFDerivAt (fun z' : X => Φ z' t) (A z t) z := by
  apply flow_hasFDerivAt_of_error
  exact isLittleO_of_gronwall_bound
    (f := fun h : X => flowError Φ A z h t)
    (C := C) (B := B) (L := L) (T := T) hC hbound

/-- The variational approximation error is continuous on an interval if the
base flow and variational linear map are continuous there. -/
theorem flowError_continuousOn
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X} {s : Set Real}
    (hzh : ContinuousOn (fun t => Φ (z + h) t) s)
    (hz : ContinuousOn (fun t => Φ z t) s)
    (hA : ContinuousOn (fun t => A z t) s) :
    ContinuousOn (flowError Φ A z h) s := by
  have happ : ContinuousOn (fun t => A z t h) s :=
    hA.clm_apply continuousOn_const
  simpa [flowError] using (hzh.sub hz).sub happ

/-- The model-independent variational error satisfies the expected
inhomogeneous linear ODE. -/
theorem flowError_hasDerivWithinAt
    {F : X -> X} {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X} {s : Set Real} {t : Real}
    (hzh : HasDerivWithinAt (Φ (z + h)) (F (Φ (z + h) t)) s t)
    (hz : HasDerivWithinAt (Φ z) (F (Φ z t)) s t)
    (hA :
      HasDerivWithinAt (A z)
        ((fderiv Real F (Φ z t)).comp (A z t)) s t) :
    HasDerivWithinAt
      (flowError Φ A z h)
      (flowErrorRHS F Φ A z h t) s t := by
  have hh : HasDerivWithinAt (fun _ : Real => h) (0 : X) s t := by
    simpa using (hasDerivWithinAt_const (c := h) (s := s) (x := t))
  have hAh :
      HasDerivWithinAt (fun t : Real => A z t h)
        (((fderiv Real F (Φ z t)).comp (A z t)) h) s t := by
    simpa [ContinuousLinearMap.comp_apply] using hA.clm_apply hh
  have herr := (hzh.sub hz).sub hAh
  simpa [flowError, flowErrorRHS, ContinuousLinearMap.comp_apply] using herr

/-- The variational approximation error vanishes initially if the flow and
linearized flow have the expected initial values. -/
@[simp] theorem flowError_zero
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X}
    (hzh : Φ (z + h) 0 = z + h)
    (hz : Φ z 0 = z)
    (hA : A z 0 = ContinuousLinearMap.id Real X) :
    flowError Φ A z h 0 = 0 := by
  simp [flowError, hzh, hz, hA]

/-- Generic Gronwall bound for the variational approximation error once the
error RHS has the standard linear-plus-forcing estimate. -/
theorem flowError_norm_le_gronwall
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) {a b δ K ε : Real}
    (hcont : ContinuousOn (flowError Φ A z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (flowError Φ A z h)
        (flowErrorRHS F Φ A z h t) (Set.Ici t) t)
    (ha : ‖flowError Φ A z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖flowErrorRHS F Φ A z h t‖ ≤ K * ‖flowError Φ A z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖flowError Φ A z h t‖ ≤ gronwallBound δ K ε (t - a) :=
  norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv ha hbound

/-- Generic fixed-time C1 dependence from the variational equation plus a
uniform Taylor-residual forcing estimate.

This is the reusable Gronwall theorem that the finite jet-prefix induction
should instantiate for each finite-dimensional jet RHS. -/
theorem flow_hasFDerivAt_of_taylor_gronwall
    {F : X -> X} {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {b B L : Real}
    (hb0 : 0 ≤ b)
    (hcont : ∀ᶠ h : X in 𝓝 0,
      ContinuousOn (flowError Φ A z h) (Set.Icc (0 : Real) b))
    (hderiv : ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        HasDerivWithinAt (flowError Φ A z h)
          (flowErrorRHS F Φ A z h t) (Set.Ici t) t)
    (hzero : ∀ᶠ h : X in 𝓝 0, flowError Φ A z h 0 = 0)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real F (Φ z t)‖ ≤ B)
    (hRem : ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F Φ z h t‖ ≤ η * (L * ‖h‖)) :
    HasFDerivAt (fun z' : X => Φ z' b) (A z b) z := by
  apply flow_hasFDerivAt_of_error
  refine
    isLittleO_of_gronwall_bound_eventually
      (X := X) (Y := X) (B := B) (L := L) (T := b) ?_
  intro η hη
  filter_upwards [hcont, hderiv, hzero, hRem η hη] with h hcont_h hderiv_h hzero_h hRem_h
  have hgr :
      ∀ t ∈ Set.Icc (0 : Real) b,
        ‖flowError Φ A z h t‖ ≤
          gronwallBound 0 B (η * (L * ‖h‖)) (t - 0) := by
    refine flowError_norm_le_gronwall F Φ A z h hcont_h hderiv_h ?_ ?_
    · simp [hzero_h]
    · intro t ht
      exact flowErrorRHS_norm_le F Φ A z h t (hB t ht) (hRem_h t ht)
  simpa using hgr b ⟨hb0, le_rfl⟩

/-- Generic controlled C1 dependence for an augmented variational flow, once
the uniform derivative bound and Taylor-residual estimate have been produced.

This theorem removes the model-spray and chart-source assumptions from the
Gronwall argument.  The remaining analytic inputs are exactly the estimates
needed by `flow_hasFDerivAt_of_taylor_gronwall`. -/
theorem controlledVarFlow_hasFDerivAt
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r : NNReal} {ε b B L : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ B)
    (hRem : ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * (L * ‖h‖))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  refine
    flow_hasFDerivAt_of_taylor_gronwall
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (A := fun y τ => controlledDerivEndpoint Ψ τ y)
      (z := z) (b := b) (B := B) (L := L)
      hb0 ?_ ?_ ?_ hB hRem
  · filter_upwards [hzh_eventually] with h hzh0
    have hcont_zh :
        ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t (z + h))
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ (z + h, idLin)) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow (z + h, idLin) hzh0).2)
      simpa [controlledBaseEndpoint, idLin] using
        continuous_fst.comp_continuousOn (hcont.mono hb)
    have hcont_z :
        ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
      simpa [controlledBaseEndpoint, pz, idLin] using
        continuous_fst.comp_continuousOn (hcont.mono hb)
    have hcont_A :
        ContinuousOn (fun t : Real => controlledDerivEndpoint Ψ t z)
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
      simpa [controlledDerivEndpoint, pz, idLin] using
        continuous_snd.comp_continuousOn (hcont.mono hb)
    exact flowError_continuousOn hcont_zh hcont_z hcont_A
  · filter_upwards [hzh_eventually] with h hzh0
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : Real) b :=
      Set.Ico_subset_Icc_self ht
    have htbig : t ∈ Set.Icc (-ε) ε := hb htIcc
    have hbase_zh :
        HasDerivWithinAt
          (controlledBaseEndpoint Ψ · (z + h))
          (F (controlledBaseEndpoint Ψ t (z + h)))
          (Set.Icc (-ε) ε) t :=
      controlledBase_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow (z + h, idLin) hzh0).2 t htbig)
    have hbase_z :
        HasDerivWithinAt
          (controlledBaseEndpoint Ψ · z)
          (F (controlledBaseEndpoint Ψ t z))
          (Set.Icc (-ε) ε) t :=
      controlledBase_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow pz hz0).2 t htbig)
    have hA :
        HasDerivWithinAt
          (controlledDerivEndpoint Ψ · z)
          ((fderiv Real F (controlledBaseEndpoint Ψ t z)).comp
            (controlledDerivEndpoint Ψ t z))
          (Set.Icc (-ε) ε) t :=
      controlledDeriv_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow pz hz0).2 t htbig)
    have herr :
        HasDerivWithinAt
          (flowError (fun y τ => controlledBaseEndpoint Ψ τ y)
            (fun y τ => controlledDerivEndpoint Ψ τ y) z h)
          (flowErrorRHS F (fun y τ => controlledBaseEndpoint Ψ τ y)
            (fun y τ => controlledDerivEndpoint Ψ τ y) z h t)
          (Set.Icc (-ε) ε) t :=
      flowError_hasDerivWithinAt
        (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
        (A := fun y τ => controlledDerivEndpoint Ψ τ y) (z := z) (h := h)
        hbase_zh hbase_z hA
    exact
      (herr.mono hb).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
  · filter_upwards [hzh_eventually] with h hzh0
    have hbase_zh :
        controlledBaseEndpoint Ψ 0 (z + h) = z + h := by
      simpa [controlledBaseEndpoint, idLin] using
        congrArg Prod.fst ((hflow (z + h, idLin) hzh0).1)
    have hbase_z : controlledBaseEndpoint Ψ 0 z = z := by
      simpa [controlledBaseEndpoint, pz, idLin] using
        congrArg Prod.fst ((hflow pz hz0).1)
    have hA0 :
        controlledDerivEndpoint Ψ 0 z = ContinuousLinearMap.id Real X := by
      simpa [controlledDerivEndpoint, pz, idLin] using
        congrArg Prod.snd ((hflow pz hz0).1)
    exact flowError_zero hbase_zh hbase_z hA0

/-- Generic controlled C1 dependence where the analytic estimates are produced
from continuity of `D F` along the compact base trajectory. -/
theorem controlledVarFlow_hasFDerivAt_of_fderiv_continuous
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b) := by
    have hcont :
        ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
      HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
    simpa [controlledBaseEndpoint, pz, idLin] using
      continuous_fst.comp_continuousOn (hcont.mono hb)
  obtain ⟨B, hBcc⟩ :=
    fderiv_bound_on_base
      (F := F) (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont
  have hRem :=
    controlledTaylorRem_eventually_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hFdiff hbase hDcont
      (fun t ht => hLip t (hb (Set.Ico_subset_Icc_self ht)))
      hzopen
  exact
    controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := (L' : Real))
      hb0 hb hflow
      (fun t ht => hBcc t (Set.Ico_subset_Icc_self ht))
      hRem hzopen

/-- Generic controlled C1 dependence from controlled-ball differentiability
and continuity of `D F`. -/
theorem controlledVarFlow_hasFDerivAt_of_fderiv_ball
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b) := by
    have hcont :
        ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
      HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
    simpa [controlledBaseEndpoint, pz, idLin] using
      continuous_fst.comp_continuousOn (hcont.mono hb)
  have hbase_mem :
      ∀ t ∈ Set.Icc (0 : Real) b,
        controlledBaseEndpoint Ψ t z ∈ Metric.closedBall x0 (a : Real) := by
    intro t _ht
    have hp := hbound pz hz0 t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  have hDcont_img :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hDcont _ (hbase_mem t ht)
  obtain ⟨B, hBcc⟩ :=
    fderiv_bound_on_base
      (F := F) (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont_img
  have hRem :=
    controlledTaylorRem_eventually_of_lipschitz_on_ball
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (a := a) (r := r) (L' := L') (b := b)
      hbound hFdiff hDcont hbase
      (fun t ht => hLip t (hb (Set.Ico_subset_Icc_self ht)))
      hzopen
  exact
    controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := (L' : Real))
      hb0 hb hflow
      (fun t ht => hBcc t (Set.Ico_subset_Icc_self ht))
      hRem hzopen

/-- Generic `C1` fixed-time dependence for a controlled augmented variational
flow, assuming the Taylor-residual estimates are available uniformly on a
neighborhood. -/
theorem controlledBaseEndpoint_contDiffAt_one
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b B L : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hB : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖fderiv Real F (controlledBaseEndpoint Ψ t y)‖ ≤ B)
    (hRem : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
        ∀ t ∈ Set.Ico (0 : Real) b,
          ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y)
              y h t‖ ≤ η * (L * ‖h‖))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := L)
      hb0 hb hflow (hB y (by simpa [U, idLin] using hy))
      (hRem y (by simpa [U, idLin] using hy))
      (by simpa [U, idLin] using hy)

/-- Generic `C1` fixed-time dependence from continuity of `D F` along all
nearby compact base trajectories. -/
theorem controlledBaseEndpoint_contDiffAt_one_of_fderiv_continuous
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hDcont : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ q ∈ (fun t : Real => controlledBaseEndpoint Ψ t y) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt_of_fderiv_continuous
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hLip hFdiff
      (hDcont y (by simpa [U, idLin] using hy))
      (by simpa [U, idLin] using hy)

/-- Generic `C1` fixed-time dependence from controlled-ball differentiability
and continuity of `D F`, uniformly for nearby initial points. -/
theorem controlledBaseEndpoint_contDiffAt_one_of_fderiv_ball
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt_of_fderiv_ball
      (F := F) (x0 := x0) (Ψ := Ψ)
      (a := a) (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hbound hLip hFdiff hDcont
      (by simpa [U, idLin] using hy)

end GenericC1Flow

/-- Smoothness of the augmented variational RHS for a finite jet-prefix ODE. -/
theorem jetVarRHS_cdAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelJetPrefix (E := E) N →L[Real] ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (variationalRHS (jetRHSPrefix (E := E) F N))
      (P, A) :=
  variationalRHS_contDiffAt (X := ModelJetPrefix (E := E) N)
    (F := jetRHSPrefix (E := E) F N) (z := P) (A := A)
    (jetRHSPrefix_contDiffAt (E := E) F N P hF)

/-- Smoothness of the parameterized augmented variational RHS for a finite
jet-prefix ODE, where the parameter space is the original model phase. -/
theorem jetParamVarRHS_cdAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) F N))
      (P, A) :=
  paramVariationalRHS_contDiffAt
    (X := ModelJetPrefix (E := E) N) (P := ModelPhase (E := E))
    (F := jetRHSPrefix (E := E) F N) (z := P) (A := A)
    (jetRHSPrefix_contDiffAt (E := E) F N P hF)

/-- The successor finite-prefix RHS is the parameterized variational RHS of
the previous finite-prefix RHS along an actual fixed-time Taylor jet.  This is
the finite-state version of "the first variational equation of the `N`-jet ODE
is the `(N+1)`-jet ODE". -/
theorem jetRHSPrefix_succ_as_paramVarRHS
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Phi : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real)
    (hFcont : ContDiffAt Real ∞ F (Phi z t))
    (hF :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        F
        (fun y : ModelPhase (E := E) => ftaylorSeries Real F y)
        Set.univ)
    (hPhi :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        (fun y : ModelPhase (E := E) => Phi y t)
        (fun y : ModelPhase (E := E) => flowJet (E := E) Phi y t)
        Set.univ) :
    paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) F N)
        (flowJetPrefix (E := E) Phi N z t,
          ModelJetPrefix.shiftedDeriv (E := E) N
            (flowJetPrefix (E := E) Phi (N + 1) z t))
      =
        (jetRHSPrefix (E := E) F N
            (flowJetPrefix (E := E) Phi N z t),
          ModelJetPrefix.shiftedDeriv (E := E) N
            (jetRHSPrefix (E := E) F (N + 1)
              (flowJetPrefix (E := E) Phi (N + 1) z t))) := by
  apply Prod.ext
  · rfl
  · dsimp [paramVariationalRHS]
    let P0 : ModelJetPrefix (E := E) N :=
      flowJetPrefix (E := E) Phi N z t
    let A0 : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N :=
      ModelJetPrefix.shiftedDeriv (E := E) N
        (flowJetPrefix (E := E) Phi (N + 1) z t)
    have hflow :
        HasFDerivAt
          (fun y : ModelPhase (E := E) => flowJetPrefix (E := E) Phi N y t)
          A0 z := by
      simpa [A0] using
        flowJetPrefix_hasFDerivAt_of_hasFTaylor (E := E) Phi N z t
          (hasFTaylorSeriesUpToOn_univ_iff.mp hPhi)
    have hjet :
        HasFDerivAt
          (jetRHSPrefix (E := E) F N)
          (fderiv Real (jetRHSPrefix (E := E) F N) P0) P0 := by
      exact
        ((jetRHSPrefix_contDiffAt (E := E) F N P0
          (by simpa [P0] using hFcont)).differentiableAt (by simp)).hasFDerivAt
    have hchain :
        HasFDerivAt
          (fun y : ModelPhase (E := E) =>
            jetRHSPrefix (E := E) F N
              (flowJetPrefix (E := E) Phi N y t))
          ((fderiv Real (jetRHSPrefix (E := E) F N) P0).comp A0) z := by
      simpa [P0] using hjet.comp z hflow
    have hdirect :=
      jetRHSPrefix_flowJetPrefix_hasFDerivAt (E := E) F Phi N z t hF hPhi
    exact (hdirect.unique hchain).symm

/-- Smoothness of the augmented variational RHS for the fixed-chart spray
finite jet-prefix ODE on the controlled chart/source region. -/
theorem sprayJetVarRHS_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelJetPrefix (E := E) N →L[Real] ModelJetPrefix (E := E) N)
    (hztarget :
      ModelJetPrefix.base (E := E) N P ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc :
      (phaseOfModel (I := I) x (ModelJetPrefix.base (E := E) N P)).proj ∈
        (extChartAt I x).source) :
    ContDiffAt Real ∞
      (variationalRHS
        (jetRHSPrefix (E := E) (modelSpray (I := I) g x) N))
      (P, A) :=
  jetVarRHS_cdAt (E := E) (modelSpray (I := I) g x) N P A
    (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- Smoothness of the parameterized augmented variational RHS for the
fixed-chart spray finite jet-prefix ODE on the controlled chart/source region. -/
theorem sprayJetParamVarRHS_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N)
    (hztarget :
      ModelJetPrefix.base (E := E) N P ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc :
      (phaseOfModel (I := I) x (ModelJetPrefix.base (E := E) N P)).proj ∈
        (extChartAt I x).source) :
    ContDiffAt Real ∞
      (paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) (modelSpray (I := I) g x) N))
      (P, A) :=
  jetParamVarRHS_cdAt (E := E) (modelSpray (I := I) g x) N P A
    (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- The zero point for the variational equation: zero phase and identity
linearized initial data. -/
def varPhaseZero (x : M) : ModelPhase (E := E) × ModelLin (E := E) :=
  (extChartAt I.tangent (phaseZero (I := I) x)
    (phaseZero (I := I) x),
    ContinuousLinearMap.id Real (ModelPhase (E := E)))

/-- The augmented vector field for the variational equation.

The first component is the model spray.  The second component is the linear ODE
`A' = DF(z) ∘ A` for derivatives with respect to the initial phase. -/
def varSpray
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    ModelPhase (E := E) × ModelLin (E := E) :=
  (modelSpray (I := I) g x p.1,
    (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2)

@[simp] theorem varSpray_fst
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).1 = modelSpray (I := I) g x p.1 := rfl

@[simp] theorem varSpray_snd
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).2 =
      (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2 := rfl

/-- The augmented variational vector field is smooth at `(0_x, id)`.

This is the higher-order regularity input for iterating the variational-equation
route: the augmented vector field loses one derivative through `fderiv`, but the
fixed-chart model spray is already smooth. -/
theorem varSpray_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞
      (varSpray (I := I) g x)
      (varPhaseZero (I := I) (E := E) x) := by
  let Z := ModelPhase (E := E)
  let z0 : Z :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  change
    ContDiffAt Real ∞
      (variationalRHS (modelSpray (I := I) g x))
      (z0, ContinuousLinearMap.id Real Z)
  exact variationalRHS_contDiffAt (X := Z)
    (F := modelSpray (I := I) g x) (z := z0)
    (A := ContinuousLinearMap.id Real Z)
    (modelSpray_contDiffAt (I := I) g x)

/-- The augmented variational vector field is `C¹` at `(0_x, id)`.

This corollary is the Picard-Lindelöf input used by the existing C1
variational-flow construction. -/
theorem varSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (varSpray (I := I) g x)
      (varPhaseZero (I := I) (E := E) x) := by
  exact (varSpray_contDiffAt (I := I) g x).of_le (by simp)

/-- The augmented variational vector field is smooth at every controlled phase
point. -/
theorem varSpray_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {p : ModelPhase (E := E) × ModelLin (E := E)}
    (hztarget : p.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x p.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real ∞ (varSpray (I := I) g x) p := by
  let Z := ModelPhase (E := E)
  have hF :
      ContDiffAt Real ∞ (modelSpray (I := I) g x) p.1 :=
    modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc
  change
      ContDiffAt Real ∞
        (variationalRHS (modelSpray (I := I) g x)) p
  exact variationalRHS_contDiffAt (X := Z)
    (F := modelSpray (I := I) g x) (z := p.1) (A := p.2) hF

/-- The augmented variational vector field is `C¹` at every controlled phase
point. -/
theorem varSpray_cdAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {p : ModelPhase (E := E) × ModelLin (E := E)}
    (hztarget : p.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x p.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real 1 (varSpray (I := I) g x) p := by
  exact (varSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc).of_le (by simp)

/-- Source-control domain for the augmented variational spray. -/
def varSource [I.Boundaryless] (x : M) : Set (VarPhase (E := E)) :=
  {p : VarPhase (E := E) |
    p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
      (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source}

/-- The augmented variational source-control domain is open. -/
theorem isOpen_varSource
    [I.Boundaryless] (x : M) :
    IsOpen (varSource (I := I) (E := E) x) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have htarget :
      {q : VarPhase (E := E) |
        q.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target} ∈ 𝓝 p := by
    exact continuousAt_fst.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I.tangent)
        (phaseZero (I := I) x)).mem_nhds hp.1)
  have hphase :
      ContinuousAt (fun q : VarPhase (E := E) => phaseOfModel (I := I) x q.1) p := by
    exact (continuousAt_extChartAt_symm'' (I := I.tangent) hp.1).comp continuousAt_fst
  have hproj :
      ContinuousAt
        (fun q : VarPhase (E := E) => (phaseOfModel (I := I) x q.1).proj) p := by
    exact ((FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt).comp hphase
  have hsource :
      {q : VarPhase (E := E) |
        (phaseOfModel (I := I) x q.1).proj ∈ (extChartAt I x).source} ∈ 𝓝 p := by
    exact hproj.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x).mem_nhds hp.2)
  change
    ({q : VarPhase (E := E) |
        q.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target} ∩
      {q : VarPhase (E := E) |
        (phaseOfModel (I := I) x q.1).proj ∈ (extChartAt I x).source}) ∈ 𝓝 p
  exact Filter.inter_mem htarget hsource

/-- The augmented variational spray is smooth on its source-control domain. -/
theorem varSpray_cdOn_source
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffOn Real ∞
      (varSpray (I := I) g x)
      (varSource (I := I) (E := E) x) := by
  intro p hp
  exact (varSpray_contDiffAt_of_mem (I := I) g x hp.1 hp.2).contDiffWithinAt

/-- The time-independent augmented variational spray is smooth on
`ℝ × varSource`. -/
theorem varSpray_time_cdOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffOn Real ∞
      (fun q : Real × VarPhase (E := E) => varSpray (I := I) g x q.2)
      (Set.univ ×ˢ varSource (I := I) (E := E) x) := by
  have hsrc := varSpray_cdOn_source (I := I) g x
  have hsnd :
      ContDiffOn Real ∞
        (fun q : Real × VarPhase (E := E) => q.2)
        (Set.univ ×ˢ varSource (I := I) (E := E) x) :=
    contDiff_snd.contDiffOn
  exact hsrc.comp hsnd (by intro q hq; exact hq.2)

/-- Local Picard-Lindelof data for the augmented variational equation. -/
theorem varSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => varSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (varPhaseZero (I := I) (E := E) x)
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (varSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- The augmented variational phase is source-controlled near `(0_x, id)` as
soon as its base phase is source-controlled. -/
theorem varSrc_nhds
    [I.Boundaryless] (x : M) :
    {p : ModelPhase (E := E) × ModelLin (E := E) |
      p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source} ∈
      𝓝 (varPhaseZero (I := I) (E := E) x) := by
  have hsrc := modelSrc_nhds (I := I) (E := E) x
  have hfst :
      ContinuousAt (fun p : ModelPhase (E := E) × ModelLin (E := E) => p.1)
        (varPhaseZero (I := I) (E := E) x) :=
    continuousAt_fst
  simpa [varPhaseZero, Set.preimage] using hfst.preimage_mem_nhds hsrc

/-- Picard-Lindelof data for the augmented variational equation, shrunk so the
whole controlling augmented ball keeps the base phase in the fixed chart
source. -/
theorem varSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
          {p : ModelPhase (E := E) × ModelLin (E := E) |
            p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x p.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => varSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (varPhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := varSpray_pl (I := I) g x
  let p0 : ModelPhase (E := E) × ModelLin (E := E) :=
    varPhaseZero (I := I) (E := E) x
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => varSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro p hp
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist p p0 ≤ (a' : Real) := by
    simpa [p0] using Metric.mem_closedBall.mp hp
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist p p0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time augmented variational flow with Lipschitz dependence on
the augmented initial phase. -/
theorem varFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, Ψ, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence and
the closed-ball bound for the same chosen flow. -/
theorem varFlow_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) (hpl 0)
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence,
closed-ball bound, and base-phase source control for the same chosen flow. -/
theorem varFlow_src_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    varSpray_pl0_src (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) hpl
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro p hp t
    exact hsrc (hbound p hp t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Smoothness of the augmented variational RHS on a source-controlled closed
ball. -/
theorem varSpray_smoothBall
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {a : NNReal}
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source}) :
    ContDiffOn Real ∞
      (varSpray (I := I) g x)
      (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) := by
  intro p hp
  exact (varSpray_contDiffAt_of_mem (I := I) g x (hsrc hp).1 (hsrc hp).2).contDiffWithinAt

/-- The source-controlled augmented variational flow also carries smoothness of
the RHS on its whole closed control ball. -/
theorem varFlow_smoothTube
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          (∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
          ContDiffOn Real ∞
            (varSpray (I := I) g x)
            (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) := by
  obtain ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc, hsrc_flow, L', hLip⟩ :=
    varFlow_src_bound (I := I) g x
  exact ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc, hsrc_flow,
    ⟨L', hLip⟩, varSpray_smoothBall (I := I) g x hsrc⟩

/-- Zero point for the second augmented variational equation: the first
augmented zero and the identity on the first augmented state. -/
def var2PhaseZero (x : M) : VarPhase (E := E) × VarLin (E := E) :=
  (varPhaseZero (I := I) (E := E) x,
    ContinuousLinearMap.id Real (VarPhase (E := E)))

/-- Smoothness of the second augmented RHS at the first augmented zero. -/
theorem var2Spray_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞
      (variationalRHS (varSpray (I := I) g x))
      (var2PhaseZero (I := I) (E := E) x) := by
  exact variationalRHS_contDiffAt (X := VarPhase (E := E))
    (F := varSpray (I := I) g x)
    (z := varPhaseZero (I := I) (E := E) x)
    (A := ContinuousLinearMap.id Real (VarPhase (E := E)))
    (varSpray_contDiffAt (I := I) g x)

/-- C1 regularity of the second augmented RHS at the first augmented zero. -/
theorem var2Spray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (variationalRHS (varSpray (I := I) g x))
      (var2PhaseZero (I := I) (E := E) x) := by
  exact (var2Spray_contDiffAt (I := I) g x).of_le (by simp)

/-- The second augmented RHS is smooth whenever the first augmented base point
is source-controlled. -/
theorem var2Spray_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {q : VarPhase (E := E) × VarLin (E := E)}
    (hztarget : q.1.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x q.1.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real ∞ (variationalRHS (varSpray (I := I) g x)) q := by
  exact variationalRHS_contDiffAt (X := VarPhase (E := E))
    (F := varSpray (I := I) g x) (z := q.1) (A := q.2)
    (varSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- The second augmented RHS is `C1` whenever the first augmented base point is
source-controlled. -/
theorem var2Spray_cdAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {q : VarPhase (E := E) × VarLin (E := E)}
    (hztarget : q.1.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x q.1.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real 1 (variationalRHS (varSpray (I := I) g x)) q := by
  exact (var2Spray_contDiffAt_of_mem (I := I) g x hztarget hsrc).of_le (by simp)

/-- Local Picard-Lindelof data for the second augmented variational equation. -/
theorem var2Spray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => variationalRHS (varSpray (I := I) g x))
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (var2PhaseZero (I := I) (E := E) x)
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (var2Spray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

set_option synthInstance.maxHeartbeats 80000 in
/-- Picard-Lindelof data for the second augmented equation, shrunk so the
controlling ball keeps the first augmented base phase in the fixed source. -/
theorem var2Spray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
          {q : VarPhase (E := E) × VarLin (E := E) |
            q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x q.1.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => variationalRHS (varSpray (I := I) g x))
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (var2PhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := var2Spray_pl (I := I) g x
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let q0 : VarPhase (E := E) × VarLin (E := E) :=
    (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x))
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro q hq
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist q q0 ≤ (a' : Real) := by
    simpa [q0, p0, var2PhaseZero] using Metric.mem_closedBall.mp hq
  have hfst : dist q.1 p0 ≤ dist q q0 := by
    change dist q.1 p0 ≤ dist q (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist q.1 p0 ≤ dist q q0 := hfst
    _ ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

set_option synthInstance.maxHeartbeats 80000 in
/-- Picard-Lindelof data for the second augmented equation, shrunk so the
controlling ball keeps the first augmented base point in a prescribed
first-level closed ball and in the fixed source. -/
theorem var2Spray_pl0_ball
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ρ : NNReal} (hρ : 0 < ρ) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
          {q : VarPhase (E := E) × VarLin (E := E) |
            q.1 ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x q.1.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => variationalRHS (varSpray (I := I) g x))
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (var2PhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := var2Spray_pl (I := I) g x
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let q0 : VarPhase (E := E) × VarLin (E := E) :=
    (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let ρnn : NNReal := ρ / 2
  let a' : NNReal := min a (min δnn ρnn)
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have hρnn : 0 < ρnn := by
    simpa [ρnn] using half_pos hρ
  have ha' : 0 < a' := by
    exact lt_min ha (lt_min hδnn hρnn)
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x))
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro q hq
  have hdist : dist q q0 ≤ (a' : Real) := by
    simpa [q0, p0, var2PhaseZero] using Metric.mem_closedBall.mp hq
  have hfst : dist q.1 p0 ≤ dist q q0 := by
    change dist q.1 p0 ≤ dist q (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have haρ : (a' : Real) ≤ (ρ : Real) / 2 := by
    have : a' ≤ ρnn := le_trans (min_le_right _ _) (min_le_right _ _)
    exact_mod_cast this
  have hbase : q.1 ∈ Metric.closedBall p0 ρ := by
    rw [Metric.mem_closedBall]
    calc
      dist q.1 p0 ≤ dist q q0 := hfst
      _ ≤ (a' : Real) := hdist
      _ ≤ (ρ : Real) / 2 := haρ
      _ ≤ (ρ : Real) := by
        exact half_le_self (NNReal.coe_nonneg ρ)
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := le_trans (min_le_right _ _) (min_le_left _ _)
    exact_mod_cast this
  have hsrc := hδsub (by
    rw [Metric.mem_ball]
    calc
      dist q.1 p0 ≤ dist q q0 := hfst
      _ ≤ (a' : Real) := hdist
      _ ≤ δ / 2 := haδ
      _ < δ := half_lt_self hδ)
  exact ⟨hbase, hsrc.1, hsrc.2⟩

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow with Lipschitz dependence and the
closed-ball bound for the same chosen flow. -/
theorem var2Flow_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, _hsrc, hpl⟩ :=
    var2Spray_pl0_src (I := I) g x
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow with Lipschitz dependence,
closed-ball bound, and source control for the same chosen flow. -/
theorem var2Flow_src_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x q.1.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1.1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    var2Spray_pl0_src (I := I) g x
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro q hq t
    exact hsrc (hbound q hq t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow whose control ball projects into
a prescribed first-level control ball, with source control and Lipschitz
dependence for the same chosen flow. -/
theorem var2Flow_ball
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ρ : NNReal} (hρ : 0 < ρ) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1 ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
                q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                  (phaseOfModel (I := I) x q.1.1).proj ∈
                    (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1 ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
                (Ω q t).1.1 ∈
                  (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    var2Spray_pl0_ball (I := I) g x hρ
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro q hq t
    exact hsrc (hbound q hq t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Smoothness of the second augmented RHS on a source-controlled closed ball. -/
theorem var2Spray_smoothBall
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {a : NNReal}
    (hsrc :
      Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
        {q : VarPhase (E := E) × VarLin (E := E) |
          q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x q.1.1).proj ∈ (extChartAt I x).source}) :
    ContDiffOn Real ∞
      (variationalRHS (varSpray (I := I) g x))
      (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) := by
  intro q hq
  exact
    (var2Spray_contDiffAt_of_mem (I := I) g x (hsrc hq).1 (hsrc hq).2).contDiffWithinAt

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The second augmented flow also carries smoothness of its RHS on the closed
control ball. -/
theorem var2Flow_smoothTube
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x q.1.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1.1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          (∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r)) ∧
          ContDiffOn Real ∞
            (variationalRHS (varSpray (I := I) g x))
            (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) := by
  obtain ⟨ε, hε, a, r, hr, Ω, hflow, hbound, hsrc, hsrc_flow, L', hLip⟩ :=
    var2Flow_src_bound (I := I) g x
  exact ⟨ε, hε, a, r, hr, Ω, hflow, hbound, hsrc, hsrc_flow,
    ⟨L', hLip⟩, var2Spray_smoothBall (I := I) g x hsrc⟩

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The base endpoint of the second augmented flow is `C1` in its first
augmented initial condition. -/
theorem var2Base_c1_of_flow
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
      VarPhase (E := E) × VarLin (E := E))
    {ε b : Real} {a r L' : NNReal}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
        Ω q 0 = q ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ω q)
              (variationalRHS (varSpray (I := I) g x) (Ω q t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ω q t ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
        {q : VarPhase (E := E) × VarLin (E := E) |
          q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x q.1.1).proj ∈
              (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun q => Ω q t)
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r))
    {q : VarPhase (E := E)}
    (hqopen :
      (q, ContinuousLinearMap.id Real (VarPhase (E := E))) ∈
        Metric.ball (var2PhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun q' : VarPhase (E := E) =>
        (Ω (q', ContinuousLinearMap.id Real (VarPhase (E := E))) b).1)
      q := by
  let idLin : VarLin (E := E) := ContinuousLinearMap.id Real (VarPhase (E := E))
  let q0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  have hFdiff :
      ∀ p ∈ Metric.closedBall q0 (a : Real),
        DifferentiableAt Real (varSpray (I := I) g x) p := by
    intro p hp
    have hp2 :
        (p, idLin) ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a := by
      rw [Metric.mem_closedBall] at hp ⊢
      rw [Prod.dist_eq]
      have hid : dist idLin (ContinuousLinearMap.id Real (VarPhase (E := E))) = 0 := by
        simp [idLin]
      have hq : dist p q0 ≤ (a : Real) := hp
      have hmax : max (dist p q0) (dist idLin
          (ContinuousLinearMap.id Real (VarPhase (E := E)))) ≤ (a : Real) := by
        rw [hid, max_eq_left]
        · exact hq
        · exact dist_nonneg
      simpa [var2PhaseZero, q0] using hmax
    have hp_src := hsrc hp2
    exact
      (varSpray_contDiffAt_of_mem (I := I) g x hp_src.1 hp_src.2).differentiableAt
        (by simp)
  have hDcont :
      ∀ p ∈ Metric.closedBall q0 (a : Real),
        ContinuousAt (fderiv Real (varSpray (I := I) g x)) p := by
    intro p hp
    have hp2 :
        (p, idLin) ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a := by
      rw [Metric.mem_closedBall] at hp ⊢
      rw [Prod.dist_eq]
      have hid : dist idLin (ContinuousLinearMap.id Real (VarPhase (E := E))) = 0 := by
        simp [idLin]
      have hq : dist p q0 ≤ (a : Real) := hp
      have hmax : max (dist p q0) (dist idLin
          (ContinuousLinearMap.id Real (VarPhase (E := E)))) ≤ (a : Real) := by
        rw [hid, max_eq_left]
        · exact hq
        · exact dist_nonneg
      simpa [var2PhaseZero, q0] using hmax
    have hp_src := hsrc hp2
    have hcd :
        ContDiffAt Real ∞ (varSpray (I := I) g x) p :=
      varSpray_contDiffAt_of_mem (I := I) g x hp_src.1 hp_src.2
    exact (hcd.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).continuousAt
  exact
    controlledBaseEndpoint_contDiffAt_one_of_fderiv_ball
      (X := VarPhase (E := E)) (F := varSpray (I := I) g x)
      (x0 := q0) (z := q) (Ψ := Ω)
      (a := a) (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hbound hLip hFdiff hDcont
      (by
        change
          (q, ContinuousLinearMap.id Real (VarPhase (E := E))) ∈
            Metric.ball (var2PhaseZero (I := I) (E := E) x) r
        exact hqopen)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The base projection of a second augmented solution agrees with the
first-level augmented Picard flow through the same first-level initial point,
as long as the projected curve stays in the first-level controlling ball. -/
theorem var2Base_eq_varFlow_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {eps delta : Real} (heps : 0 < eps) (hdelta : 0 < delta)
    (hdle : delta ≤ eps)
    {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - eps) (tmax := 0 + eps)
      ⟨0, by simp [le_of_lt heps]⟩
      (varPhaseZero (I := I) (E := E) x)
      a r L K)
    {Psi : VarPhase (E := E) -> Real -> VarPhase (E := E)}
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Psi p 0 = p ∧
          ∀ t ∈ Set.Icc (-eps) eps,
            HasDerivWithinAt (Psi p)
              (varSpray (I := I) g x (Psi p t))
              (Set.Icc (-eps) eps) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Psi p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    {Omega : VarPhase (E := E) × VarLin (E := E) -> Real ->
      VarPhase (E := E) × VarLin (E := E)}
    {p : VarPhase (E := E)}
    (hp : p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hOinit :
      Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) 0 =
        (p, ContinuousLinearMap.id Real (VarPhase (E := E))))
    (hOderiv :
      ∀ t ∈ Set.Icc (-delta) delta,
        HasDerivWithinAt
          (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))))
          (variationalRHS (varSpray (I := I) g x)
            (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t))
          (Set.Icc (-delta) delta) t)
    (hObound :
      ∀ t ∈ Set.Icc (-delta) delta,
        (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1 ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ t ∈ Set.Icc (-delta) delta,
      (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1 =
        Psi p t := by
  let t0delta : Set.Icc (0 - delta) (0 + delta) :=
    ⟨0, by simp [le_of_lt hdelta]⟩
  have hpldelta :
      IsPicardLindelof
        (fun _ : Real => varSpray (I := I) g x)
        (tmin := 0 - delta) (tmax := 0 + delta)
        t0delta
        (varPhaseZero (I := I) (E := E) x)
        a r L K := by
    exact hpl.shrink_time t0delta (by rfl) (by linarith) (by linarith)
  have hflowdelta :
      ∀ q ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Psi q t0delta = q ∧
          ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
            HasDerivWithinAt (Psi q)
              ((fun _ : Real => varSpray (I := I) g x) t (Psi q t))
              (Set.Icc (0 - delta) (0 + delta)) t := by
    intro q hq
    refine ⟨by simpa [t0delta] using (hflow q hq).1, ?_⟩
    intro t ht
    have hteps : t ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith [ht.1, ht.2, hdle]
    have hwithin := (hflow q hq).2 t hteps
    exact hwithin.mono (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, hdle])
  have ht0delta : (t0delta : Real) ∈ Set.Ioo (0 - delta) (0 + delta) := by
    simpa [t0delta] using hdelta
  let beta : Real -> VarPhase (E := E) :=
    fun t => (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1
  have hbetawithin :
      ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
        HasDerivWithinAt beta
          ((fun _ : Real => varSpray (I := I) g x) t (beta t))
          (Set.Icc (0 - delta) (0 + delta)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (-delta) delta := by simpa using ht
    let idLin : VarLin (E := E) :=
      ContinuousLinearMap.id Real (VarPhase (E := E))
    have hfst :
        HasFDerivWithinAt (fun q : VarPhase (E := E) × VarLin (E := E) => q.1)
          (ContinuousLinearMap.fst Real (VarPhase (E := E)) (VarLin (E := E)))
          Set.univ (Omega (p, idLin) t) :=
      (hasFDerivAt_fst (𝕜 := Real) (E := VarPhase (E := E))
        (F := VarLin (E := E)) (p := Omega (p, idLin) t)).hasFDerivWithinAt
    have hmaps :
        Set.MapsTo (Omega (p, idLin)) (Set.Icc (0 - delta) (0 + delta)) Set.univ := by
      intro y hy
      trivial
    have hO' :
        HasDerivWithinAt (Omega (p, idLin))
          (variationalRHS (varSpray (I := I) g x) (Omega (p, idLin) t))
          (Set.Icc (0 - delta) (0 + delta)) t := by
      simpa [idLin] using hOderiv t ht'
    have hcomp := hfst.comp_hasDerivWithinAt t hO' hmaps
    change HasDerivWithinAt
      (fun τ : Real => (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) τ).1)
      (varSpray (I := I) g x
        (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1)
      (Set.Icc (0 - delta) (0 + delta)) t
    simpa [idLin, variationalRHS, paramVariationalRHS, Function.comp_def] using hcomp
  have hbetacont :
      ContinuousOn beta (Set.Icc (0 - delta) (0 + delta)) := by
    exact HasDerivWithinAt.continuousOn hbetawithin
  have hbetaderiv :
      ∀ t ∈ Set.Ioo (0 - delta) (0 + delta),
        HasDerivAt beta
          ((fun _ : Real => varSpray (I := I) g x) t (beta t)) t := by
    intro t ht
    have hwithin := hbetawithin t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc (0 - delta) (0 + delta) ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hbeta0 : beta t0delta = p := by
    simpa [beta, t0delta] using congrArg Prod.fst hOinit
  have hbetabound :
      ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
        beta t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
    intro t ht
    have ht' : t ∈ Set.Icc (-delta) delta := by simpa using ht
    simpa [beta] using hObound t ht'
  have hEq :=
    plFlow_eq_of_solution_at
      (F := VarPhase (E := E))
      (f := fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - delta) (tmax := 0 + delta)
      (t0 := t0delta)
      (x0 := varPhaseZero (I := I) (E := E) x)
      (x := p)
      (a := a) (r := r) (L := L) (K := K)
      hpldelta ht0delta hp
      (alpha := Psi) hflowdelta hbound
      (beta := beta)
      hbeta0 hbetacont hbetaderiv hbetabound
  intro t ht
  have ht' : t ∈ Set.Icc (0 - delta) (0 + delta) := by simpa using ht
  exact (hEq t ht').symm

/-- Source control descends from a convex augmented closed ball to base-phase
segments. -/
theorem varBase_segment_src_of_bound
    [I.Boundaryless]
    (x : M) {a : NNReal}
    {p q : ModelPhase (E := E) × ModelLin (E := E)}
    (hp : p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hq : q ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    {u : ModelPhase (E := E)}
    (hu : u ∈ segment Real p.1 q.1) :
    u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
      (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  rcases hu with ⟨c, d, hc, hd, hcd, hu⟩
  let w : ModelPhase (E := E) × ModelLin (E := E) := c • p + d • q
  have hwseg : w ∈ segment Real p q := by
    refine ⟨c, d, hc, hd, hcd, ?_⟩
    rfl
  have hwball :
      w ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a :=
    (convex_closedBall (varPhaseZero (I := I) (E := E) x) (a : Real)).segment_subset
      hp hq hwseg
  have hwsrc := hsrc hwball
  rw [← hu]
  simpa [w]
    using hwsrc

/-- Base component of an augmented variational flow. -/
def varBaseFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).1

/-- The model flow extracted from an augmented variational flow by fixing the
linear initial condition to the identity and projecting to the base phase. -/
def varModelFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)) :
    ModelPhase (E := E) -> Real -> ModelPhase (E := E) :=
  fun z t => varBaseFlow (E := E) Ψ z t

@[simp] theorem varModelFlow_apply
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    varModelFlow (E := E) Ψ z t = varBaseFlow (E := E) Ψ z t := rfl

/-- Source control for the segment between two base trajectories, obtained from
the source-controlled augmented flow bound. -/
theorem varBase_segment_src_of_flow_bound
    [I.Boundaryless]
    (x : M)
    {a r : NNReal}
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z h : ModelPhase (E := E)} {t : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ u ∈ segment Real
        (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t),
      u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  intro u hu
  exact
    varBase_segment_src_of_bound (I := I) (E := E) x
      (hbound (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) hz0 t)
      (hbound (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) hzh0 t)
      hsrc hu

/-- Linearized component of an augmented variational flow. -/
def varDerivFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelLin (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).2

/-- Explicit linear flow generated by `modelSprayLin`: `(dq, dv) ↦
`(dq + t • dv, dv)`. -/
def phaseLinFlow (t : Real) : ModelLin (E := E) :=
  ContinuousLinearMap.id Real (ModelPhase (E := E)) +
    t • modelSprayLin (E := E)

/-- The explicit augmented trajectory through the zero phase: the base phase is
fixed and the linear component is the flow of `modelSprayLin`. -/
def varZeroPhaseLin (x : M) (t : Real) :
    ModelPhase (E := E) × ModelLin (E := E) :=
  (extChartAt I.tangent (phaseZero (I := I) x)
    (phaseZero (I := I) x),
    phaseLinFlow (E := E) t)

@[simp] theorem phaseLinFlow_fst (t : Real) (z : ModelPhase (E := E)) :
    (phaseLinFlow (E := E) t z).1 = z.1 + t • z.2 := by
  simp [phaseLinFlow, modelSprayLin]

@[simp] theorem phaseLinFlow_snd (t : Real) (z : ModelPhase (E := E)) :
    (phaseLinFlow (E := E) t z).2 = z.2 := by
  simp [phaseLinFlow, modelSprayLin]

@[simp] theorem phaseLinFlow_zero :
    phaseLinFlow (E := E) 0 =
      ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
  ext z <;> simp [phaseLinFlow]

@[simp] theorem phaseLinFlow_fiber_fst (t : Real) (v : E) :
    (phaseLinFlow (E := E) t (0, v)).1 = t • v := by
  simp

@[simp] theorem modelSprayLin_comp_phaseLinFlow (t : Real) :
    (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t) =
      modelSprayLin (E := E) := by
  ext z <;> simp [phaseLinFlow, modelSprayLin]

/-- The explicit linear phase flow solves the variational equation at the zero
phase. -/
theorem phaseLinFlow_hasDerivAt (t : Real) :
    HasDerivAt
      (fun s : Real => phaseLinFlow (E := E) s)
      ((modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t))
      t := by
  have hlin :
      HasDerivAt
        (fun s : Real => s • modelSprayLin (E := E))
        (modelSprayLin (E := E)) t := by
    simpa using (hasDerivAt_id t).smul_const (modelSprayLin (E := E))
  rw [modelSprayLin_comp_phaseLinFlow]
  simpa [phaseLinFlow] using
    hlin.const_add (ContinuousLinearMap.id Real (ModelPhase (E := E)))

@[simp] theorem varZeroPhaseLin_zero (x : M) :
    varZeroPhaseLin (I := I) (E := E) x 0 =
      varPhaseZero (I := I) (E := E) x := by
  simp [varZeroPhaseLin, varPhaseZero]

/-- Along the zero base phase, the augmented variational vector field is the
explicit linearized spray equation. -/
theorem varSpray_zero_phaseLin
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    varSpray (I := I) g x (varZeroPhaseLin (I := I) (E := E) x t) =
      (0, (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t)) := by
  apply Prod.ext
  · simpa using modelSpray_zero (I := I) g x
  · have hfd :
        fderiv Real (modelSpray (I := I) g x)
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) =
          modelSprayLin (E := E) :=
      (spray_fderiv_zero (I := I) g x).fderiv
    simp only [varSpray, varZeroPhaseLin]
    change
      (fderiv Real (modelSpray (I := I) g x)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x))).comp
          (phaseLinFlow (E := E) t) =
        (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t)
    rw [hfd]

/-- The curve with zero base phase and explicit linearized flow solves the
augmented variational ODE. -/
theorem varZeroPhaseLin_hasDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    HasDerivAt
      (varZeroPhaseLin (I := I) (E := E) x)
      (varSpray (I := I) g x (varZeroPhaseLin (I := I) (E := E) x t))
      t := by
  have hbase :
      HasDerivAt
        (fun _s : Real =>
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
        (0 : ModelPhase (E := E)) t :=
    hasDerivAt_const (x := t)
      (c := extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
  have hlin := phaseLinFlow_hasDerivAt (E := E) t
  have hprod := hbase.prodMk hlin
  rw [varSpray_zero_phaseLin (I := I) g x t]
  simpa [varZeroPhaseLin] using hprod

/-- The explicit zero-phase linearized trajectory stays in any positive
augmented closed ball after shrinking time around zero. -/
theorem varZeroPhaseLin_mem_closedBall_small
    (x : M) {a : NNReal} (ha : 0 < a) :
    ∃ δ : Real, 0 < δ ∧
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
  have hbase :
      ContinuousAt
        (fun _s : Real =>
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) 0 :=
    continuousAt_const
  have hlin :
      ContinuousAt (fun s : Real => phaseLinFlow (E := E) s) 0 :=
    (phaseLinFlow_hasDerivAt (E := E) 0).continuousAt
  have hcont :
      ContinuousAt (varZeroPhaseLin (I := I) (E := E) x) 0 := by
    simpa [varZeroPhaseLin] using hbase.prodMk hlin
  have hball :
      Metric.ball (varPhaseZero (I := I) (E := E) x) (a : Real) ∈
        𝓝 (varPhaseZero (I := I) (E := E) x) :=
    Metric.ball_mem_nhds _ (by exact_mod_cast ha)
  have hev :
      ∀ᶠ t : Real in 𝓝 0,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.ball (varPhaseZero (I := I) (E := E) x) (a : Real) :=
    hcont.eventually (by simpa using hball)
  rcases Metric.mem_nhds_iff.mp hev with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro t ht
  have ht_abs : |t| ≤ ρ / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have htball : t ∈ Metric.ball (0 : Real) ρ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [sub_zero] using lt_of_le_of_lt ht_abs (half_lt_self hρ)
  exact Metric.ball_subset_closedBall (hρsub htball)

/-- On a sufficiently small time interval, any Picard-Lindelof augmented flow
through the zero variational phase agrees with the explicit zero-phase
linearized trajectory. -/
theorem varFlow_zero_phaseLin_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε δ : Real} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε)
    {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (varPhaseZero (I := I) (E := E) x)
      a r L K)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall
            (varPhaseZero (I := I) (E := E) x) a)
    (hcand :
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ t ∈ Set.Icc (-δ) δ,
      Ψ (varPhaseZero (I := I) (E := E) x) t =
        varZeroPhaseLin (I := I) (E := E) x t := by
  let t0ε : Set.Icc (0 - ε) (0 + ε) := ⟨0, by simp [le_of_lt hε]⟩
  let t0δ : Set.Icc (0 - δ) (0 + δ) := ⟨0, by simp [le_of_lt hδ]⟩
  have hplδ :
      IsPicardLindelof
        (fun _ : Real => varSpray (I := I) g x)
        (tmin := 0 - δ) (tmax := 0 + δ)
        t0δ
        (varPhaseZero (I := I) (E := E) x)
        a r L K := by
    exact hpl.shrink_time t0δ (by rfl) (by linarith) (by linarith)
  have hflowδ :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p t0δ = p ∧
          ∀ t ∈ Set.Icc (0 - δ) (0 + δ),
            HasDerivWithinAt (Ψ p)
              ((fun _ : Real => varSpray (I := I) g x) t (Ψ p t))
              (Set.Icc (0 - δ) (0 + δ)) t := by
    intro p hp
    refine ⟨by simpa [t0δ] using (hflow p hp).1, ?_⟩
    intro t ht
    have htε : t ∈ Set.Icc (-ε) ε := by
      constructor <;> linarith [ht.1, ht.2, hδε]
    have hwithin := (hflow p hp).2 t htε
    exact hwithin.mono (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, hδε])
  have ht0δ : (t0δ : Real) ∈ Set.Ioo (0 - δ) (0 + δ) := by
    simpa [t0δ] using hδ
  have hβcont :
      ContinuousOn (varZeroPhaseLin (I := I) (E := E) x)
        (Set.Icc (0 - δ) (0 + δ)) := by
    intro t ht
    exact (varZeroPhaseLin_hasDerivAt (I := I) g x t).continuousAt.continuousWithinAt
  have hβderiv :
      ∀ t ∈ Set.Ioo (0 - δ) (0 + δ),
        HasDerivAt (varZeroPhaseLin (I := I) (E := E) x)
          ((fun _ : Real => varSpray (I := I) g x) t
            (varZeroPhaseLin (I := I) (E := E) x t)) t := by
    intro t _ht
    simpa using varZeroPhaseLin_hasDerivAt (I := I) g x t
  have hEq :=
    plFlow_eq_of_solution
      (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - δ) (tmax := 0 + δ)
      (t0 := t0δ)
      (x0 := varPhaseZero (I := I) (E := E) x)
      (a := a) (r := r) (L := L) (K := K)
      hplδ ht0δ
      (α := Ψ) hflowδ hbound
      (β := varZeroPhaseLin (I := I) (E := E) x)
      (by simp [t0δ]) hβcont hβderiv
      (by
        intro t ht
        have ht' : t ∈ Set.Icc (-δ) δ := by simpa using ht
        exact hcand t ht')
  intro t ht
  have ht' : t ∈ Set.Icc (0 - δ) (0 + δ) := by simpa using ht
  exact hEq t ht'

/-- The base trajectory of an augmented solution is continuous on any smaller
time interval. -/
theorem varBaseFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varBaseFlow] using continuous_fst.comp_continuousOn hcont

/-- The linearized trajectory of an augmented solution is continuous on any
smaller time interval. -/
theorem varDerivFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varDerivFlow] using continuous_snd.comp_continuousOn hcont

/-- The derivative of the model spray is bounded along a source-controlled base
trajectory on a compact time interval. -/
theorem modelSpray_fderiv_bound_on_baseFlow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source) :
    ∃ B : Real, ∀ t ∈ Set.Icc (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B := by
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hDF :
      ContinuousOn
        (fun t =>
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (0 : Real) b) := by
    intro t ht
    have hDFat :
        ContinuousAt
          (fderiv Real (modelSpray (I := I) g x))
          (varBaseFlow (E := E) Ψ z t) := by
      exact
        ((modelSpray_contDiffAt_of_mem (I := I) g x
          (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
          (by
            exact WithTop.coe_le_coe.2
              (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
    exact hDFat.comp_continuousWithinAt (hbase.continuousWithinAt ht)
  exact isCompact_Icc.exists_bound_of_continuousOn hDF

/-- Uniform continuity of `D(modelSpray)` in a tube around a compact,
source-controlled base trajectory. -/
theorem modelSpray_fderiv_uniform_tube
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {K : Set Real} (hK : IsCompact K)
    {γ : Real -> ModelPhase (E := E)}
    (hγ : ContinuousOn γ K)
    (hsrc : ∀ t ∈ K,
      γ t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (γ t)).proj ∈ (extChartAt I x).source) :
    ∀ c > 0, ∃ δ > 0, ∀ t ∈ K, ∀ u : ModelPhase (E := E),
      dist u (γ t) < δ ->
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x) (γ t)‖ ≤ c := by
  intro c hc
  let D : ModelPhase (E := E) -> ModelLin (E := E) :=
    fderiv Real (modelSpray (I := I) g x)
  have hcomp : IsCompact (γ '' K) :=
    hK.image_of_continuousOn hγ
  have hDcont : ∀ y ∈ γ '' K, ContinuousAt D y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact
      ((modelSpray_contDiffAt_of_mem (I := I) g x
        (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
        (by
          exact WithTop.coe_le_coe.2
            (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
  have hU :
      {p : ModelPhase (E := E) × ModelPhase (E := E) |
        p.1 ∈ γ '' K ->
          (D p.1, D p.2) ∈
            {q : ModelLin (E := E) × ModelLin (E := E) |
              dist q.1 q.2 < c}} ∈
        𝓤 (ModelPhase (E := E)) :=
    hcomp.uniformContinuousAt_of_continuousAt D hDcont
      (Metric.dist_mem_uniformity hc)
  rcases Metric.mem_uniformity_dist.mp hU with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu
  have hpair :
      ((γ t, u) : ModelPhase (E := E) × ModelPhase (E := E)) ∈
        {p : ModelPhase (E := E) × ModelPhase (E := E) |
          p.1 ∈ γ '' K ->
            (D p.1, D p.2) ∈
              {q : ModelLin (E := E) × ModelLin (E := E) |
                dist q.1 q.2 < c}} :=
    hδsub (by simpa [dist_comm] using hu)
  have hγmem : γ t ∈ γ '' K := ⟨t, ht, rfl⟩
  have hdist : dist (D (γ t)) (D u) < c := hpair hγmem
  have hnorm : ‖D u - D (γ t)‖ < c := by
    have hdist' : dist (D u) (D (γ t)) < c := by
      simpa [dist_comm] using hdist
    simpa [D, dist_eq_norm] using hdist'
  simpa [D] using le_of_lt hnorm

@[simp] theorem varBaseFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varBaseFlow (E := E) Ψ z 0 = z := by
  simpa [varBaseFlow] using congrArg Prod.fst hΨ0

@[simp] theorem varDerivFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varDerivFlow (E := E) Ψ z 0 =
      ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
  simpa [varDerivFlow] using congrArg Prod.snd hΨ0

/-- A base phase in the model closed ball gives an augmented phase in the
corresponding variational closed ball when the linear component is the identity. -/
theorem varPhase_mem_closedBall_of_base_mem
    {x : M} {r : NNReal} {z : ModelPhase (E := E)}
    (hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) r) :
    (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) r := by
  rw [Metric.mem_closedBall] at hz ⊢
  simpa [varPhaseZero, Prod.dist_eq] using hz

/-- The base component of an augmented flow solves the original model ODE. -/
theorem varBaseFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varBaseFlow (E := E) Ψ z)
      (modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hfst :
      HasFDerivWithinAt (fun q : Z × L => q.1)
        (ContinuousLinearMap.fst Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_fst (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hfst.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varSpray, Z, L, p, A] using hcomp

/-- A source-controlled augmented variational flow projects to a functional
model flow solving the original model spray ODE. -/
theorem varModelFlow_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {r : NNReal} {ε : Real}
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      varModelFlow (E := E) Ψ z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt
            (varModelFlow (E := E) Ψ z)
            (modelSpray (I := I) g x (varModelFlow (E := E) Ψ z t))
            (Set.Icc (-ε) ε) t := by
  intro z hz
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  refine ⟨?_, ?_⟩
  · exact varBaseFlow_zero_of_flow (E := E) (hflow _ hp).1
  · intro t ht
    exact varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x
      ((hflow _ hp).2 t ht)

/-- A closed-ball-bounded augmented variational flow projects to a
closed-ball-bounded model flow. -/
theorem varModelFlow_bound
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (x : M) {a r : NNReal}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t : Real,
        varModelFlow (E := E) Ψ z t ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) a := by
  intro z hz t
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  have hq := hbound _ hp t
  rw [Metric.mem_closedBall] at hq ⊢
  let z0 : ModelPhase (E := E) :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hfst :
      dist (varModelFlow (E := E) Ψ z t) z0 ≤
        dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t)
          (varPhaseZero (I := I) (E := E) x) := by
    change
      dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).1 z0 ≤
        dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t)
          (z0, ContinuousLinearMap.id Real (ModelPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  exact hfst.trans hq

/-- Source control for the projected model flow extracted from an augmented
closed-ball-bounded variational flow. -/
theorem varModelFlow_src
    [I.Boundaryless]
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (x : M) {a r : NNReal} {ε : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈
              (extChartAt I x).source}) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        varModelFlow (E := E) Ψ z t ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (varModelFlow (E := E) Ψ z t)).proj ∈
            (extChartAt I x).source := by
  intro z hz t _ht
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  have hs := hsrc (hbound _ hp t)
  simpa [varModelFlow, varBaseFlow] using hs

/-- The linear component of an augmented flow solves the variational equation. -/
theorem varDerivFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varDerivFlow (E := E) Ψ z)
      ((fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)).comp
        (varDerivFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hsnd :
      HasFDerivWithinAt (fun q : Z × L => q.2)
        (ContinuousLinearMap.snd Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_snd (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hsnd.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varDerivFlow, varSpray, Z, L, p, A] using hcomp

/-- Error between the base flow at `z + h` and the linearized approximation
from the augmented flow at `z`. -/
def varError
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  varBaseFlow (E := E) Ψ (z + h) t -
    varBaseFlow (E := E) Ψ z t -
    varDerivFlow (E := E) Ψ z t h

/-- The variational approximation error is continuous on any smaller time
interval where both augmented trajectories solve the ODE. -/
theorem varError_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z h : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b) := by
  have hbase_zh :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ (z + h) t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨzh
  have hbase_z :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hder_z :
      ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varDerivFlow_continuousOn_of_flow (E := E) hb hΨz
  simpa [varError, flowError] using
    flowError_continuousOn (Φ := varBaseFlow (E := E) Ψ)
      (A := varDerivFlow (E := E) Ψ) hbase_zh hbase_z hder_z

/-- Raw right-hand side of the error equation. -/
def varErrorRHS
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varDerivFlow (E := E) Ψ z t h)

/-- Taylor residual part of the error equation. -/
def varTaylorRem
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t)

/-- Pointwise Taylor-residual estimate for the error equation. -/
theorem varTaylorRem_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ‖varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t‖ := by
  simpa [varTaylorRem] using
    modelSpray_taylor_bound (I := I) g x hs hctrl hz hzh hD

/-- Lipschitz dependence of the augmented flow controls the separation of the
base components. -/
theorem varBaseFlow_dist_le_of_lipschitz
    (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {r L' : NNReal} {z h : ModelPhase (E := E)} {t : Real}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    dist (varBaseFlow (E := E) Ψ (z + h) t)
      (varBaseFlow (E := E) Ψ z t) ≤ (L' : Real) * ‖h‖ := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let pzh : Z × L := (z + h, ContinuousLinearMap.id Real Z)
  let pz : Z × L := (z, ContinuousLinearMap.id Real Z)
  have hdist := hLip.dist_le_mul pzh hzh pz hz
  have hfst :
      dist (varBaseFlow (E := E) Ψ (z + h) t)
        (varBaseFlow (E := E) Ψ z t) ≤
          dist (Ψ pzh t) (Ψ pz t) := by
    change dist (Ψ pzh t).1 (Ψ pz t).1 ≤ dist (Ψ pzh t) (Ψ pz t)
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hpdist : dist pzh pz = ‖h‖ := by
    have hzdist : dist (z + h) z = ‖h‖ := by
      rw [dist_eq_norm]
      have hsub : z + h - z = h := by
        abel
      rw [hsub]
    simp [pzh, pz, dist_prod_same_right, hzdist]
  exact hfst.trans (by simpa [hpdist] using hdist)

/-- The Lipschitz flow estimate turns the compact tube continuity of
`D(modelSpray)` into a uniform derivative-difference bound on trajectory
segments for sufficiently small initial perturbations. -/
theorem modelSpray_fderiv_segment_small_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ η > 0, ∃ ρ > 0, ∀ h : ModelPhase (E := E),
      (L' : Real) * ‖h‖ < ρ ->
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
        ∀ u ∈ segment Real
            (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t),
          ‖fderiv Real (modelSpray (I := I) g x) u -
            fderiv Real (modelSpray (I := I) g x)
              (varBaseFlow (E := E) Ψ z t)‖ ≤ η := by
  intro η hη
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  obtain ⟨ρ, hρ, hρsmall⟩ :=
    modelSpray_fderiv_uniform_tube (I := I) g x
      (K := Set.Icc (0 : Real) b) isCompact_Icc hbase hsrc_base η hη
  refine ⟨ρ, hρ, ?_⟩
  intro h hsmall hzh0 t ht u hu
  have htcc : t ∈ Set.Icc (0 : Real) b := ⟨ht.1, le_of_lt ht.2⟩
  have hsegball :
      u ∈ Metric.closedBall
          (varBaseFlow (E := E) Ψ z t)
          (dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t)) :=
    segment_subset_closedBall_left
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t) hu
  have hbase_dist :
      dist (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t) ≤ (L' : Real) * ‖h‖ := by
    simpa [dist_comm] using
      varBaseFlow_dist_le_of_lipschitz (E := E) x (hLip t ht) hz0 hzh0
  have hu_dist :
      dist u (varBaseFlow (E := E) Ψ z t) < ρ := by
    have hle :
        dist u (varBaseFlow (E := E) Ψ z t) ≤
          dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t) := by
      simpa [Metric.mem_closedBall] using hsegball
    exact lt_of_le_of_lt (hle.trans hbase_dist) hsmall
  exact hρsmall t htcc u hu_dist

/-- Taylor residual estimate after applying the augmented-flow Lipschitz bound
to the base separation. -/
theorem varTaylorRem_norm_le_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ((L' : Real) * ‖h‖) := by
  have hTaylor :=
    varTaylorRem_norm_le (I := I) g x Ψ z h t hs hctrl hz hzh hD
  have hsep :=
    varBaseFlow_dist_le_of_lipschitz (I := I) (E := E) x hLip hz0 hzh0
  rw [dist_eq_norm] at hsep
  have hC : 0 ≤ C := (norm_nonneg _).trans (hD _ hz)
  exact hTaylor.trans (mul_le_mul_of_nonneg_left hsep hC)

/-- Gronwall-ready pointwise estimate for the approximation-error RHS. -/
theorem varErrorRHS_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {B C : Real}
    (hB :
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
      B * ‖varError (E := E) Ψ z h t‖ +
        C * ((L' : Real) * ‖h‖) := by
  have hRem :
      ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
        C * ((L' : Real) * ‖h‖) :=
    varTaylorRem_norm_le_of_lipschitz (I := I) g x Ψ z h t
      hs hctrl hz hzh hD hLip hz0 hzh0
  change
    ‖flowErrorRHS (modelSpray (I := I) g x)
        (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t‖ ≤
      B * ‖flowError (varBaseFlow (E := E) Ψ)
          (varDerivFlow (E := E) Ψ) z h t‖ +
        C * ((L' : Real) * ‖h‖)
  exact flowErrorRHS_norm_le
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    z h t hB (by simpa [flowTaylorRem, varTaylorRem] using hRem)

/-- The raw error RHS is the Taylor residual plus the linearized equation
applied to the current error. -/
theorem varErrorRHS_eq_taylorRem_add
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) :
    varErrorRHS (I := I) g x Ψ z h t =
      varTaylorRem (I := I) g x Ψ z h t +
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)
          (varError (E := E) Ψ z h t) := by
  change
    flowErrorRHS (modelSpray (I := I) g x)
        (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t =
      flowTaylorRem (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ) z h t +
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)
          (flowError (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t)
  exact flowErrorRHS_eq_taylorRem_add
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ) z h t

/-- The approximation error satisfies the expected inhomogeneous linear ODE. -/
theorem varError_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε t : Real}
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  have hbase_zh :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ (z + h))
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ (z + h) t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨzh
  have hbase_z :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ z)
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  have hA :
      HasDerivWithinAt
        (varDerivFlow (E := E) Ψ z)
        ((fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)).comp
          (varDerivFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varDerivFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  simpa [varError, varErrorRHS, flowError, flowErrorRHS, Z] using
    flowError_hasDerivWithinAt
      (F := modelSpray (I := I) g x)
      (Φ := varBaseFlow (E := E) Ψ)
      (A := varDerivFlow (E := E) Ψ)
      (z := z) (h := h) (s := Set.Icc (-ε) ε) (t := t)
      hbase_zh hbase_z hA

/-- Restrict the approximation-error ODE from the Picard time interval to a
smaller closed interval. -/
theorem varError_hasDerivWithinAt_Icc
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε a b t : Real}
    (hab : Set.Icc a b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc a b) t :=
  (varError_hasDerivWithinAt (I := I) g x hΨzh hΨz).mono hab

/-- The approximation error is zero at the initial time for a flow with the
expected augmented initial conditions. -/
theorem varError_zero
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (z h : ModelPhase (E := E))
    (hΨzh :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varError (E := E) Ψ z h 0 = 0 := by
  simp [varError, varBaseFlow, varDerivFlow, hΨzh, hΨz]

/-- If the variational approximation error is little-o in the initial
perturbation, then the linear component of the augmented flow is the Frechet
derivative of the base flow at the fixed time. -/
theorem varBaseFlow_hasFDerivAt_of_error
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t : Real}
    (herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h t)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h)) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  exact flow_hasFDerivAt_of_error (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    (by simpa [flowError, varError] using herr)

/-- Fixed-time C1-dependence checkpoint from an eventual Gronwall bound with a
vanishing Taylor-residual coefficient. -/
theorem varBaseFlow_hasFDerivAt_of_gronwall
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t B L T : Real}
    {C : ModelPhase (E := E) -> Real}
    (hC : Tendsto C (𝓝 0) (𝓝 0))
    (hbound : ∀ᶠ h in 𝓝 (0 : ModelPhase (E := E)),
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  exact flow_hasFDerivAt_of_gronwall (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ) (C := C) (B := B) (L := L) (T := T)
    hC (by simpa [flowError, varError] using hbound)

/-- Gronwall bound for the approximation error once the error RHS has the
standard linear-plus-forcing estimate. -/
theorem varError_norm_le_gronwall
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Ici t) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  flowError_norm_le_gronwall
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    z h (by simpa [flowError, varError] using hcont)
    (by
      intro t ht
      simpa [flowError, flowErrorRHS, varError, varErrorRHS] using hderiv t ht)
    (by simpa [flowError, varError] using ha)
    (by
      intro t ht
      simpa [flowError, flowErrorRHS, varError, varErrorRHS] using hbound t ht)

/-- Version of `varError_norm_le_gronwall` for derivatives known on the
closed interval itself. -/
theorem varError_norm_le_gronwall_Icc
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Icc a b) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  varError_norm_le_gronwall (I := I) g x Ψ z h hcont
    (fun t ht =>
      (hderiv t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
    ha hbound

/-- Main checked Gronwall estimate for the variational approximation error on
a fixed forward time interval. -/
theorem varError_norm_le_gronwall_of_flow_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal} {s : Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t hs hctrl
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Time-dependent convex-set version of
`varError_norm_le_gronwall_of_flow_bounds`.

This is the useful form for the C1-dependence proof: at each time the Taylor
estimate can be taken on the segment between the two base trajectories. -/
theorem varError_norm_le_gronwall_of_time_sets
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    {s : Real -> Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : ∀ t ∈ Set.Ico (0 : Real) b, Convex Real (s t))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b, ∀ q ∈ s t,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s t)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s t)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s t,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t (hs t ht) (hctrl t ht)
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Segment-specialized Gronwall estimate for the variational approximation
error.

This is the form closest to the differentiability proof: the Taylor estimate is
taken on the segment from `Phi z t` to `Phi (z + h) t`. -/
theorem varError_norm_le_gronwall_of_segment_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ q ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_time_sets (I := I) g x Ψ z h hb
      hcont hΨzh hΨz hΨzh0 hΨz0 ?_ hctrl ?_ ?_ hB hD hLip hz0 hzh0
  · intro t _ht
    exact convex_segment (𝕜 := Real)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact left_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact right_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)

/-- Segment-specialized Gronwall estimate using source control and continuity
directly from the bounded augmented flow. -/
theorem varError_norm_le_gronwall_of_segment_bounds_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a r : NNReal} {ε b B C : Real} {L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_segment_bounds (I := I) g x Ψ z h hb
      ?_ (fun t ht => hΨzh t (hb ht)) (fun t ht => hΨz t (hb ht))
      hΨzh0 hΨz0 ?_ hB hD hLip hz0 hzh0
  · exact varError_continuousOn_of_flow (E := E) hb hΨzh hΨz
  · intro t _ht
    exact
      varBase_segment_src_of_flow_bound (I := I) (E := E) x
        hbound hsrc hz0 hzh0

/-- C1-dependence checkpoint: for a source-controlled augmented flow, the
linearized component is the Frechet derivative of the fixed-time base flow at
any interior initial phase. -/
theorem varBaseFlow_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z := by
  let pz : ModelPhase (E := E) × ModelLin (E := E) :=
    (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))
  have hz0 : pz ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    Metric.ball_subset_closedBall hzopen
  have hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source := by
    intro t ht
    have hs := hsrc (hbound pz hz0 t)
    simpa [pz, varBaseFlow] using hs
  obtain ⟨B, hBcc⟩ :=
    modelSpray_fderiv_bound_on_baseFlow (I := I) g x hb
      (hflow pz hz0).2 hsrc_base
  have hDsmall :=
    modelSpray_fderiv_segment_small_of_lipschitz (I := I) g x
      (Ψ := Ψ) (z := z) (ε := ε) (b := b) (r := r) (L' := L') hb
      (hflow pz hz0).2 hsrc_base
      (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩)) hz0
  have hinit_cont :
      ContinuousAt
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        0 := by
    have hleft : ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0)
    have hright :
        ContinuousAt
          (fun _h : ModelPhase (E := E) =>
            ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 :=
      continuousAt_const
    exact hleft.prodMk_nhds hright
  have hzh_eventually :
      ∀ᶠ h : ModelPhase (E := E) in 𝓝 0,
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) r := by
    have hzopen0 :
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))) 0 ∈
            Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
      simpa using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  have herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h b)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h) := by
    refine
      isLittleO_of_gronwall_bound_eventually
        (X := ModelPhase (E := E)) (Y := ModelPhase (E := E))
        (B := B) (L := (L' : Real)) (T := b) ?_
    intro η hη
    obtain ⟨ρ, hρ, hDρ⟩ := hDsmall η hη
    have hmul_cont :
        Continuous
          (fun h : ModelPhase (E := E) => (L' : Real) * ‖h‖) :=
      continuous_const.mul continuous_norm
    have hsmall_eventually :
        ∀ᶠ h : ModelPhase (E := E) in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
      have hball :=
        (hmul_cont.continuousAt (x := (0 : ModelPhase (E := E)))).eventually
          (Metric.ball_mem_nhds
            ((L' : Real) * ‖(0 : ModelPhase (E := E))‖) hρ)
      filter_upwards [hball] with h hh
      have habs : |(L' : Real) * ‖h‖| < ρ := by
        simpa [Real.dist_eq] using hh
      exact (abs_lt.1 habs).2
    filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
    let pzh : ModelPhase (E := E) × ModelLin (E := E) :=
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))
    have hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ η :=
      hDρ h hsmall hzh0
    have hgr :=
      varError_norm_le_gronwall_of_segment_bounds_flow (I := I) g x Ψ z h
        (a := a) (r := r) (L' := L') hb
        (hflow pzh hzh0).2 (hflow pz hz0).2
        (hflow pzh hzh0).1 (hflow pz hz0).1
        hbound hsrc
        (fun t ht => hBcc t ⟨ht.1, le_of_lt ht.2⟩)
        hD
        (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩))
        hz0 hzh0
    simpa using hgr b ⟨hb0, le_rfl⟩
  exact varBaseFlow_hasFDerivAt_of_error (E := E) herr

/-- Fixed-time endpoint derivative for a source-controlled augmented flow.

This is the endpoint-facing name for `varBaseFlow_hasFDerivAt_of_flow`: the
map sending an initial phase to its fixed-time model endpoint has derivative
given by the variational component. -/
theorem timeEndpoint_hasFDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z :=
  varBaseFlow_hasFDerivAt_of_flow (I := I) g x Ψ z
    hb0 hb hflow hbound hsrc hLip hzopen

/-- Strict fixed-time endpoint derivative for a source-controlled augmented
flow.  This upgrades the checked C1 dependence using the fixed-time Lipschitz
dependence of the augmented Picard flow. -/
theorem timeEndpoint_hasStrictFDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z := by
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  have hpairCont :
      ContinuousAt (fun z' : ModelPhase (E := E) => (z', idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun y : ModelPhase (E := E) => varDerivFlow (E := E) Ψ y b) ?_ ?_
  · have hU :
        {z' : ModelPhase (E := E) |
          (z', idLin) ∈ Metric.ball (varPhaseZero (I := I) (E := E) x) r} ∈
          𝓝 z :=
      hpairCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
    filter_upwards [hU] with y hy
    exact timeEndpoint_hasFDerivAt (I := I) g x Ψ y hb0 hb
      hflow hbound hsrc hLip (by simpa [idLin] using hy)
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontAt :
        ContinuousAt (fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
          (z, idLin) :=
      (hLip b hbmem).continuousOn.continuousAt
        (Metric.closedBall_mem_nhds_of_mem (by simpa [idLin] using hzopen))
    have hcomp :
        ContinuousAt
          (fun z' : ModelPhase (E := E) => Ψ (z', idLin) b) z :=
      ContinuousAt.comp
        (f := fun z' : ModelPhase (E := E) => (z', idLin))
        (g := fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
        (x := z) hΨcontAt hpairCont
    simpa [varDerivFlow, idLin] using continuous_snd.continuousAt.comp hcomp

/-- Fixed-time endpoint is `C1` in the initial phase for a source-controlled
augmented variational flow. -/
theorem timeEndpoint_contDiffAt_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      z := by
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  let U : Set (ModelPhase (E := E)) :=
    {z' | (z', idLin) ∈ Metric.ball (varPhaseZero (I := I) (E := E) x) r}
  have hpairCont :
      ContinuousAt (fun z' : ModelPhase (E := E) => (z', idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine ⟨fun y : ModelPhase (E := E) => varDerivFlow (E := E) Ψ y b,
    U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : ModelPhase (E := E) => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : ModelPhase (E := E) => (y, idLin)) U
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn
          (fun y : ModelPhase (E := E) => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [varDerivFlow, idLin] using hcomp.snd
  · intro y hy
    exact timeEndpoint_hasFDerivAt (I := I) g x Ψ y hb0 hb
      hflow hbound hsrc hLip (by simpa [U, idLin] using hy)

/-- First coordinate of the fixed-time model endpoint.  This is the chart-base
coordinate that will become the normal exponential endpoint in the construction
chart. -/
def timeBaseEndpoint
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (z : ModelPhase (E := E)) : E :=
  (varBaseFlow (E := E) Ψ z b).1

/-- Derivative of the fixed-time base-coordinate endpoint. -/
theorem timeBaseEndpoint_hasFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real} {A : ModelLin (E := E)}
    (hA :
      HasFDerivAt
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        A z) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp A)
      z := by
  have hfst :
      HasFDerivAt (fun w : ModelPhase (E := E) => w.1)
        (ContinuousLinearMap.fst Real E E) (varBaseFlow (E := E) Ψ z b) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [timeBaseEndpoint, Function.comp_def] using hfst.comp z hA

/-- Strict derivative of the first coordinate of the fixed-time model
endpoint. -/
theorem timeBaseEndpoint_hasStrictFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real} {A : ModelLin (E := E)}
    (hA :
      HasStrictFDerivAt
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        A z) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp A)
      z := by
  have hfst :
      HasStrictFDerivAt (fun w : ModelPhase (E := E) => w.1)
        (ContinuousLinearMap.fst Real E E) (varBaseFlow (E := E) Ψ z b) :=
    (ContinuousLinearMap.fst Real E E).hasStrictFDerivAt
  simpa [timeBaseEndpoint, Function.comp_def] using
    HasStrictFDerivAt.comp (x := z) hfst hA

/-- `C1` regularity of the first coordinate of the fixed-time model
endpoint. -/
theorem timeBaseEndpoint_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real}
    (hA :
      ContDiffAt Real 1
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        z) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      z := by
  simpa [timeBaseEndpoint, Function.comp_def] using hA.fst

/-- Source-controlled version of `timeBaseEndpoint_hasFDerivAt`. -/
theorem timeBaseEndpoint_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp (varDerivFlow (E := E) Ψ z b))
      z :=
  timeBaseEndpoint_hasFDerivAt (E := E)
    (timeEndpoint_hasFDerivAt (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Smooth dependence of the flat augmented variational flow on its augmented
initial condition, on an open neighborhood inside the controlled augmented
closed ball.

This is the robust self-map smooth-dependence frontier: the state space is the
plain Banach space `ModelPhase × ModelLin`, avoiding the dependent-pi
`ModelJetPrefix` coercion issue. -/
theorem varFlow_smoothOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ : (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
      ModelPhase (E := E) × ModelLin (E := E))
    {ε τ : Real} {a r : NNReal} {L' : NNReal}
    (_hr : 0 < r)
    {T_out T_mid T B : Real}
    (hτT : τ ∈ Set.Ioo (0 - T) (0 + T))
    (hT : 0 < T)
    (hT_lt_mid : T < T_mid)
    (hT_mid_lt_out : T_mid < T_out)
    (hB : 0 ≤ B)
    (hBT_mid : B * T_mid < 1)
    (hTsub : Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-ε) ε)
    {ρ_out ρ_mid ρ : NNReal} {r' : NNReal}
    (hr' : 0 < r')
    (hρpos : 0 < (ρ : Real))
    (hρ_lt_mid : (ρ : Real) < (ρ_mid : Real))
    (hρ_mid_lt_out : (ρ_mid : Real) < (ρ_out : Real))
    (hρρ' : (ρ_mid : Real) + (r' : Real) ≤ (r : Real))
    (hρ_out_le_r : (ρ_out : Real) ≤ (r : Real))
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hA_bd :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) (ρ_out : Real),
        ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
          ‖fderiv Real (varSpray (I := I) g x) (Ψ p t)‖ ≤ B) :
    ∃ W : Set (ModelPhase (E := E) × ModelLin (E := E)),
      IsOpen W ∧
        varPhaseZero (I := I) (E := E) x ∈ W ∧
        W ⊆ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r ∧
        ContDiffOn Real ∞ (fun p => Ψ p τ) W := by
  classical
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let Φ : VarPhase (E := E) × Real -> VarPhase (E := E) :=
    fun q => Ψ q.1 q.2
  let F : Real -> VarPhase (E := E) -> VarPhase (E := E) :=
    fun _ => varSpray (I := I) g x
  let W : Set (ModelPhase (E := E) × ModelLin (E := E)) :=
    Metric.ball p0 (ρ : Real)
  refine ⟨W, Metric.isOpen_ball, ?_, ?_, ?_⟩
  · exact Metric.mem_ball_self hρpos
  · intro p hp
    have hρ_le_r : (ρ : Real) ≤ (r : Real) :=
      le_trans (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hρ_out_le_r
    exact Metric.closedBall_subset_closedBall hρ_le_r (Metric.ball_subset_closedBall hp)
  · have hΦflow :
        RicciFlower.Analysis.ODE.Flow.IsLocalFlow
          F 0 p0 r (-ε) ε Φ := by
      have hT_out_pos : 0 < T_out := lt_trans (lt_trans hT hT_lt_mid) hT_mid_lt_out
      have hT_out_mem : T_out ∈ Set.Icc (0 - T_out) (0 + T_out) := by
        constructor <;> linarith
      have hεpos : 0 < ε := by
        have h := hTsub hT_out_mem
        linarith [h.2, hT_out_pos]
      have hcont :
          ContinuousOn Φ
            (Metric.closedBall p0 (r : Real) ×ˢ Set.Icc (-ε) ε) := by
        apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hLip
        intro p hp
        exact HasDerivWithinAt.continuousOn (hflow p hp).2
      refine
      { htmin_le := by linarith [hεpos],
        ht₀_le := by linarith [hεpos],
        apply_initial := ?_,
        hasDerivWithinAt := ?_,
        continuousOn := hcont,
        exists_lipschitz := ?_ }
      · intro p hp
        simpa [Φ, p0] using (hflow p hp).1
      · intro p hp t ht
        simpa [Φ, F] using (hflow p hp).2 t ht
      · exact ⟨L', by
          intro t ht
          simpa [Φ] using hLip t ht⟩
    let Ω : Set (Real × VarPhase (E := E)) :=
      Set.univ ×ˢ varSource (I := I) (E := E) x
    have hΩopen : IsOpen Ω := by
      simpa [Ω] using isOpen_univ.prod (isOpen_varSource (I := I) (E := E) x)
    have hΩsmooth :
        ContDiffOn Real ∞ (Function.uncurry F) Ω := by
      simpa [F, Ω, Function.uncurry] using
        varSpray_time_cdOn (I := I) g x
    have hΩflow :
        ∀ p ∈ Metric.closedBall p0 (r : Real), ∀ t ∈ Set.Icc (-ε) ε,
          (t, Φ (p, t)) ∈ Ω := by
      intro p hp t _ht
      have hpsrc : Ψ p t ∈ varSource (I := I) (E := E) x := by
        simpa [varSource] using hsrc (hbound p hp t)
      exact ⟨Set.mem_univ _, by simpa [Φ] using hpsrc⟩
    have hA_bd' :
        ∀ p ∈ Metric.closedBall p0 (ρ_out : Real),
          ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
            ‖fderiv Real (F t) (Φ (p, t))‖ ≤ B := by
      intro p hp t ht
      simpa [F, Φ] using hA_bd p hp t ht
    have hjoint :
        ContDiffOn Real ∞ Φ
          (Metric.ball p0 ρ ×ˢ Set.Ioo (0 - T) (0 + T)) :=
      RicciFlower.Analysis.ODE.Flow.IsLocalFlow.contDiffOn_top_local
        (f := F) (t₀ := 0) (x₀ := p0) (r := r)
        (tmin := -ε) (tmax := ε) (Φ := Φ)
        hΦflow hΩopen hΩsmooth hΩflow hT hT_lt_mid hT_mid_lt_out
        hB hBT_mid hTsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd'
    have hconst :
        ContDiffOn Real ∞ (fun p : VarPhase (E := E) => (p, τ))
          W := by
      exact contDiff_id.contDiffOn.prodMk contDiff_const.contDiffOn
    have hfixed :
        ContDiffOn Real ∞ (fun p : VarPhase (E := E) => Φ (p, τ)) W :=
      hjoint.comp hconst (by
        intro p hp
        exact ⟨by simpa [W, p0] using hp, hτT⟩)
    simpa [Φ] using hfixed

/-- Smooth dependence of the fixed-time base endpoint on the initial model
phase, on an open neighborhood inside the controlled phase ball.

This is now a consumer of the flat augmented-flow smoothness frontier
`varFlow_smoothOn`. -/
theorem timeBaseEnd_smoothOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ : (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
      ModelPhase (E := E) × ModelLin (E := E))
    {ε τ : Real} {a r : NNReal} {L' : NNReal}
    (hr : 0 < r)
    {T_out T_mid T B : Real}
    (hτT : τ ∈ Set.Ioo (0 - T) (0 + T))
    (hT : 0 < T)
    (hT_lt_mid : T < T_mid)
    (hT_mid_lt_out : T_mid < T_out)
    (hB : 0 ≤ B)
    (hBT_mid : B * T_mid < 1)
    (hTsub : Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-ε) ε)
    {ρ_out ρ_mid ρVar : NNReal} {r' : NNReal}
    (hr' : 0 < r')
    (hρVar_pos : 0 < (ρVar : Real))
    (hρ_lt_mid : (ρVar : Real) < (ρ_mid : Real))
    (hρ_mid_lt_out : (ρ_mid : Real) < (ρ_out : Real))
    (hρρ' : (ρ_mid : Real) + (r' : Real) ≤ (r : Real))
    (hρ_out_le_r : (ρ_out : Real) ≤ (r : Real))
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hA_bd :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) (ρ_out : Real),
        ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
          ‖fderiv Real (varSpray (I := I) g x) (Ψ p t)‖ ≤ B) :
    ∃ w : Set (ModelPhase (E := E)),
      IsOpen w ∧
        initPhase (I := I) x (0 : TangentSpace I x) ∈ w ∧
        w ⊆ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r ∧
        ContDiffOn Real ∞ (fun z => timeBaseEndpoint (E := E) Ψ τ z) w := by
  classical
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  let c : ModelPhase (E := E) :=
    extChartAt I.tangent (phaseZero (I := I) x) (phaseZero (I := I) x)
  let ι : ModelPhase (E := E) -> ModelPhase (E := E) × ModelLin (E := E) :=
    fun z => (z, idLin)
  obtain ⟨W, hWopen, hWzero, _hWsub, hWsmooth⟩ :=
    varFlow_smoothOn (I := I) g x Ψ (ε := ε) (τ := τ)
      (a := a) (r := r) (L' := L') hr hτT hT hT_lt_mid hT_mid_lt_out
      hB hBT_mid hTsub hr' hρVar_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r
      hflow hbound hsrc hLip hA_bd
  let w : Set (ModelPhase (E := E)) :=
    ι ⁻¹' W ∩ Metric.ball (c : ModelPhase (E := E)) (r : Real)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have hιcont : Continuous ι :=
      continuous_id.prodMk continuous_const
    exact (hWopen.preimage hιcont).inter Metric.isOpen_ball
  · have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
    have hball :
        (c : ModelPhase (E := E)) ∈
          Metric.ball (c : ModelPhase (E := E)) (r : Real) :=
      Metric.mem_ball_self hrReal
    exact ⟨by simpa [ι, idLin, c, initPhase_zero, varPhaseZero] using hWzero,
      by simpa [c, initPhase_zero] using hball⟩
  · intro z hz
    exact Metric.ball_subset_closedBall hz.2
  · have hιsmooth : ContDiff Real ∞ ι :=
      contDiff_id.prodMk contDiff_const
    have hcomp :
        ContDiffOn Real ∞ (fun z : ModelPhase (E := E) => Ψ (ι z) τ) w :=
      hWsmooth.comp hιsmooth.contDiffOn (by intro z hz; exact hz.1)
    simpa [timeBaseEndpoint, varBaseFlow, ι, idLin] using hcomp.fst.fst

/-- Source-controlled strict derivative of the fixed-time base-coordinate
endpoint. -/
theorem timeBaseEndpoint_hasStrictFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp (varDerivFlow (E := E) Ψ z b))
      z :=
  timeBaseEndpoint_hasStrictFDerivAt (E := E)
    (timeEndpoint_hasStrictFDerivAt (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Source-controlled `C1` regularity of the fixed-time base-coordinate
endpoint. -/
theorem timeBaseEndpoint_contDiffAt_one_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      z :=
  timeBaseEndpoint_contDiffAt_one (E := E)
    (timeEndpoint_contDiffAt_one (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Pull back the base-coordinate endpoint derivative along the initial-phase
map `v ↦ initPhase x v`. -/
theorem timeBaseEndpoint_initPhase_hasFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    {A : ModelPhase (E := E) →L[Real] E}
    (hA :
      HasFDerivAt
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        A
        (initPhase (I := I) x v)) :
    HasFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (A.comp (initPhaseLin (I := I) x))
      v :=
  hA.comp v (initPhase_hasFDerivAt (I := I) x v)

/-- Pull back the strict base-coordinate endpoint derivative along the
initial-phase map `v ↦ initPhase x v`. -/
theorem timeBaseEndpoint_initPhase_hasStrictFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    {A : ModelPhase (E := E) →L[Real] E}
    (hA :
      HasStrictFDerivAt
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        A
        (initPhase (I := I) x v)) :
    HasStrictFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (A.comp (initPhaseLin (I := I) x))
      v :=
  HasStrictFDerivAt.comp (x := v) hA
    (initPhase_hasStrictFDerivAt (I := I) x v)

/-- Pull back `C1` regularity of the base-coordinate endpoint along the
initial-phase map. -/
theorem timeBaseEndpoint_initPhase_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    (hA :
      ContDiffAt Real 1
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        (initPhase (I := I) x v)) :
    ContDiffAt Real 1
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      v := by
  exact hA.comp v (initPhase_contDiffAt (I := I) (n := (1 : WithTop ℕ∞)) x v)

/-- Base-coordinate endpoint after the homogeneous time rescaling
`v ↦ b⁻¹ • v`.  This is the local chart expression of the exponential endpoint
when a short time `b` is used to reach time one by rescaling the initial
velocity. -/
def scaledBaseEnd
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (x : M) (v : TangentSpace I x) : E :=
  timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x (b⁻¹ • v))

/-- Source-controlled version of the velocity-space base endpoint derivative. -/
theorem timeBaseEndpoint_initPhase_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (v : TangentSpace I x)
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hvopen :
      (initPhase (I := I) x v,
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (((ContinuousLinearMap.fst Real E E).comp
        (varDerivFlow (E := E) Ψ (initPhase (I := I) x v) b)).comp
          (initPhaseLin (I := I) x))
      v :=
  timeBaseEndpoint_initPhase_hasFDerivAt (E := E)
      (timeBaseEndpoint_hasFDerivAt_of_flow (I := I) g x Ψ
      (initPhase (I := I) x v) hb0 hb hflow hbound hsrc hLip hvopen)

/-- Source-controlled strict version of the velocity-space base endpoint
derivative. -/
theorem timeBaseEndpoint_initPhase_hasStrictFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (v : TangentSpace I x)
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hvopen :
      (initPhase (I := I) x v,
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (((ContinuousLinearMap.fst Real E E).comp
        (varDerivFlow (E := E) Ψ (initPhase (I := I) x v) b)).comp
          (initPhaseLin (I := I) x))
      v :=
  timeBaseEndpoint_initPhase_hasStrictFDerivAt (E := E)
      (timeBaseEndpoint_hasStrictFDerivAt_of_flow (I := I) g x Ψ
      (initPhase (I := I) x v) hb0 hb hflow hbound hsrc hLip hvopen)

/-- If the unscaled short-time endpoint has derivative `b • id`, then the
homogeneously rescaled endpoint has derivative `id`. -/
theorem scaledBaseEnd_deriv0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (hb : b ≠ 0)
    (h :
      HasFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasFDerivAt
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  have hscale :
      HasFDerivAt
        (fun v : TangentSpace I x => b⁻¹ • v)
        (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x))
        0 := by
    simpa using
      ((ContinuousLinearMap.id Real (TangentSpace I x)).hasFDerivAt.const_smul b⁻¹)
  have h_at :
      HasFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  have hcomp := h_at.comp (0 : TangentSpace I x) hscale
  have hlin :
      (b • ContinuousLinearMap.id Real (TangentSpace I x)).comp
          (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x)) =
        ContinuousLinearMap.id Real (TangentSpace I x) := by
    ext v
    change b • (b⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
  convert hcomp using 1
  exact hlin.symm

/-- Strict version of `scaledBaseEnd_deriv0`. -/
theorem scaledBaseEnd_strict0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (hb : b ≠ 0)
    (h :
      HasStrictFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasStrictFDerivAt
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  have hscale :
      HasStrictFDerivAt
        (fun v : TangentSpace I x => b⁻¹ • v)
        (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x))
        0 := by
    simpa using
      ((ContinuousLinearMap.id Real (TangentSpace I x)).hasStrictFDerivAt.const_smul b⁻¹)
  have h_at :
      HasStrictFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  have hcomp := HasStrictFDerivAt.comp (x := (0 : TangentSpace I x)) h_at hscale
  have hlin :
      (b • ContinuousLinearMap.id Real (TangentSpace I x)).comp
          (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x)) =
        ContinuousLinearMap.id Real (TangentSpace I x) := by
    ext v
    change b • (b⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
  convert hcomp using 1
  exact hlin.symm

/-- `C1` regularity of the rescaled base endpoint at zero. -/
theorem scaledBaseEnd_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      ContDiffAt Real 1
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        0) :
    ContDiffAt Real 1
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      0 := by
  have hscale :
      ContDiffAt Real 1
        (fun v : TangentSpace I x => b⁻¹ • v)
        (0 : TangentSpace I x) := by
    simpa using
      ((contDiff_const_smul (𝕜 := Real)
        (n := (1 : WithTop ℕ∞)) (F := TangentSpace I x) b⁻¹).contDiffAt :
          ContDiffAt Real 1 (fun v : TangentSpace I x => b⁻¹ • v) 0)
  have h_at :
      ContDiffAt Real 1
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  simpa [scaledBaseEnd] using h_at.comp (0 : TangentSpace I x) hscale

/-- The rescaled base endpoint is exactly the existing `chartEnd` for the
model flow projected from the augmented variational flow. -/
theorem chartEnd_varModelFlow_eq_scaledBaseEnd
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (x : M) :
    chartEnd (I := I) (varModelFlow (E := E) Ψ) b x =
      scaledBaseEnd (I := I) (E := E) Ψ b x := by
  rfl

/-- Derivative of `chartEnd` for the model flow projected from an augmented
variational flow. -/
theorem chartEnd_varModelFlow_deriv0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      HasFDerivAt
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        (ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasFDerivAt
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- Strict derivative of `chartEnd` for the model flow projected from an
augmented variational flow. -/
theorem chartEnd_varModelFlow_strict0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      HasStrictFDerivAt
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        (ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasStrictFDerivAt
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- `C1` regularity of `chartEnd` for the model flow projected from an
augmented variational flow. -/
theorem chartEnd_varModelFlow_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      ContDiffAt Real 1
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        0) :
    ContDiffAt Real 1
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- Local augmented variational flow whose base component has the variational
component as Frechet derivative at every interior initial phase, for forward
times in the Picard interval. -/
theorem varFlow_hasFDerivAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Icc (0 : Real) ε,
              ∀ z : ModelPhase (E := E),
                (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
                  Metric.ball (varPhaseZero (I := I) (E := E) x) r ->
                HasFDerivAt
                  (fun z' : ModelPhase (E := E) =>
                    varBaseFlow (E := E) Ψ z' b)
                  (varDerivFlow (E := E) Ψ z b)
                  z := by
  obtain ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip⟩ :=
    varFlow_src_bound (I := I) g x
  refine ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip, ?_⟩
  intro b hb z hzopen
  have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor
    · linarith [hε, ht.1]
    · exact le_trans ht.2 hb.2
  exact
    varBaseFlow_hasFDerivAt_of_flow (I := I) g x Ψ z
      hb.1 hbsub hflow hbound hsrc_ball hLip hzopen

/-- Short-time augmented variational flow whose base-coordinate endpoint has
the expected zero-velocity derivative in the initial tangent vector. -/
theorem varFlow_deriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            Ψ (varPhaseZero (I := I) (E := E) x) t =
              varZeroPhaseLin (I := I) (E := E) x t) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Icc (0 : Real) δ,
              HasFDerivAt
                (fun v : TangentSpace I x =>
                  timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
                (b • ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    varSpray_pl0_src (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) hpl
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  obtain ⟨δ0, hδ0, hcand0⟩ :=
    varZeroPhaseLin_mem_closedBall_small (I := I) (E := E) x (a := a) ha
  let δ : Real := min δ0 ε
  have hδ : 0 < δ := lt_min hδ0 hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hcand :
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
    intro t ht
    exact hcand0 t ⟨by linarith [ht.1, hδδ0], by linarith [ht.2, hδδ0]⟩
  have hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t := by
    intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by simpa using ht
    simpa using (hΨ p hp).2 t ht'
  have hLip' :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by simpa using ht
    simpa using hLip t ht'
  have hzeroEq :
      ∀ t ∈ Set.Icc (-δ) δ,
        Ψ (varPhaseZero (I := I) (E := E) x) t =
          varZeroPhaseLin (I := I) (E := E) x t :=
    varFlow_zero_phaseLin_of_pl (I := I) g x hε hδ hδε hpl
      hflow hbound hcand
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzeroEq, L', hLip', ?_⟩
  intro b hb
  have hbε : b ∈ Set.Icc (0 : Real) ε := ⟨hb.1, le_trans hb.2 hδε⟩
  have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor
    · linarith [hε, ht.1]
    · exact le_trans ht.2 hbε.2
  have hinit :
      (initPhase (I := I) x (0 : TangentSpace I x),
          ContinuousLinearMap.id Real (ModelPhase (E := E))) =
        varPhaseZero (I := I) (E := E) x := by
    simp [varPhaseZero, initPhase_zero]
  have hvopen :
      (initPhase (I := I) x (0 : TangentSpace I x),
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
    rw [hinit]
    exact Metric.mem_ball_self hrR
  have hderiv :=
    timeBaseEndpoint_initPhase_hasFDerivAt_of_flow (I := I) g x Ψ
      (0 : TangentSpace I x) hb.1 hbsub hflow hbound hsrc hLip' hvopen
  have hbδ : b ∈ Set.Icc (-δ) δ := ⟨by linarith [hb.1], hb.2⟩
  have hA :
      varDerivFlow (E := E) Ψ (initPhase (I := I) x (0 : TangentSpace I x)) b =
        phaseLinFlow (E := E) b := by
    have hΨeq :
        Ψ (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) b =
          varZeroPhaseLin (I := I) (E := E) x b := by
      simpa [hinit] using hzeroEq b hbδ
    simpa [varDerivFlow, varZeroPhaseLin] using congrArg Prod.snd hΨeq
  have hclm :
      (((ContinuousLinearMap.fst Real E E).comp
          (varDerivFlow (E := E) Ψ
            (initPhase (I := I) x (0 : TangentSpace I x)) b)).comp
          (initPhaseLin (I := I) x)) =
        b • ContinuousLinearMap.id Real (TangentSpace I x) := by
    rw [hA]
    ext v
    simp [initPhaseLin, phaseLinFlow, modelSprayLin]
    rfl
  rw [hclm] at hderiv
  exact hderiv

/-- Short-time augmented variational flow whose homogeneously rescaled
base-coordinate endpoint has derivative `id` at the zero initial tangent
vector. -/
theorem varFlow_scaledDeriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            Ψ (varPhaseZero (I := I) (E := E) x) t =
              varZeroPhaseLin (I := I) (E := E) x t) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (scaledBaseEnd (I := I) (E := E) Ψ b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, hderiv⟩ :=
    varFlow_deriv0 (I := I) g x
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, ?_⟩
  intro b hb
  exact scaledBaseEnd_deriv0 (I := I) (E := E) (Ψ := Ψ) (x := x)
    (b := b) (ne_of_gt hb.1) (hderiv b ⟨le_of_lt hb.1, hb.2⟩)

/-- Endpoint-facing package for the model flow projected from the augmented
variational flow: it solves the original model spray ODE, has fixed-chart
source control, and its rescaled `chartEnd` has derivative `id` at zero. -/
theorem varFlow_chartEndDeriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, hderiv⟩ :=
    varFlow_scaledDeriv0 (I := I) g x
  have hmodelZero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have h := hzero t ht
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, r, hr, Ψ, ?_, ?_, hmodelZero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
      (x := x) (b := b) (hderiv b hb)

/-- Flow-retaining endpoint package for the projected augmented flow.

Compared with `varFlow_chartEndDeriv0`, this keeps the projected closed-ball
bound for `varModelFlow`.  That control is needed by the homogeneous scaling
lemmas used to build radial exponential geodesic germs. -/
theorem varFlow_modelData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t : Real,
              varModelFlow (E := E) Ψ z t ∈
                Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) a) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip,
      hderiv⟩ :=
    varFlow_scaledDeriv0 (I := I) g x
  have hmodelZero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have h := hzero t ht
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, ?_, ?_, ?_, hmodelZero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_bound (I := I) (E := E) x hbound
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
      (x := x) (b := b) (hderiv b hb)

/-- Endpoint-facing package for the projected augmented flow with both `C1`
regularity and derivative `id` at the zero initial tangent vector. -/
theorem varFlow_chartEndC1
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              ContDiffAt Real 1
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                0 ∧
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ0, hδ0, a, r, hr, Ψ, hflow, hbound, hsrc, hzero0, L', hLip, hderiv⟩ :=
    varFlow_deriv0 (I := I) g x
  let δ : Real := min δ0 ε
  have hδ : 0 < δ := lt_min hδ0 hε
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  have hzero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have ht0 : t ∈ Set.Icc (-δ0) δ0 := by
      constructor <;> linarith [ht.1, ht.2, hδδ0]
    have h := hzero0 t ht0
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, r, hr, Ψ, ?_, ?_, hzero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    have hbIcc : b ∈ Set.Icc (0 : Real) δ0 :=
      ⟨le_of_lt hb.1, le_trans hb.2 hδδ0⟩
    have hbε : b ≤ ε := le_trans hb.2 hδε
    have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
      intro t ht
      constructor
      · linarith [hε, ht.1]
      · exact le_trans ht.2 hbε
    have hinit :
        (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) =
          varPhaseZero (I := I) (E := E) x := by
      simp [varPhaseZero, initPhase_zero]
    have hvopen :
        (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
          Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
      rw [hinit]
      have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
      exact Metric.mem_ball_self hrR
    have hbaseC1 :
        ContDiffAt Real 1
          (fun z' : ModelPhase (E := E) =>
            timeBaseEndpoint (E := E) Ψ b z')
          (initPhase (I := I) x (0 : TangentSpace I x)) :=
      timeBaseEndpoint_contDiffAt_one_of_flow (I := I) g x Ψ
        (initPhase (I := I) x (0 : TangentSpace I x))
        (le_of_lt hb.1) hbsub hflow hbound hsrc hLip hvopen
    have hpull :
        ContDiffAt Real 1
          (fun v : TangentSpace I x =>
            timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
          0 :=
      timeBaseEndpoint_initPhase_contDiffAt_one (E := E) hbaseC1
    refine ⟨?_, ?_⟩
    · exact chartEnd_varModelFlow_contDiffAt_one (I := I) (E := E)
        (Ψ := Ψ) (x := x) (b := b)
        (scaledBaseEnd_contDiffAt_one (I := I) (E := E) (Ψ := Ψ)
          (x := x) (b := b) hpull)
    · exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
        (x := x) (b := b)
        (scaledBaseEnd_deriv0 (I := I) (E := E) (Ψ := Ψ) (x := x)
          (b := b) (ne_of_gt hb.1) (hderiv b hbIcc))

end Coordinates
end RicciFlower
