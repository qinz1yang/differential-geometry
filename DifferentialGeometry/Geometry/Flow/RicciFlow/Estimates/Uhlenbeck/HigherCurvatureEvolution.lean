import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.HeatCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Components
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.MultiNormHeat

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

abbrev SlotArray (Idx : Type*) := (ℕ → Idx) → Real

abbrev ContractionMap (Idx : Type*) :=
  SlotArray Idx → SlotArray Idx → SlotArray Idx

variable {Idx : Type*}

def consSlot (a : Idx) (s : ℕ → Idx) : ℕ → Idx
  | 0 => a
  | (n + 1) => s n

def tailSlot (s : ℕ → Idx) : ℕ → Idx := fun n => s (n + 1)

@[simp] theorem consSlot_zero (a : Idx) (s : ℕ → Idx) : consSlot a s 0 = a := rfl

@[simp] theorem consSlot_succ (a : Idx) (s : ℕ → Idx) (n : ℕ) :
    consSlot a s (n + 1) = s n := rfl

@[simp] theorem tailSlot_apply (s : ℕ → Idx) (n : ℕ) : tailSlot s n = s (n + 1) := rfl

def slotIndexArray (a b c d : Idx) : ℕ → Idx
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def slotArrayOfComponents {r : ℕ} (X : (Fin r → Idx) → Real) : SlotArray Idx :=
  fun s => X (fun t => s (t : ℕ))

def componentSlotSeq {k : ℕ} (m : Fin (4 + k) → Idx) : ℕ → Idx :=
  fun n => if h : n < 4 + k then m ⟨n, h⟩ else m ⟨0, by omega⟩

theorem slotArrayOfComponents_componentSlotSeq {k : ℕ}
    (X : (Fin (4 + k) → Idx) → Real) (m : Fin (4 + k) → Idx) :
    slotArrayOfComponents X (componentSlotSeq m) = X m := by
  unfold slotArrayOfComponents componentSlotSeq
  congr 1
  funext t
  rw [dif_pos t.isLt, Fin.eta]

def firstSlotDerivativeLift (B : ContractionMap Idx) : ContractionMap Idx :=
  fun X Y s => B (fun m => X (consSlot (s 0) m)) Y (tailSlot s)

def secondSlotDerivativeLift (B : ContractionMap Idx) : ContractionMap Idx :=
  fun X Y s => B X (fun m => Y (consSlot (s 0) m)) (tailSlot s)

def curvatureSlotContraction [Fintype Idx] (q : ℕ) : ContractionMap Idx :=
  fun P Z s =>
    2 * ∑ r : Fin q, ∑ e : Idx, ∑ d : Idx,
      P (slotIndexArray (s 0) e d (s ((r : ℕ) + 1))) *
        Z (consSlot e (Function.update (tailSlot s) (r : ℕ) d))

theorem curvatureSlotContraction_eq_curvatureSlotActionContraction
    [Fintype Idx] {q : ℕ}
    (R : Idx → Idx → Idx → Idx → Real)
    (DA : Idx → (Fin q → Idx) → Real)
    (P Z : SlotArray Idx)
    (hP : ∀ σ : ℕ → Idx, P σ = R (σ 0) (σ 1) (σ 2) (σ 3))
    (hZ : ∀ σ : ℕ → Idx, Z σ = DA (σ 0) (fun t : Fin q => σ ((t : ℕ) + 1)))
    (s : ℕ → Idx) :
    curvatureSlotContraction q P Z s =
      curvatureSlotActionContraction R DA (s 0) (fun t : Fin q => s ((t : ℕ) + 1)) := by
  classical
  unfold curvatureSlotContraction curvatureSlotActionContraction
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hP, hZ]
  have hslots :
      (fun t : Fin q =>
          consSlot e (Function.update (tailSlot s) (r : ℕ) d) ((t : ℕ) + 1)) =
        Function.update (fun t : Fin q => s ((t : ℕ) + 1)) r d := by
    funext t
    by_cases htr : t = r
    · subst htr
      simp
    · have hval : (t : ℕ) ≠ (r : ℕ) := fun h => htr (Fin.ext h)
      simp [htr, hval]
  rw [hslots]
  rfl

def curvatureSquarePair [Fintype Idx]
    (P S : SlotArray Idx) (a b c d : Idx) : Real :=
  (1 / 2 : Real) * ∑ e : Idx, ∑ f : Idx,
    (P (slotIndexArray a e b f) * S (slotIndexArray c e d f) +
      S (slotIndexArray a e b f) * P (slotIndexArray c e d f))

def curvatureReactionPair [Fintype Idx] : ContractionMap Idx :=
  fun P S s =>
    2 * (curvatureSquarePair P S (s 0) (s 1) (s 2) (s 3) -
        curvatureSquarePair P S (s 0) (s 1) (s 3) (s 2) +
        curvatureSquarePair P S (s 0) (s 2) (s 1) (s 3) -
        curvatureSquarePair P S (s 0) (s 3) (s 1) (s 2))

theorem curvatureSquarePair_self_eq_bTensorDown [Fintype Idx]
    (R : Idx → Idx → Idx → Idx → Real) (P : SlotArray Idx)
    (hP : ∀ σ : ℕ → Idx, P σ = R (σ 0) (σ 1) (σ 2) (σ 3))
    (a b c d : Idx) :
    curvatureSquarePair P P a b c d = bTensorDown R a b c d := by
  unfold curvatureSquarePair bTensorDown
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hP, hP]
  simp only [slotIndexArray]
  ring

theorem curvatureReactionPair_self_eq [Fintype Idx]
    (R : Idx → Idx → Idx → Idx → Real) (P : SlotArray Idx)
    (hP : ∀ σ : ℕ → Idx, P σ = R (σ 0) (σ 1) (σ 2) (σ 3))
    (s : ℕ → Idx) :
    curvatureReactionPair P P s =
      2 * (bTensorDown R (s 0) (s 1) (s 2) (s 3) -
          bTensorDown R (s 0) (s 1) (s 3) (s 2) +
          bTensorDown R (s 0) (s 2) (s 1) (s 3) -
          bTensorDown R (s 0) (s 3) (s 1) (s 2)) := by
  unfold curvatureReactionPair
  rw [curvatureSquarePair_self_eq_bTensorDown R P hP,
    curvatureSquarePair_self_eq_bTensorDown R P hP,
    curvatureSquarePair_self_eq_bTensorDown R P hP,
    curvatureSquarePair_self_eq_bTensorDown R P hP]

def recursiveCurvatureContraction [Fintype Idx] (Q : ContractionMap Idx) :
    ℕ → ℕ → ContractionMap Idx
  | 0, 0 => Q
  | (i + 1), 0 => firstSlotDerivativeLift (recursiveCurvatureContraction Q i 0)
  | 0, (j + 1) =>
      fun X Y s =>
        secondSlotDerivativeLift (recursiveCurvatureContraction Q 0 j) X Y s +
          curvatureSlotContraction (4 + j) X Y s
  | (i + 1), (j + 1) =>
      fun X Y s =>
        firstSlotDerivativeLift (recursiveCurvatureContraction Q i (j + 1)) X Y s +
          secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) j) X Y s
  termination_by i j => i + j

theorem recursiveCurvatureContraction_zero_zero [Fintype Idx]
    (Q : ContractionMap Idx) :
    recursiveCurvatureContraction Q 0 0 = Q := by
  simp [recursiveCurvatureContraction]

theorem recursiveCurvatureContraction_succ_zero [Fintype Idx]
    (Q : ContractionMap Idx) (i : ℕ) :
    recursiveCurvatureContraction Q (i + 1) 0 =
      firstSlotDerivativeLift (recursiveCurvatureContraction Q i 0) := by
  simp [recursiveCurvatureContraction]

theorem recursiveCurvatureContraction_zero_succ [Fintype Idx]
    (Q : ContractionMap Idx) (j : ℕ) (X Y : SlotArray Idx) (s : ℕ → Idx) :
    recursiveCurvatureContraction Q 0 (j + 1) X Y s =
      secondSlotDerivativeLift (recursiveCurvatureContraction Q 0 j) X Y s +
        curvatureSlotContraction (4 + j) X Y s := by
  simp [recursiveCurvatureContraction]

theorem recursiveCurvatureContraction_succ_succ [Fintype Idx]
    (Q : ContractionMap Idx) (i j : ℕ) (X Y : SlotArray Idx) (s : ℕ → Idx) :
    recursiveCurvatureContraction Q (i + 1) (j + 1) X Y s =
      firstSlotDerivativeLift (recursiveCurvatureContraction Q i (j + 1)) X Y s +
        secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) j) X Y s := by
  simp [recursiveCurvatureContraction]

theorem recursiveCurvatureContraction_succ_left [Fintype Idx]
    (Q : ContractionMap Idx) (i j : ℕ) (X Y : SlotArray Idx) (s : ℕ → Idx) :
    recursiveCurvatureContraction Q (i + 1) j X Y s =
      firstSlotDerivativeLift (recursiveCurvatureContraction Q i j) X Y s +
        (if j = 0 then 0 else
          secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (j - 1)) X Y s) := by
  cases j with
  | zero => rw [recursiveCurvatureContraction_succ_zero]; simp
  | succ j => rw [recursiveCurvatureContraction_succ_succ]; simp

theorem sum_recursiveCurvatureContraction_succ [Fintype Idx]
    (Q : ContractionMap Idx) (A : ℕ → SlotArray Idx) (k : ℕ) (s : ℕ → Idx) :
    (∑ i ∈ Finset.range (k + 1 + 1),
        recursiveCurvatureContraction Q i (k + 1 - i) (A i) (A (k + 1 - i)) s) =
      (∑ i ∈ Finset.range (k + 1),
          (firstSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
              (A (i + 1)) (A (k - i)) s +
            secondSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
              (A i) (A (k - i + 1)) s)) +
        curvatureSlotContraction (4 + k) (A 0) (A (k + 1)) s := by
  classical
  rw [Finset.sum_range_succ' (fun i =>
    recursiveCurvatureContraction Q i (k + 1 - i) (A i) (A (k + 1 - i)) s) (k + 1)]
  have hstep : ∀ i ∈ Finset.range (k + 1),
      recursiveCurvatureContraction Q (i + 1) (k + 1 - (i + 1))
          (A (i + 1)) (A (k + 1 - (i + 1))) s =
        firstSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
            (A (i + 1)) (A (k - i)) s +
          (if k - i = 0 then (0 : Real) else
            secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (k - i - 1))
              (A (i + 1)) (A (k - i)) s) := by
    intro i _
    have hsub : k + 1 - (i + 1) = k - i := by omega
    rw [hsub]
    exact recursiveCurvatureContraction_succ_left Q i (k - i) (A (i + 1)) (A (k - i)) s
  have hzeroterm :
      recursiveCurvatureContraction Q 0 (k + 1 - 0) (A 0) (A (k + 1 - 0)) s =
        secondSlotDerivativeLift (recursiveCurvatureContraction Q 0 k) (A 0) (A (k + 1)) s +
          curvatureSlotContraction (4 + k) (A 0) (A (k + 1)) s := by
    have hsub : k + 1 - 0 = k + 1 := by omega
    rw [hsub]
    exact recursiveCurvatureContraction_zero_succ Q k (A 0) (A (k + 1)) s
  rw [Finset.sum_congr rfl hstep, hzeroterm, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hsecond :
      (∑ i ∈ Finset.range (k + 1),
          (if k - i = 0 then (0 : Real) else
            secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (k - i - 1))
              (A (i + 1)) (A (k - i)) s)) +
        secondSlotDerivativeLift (recursiveCurvatureContraction Q 0 k) (A 0) (A (k + 1)) s =
      ∑ i ∈ Finset.range (k + 1),
        secondSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
          (A i) (A (k - i + 1)) s := by
    rw [Finset.sum_range_succ' (fun i =>
      secondSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
        (A i) (A (k - i + 1)) s) k]
    rw [Finset.sum_range_succ (fun i =>
      (if k - i = 0 then (0 : Real) else
        secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (k - i - 1))
          (A (i + 1)) (A (k - i)) s)) k]
    have hlast : k - k = 0 := by omega
    rw [if_pos hlast]
    have hterm : ∀ i ∈ Finset.range k,
        (if k - i = 0 then (0 : Real) else
          secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (k - i - 1))
            (A (i + 1)) (A (k - i)) s) =
          secondSlotDerivativeLift (recursiveCurvatureContraction Q (i + 1) (k - (i + 1)))
            (A (i + 1)) (A (k - (i + 1) + 1)) s := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h1 : k - i ≠ 0 := by omega
      have h2 : k - i - 1 = k - (i + 1) := by omega
      have h3 : k - i = k - (i + 1) + 1 := by omega
      rw [if_neg h1, h2, h3]
    rw [Finset.sum_congr rfl hterm]
    have h4 : k - 0 = k := by omega
    rw [h4]
    ring
  linarith [hsecond]

theorem der_sum_range (der : SlotArray Idx → SlotArray Idx → Prop)
    (hzero : der (fun _ => 0) (fun _ => 0))
    (hadd : ∀ X X' Y Y' : SlotArray Idx, der X X' → der Y Y' →
      der (fun s => X s + Y s) (fun s => X' s + Y' s))
    (f g : ℕ → SlotArray Idx) (h : ∀ i : ℕ, der (f i) (g i)) (n : ℕ) :
    der (fun s => ∑ i ∈ Finset.range n, f i s)
      (fun s => ∑ i ∈ Finset.range n, g i s) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hf : (fun s => ∑ i ∈ Finset.range (n + 1), f i s) =
          (fun s : ℕ → Idx => (∑ i ∈ Finset.range n, f i s) + f n s) := by
        funext s
        exact Finset.sum_range_succ (fun i => f i s) n
      have hg : (fun s => ∑ i ∈ Finset.range (n + 1), g i s) =
          (fun s : ℕ → Idx => (∑ i ∈ Finset.range n, g i s) + g n s) := by
        funext s
        exact Finset.sum_range_succ (fun i => g i s) n
      rw [hf, hg]
      exact hadd _ _ _ _ ih (h n)

theorem uhlenbeck_higher_curvature_evolution_of_commutator [Fintype Idx]
    (Q : ContractionMap Idx) (A LA DLA : ℕ → SlotArray Idx)
    (der : SlotArray Idx → SlotArray Idx → Prop)
    (hzero : der (fun _ => 0) (fun _ => 0))
    (hadd : ∀ X X' Y Y' : SlotArray Idx, der X X' → der Y Y' →
      der (fun s => X s + Y s) (fun s => X' s + Y' s))
    (huniq : ∀ X Y Z : SlotArray Idx, der X Y → der X Z → Y = Z)
    (hleibniz : ∀ (i j : ℕ) (X X' Y Y' : SlotArray Idx), der X X' → der Y Y' →
      der (recursiveCurvatureContraction Q i j X Y)
        (fun s =>
          firstSlotDerivativeLift (recursiveCurvatureContraction Q i j) X' Y s +
            secondSlotDerivativeLift (recursiveCurvatureContraction Q i j) X Y' s))
    (hderA : ∀ i : ℕ, der (A i) (A (i + 1)))
    (hderLA : ∀ i : ℕ, der (LA i) (DLA i))
    (hbase : ∀ s : ℕ → Idx, LA 0 s = Q (A 0) (A 0) s)
    (hcomm : ∀ (i : ℕ) (s : ℕ → Idx),
      LA (i + 1) s = DLA i s + curvatureSlotContraction (4 + i) (A 0) (A (i + 1)) s)
    (k : ℕ) :
    LA k = fun s => ∑ i ∈ Finset.range (k + 1),
      recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) s := by
  classical
  induction k with
  | zero =>
      funext s
      rw [hbase s]
      rw [Finset.sum_range_one]
      have h0 : (0 : ℕ) - 0 = 0 := by omega
      rw [h0, recursiveCurvatureContraction_zero_zero]
  | succ k ih =>
      have hder1 :
          der (fun s => ∑ i ∈ Finset.range (k + 1),
              recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) s)
            (fun s => ∑ i ∈ Finset.range (k + 1),
              (firstSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
                  (A (i + 1)) (A (k - i)) s +
                secondSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
                  (A i) (A (k - i + 1)) s)) :=
        der_sum_range der hzero hadd
          (fun i => recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)))
          (fun i s =>
            firstSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
                (A (i + 1)) (A (k - i)) s +
              secondSlotDerivativeLift (recursiveCurvatureContraction Q i (k - i))
                (A i) (A (k - i + 1)) s)
          (fun i => hleibniz i (k - i) (A i) (A (i + 1)) (A (k - i)) (A (k - i + 1))
            (hderA i) (hderA (k - i))) (k + 1)
      have hderLAk := hderLA k
      rw [ih] at hderLAk
      have hDLA := huniq _ _ _ hderLAk hder1
      funext s
      rw [hcomm k s, congrFun hDLA s]
      exact (sum_recursiveCurvatureContraction_succ Q A k s).symm

theorem uhlenbeck_heat_covariantDerivative_commutator_slotArray
    [Fintype Idx] [DecidableEq Idx] {q : ℕ}
    (R : Idx → Idx → Idx → Idx → Real)
    (nablaR : Idx → Idx → Idx → Idx → Idx → Real)
    (Ric : Idx → Idx → Real)
    (nablaRic : Idx → Idx → Idx → Real)
    (A : (Fin q → Idx) → Real)
    (DA : Idx → (Fin q → Idx) → Real)
    (nablaDtA : Idx → (Fin q → Idx) → Real)
    (D3A : Idx → Idx → Idx → (Fin q → Idx) → Real)
    (P Z : SlotArray Idx)
    (hP : ∀ σ : ℕ → Idx, P σ = R (σ 0) (σ 1) (σ 2) (σ 3))
    (hZ : ∀ σ : ℕ → Idx, Z σ = DA (σ 0) (fun t : Fin q => σ ((t : ℕ) + 1)))
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR A DA D3A)
    (hgrad : tensorGradientRicciIdentityComponents R DA D3A)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : ∀ a e c d, R a e c d = -R e a c d)
    (hskewLast : ∀ a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (s : ℕ → Idx) :
    (uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic A DA nablaDtA
          (s 0) (fun t : Fin q => s ((t : ℕ) + 1)) -
        roughLaplacianCovariantDerivativeComponents D3A
          (s 0) (fun t : Fin q => s ((t : ℕ) + 1))) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic A DA nablaDtA
          (s 0) (fun t : Fin q => s ((t : ℕ) + 1)) -
        covariantDerivativeRoughLaplacianComponents D3A
          (s 0) (fun t : Fin q => s ((t : ℕ) + 1))) =
      curvatureSlotContraction q P Z s := by
  rw [uhlenbeck_heat_covariantDerivative_commutator R nablaR Ric nablaRic A DA nablaDtA D3A
    hdiff hgrad hcontract hskewFirst hskewLast htrace (s 0)
    (fun t : Fin q => s ((t : ℕ) + 1))]
  exact (curvatureSlotContraction_eq_curvatureSlotActionContraction R DA P Z hP hZ s).symm

theorem components_eq_sum_recursiveCurvatureContraction [Fintype Idx]
    (Q : ContractionMap Idx) (A : ℕ → SlotArray Idx) (k : ℕ)
    (L : (Fin (4 + k) → Idx) → Real)
    (hL : slotArrayOfComponents L =
      fun s => ∑ i ∈ Finset.range (k + 1),
        recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) s)
    (m : Fin (4 + k) → Idx) :
    L m = ∑ i ∈ Finset.range (k + 1),
      recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m) := by
  rw [← slotArrayOfComponents_componentSlotSeq L m, hL]

def contractionBoundedBy (B : ContractionMap Idx) (c : Real) : Prop :=
  ∀ (X Y : SlotArray Idx) (p r : Real),
    (∀ s : ℕ → Idx, |X s| ≤ p) → (∀ s : ℕ → Idx, |Y s| ≤ r) →
      ∀ s : ℕ → Idx, |B X Y s| ≤ c * (p * r)

theorem contractionBoundedBy_firstSlotDerivativeLift
    {B : ContractionMap Idx} {c : Real} (h : contractionBoundedBy B c) :
    contractionBoundedBy (firstSlotDerivativeLift B) c := by
  intro X Y p r hX hY s
  exact h (fun m => X (consSlot (s 0) m)) Y p r (fun _ => hX _) hY (tailSlot s)

theorem contractionBoundedBy_secondSlotDerivativeLift
    {B : ContractionMap Idx} {c : Real} (h : contractionBoundedBy B c) :
    contractionBoundedBy (secondSlotDerivativeLift B) c := by
  intro X Y p r hX hY s
  exact h X (fun m => Y (consSlot (s 0) m)) p r hX (fun _ => hY _) (tailSlot s)

theorem contractionBoundedBy_of_add {B B₁ B₂ : ContractionMap Idx} {c₁ c₂ : Real}
    (hB : ∀ X Y s, B X Y s = B₁ X Y s + B₂ X Y s)
    (h₁ : contractionBoundedBy B₁ c₁) (h₂ : contractionBoundedBy B₂ c₂) :
    contractionBoundedBy B (c₁ + c₂) := by
  intro X Y p r hX hY s
  rw [hB]
  calc |B₁ X Y s + B₂ X Y s| ≤ |B₁ X Y s| + |B₂ X Y s| := abs_add_le _ _
    _ ≤ c₁ * (p * r) + c₂ * (p * r) :=
      add_le_add (h₁ X Y p r hX hY s) (h₂ X Y p r hX hY s)
    _ = (c₁ + c₂) * (p * r) := by ring

theorem contractionBoundedBy_curvatureSlotContraction [Fintype Idx] (q : ℕ) :
    contractionBoundedBy (Idx := Idx) (curvatureSlotContraction q)
      (2 * (q : Real) * (Fintype.card Idx : Real) ^ 2) := by
  classical
  intro X Y p r hX hY s
  have hp : (0 : Real) ≤ p := le_trans (abs_nonneg _) (hX s)
  have hterm : ∀ t : Fin q,
      |∑ e : Idx, ∑ d : Idx,
          X (slotIndexArray (s 0) e d (s ((t : ℕ) + 1))) *
            Y (consSlot e (Function.update (tailSlot s) (t : ℕ) d))| ≤
        (Fintype.card Idx : Real) ^ 2 * (p * r) := by
    intro t
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : Idx => (Fintype.card Idx : Real) * (p * r)) fun e _ => ?_) ?_
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ : Idx => p * r) fun d _ => ?_) ?_
      · rw [abs_mul]
        exact mul_le_mul (hX _) (hY _) (abs_nonneg _) hp
      · exact le_of_eq (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
    · refine le_of_eq ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
  unfold curvatureSlotContraction
  set S : Real := ∑ t : Fin q, ∑ e : Idx, ∑ d : Idx,
      X (slotIndexArray (s 0) e d (s ((t : ℕ) + 1))) *
        Y (consSlot e (Function.update (tailSlot s) (t : ℕ) d)) with hS
  have hsum : |S| ≤ (q : Real) * ((Fintype.card Idx : Real) ^ 2 * (p * r)) := by
    rw [hS]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : Fin q => (Fintype.card Idx : Real) ^ 2 * (p * r)) fun t _ => hterm t) ?_
    exact le_of_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
  rw [abs_mul]
  have habs2 : |(2 : Real)| = 2 := by norm_num
  rw [habs2]
  nlinarith [hsum]

theorem abs_curvatureSquarePair_le [Fintype Idx]
    (X Y : SlotArray Idx) (p r : Real)
    (hX : ∀ s : ℕ → Idx, |X s| ≤ p) (hY : ∀ s : ℕ → Idx, |Y s| ≤ r)
    (a b c d : Idx) :
    |curvatureSquarePair X Y a b c d| ≤ (Fintype.card Idx : Real) ^ 2 * (p * r) := by
  classical
  have hp : (0 : Real) ≤ p := le_trans (abs_nonneg _) (hX (fun _ => a))
  have hr : (0 : Real) ≤ r := le_trans (abs_nonneg _) (hY (fun _ => a))
  have hterm : ∀ e : Idx,
      |∑ f : Idx,
          (X (slotIndexArray a e b f) * Y (slotIndexArray c e d f) +
            Y (slotIndexArray a e b f) * X (slotIndexArray c e d f))| ≤
        (Fintype.card Idx : Real) * (2 * (p * r)) := by
    intro e
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : Idx => 2 * (p * r)) fun f _ => ?_) ?_
    · refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have h1 : |X (slotIndexArray a e b f)| * |Y (slotIndexArray c e d f)| ≤ p * r :=
        mul_le_mul (hX _) (hY _) (abs_nonneg _) hp
      have h2 : |Y (slotIndexArray a e b f)| * |X (slotIndexArray c e d f)| ≤ r * p :=
        mul_le_mul (hY _) (hX _) (abs_nonneg _) hr
      nlinarith [h1, h2]
    · exact le_of_eq (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  unfold curvatureSquarePair
  set S : Real := ∑ e : Idx, ∑ f : Idx,
      (X (slotIndexArray a e b f) * Y (slotIndexArray c e d f) +
        Y (slotIndexArray a e b f) * X (slotIndexArray c e d f)) with hS
  have hsum : |S| ≤
      (Fintype.card Idx : Real) * ((Fintype.card Idx : Real) * (2 * (p * r))) := by
    rw [hS]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : Idx => (Fintype.card Idx : Real) * (2 * (p * r))) fun e _ => hterm e) ?_
    exact le_of_eq (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  rw [abs_mul]
  have habs : |(1 / 2 : Real)| = 1 / 2 := by norm_num
  rw [habs]
  nlinarith [hsum]

theorem contractionBoundedBy_curvatureReactionPair [Fintype Idx] :
    contractionBoundedBy (Idx := Idx) curvatureReactionPair
      (8 * (Fintype.card Idx : Real) ^ 2) := by
  intro X Y p r hX hY s
  unfold curvatureReactionPair
  have h1 := abs_curvatureSquarePair_le X Y p r hX hY (s 0) (s 1) (s 2) (s 3)
  have h2 := abs_curvatureSquarePair_le X Y p r hX hY (s 0) (s 1) (s 3) (s 2)
  have h3 := abs_curvatureSquarePair_le X Y p r hX hY (s 0) (s 2) (s 1) (s 3)
  have h4 := abs_curvatureSquarePair_le X Y p r hX hY (s 0) (s 3) (s 1) (s 2)
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have hb3 := abs_le.mp h3
  have hb4 := abs_le.mp h4
  rw [abs_le]
  constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2]

def contractionBoundConstant (κ : Real) : ℕ → ℕ → Real
  | 0, 0 => 8 * κ
  | (i + 1), 0 => contractionBoundConstant κ i 0
  | 0, (j + 1) => contractionBoundConstant κ 0 j + 2 * ((4 + j : ℕ) : Real) * κ
  | (i + 1), (j + 1) =>
      contractionBoundConstant κ i (j + 1) + contractionBoundConstant κ (i + 1) j
  termination_by i j => i + j

theorem contractionBoundConstant_zero_zero (κ : Real) :
    contractionBoundConstant κ 0 0 = 8 * κ := by
  simp [contractionBoundConstant]

theorem contractionBoundConstant_succ_zero (κ : Real) (i : ℕ) :
    contractionBoundConstant κ (i + 1) 0 = contractionBoundConstant κ i 0 := by
  simp [contractionBoundConstant]

theorem contractionBoundConstant_zero_succ (κ : Real) (j : ℕ) :
    contractionBoundConstant κ 0 (j + 1) =
      contractionBoundConstant κ 0 j + 2 * ((4 + j : ℕ) : Real) * κ := by
  simp [contractionBoundConstant]

theorem contractionBoundConstant_succ_succ (κ : Real) (i j : ℕ) :
    contractionBoundConstant κ (i + 1) (j + 1) =
      contractionBoundConstant κ i (j + 1) + contractionBoundConstant κ (i + 1) j := by
  simp [contractionBoundConstant]

theorem contractionBoundedBy_recursiveCurvatureContraction [Fintype Idx]
    (Q : ContractionMap Idx) (κ : Real)
    (hQ : contractionBoundedBy Q (8 * κ))
    (hC : ∀ q : ℕ,
      contractionBoundedBy (Idx := Idx) (curvatureSlotContraction q) (2 * (q : Real) * κ))
    (i j : ℕ) :
    contractionBoundedBy (recursiveCurvatureContraction Q i j)
      (contractionBoundConstant κ i j) := by
  induction i generalizing j with
  | zero =>
      induction j with
      | zero =>
          rw [recursiveCurvatureContraction_zero_zero, contractionBoundConstant_zero_zero]
          exact hQ
      | succ j ihj =>
          rw [contractionBoundConstant_zero_succ]
          refine contractionBoundedBy_of_add
            (recursiveCurvatureContraction_zero_succ Q j)
            (contractionBoundedBy_secondSlotDerivativeLift ihj) ?_
          exact hC (4 + j)
  | succ i ihi =>
      induction j with
      | zero =>
          rw [recursiveCurvatureContraction_succ_zero, contractionBoundConstant_succ_zero]
          exact contractionBoundedBy_firstSlotDerivativeLift (ihi 0)
      | succ j ihj =>
          rw [contractionBoundConstant_succ_succ]
          exact contractionBoundedBy_of_add
            (recursiveCurvatureContraction_succ_succ Q i j)
            (contractionBoundedBy_firstSlotDerivativeLift (ihi (j + 1)))
            (contractionBoundedBy_secondSlotDerivativeLift ihj)

theorem abs_sum_recursiveCurvatureContraction_le [Fintype Idx]
    (Q : ContractionMap Idx) (κ : Real)
    (hQ : contractionBoundedBy Q (8 * κ))
    (hC : ∀ q : ℕ,
      contractionBoundedBy (Idx := Idx) (curvatureSlotContraction q) (2 * (q : Real) * κ))
    (A : ℕ → SlotArray Idx) (b : ℕ → Real)
    (hA : ∀ (i : ℕ) (s : ℕ → Idx), |A i s| ≤ b i) (k : ℕ) (s : ℕ → Idx) :
    |∑ i ∈ Finset.range (k + 1),
        recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) s| ≤
      ∑ i ∈ Finset.range (k + 1),
        contractionBoundConstant κ i (k - i) * (b i * b (k - i)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  exact contractionBoundedBy_recursiveCurvatureContraction Q κ hQ hC i (k - i)
    (A i) (A (k - i)) (b i) (b (k - i)) (hA i) (hA (k - i)) s

theorem sum_contractionBoundConstant_succ (κ : Real) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), contractionBoundConstant κ i (k + 1 - i)) =
      2 * (∑ i ∈ Finset.range (k + 1), contractionBoundConstant κ i (k - i)) +
        2 * ((4 + k : ℕ) : Real) * κ := by
  classical
  rw [Finset.sum_range_succ' (fun i => contractionBoundConstant κ i (k + 1 - i)) (k + 1)]
  have hstep : ∀ i ∈ Finset.range (k + 1),
      contractionBoundConstant κ (i + 1) (k + 1 - (i + 1)) =
        contractionBoundConstant κ i (k - i) +
          (if k - i = 0 then (0 : Real) else contractionBoundConstant κ (i + 1) (k - i - 1)) := by
    intro i _
    have hsub : k + 1 - (i + 1) = k - i := by omega
    rw [hsub]
    cases hk : k - i with
    | zero => simp [contractionBoundConstant_succ_zero]
    | succ n => simp [contractionBoundConstant_succ_succ]
  have hzeroterm :
      contractionBoundConstant κ 0 (k + 1 - 0) =
        contractionBoundConstant κ 0 k + 2 * ((4 + k : ℕ) : Real) * κ := by
    have hsub : k + 1 - 0 = k + 1 := by omega
    rw [hsub, contractionBoundConstant_zero_succ]
  rw [Finset.sum_congr rfl hstep, hzeroterm, Finset.sum_add_distrib]
  have hsecond :
      (∑ i ∈ Finset.range (k + 1),
          (if k - i = 0 then (0 : Real) else
            contractionBoundConstant κ (i + 1) (k - i - 1))) +
          contractionBoundConstant κ 0 k =
        ∑ i ∈ Finset.range (k + 1), contractionBoundConstant κ i (k - i) := by
    rw [Finset.sum_range_succ' (fun i => contractionBoundConstant κ i (k - i)) k]
    rw [Finset.sum_range_succ (fun i =>
      (if k - i = 0 then (0 : Real) else
        contractionBoundConstant κ (i + 1) (k - i - 1))) k]
    have hlast : k - k = 0 := by omega
    rw [if_pos hlast]
    have hterm : ∀ i ∈ Finset.range k,
        (if k - i = 0 then (0 : Real) else
          contractionBoundConstant κ (i + 1) (k - i - 1)) =
          contractionBoundConstant κ (i + 1) (k - (i + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h1 : k - i ≠ 0 := by omega
      have h2 : k - i - 1 = k - (i + 1) := by omega
      rw [if_neg h1, h2]
    rw [Finset.sum_congr rfl hterm]
    have h4 : k - 0 = k := by omega
    rw [h4]
    ring
  linarith [hsecond]

theorem sum_contractionBoundConstant_eq (κ : Real) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), contractionBoundConstant κ i (k - i)) =
      (18 * 2 ^ k - 2 * (k : Real) - 10) * κ := by
  induction k with
  | zero =>
      rw [Finset.sum_range_one]
      have h0 : (0 : ℕ) - 0 = 0 := by omega
      rw [h0, contractionBoundConstant_zero_zero]
      norm_num
  | succ k ih =>
      rw [sum_contractionBoundConstant_succ, ih]
      push_cast
      ring

theorem compPairMulti_sum [Fintype Idx] {r n : ℕ}
    (F : ℕ → (Fin r → Idx) → Real) (B : (Fin r → Idx) → Real) :
    compPairMulti (fun m => ∑ i ∈ Finset.range n, F i m) B =
      ∑ i ∈ Finset.range n, compPairMulti (F i) B := by
  unfold compPairMulti
  have hstep : ∀ m : Fin r → Idx,
      (∑ i ∈ Finset.range n, F i m) * B m = ∑ i ∈ Finset.range n, F i m * B m := by
    intro m
    exact Finset.sum_mul _ _ _
  simp_rw [hstep]
  exact Finset.sum_comm

theorem abs_compPairMulti_le [Fintype Idx] {r : ℕ}
    (F G : (Fin r → Idx) → Real) (u v : Real)
    (hF : ∀ m : Fin r → Idx, |F m| ≤ u) (hG : ∀ m : Fin r → Idx, |G m| ≤ v) :
    |compPairMulti F G| ≤ (Fintype.card Idx : Real) ^ r * (u * v) := by
  classical
  unfold compPairMulti
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin r → Idx => u * v) fun m _ => ?_) ?_
  · rw [abs_mul]
    have hu : (0 : Real) ≤ u := le_trans (abs_nonneg _) (hF m)
    exact mul_le_mul (hF m) (hG m) (abs_nonneg _) hu
  · refine le_of_eq ?_
    have hcard : (Fintype.card (Fin r → Idx) : Real) = (Fintype.card Idx : Real) ^ r := by
      rw [Fintype.card_pi]
      simp [Finset.prod_const, Finset.card_univ]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

theorem multiReactionDown_eq_contraction_pair_sum
    [Fintype Idx] {M : Type*} {k : ℕ}
    (level levelDt levelLap : Real → M → (Fin (4 + k) → Idx) → Real)
    (Q : ContractionMap Idx) (A : ℕ → SlotArray Idx) (t : Real) (x : M)
    (hres : ∀ m : Fin (4 + k) → Idx,
      levelDt t x m - levelLap t x m =
        ∑ i ∈ Finset.range (k + 1),
          recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m)) :
    multiReactionDown level levelDt levelLap t x =
      2 * ∑ i ∈ Finset.range (k + 1),
        compPairMulti
          (fun m : Fin (4 + k) → Idx =>
            recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m))
          (level t x) := by
  rw [multiReactionDown_eq_of_residual level levelDt levelLap
    (fun _ _ m => ∑ i ∈ Finset.range (k + 1),
      recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m)) t x hres,
    compPairMulti_sum]

theorem abs_multiReactionDown_le_contractionBoundConstant
    [Fintype Idx] {M : Type*} {k : ℕ}
    (level levelDt levelLap : Real → M → (Fin (4 + k) → Idx) → Real)
    (Q : ContractionMap Idx) (κ : Real)
    (hQ : contractionBoundedBy Q (8 * κ))
    (hC : ∀ q : ℕ,
      contractionBoundedBy (Idx := Idx) (curvatureSlotContraction q) (2 * (q : Real) * κ))
    (A : ℕ → SlotArray Idx) (b : ℕ → Real)
    (hA : ∀ (i : ℕ) (s : ℕ → Idx), |A i s| ≤ b i)
    (t : Real) (x : M)
    (hlevel : ∀ m : Fin (4 + k) → Idx, |level t x m| ≤ b k)
    (hres : ∀ m : Fin (4 + k) → Idx,
      levelDt t x m - levelLap t x m =
        ∑ i ∈ Finset.range (k + 1),
          recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m)) :
    |multiReactionDown level levelDt levelLap t x| ≤
      2 * ((Fintype.card Idx : Real) ^ (4 + k) *
        ((∑ i ∈ Finset.range (k + 1),
            contractionBoundConstant κ i (k - i) * (b i * b (k - i))) * b k)) := by
  rw [multiReactionDown_eq_of_residual level levelDt levelLap
    (fun _ _ m => ∑ i ∈ Finset.range (k + 1),
      recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m)) t x hres]
  have hbound : ∀ m : Fin (4 + k) → Idx,
      |∑ i ∈ Finset.range (k + 1),
          recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m)| ≤
        ∑ i ∈ Finset.range (k + 1),
          contractionBoundConstant κ i (k - i) * (b i * b (k - i)) := fun m =>
    abs_sum_recursiveCurvatureContraction_le Q κ hQ hC A b hA k (componentSlotSeq m)
  rw [abs_mul]
  have habs2 : |(2 : Real)| = 2 := by norm_num
  rw [habs2]
  have hpair := abs_compPairMulti_le
    (fun m : Fin (4 + k) → Idx =>
      ∑ i ∈ Finset.range (k + 1),
        recursiveCurvatureContraction Q i (k - i) (A i) (A (k - i)) (componentSlotSeq m))
    (level t x)
    (∑ i ∈ Finset.range (k + 1),
      contractionBoundConstant κ i (k - i) * (b i * b (k - i)))
    (b k) hbound hlevel
  exact mul_le_mul_of_nonneg_left hpair (by norm_num)

end DifferentialGeometry.PDE.RicciFlow
