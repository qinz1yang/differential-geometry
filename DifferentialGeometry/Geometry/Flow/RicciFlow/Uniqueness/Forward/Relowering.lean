import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureBridge
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

section Perm

def reLowerPermutationWithTwoInputs (s : ℕ) : Equiv.Perm (Fin (s + 1 + 2)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 2) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 2, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 2) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 2 then ⟨(l : ℕ) - 2, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 2 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

theorem reLowerPermutationWithTwoInputs_value (s : ℕ) (k : Fin (s + 1 + 2)) :
    ((reLowerPermutationWithTwoInputs s k : Fin (s + 1 + 2)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 2
      else if (k : ℕ) = s then 0 else if (k : ℕ) = s + 1 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 2, by omega⟩ : Fin (s + 1 + 2))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩ else k : Fin (s + 1 + 2)) : ℕ) = _
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_first_block {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k)) =
      Function.update tail (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 2 k : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) + 2 := by
      rw [reLowerPermutationWithTwoInputs_value, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 2 = 0)), dif_neg (by omega : ¬((k : ℕ) + 2 = 1))]
    exact congrArg tail (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = 0 := by
      rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_tail_zero {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = 1 := by
    rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_tail_one {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2))) =
      tail (Fin.last s) := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 2 = 0)), dif_neg (by omega : ¬(s + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

end Perm

section ReLower

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem traceField_eq_sum {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace.eval (metricTraceFirstTwoField (I := I) (M := M) g A x) tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * Tensor0SSpace.eval (A x)
          (metricTraceInput (I := I) (basis i) (basis j) tail) := by
  have h := metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv (A x) tail
  calc
    Tensor0SSpace.eval (metricTraceFirstTwoField (I := I) (M := M) g A x) tail =
        metricTraceFirstTwo0SAt (I := I) g (A x) tail := by
      rw [metricTraceFirstTwoField_apply]
      exact metricTraceFirstTwo0STensor_apply (I := I) g (A x) tail
    _ = metricTrace0S2InBasis (I := I) basis gInv (A x) tail := h
    _ = ∑ i : Idx, ∑ j : Idx,
        gInv i j * Tensor0SSpace.eval (A x)
          (metricTraceInput (I := I) (basis i) (basis j) tail) := rfl

private theorem sum_comm4 {Idx : Type*} [Fintype Idx] (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j := by
  classical
  calc (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j)
      = ∑ a : Idx, ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j := Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem slot_expand {s : ℕ} {Idx : Type*} [Fintype Idx] {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (m : Fin s -> TangentSpace I x) (i : Fin s) (c : Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    Tensor0SSpace.eval A (Function.update m i (∑ p : Idx, c p • basis p)) =
      ∑ p : Idx, c p * Tensor0SSpace.eval A (Function.update m i (basis p)) := by
  classical
  calc Tensor0SSpace.eval A (Function.update m i (∑ p : Idx, c p • basis p))
      = ∑ p : Idx, Tensor0SSpace.eval A (Function.update m i (c p • basis p)) :=
        A.toMultilinearMap.map_update_sum Finset.univ i (fun p => c p • basis p) m
    _ = ∑ p : Idx, c p * Tensor0SSpace.eval A (Function.update m i (basis p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := Tensor0SSpace.map_update_smul (I := I) A m i (c p) (basis p)
        change Tensor0SSpace.eval A (Function.update m i (c p • basis p)) =
          c p • Tensor0SSpace.eval A (Function.update m i (basis p)) at h
        simpa [smul_eq_mul] using h

def reLower (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
    (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) (reLowerPermutationWithTwoInputs s)
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁)))

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_eval (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ T x) tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (Tensor0SSpace.eval (T x)
          (Function.update tail (Fin.last s) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last s))) := by
  classical
  with_unfolding_all
    rw [reLower, traceField_eq_sum (I := I) g₂ _ basis gInv hinv tail]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change Tensor0SSpace.eval
      (Tensor0SSpace.domDomCongr
        (tensor0SField_product (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁) x)
        (reLowerPermutationWithTwoInputs s)) _ = _
  rw [Tensor0SSpace.eval_domDomCongr, tensor0SField_product_eval, metricTensorField_eval]
  congr 1
  · exact congrArg (Tensor0SSpace.eval (T x))
      (funext fun k => reLowerPermutationWithTwoInputs_first_block (I := I) (basis i) (basis j) tail k)
  · change g₁.inner x
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2))))
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2)))) = _
    rw [reLowerPermutationWithTwoInputs_tail_zero (I := I) (basis i) (basis j) tail,
      reLowerPermutationWithTwoInputs_tail_one (I := I) (basis i) (basis j) tail]

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem sharpFlat_eq_raise (g₁ g₂ : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    sharpFlat (I := I) g₁ g₂ x V =
      raiseAt (I := I) g₂ x basis (fun l : Idx => g₁.inner x V (basis l)) := by
  have hflat : ∀ l : Idx,
      g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) = g₁.inner x V (basis l) := by
    intro l
    have h2 : tangentFlatEquiv_gen (I := I) g₂ x (sharpFlat (I := I) g₁ g₂ x V) =
        tangentFlatEquiv_gen (I := I) g₁ x V := by
      change tangentFlatEquiv_gen (I := I) g₂ x
        ((tangentFlatEquiv_gen (I := I) g₂ x).symm
          ((tangentFlatEquiv_gen (I := I) g₁ x) V)) = _
      exact (tangentFlatEquiv_gen (I := I) g₂ x).apply_symm_apply _
    rw [← tangentFlatEquiv_apply_gen (I := I) g₂ x, h2,
      tangentFlatEquiv_apply_gen (I := I) g₁ x]
  rw [show (fun l : Idx => g₁.inner x V (basis l)) =
      fun l : Idx => g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) from
    (funext fun l => (hflat l).symm)]
  exact (raiseAt_lower (I := I) g₂ x basis (sharpFlat (I := I) g₁ g₂ x V)).symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_apply (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) (tail : Fin (s + 1) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ T x) tail =
      Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s)
        (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last s)))) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  rw [reLower_eval (I := I) g₁ g₂ T basis gInv hinv tail,
    sharpFlat_eq_raise (I := I) g₁ g₂ basis (tail (Fin.last s)), raiseAt_eq,
    slot_expand (I := I) (T x) tail (Fin.last s)
      (fun p => ∑ l, gInv p l * g₁.inner x (tail (Fin.last s)) (basis l)) basis]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [g₁.symm x (basis l) (tail (Fin.last s))]
  ring

omit [SigmaCompactSpace M] in
theorem reLower_rm04 (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (hRm : Rm2 x = metricRm04At (I := I) g₂ x)
    (X Y Z W : TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ Rm2 x)
        (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  classical
  have hlast : (vec4 (I := I) X Y Z W) (Fin.last 3) = W := by
    simp [vec4]
  have hupd : Function.update (vec4 (I := I) X Y Z W) (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x W) =
      vec4 (I := I) X Y Z (sharpFlat (I := I) g₁ g₂ x W) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [reLower_apply (I := I) g₁ g₂ Rm2 x, hlast, hupd, hRm]
  exact mixLow_eq_rm04 (I := I) g₁ g₂ x X Y Z W

end ReLower

section Pair

def reLowerPermutationWithThreeInputs (s : ℕ) : Equiv.Perm (Fin (s + 1 + 3)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 3) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 3, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 3) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 2, by omega⟩
      else if (l : ℕ) = 2 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 3 then ⟨(l : ℕ) - 3, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 3 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

theorem reLowerPermutationWithThreeInputs_value (s : ℕ) (k : Fin (s + 1 + 3)) :
    ((reLowerPermutationWithThreeInputs s k : Fin (s + 1 + 3)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 3
      else if (k : ℕ) = s then 0
      else if (k : ℕ) = s + 1 then 2
      else if (k : ℕ) = s + 2 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 3, by omega⟩ : Fin (s + 1 + 3))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩ else k : Fin (s + 1 + 3)) : ℕ) = _
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_first_block {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k)) =
      Function.update (Fin.tail u) (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 3 k : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) + 3 := by
      rw [reLowerPermutationWithThreeInputs_value, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 3 = 0)), dif_neg (by omega : ¬((k : ℕ) + 3 = 1))]
    exact congrArg u (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = 0 := by
      rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_zero {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3))) = u 0 := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 2 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((2 : ℕ) = 0)), dif_neg (by omega : ¬((2 : ℕ) = 1))]
  exact congrArg u (Fin.ext (by simp))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_one {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 1 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_two {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3))) =
      u (Fin.last (s + 1)) := by
  have hcast : ((Fin.natAdd (s + 1) (2 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 3 = 0)), dif_neg (by omega : ¬(s + 3 = 1))]
  exact congrArg u (Fin.ext (by simp))

def reLowerPair (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 2) g₂
    (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) (reLowerPermutationWithThreeInputs s)
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) T K))

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPair_eval (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv)
    (u : Fin (s + 2) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLowerPair (I := I) g₂ T K x) u =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (Tensor0SSpace.eval (T x)
          (Function.update (Fin.tail u) (Fin.last s) (basis i)) *
          Tensor0SSpace.eval (K x)
            (vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))))) := by
  classical
  with_unfolding_all
    rw [reLowerPair, traceField_eq_sum (I := I) g₂ _ basis gInv hinv u]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change Tensor0SSpace.eval
      (Tensor0SSpace.domDomCongr
        (tensor0SField_product (∞ : WithTop ℕ∞) T K x)
        (reLowerPermutationWithThreeInputs s)) _ = _
  rw [Tensor0SSpace.eval_domDomCongr, tensor0SField_product_eval]
  congr 1
  · exact congrArg (Tensor0SSpace.eval (T x))
      (funext fun k => reLowerPermutationWithThreeInputs_first_block (I := I) (basis i) (basis j) u k)
  · refine congrArg (Tensor0SSpace.eval (K x)) (funext fun p => ?_)
    change metricTraceInput (I := I) (basis i) (basis j) u
        (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) p)) = _
    fin_cases p
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (0 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_zero (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (1 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_one (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (2 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_two (I := I) (basis i) (basis j) u]
      simp [vec3]

end Pair

section Defect

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_eq_trace (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    reLower (I := I) g₁ g₂ T =
      metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
        (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) (reLowerPermutationWithTwoInputs s)
          (tensor0SField_product (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁))) := rfl

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem metricCov_one (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) g) (1 : WithTop ℕ∞) := by
  simpa [metricCov] using
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g)

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem nablaProd_eval {s q : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) q cov B nablaB)
    {x : M} (X : TangentSpace I x) (w : Fin (s + q) -> TangentSpace I x) :
    Tensor0SSpace.eval
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + q) cov
          (tensor0SField_product (∞ : WithTop ℕ∞) A B) x)
        (Fin.cons X w) =
      Tensor0SSpace.eval (nablaA x) (Fin.cons X (fun a : Fin s => w (Fin.castAdd q a))) *
          Tensor0SSpace.eval (B x) (fun a : Fin q => w (Fin.natAdd s a)) +
        Tensor0SSpace.eval (A x) (fun a : Fin s => w (Fin.castAdd q a)) *
          Tensor0SSpace.eval (nablaB x)
            (Fin.cons X (fun a : Fin q => w (Fin.natAdd s a))) := by
  classical
  let Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose
  have hXsec : Xsec x = X :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose_spec
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose
  have hV : ∀ a : Fin (s + q), V a x = w a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose_spec
  have h1 := totalNabla0SFun_eval_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s + q) cov Xsec
    (tensor0SField_product (∞ : WithTop ℕ∞) A B) x
    (fun a : Fin (s + q) => V a x)
  have h2 := nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB Xsec V x
  simp only [hV, hXsec] at h1 h2
  change Tensor0SSpace.eval
      (nabla0SFun (s + q) cov Xsec (tensor0SField_product (∞ : WithTop ℕ∞) A B) x)
      (fun a => w a) = _ at h2
  exact h1.trans h2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem update_cons_last {s : ℕ} {x : M} (X : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) (v : TangentSpace I x) :
    Function.update (Fin.cons X tail : Fin (s + 1 + 1) -> TangentSpace I x)
        (Fin.last (s + 1)) v =
      Fin.cons X (Function.update tail (Fin.last s) v) := by
  classical
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · have h0 : (0 : Fin (s + 1 + 1)) ≠ Fin.last (s + 1) := by
      rw [Ne, Fin.ext_iff]
      simp
    rw [Function.update_of_ne h0, Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.cons_succ]
    by_cases hj : j = Fin.last s
    · subst hj
      rw [Fin.succ_last, Function.update_self, Function.update_self]
    · have hne : j.succ ≠ Fin.last (s + 1) := by
        rw [← Fin.succ_last]
        exact fun hc => hj (Fin.succ_injective _ hc)
      rw [Function.update_of_ne hne, Function.update_of_ne hj, Fin.cons_succ]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem cons_last {s : ℕ} {x : M} (X : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    (Fin.cons X tail : Fin (s + 1 + 1) -> TangentSpace I x) (Fin.last (s + 1)) =
      tail (Fin.last s) := by
  rw [← Fin.succ_last, Fin.cons_succ]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem cons2_vec3 {x : M} (X Y Z : TangentSpace I x)
    (v : Fin 2 -> TangentSpace I x) (h0 : v 0 = Y) (h1 : v 1 = Z) :
    (Fin.cons X v : Fin 3 -> TangentSpace I x) = vec3 (I := I) X Y Z := by
  funext p
  fin_cases p
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (0 : Fin 3) = vec3 (I := I) X Y Z (0 : Fin 3)
    rw [Fin.cons_zero]
    simp [vec3]
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (1 : Fin 3) = vec3 (I := I) X Y Z (1 : Fin 3)
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, Fin.cons_succ, h0]
    simp [vec3]
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (2 : Fin 3) = vec3 (I := I) X Y Z (2 : Fin 3)
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ, h1]
    simp [vec3]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla_reLower_eval (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    {x : M} (X : TangentSpace I x) (tail : Fin (s + 1) -> TangentSpace I x) :
    Tensor0SSpace.eval
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1)
          (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T) x)
        (Fin.cons X tail) =
      Tensor0SSpace.eval
          (reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x)
          (Fin.cons X tail) +
        Tensor0SSpace.eval
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) x)
          (Fin.cons X tail) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen
      (I := I) (metricCov (I := I) g₂) g₂ :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g₂
  have hrT : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) T (metricNabla0S (I := I) g₂ T) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) T _
  have hrG : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) g₂) (metricTensorField (I := I) g₁)
      (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) g₂) (metricTensorField (I := I) g₁) _
  let P := tensor0SField_product (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁)
  let D := Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) (reLowerPermutationWithTwoInputs s) P
  have htrace := nabla_metricTraceFirstTwo0S (I := I) (M := M) (metricCov (I := I) g₂)
    g₂ hmc D basis gInv hinv X tail
  change Tensor0SSpace.eval
      (totalNabla0SFun (s + 1) (metricCov (I := I) g₂)
        (metricTraceFirstTwoField (I := I) (M := M) g₂ D) x)
      (Fin.cons X tail) =
    ∑ i, ∑ j, gInv i j * Tensor0SSpace.eval
      (totalNabla0SFun (s + 1 + 2) (metricCov (I := I) g₂) D x)
      (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) at htrace
  change Tensor0SSpace.eval
      (totalNabla0SFun (s + 1) (metricCov (I := I) g₂)
        (metricTraceFirstTwoField (I := I) (M := M) g₂ D) x)
      (Fin.cons X tail) = _
  rw [htrace,
    reLower_eval (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) basis gInv hinv (Fin.cons X tail),
    reLowerPair_eval (I := I) g₂ T
      (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) basis gInv hinv
      (Fin.cons X tail),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add]
  congr 1
  rw [show D = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (reLowerPermutationWithTwoInputs s) P from rfl,
    totalNabla0SFun_domDomCongr (I := I) (metricCov (I := I) g₂)
      (reLowerPermutationWithTwoInputs s) P x,
    Tensor0SSpace.eval_domDomCongr]
  have harg :
      (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail) :
          Fin (s + 1 + 2 + 1) -> TangentSpace I x) ∘
        frontExtendEquiv (reLowerPermutationWithTwoInputs s) =
      (Fin.cons X (fun p : Fin (s + 1 + 2) =>
        metricTraceInput (I := I) (basis i) (basis j) tail (reLowerPermutationWithTwoInputs s p)) :
          Fin (s + 1 + 2 + 1) -> TangentSpace I x) := by
    funext p
    simp only [Function.comp_apply]
    rw [cons_apply_frontExtendEquiv]
    rfl
  rw [harg, show P = tensor0SField_product (∞ : WithTop ℕ∞)
      T (metricTensorField (I := I) g₁) from rfl,
    nablaProd_eval (I := I) (metricCov (I := I) g₂) T (metricTensorField (I := I) g₁)
    (metricNabla0S (I := I) g₂ T)
    (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) hrT hrG X
    (fun p : Fin (s + 1 + 2) =>
      metricTraceInput (I := I) (basis i) (basis j) tail (reLowerPermutationWithTwoInputs s p))]
  have hfirst : (fun a : Fin (s + 1) =>
        metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPermutationWithTwoInputs s (Fin.castAdd 2 a))) =
      Function.update tail (Fin.last s) (basis i) :=
    funext fun a => reLowerPermutationWithTwoInputs_first_block (I := I) (basis i) (basis j) tail a
  have hg0 : metricTraceInput (I := I) (basis i) (basis j) tail
      (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2))) = basis j :=
    reLowerPermutationWithTwoInputs_tail_zero (I := I) (basis i) (basis j) tail
  have hg1 : metricTraceInput (I := I) (basis i) (basis j) tail
      (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2))) = tail (Fin.last s) :=
    reLowerPermutationWithTwoInputs_tail_one (I := I) (basis i) (basis j) tail
  rw [hfirst, metricTensorField_eval, hg0, hg1,
    cons2_vec3 (I := I) X (basis j) (tail (Fin.last s))
      (fun a : Fin 2 => metricTraceInput (I := I) (basis i) (basis j) tail
        (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) a))) hg0 hg1,
    update_cons_last (I := I) X tail (basis i), cons_last (I := I) X tail,
    Fin.tail_cons, Fin.cons_zero]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T) =
      reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  classical
  have h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T)
      (metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T)) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T) _
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T)
      (reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
    intro Y x slots
    change Tensor0SSpace.eval
        ((reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
          reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) x)
        (Fin.cons (Y x) slots) =
      Tensor0SSpace.eval
        (nabla0SFun (s + 1) (metricCov (I := I) g₂) Y
          (reLower (I := I) g₁ g₂ T) x) slots
    have hsplit :
        Tensor0SSpace.eval
            ((reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
              reLowerPair (I := I) g₂ T
                (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) x)
            (Fin.cons (Y x) slots) =
          Tensor0SSpace.eval
              (reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x)
              (Fin.cons (Y x) slots) +
            Tensor0SSpace.eval
              (reLowerPair (I := I) g₂ T
                (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) x)
              (Fin.cons (Y x) slots) := by
      rfl
    rw [hsplit, ← nabla_reLower_eval (I := I) g₁ g₂ T (Y x) slots]
    exact totalNabla0SFun_eval_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) Y (reLower (I := I) g₁ g₂ T) x slots
  exact totalNabla0SRealizes_unique h1 h2

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T) =
      reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁)) := by
  rw [nabla_reLower (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem reLowerPair_self (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    reLowerPair (I := I) g T
        (metricNabla0S (I := I) g (metricTensorField (I := I) g)) = 0 := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  apply tensor0SSpace_ext (I := I) (s + 2) x
  intro u
  change Tensor0SSpace.eval
      (reLowerPair (I := I) g T
        (metricNabla0S (I := I) g (metricTensorField (I := I) g)) x) u =
    Tensor0SSpace.eval (0 : Tensor0SSpace (s + 2) I x) u
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  with_unfolding_all
    rw [reLowerPair_eval (I := I) g T _ basis (basisInvMetric (I := I) g x basis)
      (basisInvMetric_real (I := I) g x basis) u]
  have hz : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    rw [metricNabla0S_self (I := I) g]
    rfl
  simp [hz]

end Defect

section Payoff

def reLowerOp (g₁ g₂ : SmoothRiemannianMetric I M) :
    ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k
  | 0 => id
  | (_ + 1) => fun T => reLower (I := I) g₁ g₂ T

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
@[simp] theorem reLowerOp_succ (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    reLowerOp (I := I) g₁ g₂ (k + 1) T = reLower (I := I) g₁ g₂ T := rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommFlux_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommFlux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      reLowerPair (I := I) g₂ T
        (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  rw [lapCommFlux, reLowerOp_succ, reLowerOp_succ, nabla_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T := by
  have h := lapComm_eq_div_flux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T
  rw [lapCommFlux_reLower (I := I) g₁ g₂ T] at h
  simpa using h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem traceInput_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (Fin.last (k + 2)) = tail (Fin.last k) := by
  have hv : ((Fin.last (k + 2) : Fin (k + 1 + 2)) : ℕ) = k + 2 := rfl
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(k + 2 = 0)), dif_neg (by omega : ¬(k + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem traceInput_update_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) (v : TangentSpace I x) :
    Function.update (metricTraceInput (I := I) a b tail) (Fin.last (k + 2)) v =
      metricTraceInput (I := I) a b (Function.update tail (Fin.last k) v) := by
  classical
  funext p
  have hp : (p : ℕ) < k + 1 + 2 := p.isLt
  by_cases hlast : p = Fin.last (k + 2)
  · subst hlast
    rw [Function.update_self, traceInput_last, Function.update_self]
  · have hpv : (p : ℕ) ≠ k + 2 := fun hc => hlast (Fin.ext (by rw [hc]; rfl))
    rw [Function.update_of_ne hlast, metricTraceInput_apply, metricTraceInput_apply]
    split_ifs with h0 h1
    · rfl
    · rfl
    · have hne : (⟨(p : ℕ) - 2, by omega⟩ : Fin (k + 1)) ≠ Fin.last k := by
        intro hc
        have hval : (p : ℕ) - 2 = k := congrArg Fin.val hc
        omega
      exact (Function.update_of_ne hne v tail).symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem trace_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 2 + 1)) :
    metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ (reLower (I := I) g₁ g₂ A) =
      reLower (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  apply tensor0SSpace_ext (I := I) (k + 1) x
  intro tail
  change Tensor0SSpace.eval
      (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLower (I := I) g₁ g₂ A) x) tail =
    Tensor0SSpace.eval
      (reLower (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) x) tail
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  with_unfolding_all
    rw [traceField_eq_sum (I := I) g₂ (reLower (I := I) g₁ g₂ A) basis gInv hinv tail,
      reLower_eval (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) basis gInv hinv tail]
  have hL : ∀ a b : Fin (Module.finrank Real (TangentSpace I x)),
      gInv a b * Tensor0SSpace.eval ((reLower (I := I) g₁ g₂ A) x)
          (metricTraceInput (I := I) (basis a) (basis b) tail) =
        ∑ i, ∑ j, gInv a b * gInv i j *
          (Tensor0SSpace.eval (A x) (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro a b
    rw [reLower_eval (I := I) g₁ g₂ A basis gInv hinv
      (metricTraceInput (I := I) (basis a) (basis b) tail), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [traceInput_update_last, traceInput_last]
    ring
  have hR : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      gInv i j * (Tensor0SSpace.eval
          ((metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) x)
            (Function.update tail (Fin.last k) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last k))) =
        ∑ a, ∑ b, gInv a b * gInv i j *
          (Tensor0SSpace.eval (A x) (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro i j
    rw [traceField_eq_sum (I := I) g₂ A basis gInv hinv
      (Function.update tail (Fin.last k) (basis i)), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [hL, hR]
  exact sum_comm4 _

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommRem_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapCommRem, reLowerOp_succ, reLowerOp_succ, covDiv0SField, covDiv0SField,
    nabla_reLower, metricTraceFirstTwoField_add, trace_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_eq (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower (I := I) g₁ g₂ T, lapCommRem_reLower (I := I) g₁ g₂ T]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower_eq (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

end Payoff

end DifferentialGeometry.PDE.RicciFlow

end
