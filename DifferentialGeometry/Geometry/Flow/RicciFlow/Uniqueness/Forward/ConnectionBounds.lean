import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.ConnectionTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
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

variable [SigmaCompactSpace M] [T2Space M]

section Frame

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasisGen (I := I) g x b (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor02_expand_eval {Idx : Type*} [Fintype Idx] {x : M}
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (b : Module.Basis Idx Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then W else Z) =
      ∑ k, b.repr W k *
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b k else Z) := by
  have h := tensor02_expand (I := I) q b W Z
  change Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then W else Z) =
    ∑ k, b.repr W k *
      Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b k else Z) at h
  exact h


omit [SigmaCompactSpace M] [T2Space M] in
private theorem repr_inner {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0)
    (v : TangentSpace I x) (k : Idx) :
    b.repr v k = g.inner x v (b k) := by
  classical
  have : Fintype Idx := Fintype.ofFinite Idx
  have hval : g.inner x v (b k) =
      Tensor0SSpace.eval (metricTensorField (I := I) g x)
        (fun a : Fin 2 => if a = 0 then v else b k) := by
    rw [metricTensorField_eval]; simp
  rw [hval, tensor02_expand_eval (I := I) (metricTensorField (I := I) g x) b v (b k)]
  have hbb : ∀ l : Idx,
      Tensor0SSpace.eval (metricTensorField (I := I) g x)
          (fun a : Fin 2 => if a = 0 then b l else b k) =
        (if l = k then (1 : Real) else 0) := by
    intro l
    rw [metricTensorField_eval]
    simpa using hON l k
  simp only [hbb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem normSq0S_reindex (g : SmoothRiemannianMetric I M) {x : M} {s s' : ℕ}
    (e : Fin s ≃ Fin s')
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S (I := I) g x s' (N.domDomCongr e) = normSq0S (I := I) g x s N := by
  classical
  obtain ⟨b, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  exact normSq0S_domDomCongr (I := I) g x b (onFrame_inv (I := I) g b hON) e N

end Frame

section SlotSums

private def slotEq2 {Idx : Type*} : (Fin 2 -> Idx) ≃ Idx × Idx where
  toFun s := (s 0, s 1)
  invFun p := fun a => if a = 0 then p.1 else p.2
  left_inv := by intro s; funext a; fin_cases a <;> simp
  right_inv := by intro p; simp

private def slotEq3 {Idx : Type*} : (Fin 3 -> Idx) ≃ Idx × Idx × Idx where
  toFun s := (s 0, s 1, s 2)
  invFun p := fun a => if a = 0 then p.1 else if a = 1 then p.2.1 else p.2.2
  left_inv := by intro s; funext a; fin_cases a <;> simp
  right_inv := by intro p; simp

private theorem sumSlots2 {Idx : Type*} [Fintype Idx] (F : (Fin 2 -> Idx) -> Real) :
    ∑ s : Fin 2 -> Idx, F s =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  have h := Equiv.sum_comp (slotEq2 (Idx := Idx)) (fun p => F (slotEq2.symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  rfl

private theorem sumSlots3 {Idx : Type*} [Fintype Idx] (F : (Fin 3 -> Idx) -> Real) :
    ∑ s : Fin 3 -> Idx, F s =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
        F (fun a : Fin 3 => if a = 0 then i else if a = 1 then j else k) := by
  classical
  have h := Equiv.sum_comp (slotEq3 (Idx := Idx)) (fun p => F (slotEq3.symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

end SlotSums

section Contraction

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceLow_eq_lower (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceLowAt (I := I) g₁ g₂ x =
      lowerBilin (I := I) (metricTensorField (I := I) g₁ x)
        (CovariantDerivative.difference (metricCov (I := I) g₁)
          (metricCov (I := I) g₂) x) := by
  refine tensor0SSpace_ext (𝕜 := Real) 3 x fun v => ?_
  change Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
    Tensor0SSpace.eval
      (lowerBilin (I := I) (metricTensorField (I := I) g₁ x)
        (CovariantDerivative.difference (metricCov (I := I) g₁)
          (metricCov (I := I) g₂) x)) v
  rw [connectionDifferenceLowAt_apply, lowerBilin_apply, metricTensorField_eval]
  simp


omit [SigmaCompactSpace M] [T2Space M] in
private theorem comp_lowerBilin {Idx : Type*} {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (i j k : Idx) :
    component0S (I := I) b (lowerBilin (I := I) q A)
        (fun a : Fin 3 => if a = 0 then i else if a = 1 then j else k) =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then (A (b j)) (b i) else b k) := by
  classical
  change Tensor0SSpace.eval (lowerBilin (I := I) q A)
      (fun a : Fin 3 => b (if a = 0 then i else if a = 1 then j else k)) = _
  rw [lowerBilin_apply]
  congr 1


omit [SigmaCompactSpace M] [T2Space M] in
theorem lowerBilin_normSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    normSq0S (I := I) g x 3 (lowerBilin (I := I) q A) ≤
      normSq0S (I := I) g x 2 q *
        normSq0S (I := I) g x 3
          (lowerBilin (I := I) (metricTensorField (I := I) g x) A) := by
  classical
  obtain ⟨b, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := onFrame_inv (I := I) g b hON
  have hq : normSq0S (I := I) g x 2 q =
      ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
          (Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 2 b hinv, sumSlots2]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [component0S_apply]
    congr 1
    funext a
    by_cases ha : a = 0 <;> simp [ha]
  have href : normSq0S (I := I) g x 3
      (lowerBilin (I := I) (metricTensorField (I := I) g x) A) =
      ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (b.repr ((A (b j)) (b i)) l) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b _ A i j l, metricTensorField_eval,
      repr_inner (I := I) g b hON]
    simp
  have hlow : normSq0S (I := I) g x 3 (lowerBilin (I := I) q A) =
      ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            (∑ l : Fin (Module.finrank Real (TangentSpace I x)),
              b.repr ((A (b j)) (b i)) l *
                Tensor0SSpace.eval q
                  (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b q A i j k,
      tensor02_expand_eval (I := I) q b ((A (b j)) (b i)) (b k)]
  rw [hlow, hq, href, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hstep : ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
        (∑ l : Fin (Module.finrank Real (TangentSpace I x)),
          b.repr ((A (b j)) (b i)) l *
            Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 ≤
      ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
        ((∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (b.repr ((A (b j)) (b i)) l) ^ 2) *
          ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun l => b.repr ((A (b j)) (b i)) l)
        (fun l => Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b l else b k))
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_comm]
  ring

end Contraction

section Carrier

def IsRmDiffField (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) : Prop :=
  ∀ x : M, S x = rmDiffLowAt (I := I) g₁ g₂ x

def nablaRmDiff (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  metricNabla0S (I := I) g₁ S

def nablaRmDiffSq (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) : Real :=
  normSq0S (I := I) g₁ x 5 (nablaRmDiff (I := I) g₁ S x)

omit [SigmaCompactSpace M] in
theorem nablaRmDiffSq_nonneg (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    0 ≤ nablaRmDiffSq (I := I) g₁ S x :=
  normSq0S_nonneg (I := I) g₁ x 5 _

omit [SigmaCompactSpace M] in
theorem nablaRmDiffSq_self (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (hS : IsRmDiffField (I := I) g g S) (x : M) :
    nablaRmDiffSq (I := I) g S x = 0 := by
  have hzero : S = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [hS y, rmDiffLowAt_self]
    rfl
  have hn : metricNabla0S (I := I) g S = 0 := by
    rw [hzero]
    simpa using metricNabla0S_smul (I := I) (s := 4) g (0 : Real) 0
  have hfield : nablaRmDiff (I := I) g S = 0 := hn
  have hz : nablaRmDiff (I := I) g S x = 0 := by rw [hfield]; rfl
  change normSq0S (I := I) g x 5 (nablaRmDiff (I := I) g S x) = 0
  rw [hz]
  simpa using normSq0S_smul (I := I) g (0 : Real)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)

end Carrier

section NablaRicci

omit [SigmaCompactSpace M] in
theorem nablaRicDiff_split (g₁ g₂ : SmoothRiemannianMetric I M)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂ =
      metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) + lapDiffFlux (I := I) g₁ g₂ Ric₂ := by
  rw [metricNabla0S_sub, lapDiffFlux]
  abel

omit [SigmaCompactSpace M] in
theorem nablaRicDiff_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) (x : M) :
    normSq0S (I := I) g₁ x 3
        ((metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂) x) ≤
      2 * normSq0S (I := I) g₁ x 3 (metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x) +
        8 * (Module.finrank Real E : Real) ^ 3 * connectionDifferenceSq (I := I) g₁ g₂ x *
          normSq0S (I := I) g₁ x 2 (Ric₂ x) := by
  have hpt : (metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂) x =
      metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x + lapDiffFlux (I := I) g₁ g₂ Ric₂ x := by
    rw [nablaRicDiff_split (I := I) g₁ g₂ Ric₁ Ric₂]; rfl
  rw [hpt]
  refine le_trans (normSq0S_add_le (I := I) g₁ x 3 _ _) ?_
  have hflux : normSq0S (I := I) g₁ x 3 (lapDiffFlux (I := I) g₁ g₂ Ric₂ x) ≤
      4 * (Module.finrank Real E : Real) ^ 3 * connectionDifferenceSq (I := I) g₁ g₂ x *
        normSq0S (I := I) g₁ x 2 (Ric₂ x) := by
    refine (fluxNormSq_le (I := I) (s := 2) g₁ g₂ Ric₂ x).trans_eq ?_
    norm_num
  linarith

end NablaRicci

section TraceCommute

omit [SigmaCompactSpace M] in
private theorem nabla_trace_field {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricNabla0S (I := I) g
        (DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField
          (I := I) (M := M) g A) =
      DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s)
          (metricNabla0S (I := I) g A)) := by
  have hmc :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  exact totalNabla0SRealizes_unique
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
      (metricCov (I := I) g)
      (DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField
        (I := I) (M := M) g A) _)
    (DifferentialGeometry.Tensor.RSTensor.nablaRealizes_metricTraceFirstTwo
      (I := I) (M := M) (metricCov (I := I) g) g hmc A (metricNabla0S (I := I) g A)
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2)
        (metricCov (I := I) g) A _))

omit [SigmaCompactSpace M] [T2Space M] in
private theorem traceShuffle_normSq_le {s : ℕ}
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 + 1)) :
    normSq0S (I := I) g x (s + 1)
        (DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s) N) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1) (N x) := by
  have hle : normSq0S (I := I) g x (s + 1)
        (DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s) N) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1)
          ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s) N) x) :=
    traceNormSq_le (I := I) (s := s + 1) g x
      ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s) N) x)
  have hiso : normSq0S (I := I) g x (s + 2 + 1)
        ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (DifferentialGeometry.Tensor.RSTensor.traceNablaShuffle s) N) x) =
      normSq0S (I := I) g x (s + 2 + 1) (N x) :=
    normSq0S_reindex (I := I) g _ (N x)
  rwa [hiso] at hle

omit [SigmaCompactSpace M] in
private theorem nablaTracePerm_normSq_le {s : ℕ}
    (g : SmoothRiemannianMetric I M) (e : Equiv.Perm (Fin (s + 2)))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) (x : M) :
    normSq0S (I := I) g x (s + 1)
        (metricNabla0S (I := I) g
          (DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField (I := I) (M := M) g
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1) (metricNabla0S (I := I) g A x) := by
  have hna : metricNabla0S (I := I) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x =
      ContinuousMultilinearMap.domDomCongr (frontExtendEquiv e)
        (metricNabla0S (I := I) g A x) :=
    totalNabla0SFun_domDomCongr (I := I) (metricCov (I := I) g) e A x
  have hiso : normSq0S (I := I) g x (s + 2 + 1)
        (metricNabla0S (I := I) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x) =
      normSq0S (I := I) g x (s + 2 + 1) (metricNabla0S (I := I) g A x) := by
    rw [hna]
    exact normSq0S_reindex (I := I) g _ (metricNabla0S (I := I) g A x)
  rw [nabla_trace_field (I := I) g
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)]
  refine le_trans (traceShuffle_normSq_le (I := I) g x
    (metricNabla0S (I := I) g
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) e A))) ?_
  exact le_of_eq (by rw [hiso])

omit [SigmaCompactSpace M] in
theorem nablaRicDiff_trace_le
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) g₁ g₂ S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) g₁ y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) g₂ y)
    (x : M) :
    normSq0S (I := I) g₁ x 3 (metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x) ≤
      (Module.finrank Real E : Real) ^ 5 * nablaRmDiffSq (I := I) g₁ S x := by
  have hfield : Ric₁ - Ric₂ =
      DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField (I := I) (M := M) g₁
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) rm04TraceSlots S) := by
    refine DFunLike.ext _ _ fun y => ?_
    have hsub : (Ric₁ - Ric₂) y = Ric₁ y - Ric₂ y := rfl
    rw [hsub, hRic₁ y, hRic₂ y, ricciDiff_eq_trace (I := I) g₁ g₂ y, ← hS y]
    rfl
  rw [hfield]
  exact nablaTracePerm_normSq_le (I := I) (s := 2) g₁ rm04TraceSlots S x

end TraceCommute

section Hamilton

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}

omit [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem coeff_adot_eq
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (c : Idx -> Idx -> Idx -> Real)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (c i j k) t)
    (i j k : Idx) :
    hframe.coeff k x ((Adot x (frame j x)) (frame i x)) = c i j k := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  have hfr : ∀ l : Idx, MDifferentiableAt I I.tangent (T% (frame l)) x := fun l =>
    (hframe.contMDiffAt hu hx l).mdifferentiableAt (by simp)
  have hdiff : ∀ r : Real,
      CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (b j) (b i) =
        (metricCov (I := I) (g₁ r) (frame j) x) (frame i x) -
          (metricCov (I := I) (g₂ r) (frame j) x) (frame i x) := by
    intro r
    have h := IsCovariantDerivativeOn.difference_apply
      (metricCov (I := I) (g₁ r)).isCovariantDerivativeOnUniv
      (metricCov (I := I) (g₂ r)).isCovariantDerivativeOnUniv
      (x := x) (Set.mem_univ x) (σ := fun y => frame j y) (hfr j)
    have h' : CovariantDerivative.difference (metricCov (I := I) (g₁ r))
        (metricCov (I := I) (g₂ r)) x (frame j x) =
          metricCov (I := I) (g₁ r) (frame j) x -
            metricCov (I := I) (g₂ r) (frame j) x := by
      simpa [CovariantDerivative.difference] using h
    rw [hbcoe j, hbcoe i, h']
    rfl
  have hfun : (fun r : Real =>
      b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
        (metricCov (I := I) (g₂ r)) x (b j) (b i)) k) =
      fun r : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₁ r)) frame hframe x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₂ r)) frame hframe x i j k := by
    funext r
    rw [hdiff r, ← hcoeff k]
    simp only [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval]
    exact map_sub (hframe.coeff k x) _ _
  have hL : HasDerivAt
      (fun r : Real =>
        b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (b j) (b i)) k)
      (b.repr ((Adot x (b j)) (b i)) k) t := by
    have h := (LinearMap.toContinuousLinearMap
      (b.coord k)).hasFDerivAt.comp_hasDerivAt t (hA (b i) (b j))
    change HasDerivAt
      (fun r : Real => b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
        (metricCov (I := I) (g₂ r)) x (b j) (b i)) k)
      (b.repr (Adot x (b j) (b i)) k) t at h
    exact h
  rw [hfun] at hL
  have huniq := hL.unique (hΓ i j k)
  rw [hcoeff k, ← hbcoe i, ← hbcoe j]
  exact huniq

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem lower_raise_cancel [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x b gInv)
    (L : Idx -> Real) (k : Idx) :
    ∑ m : Idx, (∑ l : Idx, gInv m l * L l) * g.inner x (b m) (b k) = L k := by
  classical
  have hrow : ∀ m : Idx, (∑ l : Idx, gInv m l * L l) * g.inner x (b m) (b k) =
      ∑ l : Idx, g.inner x (b k) (b m) * gInv m l * L l := by
    intro m
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g.symm x (b m) (b k)]
    ring
  rw [Finset.sum_congr rfl fun m _ => hrow m, Finset.sum_comm]
  have hcol : ∀ l : Idx,
      (∑ m : Idx, g.inner x (b k) (b m) * gInv m l * L l) =
        (if k = l then (1 : Real) else 0) * L l := by
    intro l
    rw [← Finset.sum_mul]
    exact congrArg (fun r : Real => r * L l) (hinv k l).2
  rw [Finset.sum_congr rfl fun l _ => hcol l]
  simp


omit [SigmaCompactSpace M] [T2Space M] in
private theorem lowerBilin_basis
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (b : Module.Basis Idx Real (TangentSpace I x)) (v : Fin 3 -> Idx) :
    Tensor0SSpace.eval (lowerBilin (I := I) q A) (fun a : Fin 3 => b (v a)) =
      ∑ m : Idx, b.repr ((A (b (v 1))) (b (v 0))) m *
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then b m else b (v 2)) := by
  rw [lowerBilin_apply, tensor02_expand_eval (I := I) q b _ (b (v 2))]


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem repr_bilinOfComp
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) (i j m : Idx) :
    b.repr ((bilinOfComp (I := I) b c (b j)) (b i)) m = c i j m := by
  classical
  rw [bilinOfComp_basis]
  simp [Finsupp.single_apply]

omit [SigmaCompactSpace M] [T2Space M] in
theorem connSpeedLow_eq
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (c₁ c₂ : Idx -> Idx -> Idx -> Real)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (c₁ i j k - c₂ i j k) t) :
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) =
      lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₁) -
        lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₂) -
        lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₂) := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  have hrepr : ∀ i j m : Idx,
      b.repr ((Adot x (b j)) (b i)) m = c₁ i j m - c₂ i j m := by
    intro i j m
    have h := coeff_adot_eq (I := I) g₁ g₂ frame hframe hu hx Adot hA
      (fun i' j' k' => c₁ i' j' k' - c₂ i' j' k') hΓ i j m
    rw [hcoeff m, ← hbcoe i, ← hbcoe j] at h
    exact h
  refine tensor0SSpace_ext (𝕜 := Real) 3 x fun w => ?_
  set L : Tensor0SSpace 3 I x :=
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) with hLdef
  set R : Tensor0SSpace 3 I x :=
      lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
          (bilinOfComp (I := I) b c₁) -
        lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
          (bilinOfComp (I := I) b c₂) -
        lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (bilinOfComp (I := I) b c₂) with hRdef
  change Tensor0SSpace.eval L w = Tensor0SSpace.eval R w
  suffices h :
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x L).toMultilinearMap =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x R).toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real => T w) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 3 => b) ?_
  intro v
  change Tensor0SSpace.eval L (fun a : Fin 3 => b (v a)) =
    Tensor0SSpace.eval R (fun a : Fin 3 => b (v a))
  have hRval : Tensor0SSpace.eval R (fun a : Fin 3 => b (v a)) =
      Tensor0SSpace.eval
        (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
          (bilinOfComp (I := I) b c₁)) (fun a : Fin 3 => b (v a)) -
      Tensor0SSpace.eval
        (lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
          (bilinOfComp (I := I) b c₂)) (fun a : Fin 3 => b (v a)) -
      Tensor0SSpace.eval
        (lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (bilinOfComp (I := I) b c₂)) (fun a : Fin 3 => b (v a)) := by
    rw [hRdef]
    rw [Tensor0SSpace.eval_sub, Tensor0SSpace.eval_sub]
  rw [hLdef, hRval, lowerBilin_basis (I := I) _ _ b v, lowerBilin_basis (I := I) _ _ b v,
    lowerBilin_basis (I := I) _ _ b v, lowerBilin_basis (I := I) _ _ b v,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hrepr (v 0) (v 1) m, repr_bilinOfComp (I := I) b c₁, repr_bilinOfComp (I := I) b c₂,
    metricTensorField_eval, metricTensorField_eval, metricDiffAt,
    Tensor0SSpace.eval_sub, metricTensorField_eval, metricTensorField_eval]
  simp only []
  ring


omit [SigmaCompactSpace M] [T2Space M] in
theorem lowerHamRHS_comp [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x b gInv)
    (L : Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    component0S (I := I) b
        (lowerBilin (I := I) (metricTensorField (I := I) g x)
          (bilinOfComp (I := I) b (fun i' j' m => ∑ l : Idx, gInv m l * L i' j' l)))
        (fun s : Fin 3 => if s = 0 then i else if s = 1 then j else k) =
      L i j k := by
  classical
  rw [comp_lowerBilin (I := I) b _ (bilinOfComp (I := I) b
      (fun i' j' m => ∑ l : Idx, gInv m l * L i' j' l)) i j k,
    tensor02_expand_eval (I := I) (metricTensorField (I := I) g x) b _ (b k)]
  have hterm : ∀ m : Idx,
      b.repr ((bilinOfComp (I := I) b
          (fun i' j' m' => ∑ l : Idx, gInv m' l * L i' j' l) (b j)) (b i)) m *
        Tensor0SSpace.eval (metricTensorField (I := I) g x)
          (fun a : Fin 2 => if a = 0 then b m else b k) =
      (∑ l : Idx, gInv m l * L i j l) * g.inner x (b m) (b k) := by
    intro m
    have hg : Tensor0SSpace.eval (metricTensorField (I := I) g x)
        (fun a : Fin 2 => if a = 0 then b m else b k) = g.inner x (b m) (b k) := by
      rw [metricTensorField_eval]; simp
    rw [repr_bilinOfComp (I := I) b
      (fun i' j' m' => ∑ l : Idx, gInv m' l * L i' j' l) i j m, hg]
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  exact lower_raise_cancel (I := I) g b gInv hinv (fun l => L i j l) k

private def hamiltonConnectionDifferencePermutation : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

def reindexCovariantThreeTensor (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  N.domDomCongr e

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem reindexCovariantThreeTensor_apply (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (reindexCovariantThreeTensor (I := I) e N) v =
      Tensor0SSpace.eval N (fun a : Fin 3 => v (e a)) :=
  Tensor0SSpace.eval_domDomCongr N e v

omit [SigmaCompactSpace M] [T2Space M] in
theorem normSq0S_reindexCovariantThreeTensor (g : SmoothRiemannianMetric I M) (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    normSq0S (I := I) g x 3 (reindexCovariantThreeTensor (I := I) e N) = normSq0S (I := I) g x 3 N :=
  normSq0S_reindex (I := I) g e N

def hamiltonConnectionDifferenceCombination (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (-1 : Real) • N + (-1 : Real) • reindexCovariantThreeTensor (I := I) (Equiv.swap (0 : Fin 3) 1) N +
    reindexCovariantThreeTensor (I := I) hamiltonConnectionDifferencePermutation N

omit [SigmaCompactSpace M] [T2Space M] in
theorem lower_connection_difference_eq_hamilton_combination [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x b gInv)
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nr : Idx -> Idx -> Idx -> Real)
    (hnr : ∀ d a c : Idx, nr d a c =
      component0S (I := I) b N
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else c)) :
    lowerBilin (I := I) (metricTensorField (I := I) g x)
        (bilinOfComp (I := I) b (fun i j m =>
          ∑ l : Idx, gInv m l * (-nr i j l - nr j i l + nr l i j))) =
      hamiltonConnectionDifferenceCombination (I := I) N := by
  classical
  refine tensor0SSpace_ext (𝕜 := Real) 3 x fun w => ?_
  set LHS : Tensor0SSpace 3 I x :=
      lowerBilin (I := I) (metricTensorField (I := I) g x)
        (bilinOfComp (I := I) b (fun i j m =>
          ∑ l : Idx, gInv m l * (-nr i j l - nr j i l + nr l i j))) with hLdef
  set RHS : Tensor0SSpace 3 I x :=
    hamiltonConnectionDifferenceCombination (I := I) N with hRdef
  change Tensor0SSpace.eval LHS w = Tensor0SSpace.eval RHS w
  suffices h :
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x LHS).toMultilinearMap =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x RHS).toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real => T w) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 3 => b) ?_
  intro v
  change Tensor0SSpace.eval LHS (fun a : Fin 3 => b (v a)) =
    Tensor0SSpace.eval RHS (fun a : Fin 3 => b (v a))
  have hLval : Tensor0SSpace.eval LHS (fun a : Fin 3 => b (v a)) =
      -nr (v 0) (v 1) (v 2) - nr (v 1) (v 0) (v 2) + nr (v 2) (v 0) (v 1) := by
    rw [hLdef]
    have h := lowerHamRHS_comp (I := I) g b gInv hinv
      (fun i j l => -nr i j l - nr j i l + nr l i j) (v 0) (v 1) (v 2)
    rw [component0S_apply] at h
    have hslots : (fun a : Fin 3 =>
        b ((fun s : Fin 3 => if s = 0 then v 0 else if s = 1 then v 1 else v 2) a)) =
        fun a : Fin 3 => b (v a) := by
      funext a; fin_cases a <;> simp
    rw [hslots] at h
    exact h
  have hRval : Tensor0SSpace.eval RHS (fun a : Fin 3 => b (v a)) =
      -(Tensor0SSpace.eval N (fun a : Fin 3 => b (v a))) -
        Tensor0SSpace.eval N (fun a : Fin 3 => b (v (Equiv.swap (0 : Fin 3) 1 a))) +
        Tensor0SSpace.eval N
          (fun a : Fin 3 => b (v (hamiltonConnectionDifferencePermutation a))) := by
    rw [hRdef, hamiltonConnectionDifferenceCombination,
      Tensor0SSpace.eval_add, Tensor0SSpace.eval_add,
      Tensor0SSpace.eval_smul, Tensor0SSpace.eval_smul]
    simp only [reindexCovariantThreeTensor_apply, smul_eq_mul]
    ring
  rw [hLval, hRval]
  have hcomp : ∀ d a c : Idx, nr d a c =
      Tensor0SSpace.eval N (fun s : Fin 3 => b ((fun s' : Fin 3 =>
        if s' = 0 then d else if s' = 1 then a else c) s)) := by
    intro d a c
    rw [hnr d a c]
    change Tensor0SSpace.eval N
      (fun s : Fin 3 => b (if s = 0 then d else if s = 1 then a else c)) = _
    rfl
  have h0 : Tensor0SSpace.eval N (fun a : Fin 3 => b (v a)) =
      nr (v 0) (v 1) (v 2) := by
    rw [hcomp (v 0) (v 1) (v 2)]
    congr 1
    funext a; fin_cases a <;> simp
  have h1 : Tensor0SSpace.eval N (fun a : Fin 3 => b (v (Equiv.swap (0 : Fin 3) 1 a))) =
      nr (v 1) (v 0) (v 2) := by
    rw [hcomp (v 1) (v 0) (v 2)]
    congr 1
    funext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  have h2 : Tensor0SSpace.eval N
      (fun a : Fin 3 => b (v (hamiltonConnectionDifferencePermutation a))) =
      nr (v 2) (v 0) (v 1) := by
    rw [hcomp (v 2) (v 0) (v 1)]
    congr 1
    funext a; fin_cases a <;> simp [hamiltonConnectionDifferencePermutation]
  rw [h0, h1, h2]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem reindexCovariantThreeTensor_sub (e : Equiv.Perm (Fin 3))
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    reindexCovariantThreeTensor (I := I) e (A - B) = reindexCovariantThreeTensor (I := I) e A - reindexCovariantThreeTensor (I := I) e B :=
  domDomCongr_sub (I := I) e A B

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem hamiltonConnectionDifferenceCombination_sub (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    hamiltonConnectionDifferenceCombination (I := I) A - hamiltonConnectionDifferenceCombination (I := I) B = hamiltonConnectionDifferenceCombination (I := I) (A - B) := by
  rw [hamiltonConnectionDifferenceCombination, hamiltonConnectionDifferenceCombination, hamiltonConnectionDifferenceCombination, reindexCovariantThreeTensor_sub, reindexCovariantThreeTensor_sub]
  module

omit [SigmaCompactSpace M] [T2Space M] in
theorem hamiltonConnectionDifferenceCombination_norm_sq_le (g : SmoothRiemannianMetric I M)
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    normSq0S (I := I) g x 3 (hamiltonConnectionDifferenceCombination (I := I) N) ≤ 10 * normSq0S (I := I) g x 3 N := by
  have hp1 : normSq0S (I := I) g x 3 (reindexCovariantThreeTensor (I := I) (Equiv.swap (0 : Fin 3) 1) N) =
      normSq0S (I := I) g x 3 N := normSq0S_reindexCovariantThreeTensor (I := I) g _ N
  have hp2 : normSq0S (I := I) g x 3 (reindexCovariantThreeTensor (I := I) hamiltonConnectionDifferencePermutation N) =
      normSq0S (I := I) g x 3 N := normSq0S_reindexCovariantThreeTensor (I := I) g _ N
  have hs1 : normSq0S (I := I) g x 3 ((-1 : Real) • N) = normSq0S (I := I) g x 3 N := by
    rw [normSq0S_smul]; norm_num
  have hs2 : normSq0S (I := I) g x 3
      ((-1 : Real) • reindexCovariantThreeTensor (I := I) (Equiv.swap (0 : Fin 3) 1) N) =
      normSq0S (I := I) g x 3 N := by
    rw [normSq0S_smul, hp1]; norm_num
  have hinner := normSq0S_add_le (I := I) g x 3 ((-1 : Real) • N)
    ((-1 : Real) • reindexCovariantThreeTensor (I := I) (Equiv.swap (0 : Fin 3) 1) N)
  have houter := normSq0S_add_le (I := I) g x 3
    ((-1 : Real) • N + (-1 : Real) • reindexCovariantThreeTensor (I := I) (Equiv.swap (0 : Fin 3) 1) N)
    (reindexCovariantThreeTensor (I := I) hamiltonConnectionDifferencePermutation N)
  rw [hamiltonConnectionDifferenceCombination]
  rw [hs1, hs2] at hinner
  linarith [houter, hinner, hp2]

end Hamilton

section MetricCompare


omit [SigmaCompactSpace M] [T2Space M] in
private theorem inner_le_sum_sq {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (b i) (b j) = if i = j then (1 : Real) else 0)
    {Λ : Real} (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (v : TangentSpace I x) :
    ∑ k : Idx, (g₁.inner x v (b k)) ^ 2 ≤ Λ ^ 2 * ∑ k : Idx, (g₂.inner x v (b k)) ^ 2 := by
  classical
  have hrepr : ∀ k : Idx, b.repr v k = g₁.inner x v (b k) :=
    fun k => repr_inner (I := I) g₁ b hON v k
  have hpar : ∀ g : SmoothRiemannianMetric I M,
      g.inner x v v = ∑ k : Idx, g₁.inner x v (b k) * g.inner x v (b k) := by
    intro g
    have hv : g.inner x v v =
        Tensor0SSpace.eval (metricTensorField (I := I) g x)
          (fun a : Fin 2 => if a = 0 then v else v) := by
      rw [metricTensorField_eval]; simp
    rw [hv, tensor02_expand_eval (I := I) (metricTensorField (I := I) g x) b v v]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hval : Tensor0SSpace.eval (metricTensorField (I := I) g x)
        (fun a : Fin 2 => if a = 0 then b k else v) = g.inner x (b k) v := by
      rw [metricTensorField_eval]; simp
    rw [hval, g.symm x (b k) v, hrepr k]
  set N : Real := ∑ k : Idx, (g₁.inner x v (b k)) ^ 2 with hNdef
  set Q : Real := ∑ k : Idx, (g₂.inner x v (b k)) ^ 2 with hQdef
  have hN : g₁.inner x v v = N := by
    rw [hpar g₁, hNdef]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hNnn : 0 ≤ N := by rw [hNdef]; positivity
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hCS : (g₂.inner x v v) ^ 2 ≤ N * Q := by
    rw [hpar g₂]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => g₁.inner x v (b k)) (fun k => g₂.inner x v (b k))
  have hsq : N ^ 2 ≤ Λ ^ 2 * (g₂.inner x v v) ^ 2 := by
    have h := hΛ v
    rw [hN] at h
    nlinarith [mul_self_le_mul_self hNnn h]
  rcases eq_or_lt_of_le hNnn with hN0 | hNpos
  · rw [← hN0]; positivity
  · nlinarith [hsq, hCS, hNpos, sq_nonneg Λ, hQnn]

omit [SigmaCompactSpace M] [T2Space M] in
theorem lowerBilin_metric_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {Λ : Real} (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    normSq0S (I := I) g₁ x 3 (lowerBilin (I := I) (metricTensorField (I := I) g₁ x) A) ≤
      Λ ^ 2 * normSq0S (I := I) g₁ x 3
        (lowerBilin (I := I) (metricTensorField (I := I) g₂ x) A) := by
  classical
  obtain ⟨b, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ b hON
  have hexp : ∀ q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      normSq0S (I := I) g₁ x 3 (lowerBilin (I := I) q A) =
        ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              (Tensor0SSpace.eval q
                (fun a : Fin 2 => if a = 0 then (A (b j)) (b i) else b k)) ^ 2 := by
    intro q
    rw [normSq0S_identity_eq_sum_sq (I := I) g₁ x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b q A i j k]
  have hcomp : ∀ (g : SmoothRiemannianMetric I M) (w : TangentSpace I x)
      (k : Fin (Module.finrank Real (TangentSpace I x))),
      Tensor0SSpace.eval (metricTensorField (I := I) g x)
          (fun a : Fin 2 => if a = 0 then w else b k) =
        g.inner x w (b k) := by
    intro g w k
    rw [metricTensorField_eval]; simp
  rw [hexp, hexp, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [hcomp]
  exact inner_le_sum_sq (I := I) g₁ g₂ b hON hΛ ((A (b j)) (b i))

end MetricCompare

section MainBound

private theorem connSpeed_arith
    {n P Hm Ac Λ B₁ B₃ E1 E2 X D R2 L1 L2 : Real}
    (hn : 0 ≤ n) (hP : 0 ≤ P) (hHm : 0 ≤ Hm) (hAc : 0 ≤ Ac)
    (hB₁ : 0 ≤ B₁) (hB₃ : 0 ≤ B₃) (hΛ0 : 0 ≤ Λ)
    (hE1 : E1 ≤ 10 * X) (hX : X ≤ 2 * D + 8 * n ^ 3 * Ac * R2)
    (hD : D ≤ n ^ 5 * P) (hR2B : R2 ≤ B₃)
    (hE2 : E2 ≤ Hm * L1) (hL1 : L1 ≤ Λ ^ 2 * L2) (hL2B : L2 ≤ 10 * B₁)
    (hp5 : n ^ 5 ≤ n ^ 6 + 1) (hp3 : n ^ 3 ≤ n ^ 6 + 1) :
    2 * E1 + 2 * E2 ≤
      200 * (n ^ 6 + 1) *
        (P + (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) := by
  have hKnn : (0 : Real) ≤ n ^ 6 + 1 := by positivity
  have hK1 : (1 : Real) ≤ n ^ 6 + 1 := by have := pow_nonneg hn 6; linarith
  have hSBnn : (0 : Real) ≤ B₁ + B₃ := by linarith
  have hWnn : (0 : Real) ≤ Hm + Ac := by linarith
  have hQ1 : (1 : Real) ≤ (1 + Λ) ^ 2 := by nlinarith [sq_nonneg Λ]
  have hQnn : (0 : Real) ≤ (1 + Λ) ^ 2 := sq_nonneg _
  have hQ'nn : (0 : Real) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) :=
    mul_nonneg (mul_nonneg hQnn hSBnn) hWnn
  have hprod1 : Ac * B₃ ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by
    have h1 : Ac * B₃ ≤ (Hm + Ac) * (B₁ + B₃) :=
      mul_le_mul (by linarith) (by linarith) hB₃ hWnn
    have h2 : (Hm + Ac) * (B₁ + B₃) ≤
        (1 + Λ) ^ 2 * ((Hm + Ac) * (B₁ + B₃)) :=
      le_mul_of_one_le_left (mul_nonneg hWnn hSBnn) hQ1
    have h3 : (1 + Λ) ^ 2 * ((Hm + Ac) * (B₁ + B₃)) =
        (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by ring
    linarith [h3 ▸ h2]
  have hprod2 : Λ ^ 2 * (B₁ * Hm) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by
    have hΛ2 : Λ ^ 2 ≤ (1 + Λ) ^ 2 := by nlinarith
    have h1 : B₁ * Hm ≤ (B₁ + B₃) * (Hm + Ac) :=
      mul_le_mul (by linarith) (by linarith) hHm hSBnn
    have h2 : Λ ^ 2 * (B₁ * Hm) ≤ Λ ^ 2 * ((B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg Λ)
    have h3 : Λ ^ 2 * ((B₁ + B₃) * (Hm + Ac)) ≤
        (1 + Λ) ^ 2 * ((B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_right hΛ2 (mul_nonneg hSBnn hWnn)
    have h4 : (1 + Λ) ^ 2 * ((B₁ + B₃) * (Hm + Ac)) =
        (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by ring
    linarith [h4 ▸ h3]
  have hfl : 8 * n ^ 3 * Ac * R2 ≤ 8 * n ^ 3 * Ac * B₃ :=
    mul_le_mul_of_nonneg_left hR2B (by positivity)
  have hb1 : E1 ≤ 20 * (n ^ 5 * P) + 80 * (n ^ 3 * (Ac * B₃)) := by linarith
  have hb2 : E2 ≤ 10 * (Λ ^ 2 * (B₁ * Hm)) := by
    have hc1 : Λ ^ 2 * L2 ≤ Λ ^ 2 * (10 * B₁) := mul_le_mul_of_nonneg_left hL2B (sq_nonneg Λ)
    have hc2 : Hm * L1 ≤ Hm * (Λ ^ 2 * (10 * B₁)) :=
      mul_le_mul_of_nonneg_left (le_trans hL1 hc1) hHm
    linarith
  have hac : (0 : Real) ≤ Ac * B₃ := mul_nonneg hAc hB₃
  have hs1 : 40 * (n ^ 5 * P) ≤ 200 * ((n ^ 6 + 1) * P) := by
    have h1 : n ^ 5 * P ≤ (n ^ 6 + 1) * P := mul_le_mul_of_nonneg_right hp5 hP
    have h2 : (0 : Real) ≤ (n ^ 6 + 1) * P := mul_nonneg hKnn hP
    linarith
  have hs2 : 160 * (n ^ 3 * (Ac * B₃)) ≤
      160 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by
    have h1 : n ^ 3 * (Ac * B₃) ≤ (n ^ 6 + 1) * (Ac * B₃) :=
      mul_le_mul_of_nonneg_right hp3 hac
    have h2 : (n ^ 6 + 1) * (Ac * B₃) ≤
        (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_left hprod1 hKnn
    linarith
  have hs3 : 20 * (Λ ^ 2 * (B₁ * Hm)) ≤
      40 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by
    have h1 : Λ ^ 2 * (B₁ * Hm) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := hprod2
    have h2 : (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) ≤
        (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      le_mul_of_one_le_left hQ'nn hK1
    have h3 : (0 : Real) ≤ (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      mul_nonneg hKnn hQ'nn
    linarith
  have hexp : 200 * (n ^ 6 + 1) *
        (P + (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) =
      200 * ((n ^ 6 + 1) * P) +
        200 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by ring
  rw [hexp]
  linarith

omit [SigmaCompactSpace M] [T2Space M] in
private theorem normSq0S_sub_le (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S (I := I) g x s (A - B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have hAB : A - B = A + (-1 : Real) • B := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hAB]
  refine (normSq0S_add_le (I := I) g x s A _).trans ?_
  rw [normSq0S_smul]
  norm_num

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceDot_le_speed
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (t : Real) (x : M) {Λric : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric) :
    normSq0S (I := I) (g₁ t) x 3 (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x +
        2 * normSq0S (I := I) (g₁ t) x 3
          (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) := by
  have hdef : connectionDifferenceDot (I := I) g₁ g₂ Adot t x =
      (-2 : Real) • lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
          (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
            (metricCov (I := I) (g₂ t)) x) +
        lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) := rfl
  rw [hdef]
  refine le_trans (normSq0S_add_le (I := I) (g₁ t) x 3 _ _) ?_
  have hsmul : normSq0S (I := I) (g₁ t) x 3
      ((-2 : Real) • lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x)) =
      4 * normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
          (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
            (metricCov (I := I) (g₂ t)) x)) := by
    rw [normSq0S_smul]; norm_num
  rw [hsmul]
  have hreact : normSq0S (I := I) (g₁ t) x 3
      (lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x)) ≤
      Λric * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := by
    refine le_trans (lowerBilin_normSq_le (I := I) (g₁ t) x _ _) ?_
    rw [connectionDifferenceSq_def, connectionDifferenceLow_eq_lower]
    exact mul_le_mul_of_nonneg_right hΛric (normSq0S_nonneg (I := I) (g₁ t) x 3 _)
  linarith

omit [SigmaCompactSpace M] in
theorem connSpeedRHS_self (g₁ g₂ : Real → SmoothRiemannianMetric I M) {t : Real} (x : M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (hg : g₁ t = g₂ t) (Λ B₁ B₃ : Real) :
    200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₃) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x)) = 0 := by
  have hzero : ∀ s : Nat,
      normSq0S (I := I) (g₂ t) x s
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) = 0 :=
    fun s => ((tensor0SMetricData (I := I) (g₂ t) x s).inner_self_eq_zero_iff 0).2 rfl
  rw [hg] at hS ⊢
  rw [nablaRmDiffSq_self (I := I) (g₂ t) S hS x, metricDiffSq_def, connectionDifferenceSq_def,
    metricDiffAt_self, connectionDifferenceLowAt_self, hzero, hzero]
  ring

omit [SigmaCompactSpace M] in
theorem connSpeedLow_normSq_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (gInv₁ gInv₂ : Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (hgInv₁ : MetricInverseInBasisGen (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₁ t x i j))
    (hgInv₂ : MetricInverseInBasisGen (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₂ t x i j))
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hNR₁ : ∀ d a b : Idx, nablaRic₁ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₁ t) Ric₁ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hNR₂ : ∀ d a b : Idx, nablaRic₂ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₂ t) Ric₂ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k -
          christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    {Λ B₁ B₃ : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃) :
    normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) ≤
      200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₃) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x)) := by
  classical
  rw [connSpeedLow_eq (I := I) g₁ g₂ frame hframe hu hx Adot hA
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k)
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) hΓ]
  refine le_trans (normSq0S_sub_le (I := I) (g₁ t) x 3 _ _) ?_
  have hT₁ : lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
      (bilinOfComp (I := I) (hframe.toBasisAt hx)
        (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k)) =
      hamiltonConnectionDifferenceCombination (I := I) (metricNabla0S (I := I) (g₁ t) Ric₁ x) :=
    lower_connection_difference_eq_hamilton_combination (I := I) (g₁ t) (hframe.toBasisAt hx) (fun i j => gInv₁ t x i j) hgInv₁
      (metricNabla0S (I := I) (g₁ t) Ric₁ x) (fun d a c => nablaRic₁ t x d a c) hNR₁
  have hT₂ : lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
      (bilinOfComp (I := I) (hframe.toBasisAt hx)
        (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k)) =
      hamiltonConnectionDifferenceCombination (I := I) (metricNabla0S (I := I) (g₂ t) Ric₂ x) :=
    lower_connection_difference_eq_hamilton_combination (I := I) (g₂ t) (hframe.toBasisAt hx) (fun i j => gInv₂ t x i j) hgInv₂
      (metricNabla0S (I := I) (g₂ t) Ric₂ x) (fun d a c => nablaRic₂ t x d a c) hNR₂
  rw [hT₁, hT₂, hamiltonConnectionDifferenceCombination_sub]
  have hham := hamiltonConnectionDifferenceCombination_norm_sq_le (I := I) (g₁ t)
    (metricNabla0S (I := I) (g₁ t) Ric₁ x - metricNabla0S (I := I) (g₂ t) Ric₂ x)
  have hpt : metricNabla0S (I := I) (g₁ t) Ric₁ x - metricNabla0S (I := I) (g₂ t) Ric₂ x =
      (metricNabla0S (I := I) (g₁ t) Ric₁ - metricNabla0S (I := I) (g₂ t) Ric₂) x := rfl
  rw [hpt] at hham
  have hsplit := nablaRicDiff_le (I := I) (g₁ t) (g₂ t) Ric₁ Ric₂ x
  have hd1 := lowerBilin_normSq_le (I := I) (g₁ t) x
    (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
    (bilinOfComp (I := I) (hframe.toBasisAt hx)
      (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k))
  have hd2 := lowerBilin_metric_le (I := I) (g₁ t) (g₂ t) x hΛ
    (bilinOfComp (I := I) (hframe.toBasisAt hx)
      (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k))
  have hd3 : normSq0S (I := I) (g₁ t) x 3
      (lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
        (bilinOfComp (I := I) (hframe.toBasisAt hx)
          (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k)))
      ≤ 10 * B₁ := by
    rw [hT₂]
    exact le_trans (hamiltonConnectionDifferenceCombination_norm_sq_le (I := I) (g₁ t) _) (by linarith)
  rw [← metricDiffSq_def (I := I) (g₁ t) (g₂ t) x] at hd1
  have htrace := nablaRicDiff_trace_le (I := I) (g₁ t) (g₂ t) S hS Ric₁ Ric₂ hRic₁ hRic₂ x
  have hnnn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  have hpow : ∀ a : ℕ, a ≤ 6 →
      (Module.finrank Real E : Real) ^ a ≤ (Module.finrank Real E : Real) ^ 6 + 1 := by
    intro a ha
    rcases Nat.eq_zero_or_pos (Module.finrank Real E) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero]
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · rw [ha0]; norm_num
      · rw [zero_pow (by omega : a ≠ 0)]; norm_num
    · have hn1 : (1 : Real) ≤ (Module.finrank Real E : Real) := by exact_mod_cast hpos
      have := pow_le_pow_right₀ hn1 ha
      linarith
  exact connSpeed_arith hnnn (nablaRmDiffSq_nonneg (I := I) (g₁ t) S x)
    (normSq0S_nonneg (I := I) (g₁ t) x 2 _) (normSq0S_nonneg (I := I) (g₁ t) x 3 _)
    (le_trans (normSq0S_nonneg (I := I) (g₁ t) x 3 _) hB₁)
    (le_trans (normSq0S_nonneg (I := I) (g₁ t) x 2 _) hB₃) hΛ0
    hham hsplit htrace hB₃ hd1 hd2 hd3 (hpow 5 (by norm_num)) (hpow 3 (by norm_num))

omit [SigmaCompactSpace M] in
theorem connectionDifferenceDot_normSq_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (gInv₁ gInv₂ : Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (hgInv₁ : MetricInverseInBasisGen (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₁ t x i j))
    (hgInv₂ : MetricInverseInBasisGen (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₂ t x i j))
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hNR₁ : ∀ d a b : Idx, nablaRic₁ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₁ t) Ric₁ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hNR₂ : ∀ d a b : Idx, nablaRic₂ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₂ t) Ric₂ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k -
          christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    {Λric Λ B₁ B₃ : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃) :
    normSq0S (I := I) (g₁ t) x 3 (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x +
        2 * (200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
          (nablaRmDiffSq (I := I) (g₁ t) S x +
            (1 + Λ) ^ 2 * (B₁ + B₃) *
              (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
                connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x))) := by
  refine le_trans (connectionDifferenceDot_le_speed (I := I) g₁ g₂ Adot t x hΛric) ?_
  have h := connSpeedLow_normSq_le (I := I) g₁ g₂ Adot frame hframe hu hx S hS
    Ric₁ Ric₂ hRic₁ hRic₂ gInv₁ gInv₂ hgInv₁ hgInv₂ nablaRic₁ nablaRic₂
    hNR₁ hNR₂ hΓ hA hΛ0 hΛ hB₁ hB₃
  linarith

end MainBound

end DifferentialGeometry.PDE.RicciFlow

end
