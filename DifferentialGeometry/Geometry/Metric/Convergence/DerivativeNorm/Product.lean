import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ProductLeibniz
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.Coordinates.ComponentNorm
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Components
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow (iterCov_realizes)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M]

omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem covStep_domDomCongr [FiniteDimensional Real E] {s s' : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s'
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv e)
        (covStep (I := I) gRef s Z) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, totalNabla0SFun_domDomCongr]
  rfl

omit [Module.Finite ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [I.Boundaryless] in
theorem totalNabla0SRealizes_unique {s : ℕ}
    [FiniteDimensional Real E]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {n1 n2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n1)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n2) :
    n1 = n2 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext (I := I) (s + 1) x (fun v => ?_)
  obtain ⟨X, hX⟩ :
      ∃ X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _), X x = v 0 :=
    ⟨(ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose,
      (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose_spec⟩
  have hcons : Fin.cons (X x) (Fin.tail v) = v := by rw [hX]; exact Fin.cons_self_tail v
  have e1 := h1 X x (Fin.tail v)
  have e2 := h2 X x (Fin.tail v)
  rw [hcons] at e1 e2
  rw [e1, e2]

def shiftEquiv (r : ℕ) : (m : ℕ) → Fin ((r + 1) + m) ≃ Fin (r + (m + 1))
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (shiftEquiv r m)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_shift [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (m : ℕ) :
    iterCov (I := I) gRef r T (m + 1) =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (shiftEquiv r m)
        (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m) := by
  induction m with
  | zero =>
      simp only [shiftEquiv]
      rfl
  | succ m ih =>
      simp only [shiftEquiv]
      rw [iterCov_succ, ih, covStep_domDomCongr, ← iterCov_succ]

def frontExtendIter {s s' : ℕ} (e : Fin s ≃ Fin s') : (m : ℕ) → Fin (s + m) ≃ Fin (s' + m)
  | 0 => e
  | (m + 1) => frontExtendEquiv (frontExtendIter e m)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_domDomCongr [FiniteDimensional Real E] {s s' : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (e : Fin s ≃ Fin s')
    (Y : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (m : ℕ) :
    iterCov (I := I) gRef s'
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Y) m =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendIter e m)
        (iterCov (I := I) gRef s Y m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [frontExtendIter]
      rw [iterCov_succ, ih, covStep_domDomCongr, ← iterCov_succ]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem normSq0S_iterCov_domDomCongr [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {s s' : ℕ} (e : Fin s ≃ Fin s')
    (Y : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (m : ℕ) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    normSq0S (I := I) gRef x (s' + m)
        (iterCov (I := I) gRef s'
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Y) m x) =
      normSq0S (I := I) gRef x (s + m) (iterCov (I := I) gRef s Y m x) := by
  rw [iterCov_domDomCongr]
  change normSq0S (I := I) gRef x (s' + m)
      (ContinuousMultilinearMap.domDomCongr (frontExtendIter e m)
        ((iterCov (I := I) gRef s Y m) x)) = _
  exact normSq0S_domDomCongr (I := I) gRef x basis hinv (frontExtendIter e m)
    (iterCov (I := I) gRef s Y m x)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem normSq0S_iterCov_shift [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (m : ℕ) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    normSq0S (I := I) gRef x (r + (m + 1)) (iterCov (I := I) gRef r T (m + 1) x) =
      normSq0S (I := I) gRef x ((r + 1) + m)
        (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m x) := by
  rw [iterCov_shift]
  change normSq0S (I := I) gRef x (r + (m + 1))
      (ContinuousMultilinearMap.domDomCongr (shiftEquiv r m)
        ((iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m) x)) = _
  exact normSq0S_domDomCongr (I := I) gRef x basis hinv (shiftEquiv r m)
    (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m x)

omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_one [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) :
    iterCov (I := I) gRef r T 1 = covStep (I := I) gRef r T := rfl

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_product_one [FiniteDimensional Real E] {s q : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    iterCov (I := I) gRef (s + q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) 1 =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (iterCov (I := I) gRef s A 1) B)
        + Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A (iterCov (I := I) gRef q B 1)) :=
  totalNabla0SRealizes_unique
    (iterCov_realizes (I := I) gRef
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) 0)
    (nabla0S_product_realizes
      (leviCivitaConnectionOfMetric (I := I) gRef) A B
      (iterCov (I := I) gRef s A 1) (iterCov (I := I) gRef q B 1)
      (iterCov_realizes (I := I) gRef A 0) (iterCov_realizes (I := I) gRef B 0))

omit [Module.Finite ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [IsManifold I 2 M] in
theorem sqrt_normSq0S_add_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {s : ℕ} {x : M}
    (u v : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    Real.sqrt (normSq0S (I := I) gRef x s (u + v)) ≤
      Real.sqrt (normSq0S (I := I) gRef x s u) + Real.sqrt (normSq0S (I := I) gRef x s v) := by
  rw [normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv]
  simp only [component0S_add]
  exact DifferentialGeometry.PDE.RicciFlow.compL2_add_le
    (component0S (I := I) basis u) (component0S (I := I) basis v)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_product_sqrtNormSq_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) gRef x basis (identityInvMetric (Idx := Idx)))
    (m : ℕ) : ∀ {s q : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q),
    Real.sqrt (normSq0S (I := I) gRef x ((s + q) + m)
        (iterCov (I := I) gRef (s + q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) m x)) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
        Real.sqrt (normSq0S (I := I) gRef x (q + (m - c))
          (iterCov (I := I) gRef q B (m - c) x)) := by
  induction m with
  | zero =>
      intro s q A B
      rw [Finset.sum_range_one]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.add_zero]
      have hnn : 0 ≤ normSq0S (I := I) gRef x s (A x) := by
        rw [normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      change Real.sqrt (normSq0S (I := I) gRef x (s + q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)) ≤
        Real.sqrt (normSq0S (I := I) gRef x s (A x)) *
          Real.sqrt (normSq0S (I := I) gRef x q (B x))
      rw [normSq0S_product (I := I) gRef x basis hinv A B, Real.sqrt_mul hnn]
  | succ m ih =>
      intro s q A B
      have hL : Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
          (iterCov (I := I) gRef (s + q + 1)
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (iterCov (I := I) gRef s A 1) B)) m x)) ≤
          ∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) *
            Real.sqrt (normSq0S (I := I) gRef x (s + (c + 1)) (iterCov (I := I) gRef s A (c + 1) x))
              *
            Real.sqrt (normSq0S (I := I) gRef x (q + (m - c))
              (iterCov (I := I) gRef q B (m - c) x)) := by
        rw [normSq0S_iterCov_domDomCongr (I := I) gRef (leibnizLeftEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (iterCov (I := I) gRef s A 1) B) m x basis hinv]
        refine le_trans (ih (iterCov (I := I) gRef s A 1) B) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [normSq0S_iterCov_shift (I := I) gRef A c x basis hinv, iterCov_one]
      have hR : Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
          (iterCov (I := I) gRef (s + q + 1)
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                A (iterCov (I := I) gRef q B 1))) m x)) ≤
          ∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) *
            Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
            Real.sqrt (normSq0S (I := I) gRef x (q + (m - c + 1))
              (iterCov (I := I) gRef q B (m - c + 1) x)) := by
        rw [normSq0S_iterCov_domDomCongr (I := I) gRef (leibnizRightEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            A (iterCov (I := I) gRef q B 1)) m x basis hinv]
        refine le_trans (ih A (iterCov (I := I) gRef q B 1)) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [normSq0S_iterCov_shift (I := I) gRef B (m - c) x basis hinv, iterCov_one]
      calc Real.sqrt (normSq0S (I := I) gRef x ((s + q) + (m + 1))
              (iterCov (I := I) gRef (s + q)
                (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) (m + 1) x))
          = Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
              (iterCov (I := I) gRef (s + q + 1)
                (iterCov (I := I) gRef (s + q)
                  (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) 1) m
                      x)) := by
            rw [normSq0S_iterCov_shift (I := I) gRef
              (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) m x basis hinv,
              ← iterCov_one]
        _ ≤ Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
                (iterCov (I := I) gRef (s + q + 1)
                  (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
                    (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                      (iterCov (I := I) gRef s A 1) B)) m x)) +
              Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
                (iterCov (I := I) gRef (s + q + 1)
                  (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
                    (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                      A (iterCov (I := I) gRef q B 1))) m x)) := by
            rw [iterCov_product_one (I := I) gRef A B, iterCov_add]
            exact sqrt_normSq0S_add_le (I := I) gRef _ _ basis hinv
        _ ≤ _ := add_le_add hL hR
        _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : ℝ) *
              (Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c))
                (iterCov (I := I) gRef q B (m + 1 - c) x))) := by
            rw [← pascal_sum m (fun c => Real.sqrt (normSq0S (I := I) gRef x (s + c)
                (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c))
                (iterCov (I := I) gRef q B (m + 1 - c) x)))]
            congr 1
            · refine Finset.sum_congr rfl fun c hc => ?_
              have : m + 1 - (c + 1) = m - c := by omega
              rw [this]; ring
            · refine Finset.sum_congr rfl fun c hc => ?_
              have : m - c + 1 = m + 1 - c := by
                simp only [Finset.mem_range] at hc; omega
              rw [this]; ring
        _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : ℝ) *
              Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c))
                (iterCov (I := I) gRef q B (m + 1 - c) x)) :=
            Finset.sum_congr rfl fun c _ => by ring

omit [Module.Finite ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [IsManifold I 2 M] in
theorem smulByFun_eq_product [FiniteDimensional Real E] {q : ℕ}
    (φ : M → Real) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) φ hφ B =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (finCongr (Nat.zero_add q))
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) φ hφ) B) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext (I := I) q x (fun v => ?_)
  have he : ∀ i : Fin q, finCongr (Nat.zero_add q) (Fin.natAdd 0 i) = i := by
    intro i
    ext
    simp
  rw [tensor0SField_smulByFun_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hscalar :
      (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) φ hφ x)
          ((fun i => v (finCongr (Nat.zero_add q) i)) ∘ Fin.castAdd q) = φ x := by
    rw [Tensor0SField.fromScalarField_apply]
  rw [hscalar]
  congr 1
  refine congrArg (B x) (funext fun i => ?_)
  change v i = v (finCongr (Nat.zero_add q) (Fin.natAdd 0 i))
  exact (congrArg v (he i)).symm

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_smulF_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) gRef x basis (identityInvMetric (Idx := Idx)))
    (m : ℕ) {q : ℕ} (φ : M → Real) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    Real.sqrt (normSq0S (I := I) gRef x (q + m)
        (iterCov (I := I) gRef q
          (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) φ hφ B) m x)) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        Real.sqrt (normSq0S (I := I) gRef x (0 + c)
          (iterCov (I := I) gRef 0
            (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (∞ : WithTop ℕ∞) φ hφ) c x)) *
        Real.sqrt (normSq0S (I := I) gRef x (q + (m - c))
          (iterCov (I := I) gRef q B (m - c) x)) := by
  rw [smulByFun_eq_product (I := I) φ hφ B,
    normSq0S_iterCov_domDomCongr (I := I) gRef (finCongr (Nat.zero_add q))
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) φ hφ) B) m x basis hinv]
  exact iterCov_product_sqrtNormSq_le (I := I) gRef x basis hinv m
    (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) φ hφ) B

end HCGCompactness
end DifferentialGeometry
