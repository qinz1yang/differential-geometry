import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ProductLeibniz
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Weighted control of iterated covariant derivatives

Chapter 7, surface lemma U1, route (a), step a5.2 (iii) (lane U1C2; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, review 18 §2).

For a family of metrics `g t`, a weight `ρ t ≥ 0`, a time set `J` and a control family
`U : ℕ → ℝ → M → ℝ`, `IterCovCtl g ρ J U w m A` says that every iterated covariant derivative of
the field family `A t` obeys `ρ^(w + p) |∇^p A|² ≤ K_p U (m + p)` on `J`. The weight `w` counts
the parabolic scaling and `m` the number of derivatives of the controlling quantity. The class is
closed under
* `covStep` (`IterCovCtl.cov`), sums, differences, constant multiples, finite sums;
* slot permutations (`IterCovCtl.domDomCongr`, via `covStep_domDomCongr_frontExtend`);
* tensor products with a factor controlled by the constant family `1`
  (`IterCovCtl.product`, via the Leibniz rule `covStep_product`);
* the metric trace of the first two slots (`IterCovCtl.trace`, via `covStep_metricTrace`);
* multiplication by time-dependent scalars `a t` with `|a t| ρ t ≤ L`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local notation "TF " k => Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
  (n := (∞ : WithTop ℕ∞)) k

def IterCovCtl (g : ℝ → SmoothRiemannianMetric I M) (ρ : ℝ → ℝ) (J : Set ℝ)
    (U : ℕ → ℝ → M → ℝ) (w m : ℕ) {k : ℕ} (A : ℝ → TF k) : Prop :=
  ∀ p : ℕ, ∃ K : ℝ, ∀ t ∈ J, ∀ x : M,
    ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x) ≤ K * U (m + p) t x

theorem covStep_heq (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b) {A : TF a}
    {B : TF b} (hAB : HEq A B) : HEq (covStep g a A) (covStep g b B) := by
  subst h
  cases hAB
  rfl

theorem iterCov_covStep_heq (g : SmoothRiemannianMetric I M) {k : ℕ} (A : TF k) :
    ∀ p : ℕ, HEq (iterCov g (k + 1) (covStep g k A) p) (iterCov g k A (p + 1))
  | 0 => HEq.rfl
  | p + 1 => covStep_heq g (by omega) (iterCov_covStep_heq g A p)

omit [T2Space M] in
theorem normSq0S_heq (g : SmoothRiemannianMetric I M) (x : M) {a b : ℕ} (h : a = b) {A : TF a}
    {B : TF b} (hAB : HEq A B) : normSq0S g x a (A x) = normSq0S g x b (B x) := by
  subst h
  cases hAB
  rfl

theorem normSq0S_iterCov_covStep (g : SmoothRiemannianMetric I M) (x : M) {k : ℕ} (A : TF k)
    (p : ℕ) : normSq0S g x (k + 1 + p) (iterCov g (k + 1) (covStep g k A) p x) =
      normSq0S g x (k + (p + 1)) (iterCov g k A (p + 1) x) :=
  normSq0S_heq g x (by omega) (iterCov_covStep_heq g A p)

theorem iterCov_const_smul (g : SmoothRiemannianMetric I M) {k : ℕ} (c : ℝ) (A : TF k) :
    ∀ p : ℕ, iterCov g k (c • A) p = c • iterCov g k A p
  | 0 => rfl
  | p + 1 => by rw [iterCov_succ, iterCov_succ, iterCov_const_smul g c A p, covStep_smul]

theorem iterCov_zero_field (g : SmoothRiemannianMetric I M) {k : ℕ} :
    ∀ p : ℕ, iterCov g k (0 : TF k) p = 0
  | 0 => rfl
  | p + 1 => by rw [iterCov_succ, iterCov_zero_field g p, covStep_zero]

omit [T2Space M] in
theorem normSq0S_smul' (g : SmoothRiemannianMetric I M) (x : M) {s : ℕ} (c : ℝ)
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S g x s (c • A) = c ^ 2 * normSq0S g x s A := by
  simp only [normSq0S_eq_inner]
  rw [inner0S_smul_left, inner0S_smul_right]
  ring

theorem covStep_domDomCongr_frontExtend (g : SmoothRiemannianMetric I M) {s s' : ℕ}
    (e : Fin s ≃ Fin s') (Z : TF s) :
    covStep g s' (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv e) (covStep g s Z) := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [covStep_apply, Tensor0SField.domDomCongr_apply, covStep_apply,
    totalNabla0SFun_domDomCongr]

def iterFrontExtend {s s' : ℕ} (e : Fin s ≃ Fin s') : (p : ℕ) → (Fin (s + p) ≃ Fin (s' + p))
  | 0 => e
  | p + 1 => frontExtendEquiv (iterFrontExtend e p)

theorem iterCov_domDomCongr_iterFrontExtend (g : SmoothRiemannianMetric I M) {s s' : ℕ}
    (e : Fin s ≃ Fin s') (Z : TF s) :
    ∀ p : ℕ, iterCov g s' (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) p =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (iterFrontExtend e p) (iterCov g s Z p)
  | 0 => rfl
  | p + 1 => by
    rw [iterCov_succ, iterCov_succ, iterCov_domDomCongr_iterFrontExtend g e Z p,
      covStep_domDomCongr_frontExtend]
    rfl

omit [T2Space M] in
theorem normSq0S_domDomCongr' (g : SmoothRiemannianMetric I M) (x : M) {s s' : ℕ}
    (e : Fin s ≃ Fin s')
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S g x s' (A.domDomCongr e) = normSq0S g x s A := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  exact normSq0S_domDomCongr g x b (metricInverseInBasis_of_orthonormal g b hb) e A

omit [T2Space M] in
theorem normSq0S_product' (g : SmoothRiemannianMetric I M) (x : M) {s q : ℕ} (A : TF s)
    (B : TF q) :
    normSq0S g x (s + q) (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x) =
      normSq0S g x s (A x) * normSq0S g x q (B x) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  exact normSq0S_product g x b (metricInverseInBasis_of_orthonormal g b hb) A B

theorem covStep_product (g : SmoothRiemannianMetric I M) {s q : ℕ} (A : TF s) (B : TF q) :
    covStep g (s + q) (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (covStep g s A) B) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A (covStep g q B)) :=
  totalNabla0SRealizes_unique (iterCov_realizes g (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) 0)
    (nabla0S_product_realizes _ A B _ _ (iterCov_realizes g A 0) (iterCov_realizes g B 0))

def traceShiftEquiv (s : ℕ) : Fin (s + 2 + 1) ≃ Fin (s + 1 + 2) :=
  (Equiv.swap (0 : Fin (s + 2 + 1)) (Fin.succ 0)).trans
    (Equiv.swap (Fin.succ (0 : Fin (s + 2))) (Fin.succ (Fin.succ (0 : Fin (s + 1)))))

theorem traceShiftEquiv_comp {α : Type*} {s : ℕ} (X Y Z : α) (tail : Fin s → α) :
    (Fin.cons Y (Fin.cons Z (Fin.cons X tail)) : Fin (s + 1 + 2) → α) ∘ traceShiftEquiv s =
      Fin.cons X (Fin.cons Y (Fin.cons Z tail)) := by
  have h01 : (0 : Fin (s + 2 + 1)) ≠ Fin.succ 0 := (Fin.succ_ne_zero _).symm
  have h02 : (0 : Fin (s + 2 + 1)) ≠ Fin.succ (Fin.succ (0 : Fin (s + 1))) :=
    (Fin.succ_ne_zero _).symm
  have h12 : (Fin.succ (0 : Fin (s + 2)) : Fin (s + 2 + 1)) ≠
      Fin.succ (Fin.succ (0 : Fin (s + 1))) := fun h =>
    Fin.succ_ne_zero (0 : Fin (s + 1)) (Fin.succ_injective _ h).symm
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · simp only [Function.comp_apply, traceShiftEquiv, Equiv.trans_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_left]
    rfl
  · simp only [Function.comp_apply, traceShiftEquiv, Equiv.trans_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne h01 h02]
    rfl
  · simp only [Function.comp_apply, traceShiftEquiv, Equiv.trans_apply,
      Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm, Equiv.swap_apply_right]
    rfl
  · have h0 : (i.succ.succ.succ : Fin (s + 2 + 1)) ≠ 0 := Fin.succ_ne_zero _
    have h1 : (i.succ.succ.succ : Fin (s + 2 + 1)) ≠ Fin.succ 0 := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    have h2 : (i.succ.succ.succ : Fin (s + 2 + 1)) ≠ Fin.succ (Fin.succ (0 : Fin (s + 1))) :=
      fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ (Fin.succ_injective _ h))
    simp only [Function.comp_apply, traceShiftEquiv, Equiv.trans_apply,
      Equiv.swap_apply_of_ne_of_ne h0 h1, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rfl

theorem covStep_metricTrace (g : SmoothRiemannianMetric I M) {s : ℕ} (C : TF (s + 2)) :
    covStep g s (metricTraceFirstTwoField g C) =
      metricTraceFirstTwoField g (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceShiftEquiv s)
        (covStep g (s + 2) C)) := by
  classical
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext (s + 1) x fun v => ?_
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  rw [← Fin.cons_self_tail v, covStep_apply,
    nabla_metricTraceFirstTwo0S _ g (leviCivitaConnectionOfMetric_isMetricCompatible g) C b _ hinv,
    metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis g b _ hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply, covStep_apply]
  congr 2
  have h := traceShiftEquiv_comp (v 0) (b i) (b j) (Fin.tail v)
  simp only [metricTraceInput]
  exact (congrFun h ·) |> funext |>.symm ▸ rfl

theorem iterCov_metricTrace (g : SmoothRiemannianMetric I M) {s : ℕ} (C : TF (s + 2)) :
    ∀ p : ℕ, ∃ σ : Fin (s + 2 + p) ≃ Fin (s + p + 2),
      iterCov g s (metricTraceFirstTwoField g C) p =
        metricTraceFirstTwoField g (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
          (iterCov g (s + 2) C p))
  | 0 => ⟨Equiv.refl _, by rw [Tensor0SField.domDomCongr_refl]; rfl⟩
  | p + 1 => by
    obtain ⟨σ, hσ⟩ := iterCov_metricTrace g C p
    refine ⟨(frontExtendEquiv σ).trans (traceShiftEquiv (s + p)), ?_⟩
    rw [iterCov_succ, hσ, covStep_metricTrace, covStep_domDomCongr_frontExtend,
      Tensor0SField.domDomCongr_trans]
    rfl

omit [T2Space M] in
theorem smulByFun_eq_domDomCongr_product {k : ℕ} (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (A : TF k) :
    tensor0SFieldSmulByFun (∞ : WithTop ℕ∞) φ hφ A =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (finCongr (Nat.zero_add k))
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) φ hφ)
          A) := by
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext k x fun v => ?_
  rw [tensor0SField_smulByFun_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply,
    Tensor0SField.fromScalarField_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  congr 2
  funext j
  simp only [Function.comp_apply, finCongr_apply]
  congr 1
  ext
  simp

namespace IterCovCtl

variable {g : ℝ → SmoothRiemannianMetric I M} {ρ : ℝ → ℝ} {J : Set ℝ} {U : ℕ → ℝ → M → ℝ}

theorem cov {w m k : ℕ} {A : ℝ → TF k} (h : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U (w + 1) (m + 1) (fun t => covStep (g t) k (A t)) := by
  intro p
  obtain ⟨K, hK⟩ := h (p + 1)
  refine ⟨K, fun t ht x => ?_⟩
  rw [normSq0S_iterCov_covStep, show w + 1 + p = w + (p + 1) by omega,
    show m + 1 + p = m + (p + 1) by omega]
  exact hK t ht x

theorem add (hρ : ∀ t ∈ J, 0 ≤ ρ t) {w m k : ℕ} {A B : ℝ → TF k}
    (hA : IterCovCtl g ρ J U w m A) (hB : IterCovCtl g ρ J U w m B) :
    IterCovCtl g ρ J U w m (fun t => A t + B t) := by
  intro p
  obtain ⟨K₁, hK₁⟩ := hA p
  obtain ⟨K₂, hK₂⟩ := hB p
  refine ⟨2 * K₁ + 2 * K₂, fun t ht x => ?_⟩
  have hw : 0 ≤ ρ t ^ (w + p) := pow_nonneg (hρ t ht) _
  rw [iterCov_add]
  calc ρ t ^ (w + p) * normSq0S (g t) x (k + p)
        ((iterCov (g t) k (A t) p + iterCov (g t) k (B t) p) x)
      ≤ ρ t ^ (w + p) * (2 * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x) +
          2 * normSq0S (g t) x (k + p) (iterCov (g t) k (B t) p x)) :=
        mul_le_mul_of_nonneg_left (normSq0S_add_le _ _ _ _ _) hw
    _ = 2 * (ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x)) +
          2 * (ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (B t) p x)) := by
        ring
    _ ≤ 2 * (K₁ * U (m + p) t x) + 2 * (K₂ * U (m + p) t x) := by
        linarith [hK₁ t ht x, hK₂ t ht x]
    _ = (2 * K₁ + 2 * K₂) * U (m + p) t x := by ring

theorem sub (hρ : ∀ t ∈ J, 0 ≤ ρ t) {w m k : ℕ} {A B : ℝ → TF k}
    (hA : IterCovCtl g ρ J U w m A) (hB : IterCovCtl g ρ J U w m B) :
    IterCovCtl g ρ J U w m (fun t => A t - B t) := by
  intro p
  obtain ⟨K₁, hK₁⟩ := hA p
  obtain ⟨K₂, hK₂⟩ := hB p
  refine ⟨2 * K₁ + 2 * K₂, fun t ht x => ?_⟩
  have hw : 0 ≤ ρ t ^ (w + p) := pow_nonneg (hρ t ht) _
  rw [iterCov_sub]
  calc ρ t ^ (w + p) * normSq0S (g t) x (k + p)
        ((iterCov (g t) k (A t) p - iterCov (g t) k (B t) p) x)
      ≤ ρ t ^ (w + p) * (2 * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x) +
          2 * normSq0S (g t) x (k + p) (iterCov (g t) k (B t) p x)) :=
        mul_le_mul_of_nonneg_left (normSq0S_sub_le _ _ _ _ _) hw
    _ = 2 * (ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x)) +
          2 * (ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (B t) p x)) := by
        ring
    _ ≤ 2 * (K₁ * U (m + p) t x) + 2 * (K₂ * U (m + p) t x) := by
        linarith [hK₁ t ht x, hK₂ t ht x]
    _ = (2 * K₁ + 2 * K₂) * U (m + p) t x := by ring

theorem smul {w m k : ℕ} {A : ℝ → TF k} (c : ℝ) (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U w m (fun t => c • A t) := by
  intro p
  obtain ⟨K, hK⟩ := hA p
  refine ⟨c ^ 2 * K, fun t ht x => ?_⟩
  rw [iterCov_const_smul, ContMDiffSection.coe_smul, Pi.smul_apply, normSq0S_smul']
  calc ρ t ^ (w + p) * (c ^ 2 * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x))
      = c ^ 2 * (ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x)) := by
        ring
    _ ≤ c ^ 2 * (K * U (m + p) t x) := mul_le_mul_of_nonneg_left (hK t ht x) (sq_nonneg c)
    _ = c ^ 2 * K * U (m + p) t x := by ring

theorem zero {w m k : ℕ} : IterCovCtl g ρ J U w m (fun _ => (0 : TF k)) := by
  intro p
  refine ⟨0, fun t _ x => ?_⟩
  rw [iterCov_zero_field]
  have h0 : normSq0S (g t) x (k + p) ((0 : TF (k + p)) x) = 0 := by
    rw [normSq0S_eq_zero_iff]
    rfl
  rw [h0]
  simp

theorem congr {w m k : ℕ} {A B : ℝ → TF k} (hA : IterCovCtl g ρ J U w m A)
    (h : ∀ t ∈ J, A t = B t) : IterCovCtl g ρ J U w m B := by
  intro p
  obtain ⟨K, hK⟩ := hA p
  exact ⟨K, fun t ht x => by rw [← h t ht]; exact hK t ht x⟩

theorem sum (hρ : ∀ t ∈ J, 0 ≤ ρ t) {w m k : ℕ} {ι : Type*} (s : Finset ι)
    {A : ι → ℝ → TF k} (hA : ∀ i ∈ s, IterCovCtl g ρ J U w m (A i)) :
    IterCovCtl g ρ J U w m (fun t => ∑ i ∈ s, A i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IterCovCtl g ρ J U w m (fun _ => (0 : TF k)))
  | insert a s ha ih =>
    have h1 := hA a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
    refine (add hρ h1 h2).congr fun t _ => ?_
    rw [Finset.sum_insert ha]

theorem mono_m (hU0 : ∀ n t x, 0 ≤ U n t x) (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x)
    {w m m' k : ℕ} {A : ℝ → TF k} (hmm : m ≤ m') (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U w m' A := by
  have hmono : ∀ a b, a ≤ b → ∀ t x, U a t x ≤ U b t x := by
    intro a b hab t x
    induction b with
    | zero => rw [Nat.le_zero.mp hab]
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (hUm b t x)
      · rw [le_antisymm hab hge]
  intro p
  obtain ⟨K, hK⟩ := hA p
  refine ⟨max K 0, fun t ht x => ?_⟩
  calc _ ≤ K * U (m + p) t x := hK t ht x
    _ ≤ max K 0 * U (m + p) t x := mul_le_mul_of_nonneg_right (le_max_left _ _) (hU0 _ _ _)
    _ ≤ max K 0 * U (m' + p) t x :=
        mul_le_mul_of_nonneg_left (hmono _ _ (by omega) t x) (le_max_right _ _)

theorem timeSmul (hρ : ∀ t ∈ J, 0 ≤ ρ t) (hU0 : ∀ n t x, 0 ≤ U n t x) {w m k : ℕ}
    {A : ℝ → TF k} (a : ℝ → ℝ) {L : ℝ}
    (ha : ∀ t ∈ J, |a t| * ρ t ≤ L) (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U (w + 2) m (fun t => a t • A t) := by
  intro p
  obtain ⟨K, hK⟩ := hA p
  refine ⟨L ^ 2 * max K 0, fun t ht x => ?_⟩
  have hw : 0 ≤ ρ t ^ (w + p) := pow_nonneg (hρ t ht) _
  have hn := normSq0S_nonneg (g t) x (k + p) (iterCov (g t) k (A t) p x)
  have hL : (a t * ρ t) ^ 2 ≤ L ^ 2 := by
    rw [← sq_abs, abs_mul, abs_of_nonneg (hρ t ht)]
    exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (hρ t ht)) (ha t ht) 2
  have hK' : ρ t ^ (w + p) * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x) ≤
      max K 0 * U (m + p) t x := by
    exact (hK t ht x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hU0 _ _ _))
  rw [iterCov_const_smul, ContMDiffSection.coe_smul, Pi.smul_apply, normSq0S_smul',
    show w + 2 + p = (w + p) + 2 by omega, pow_add]
  calc ρ t ^ (w + p) * ρ t ^ 2 * (a t ^ 2 * normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x))
      = (a t * ρ t) ^ 2 * (ρ t ^ (w + p) *
          normSq0S (g t) x (k + p) (iterCov (g t) k (A t) p x)) := by ring
    _ ≤ L ^ 2 * (max K 0 * U (m + p) t x) :=
        mul_le_mul hL hK' (mul_nonneg hw hn) (sq_nonneg L)
    _ = L ^ 2 * max K 0 * U (m + p) t x := by ring

theorem domDomCongr {w m s s' : ℕ} {A : ℝ → TF s} (e : Fin s ≃ Fin s')
    (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U w m (fun t => Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e (A t)) := by
  intro p
  obtain ⟨K, hK⟩ := hA p
  refine ⟨K, fun t ht x => ?_⟩
  rw [iterCov_domDomCongr_iterFrontExtend, Tensor0SField.domDomCongr_apply, normSq0S_domDomCongr']
  exact hK t ht x

theorem trace (hρ : ∀ t ∈ J, 0 ≤ ρ t) {w m s : ℕ} {A : ℝ → TF (s + 2)}
    (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U w m (fun t => metricTraceFirstTwoField (g t) (A t)) := by
  intro p
  obtain ⟨K, hK⟩ := hA p
  refine ⟨(Module.finrank ℝ E : ℝ) ^ (s + p + 2) * K, fun t ht x => ?_⟩
  obtain ⟨σ, hσ⟩ := iterCov_metricTrace (g t) (A t) p
  have hw : 0 ≤ ρ t ^ (w + p) := pow_nonneg (hρ t ht) _
  have hN : 0 ≤ (Module.finrank ℝ E : ℝ) ^ (s + p + 2) := pow_nonneg (Nat.cast_nonneg _) _
  rw [hσ, metricTraceFirstTwoField_apply]
  have htr := trace_normSq_rank_le (g t)
    ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ (iterCov (g t) (s + 2) (A t) p)) x)
  rw [Tensor0SField.domDomCongr_apply, normSq0S_domDomCongr'] at htr
  calc ρ t ^ (w + p) * normSq0S (g t) x (s + p) (metricTraceFirstTwo0STensor (g t)
        ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ (iterCov (g t) (s + 2) (A t) p)) x))
      ≤ ρ t ^ (w + p) * ((Module.finrank ℝ E : ℝ) ^ (s + p + 2) *
          normSq0S (g t) x (s + 2 + p) (iterCov (g t) (s + 2) (A t) p x)) :=
        mul_le_mul_of_nonneg_left htr hw
    _ = (Module.finrank ℝ E : ℝ) ^ (s + p + 2) *
          (ρ t ^ (w + p) * normSq0S (g t) x (s + 2 + p) (iterCov (g t) (s + 2) (A t) p x)) := by
        ring
    _ ≤ (Module.finrank ℝ E : ℝ) ^ (s + p + 2) * (K * U (m + p) t x) :=
        mul_le_mul_of_nonneg_left (hK t ht x) hN
    _ = _ := by ring

theorem one_m {w m m' k : ℕ} {A : ℝ → TF k}
    (hA : IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) w m A) :
    IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) w m' A := fun p => hA p

private theorem product_aux (hρ : ∀ t ∈ J, 0 ≤ ρ t) (hU0 : ∀ n t x, 0 ≤ U n t x)
    (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x) :
    ∀ p : ℕ, ∀ {c w m c₀ k : ℕ} (P : ℝ → TF c₀) (A : ℝ → TF k),
      IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) c 0 P → IterCovCtl g ρ J U w m A →
      ∃ K : ℝ, ∀ t ∈ J, ∀ x : M, ρ t ^ (c + w + p) * normSq0S (g t) x (c₀ + k + p)
        (iterCov (g t) (c₀ + k) (tensor0SFieldProduct (∞ : WithTop ℕ∞) (P t) (A t)) p x) ≤
          K * U (m + p) t x := by
  intro p
  induction p with
  | zero =>
    intro c w m c₀ k P A hP hA
    obtain ⟨K₁, hK₁⟩ := hP 0
    obtain ⟨K₂, hK₂⟩ := hA 0
    refine ⟨max K₁ 0 * K₂, fun t ht x => ?_⟩
    have h1 := hK₁ t ht x
    have h2 := hK₂ t ht x
    simp only [Nat.add_zero, mul_one] at h1 h2
    change ρ t ^ (c + w) * normSq0S (g t) x (c₀ + k)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (P t) (A t) x) ≤ max K₁ 0 * K₂ * U m t x
    change ρ t ^ c * normSq0S (g t) x c₀ (P t x) ≤ K₁ at h1
    change ρ t ^ w * normSq0S (g t) x k (A t x) ≤ K₂ * U m t x at h2
    rw [normSq0S_product', pow_add]
    have hP0 : 0 ≤ ρ t ^ c * normSq0S (g t) x c₀ (P t x) :=
      mul_nonneg (pow_nonneg (hρ t ht) _) (normSq0S_nonneg _ _ _ _)
    have hA0 : 0 ≤ ρ t ^ w * normSq0S (g t) x k (A t x) :=
      mul_nonneg (pow_nonneg (hρ t ht) _) (normSq0S_nonneg _ _ _ _)
    calc ρ t ^ c * ρ t ^ w * (normSq0S (g t) x c₀ (P t x) * normSq0S (g t) x k (A t x))
        = (ρ t ^ c * normSq0S (g t) x c₀ (P t x)) * (ρ t ^ w * normSq0S (g t) x k (A t x)) := by
          ring
      _ ≤ max K₁ 0 * (K₂ * U m t x) :=
          mul_le_mul (h1.trans (le_max_left _ _)) h2 hA0 (le_max_right _ _)
      _ = max K₁ 0 * K₂ * U m t x := by ring
  | succ p ih =>
    intro c w m c₀ k P A hP hA
    obtain ⟨K₁, hK₁⟩ := ih (fun t => covStep (g t) c₀ (P t)) A (one_m hP.cov) hA
    obtain ⟨K₂, hK₂⟩ := ih P (fun t => covStep (g t) k (A t)) hP hA.cov
    refine ⟨2 * max K₁ 0 + 2 * max K₂ 0, fun t ht x => ?_⟩
    have hw : 0 ≤ ρ t ^ (c + w + (p + 1)) := pow_nonneg (hρ t ht) _
    rw [← normSq0S_iterCov_covStep, covStep_product, iterCov_add, ContMDiffSection.coe_add,
      Pi.add_apply, iterCov_domDomCongr_iterFrontExtend, iterCov_domDomCongr_iterFrontExtend]
    have hle := normSq0S_add_le (g t) x _
      ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (iterFrontExtend (leibnizLeftEquiv c₀ k) p)
        (iterCov (g t) (c₀ + 1 + k) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (covStep (g t) c₀ (P t)) (A t)) p)) x)
      ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (iterFrontExtend (leibnizRightEquiv c₀ k) p)
        (iterCov (g t) (c₀ + (k + 1)) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (P t) (covStep (g t) k (A t))) p)) x)
    rw [Tensor0SField.domDomCongr_apply, Tensor0SField.domDomCongr_apply,
      normSq0S_domDomCongr', normSq0S_domDomCongr'] at hle
    rw [Tensor0SField.domDomCongr_apply, Tensor0SField.domDomCongr_apply]
    have e1 := hK₁ t ht x
    have e2 := hK₂ t ht x
    rw [show c + 1 + w + p = c + w + (p + 1) by omega] at e1
    rw [show c + (w + 1) + p = c + w + (p + 1) by omega,
      show m + 1 + p = m + (p + 1) by omega] at e2
    have hU1 : U (m + p) t x ≤ U (m + (p + 1)) t x := hUm _ t x
    have hUp : 0 ≤ U (m + p) t x := hU0 _ t x
    calc ρ t ^ (c + w + (p + 1)) * normSq0S (g t) x (c₀ + k + 1 + p) _
        ≤ ρ t ^ (c + w + (p + 1)) * (2 * normSq0S (g t) x (c₀ + 1 + k + p)
            (iterCov (g t) (c₀ + 1 + k) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
              (covStep (g t) c₀ (P t)) (A t)) p x) +
          2 * normSq0S (g t) x (c₀ + (k + 1) + p)
            (iterCov (g t) (c₀ + (k + 1)) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
              (P t) (covStep (g t) k (A t))) p x)) := mul_le_mul_of_nonneg_left hle hw
      _ = 2 * (ρ t ^ (c + w + (p + 1)) * normSq0S (g t) x (c₀ + 1 + k + p)
            (iterCov (g t) (c₀ + 1 + k) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
              (covStep (g t) c₀ (P t)) (A t)) p x)) +
          2 * (ρ t ^ (c + w + (p + 1)) * normSq0S (g t) x (c₀ + (k + 1) + p)
            (iterCov (g t) (c₀ + (k + 1)) (tensor0SFieldProduct (∞ : WithTop ℕ∞)
              (P t) (covStep (g t) k (A t))) p x)) := by ring
      _ ≤ 2 * (max K₁ 0 * U (m + (p + 1)) t x) + 2 * (max K₂ 0 * U (m + (p + 1)) t x) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le_two)
            (mul_le_mul_of_nonneg_left ?_ zero_le_two)
          · exact e1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hUp).trans
              (mul_le_mul_of_nonneg_left hU1 (le_max_right _ _)))
          · exact e2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hU0 _ t x))
      _ = (2 * max K₁ 0 + 2 * max K₂ 0) * U (m + (p + 1)) t x := by ring

theorem product (hρ : ∀ t ∈ J, 0 ≤ ρ t) (hU0 : ∀ n t x, 0 ≤ U n t x)
    (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x) {c w m c₀ k : ℕ} {P : ℝ → TF c₀} {A : ℝ → TF k}
    (hP : IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) c 0 P) (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U (c + w) m
      (fun t => tensor0SFieldProduct (∞ : WithTop ℕ∞) (P t) (A t)) :=
  fun p => product_aux hρ hU0 hUm p P A hP hA

theorem smulByFun (hρ : ∀ t ∈ J, 0 ≤ ρ t) (hU0 : ∀ n t x, 0 ≤ U n t x)
    (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x) {c w m k : ℕ} (φ : ℝ → M → ℝ)
    (hφ : ∀ t, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ t)) {A : ℝ → TF k}
    (hP : IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) c 0
      (fun t => Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (φ t) (hφ t)))
    (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U (c + w) m
      (fun t => tensor0SFieldSmulByFun (∞ : WithTop ℕ∞) (φ t) (hφ t) (A t)) :=
  ((product hρ hU0 hUm hP hA).domDomCongr (finCongr (Nat.zero_add k))).congr fun t _ =>
    (smulByFun_eq_domDomCongr_product (φ t) (hφ t) (A t)).symm

end IterCovCtl

end GC.Geometry
