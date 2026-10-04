import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorCalculus
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionTime

/-!
# The spatial commutator of the rough Laplacian with the Levi-Civita derivative

Chapter 7, surface lemma U1, route (a), step a5.2 (iii) (lane U1C2; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, review 18 §2).

All derivatives are `covStep`/`iterCov` of one metric `g`, new slots first.
* `ricciSwapField g k A = ∇²A - (∇²A with the two derivative slots swapped)`;
* `lapField g k A = tr₀₁ ∇²A` (the rough Laplacian as a field);
* `lapField_covStep`: `Δ(∇A) = ∇(ΔA) + tr₀₁ ∇(ricciSwapField A) +
  tr₀₁ ((ricciSwapField ∇A) with slots 1, 2 swapped)`, valid in every dimension: it only
  reorders the three derivatives of `∇³A`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
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

def swap01 (n : ℕ) : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 (Fin.succ 0)

theorem cons_comp_swap01 {α : Type*} {n : ℕ} (a b : α) (r : Fin n → α) :
    (Fin.cons a (Fin.cons b r) : Fin (n + 2) → α) ∘ swap01 n = Fin.cons b (Fin.cons a r) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [swap01]
  · simp [swap01]
  · have h0 : (i.succ.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
    have h1 : (i.succ.succ : Fin (n + 2)) ≠ Fin.succ 0 := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    simp only [Function.comp_apply, swap01, Equiv.swap_apply_of_ne_of_ne h0 h1]
    rfl

theorem cons_comp_frontExtend_swap01 {α : Type*} {n : ℕ} (a b c : α) (r : Fin n → α) :
    (Fin.cons a (Fin.cons b (Fin.cons c r)) : Fin (n + 2 + 1) → α) ∘
        frontExtendEquiv (swap01 n) = Fin.cons a (Fin.cons c (Fin.cons b r)) := by
  funext i
  rw [Function.comp_apply, cons_apply_frontExtendEquiv, cons_comp_swap01]

omit [T2Space M] in
theorem metricTraceFirstTwoField_apply_basis (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : TF (s + 2)) (x : M) {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (b : Module.Basis Idx ℝ (TangentSpace I x)) (gInv : Idx → Idx → ℝ)
    (hinv : MetricInverseInBasis (I := I) g x b gInv) (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwoField g A x tail =
      ∑ i, ∑ j, gInv i j * A x (Fin.cons (b i) (Fin.cons (b j) tail)) := by
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis g b gInv hinv]
  rfl

def ricciSwapField (g : SmoothRiemannianMetric I M) (k : ℕ) (A : TF k) : TF (k + 2) :=
  iterCov g k A 2 - Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (swap01 k) (iterCov g k A 2)

def lapField (g : SmoothRiemannianMetric I M) (k : ℕ) (A : TF k) : TF k :=
  metricTraceFirstTwoField g (iterCov g k A 2)

def lapCommField (g : SmoothRiemannianMetric I M) (k : ℕ) (A : TF k) : TF (k + 1) :=
  metricTraceFirstTwoField g (covStep g (k + 2) (ricciSwapField g k A)) +
    metricTraceFirstTwoField g (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (swap01 k)) (ricciSwapField g (k + 1) (covStep g k A)))

theorem ricciSwapField_apply (g : SmoothRiemannianMetric I M) {k : ℕ} (A : TF k) (x : M)
    (X Y : TangentSpace I x) (r : Fin k → TangentSpace I x) :
    ricciSwapField g k A x (Fin.cons X (Fin.cons Y r)) =
      iterCov g k A 2 x (Fin.cons X (Fin.cons Y r)) -
        iterCov g k A 2 x (Fin.cons Y (Fin.cons X r)) := by
  rw [ricciSwapField, ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  congr 1
  exact congrArg _ (cons_comp_swap01 X Y r)

theorem covStep_ricciSwapField_apply (g : SmoothRiemannianMetric I M) {k : ℕ} (A : TF k)
    (x : M) (W X Y : TangentSpace I x) (r : Fin k → TangentSpace I x) :
    covStep g (k + 2) (ricciSwapField g k A) x (Fin.cons W (Fin.cons X (Fin.cons Y r))) =
      iterCov g k A 3 x (Fin.cons W (Fin.cons X (Fin.cons Y r))) -
        iterCov g k A 3 x (Fin.cons W (Fin.cons Y (Fin.cons X r))) := by
  rw [ricciSwapField, covStep_sub, covStep_domDomCongr_frontExtend, ContMDiffSection.coe_sub,
    Pi.sub_apply, Tensor0SSpace.sub_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply]
  congr 1
  exact congrArg _ (cons_comp_frontExtend_swap01 W X Y r)

theorem lapField_covStep (g : SmoothRiemannianMetric I M) {k : ℕ} (A : TF k) :
    lapField g (k + 1) (covStep g k A) = covStep g k (lapField g k A) + lapCommField g k A := by
  classical
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext (k + 1) x fun v => ?_
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  rw [← Fin.cons_self_tail v]
  set c := v 0
  set r := Fin.tail v
  rw [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply, lapCommField,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply, lapField, lapField,
    covStep_metricTrace]
  rw [metricTraceFirstTwoField_apply_basis g _ x b _ hinv,
    metricTraceFirstTwoField_apply_basis g _ x b _ hinv,
    metricTraceFirstTwoField_apply_basis g _ x b _ hinv,
    metricTraceFirstTwoField_apply_basis g _ x b _ hinv, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    show (fun a => (Fin.cons (b i) (Fin.cons (b j) (Fin.cons c r)) :
        Fin (k + 1 + 2) → TangentSpace I x) (traceShiftEquiv k a)) =
      Fin.cons c (Fin.cons (b i) (Fin.cons (b j) r)) from traceShiftEquiv_comp c (b i) (b j) r,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    show (fun a => (Fin.cons (b i) (Fin.cons (b j) (Fin.cons c r)) :
        Fin (k + 2 + 1) → TangentSpace I x) (frontExtendEquiv (swap01 k) a)) =
      Fin.cons (b i) (Fin.cons c (Fin.cons (b j) r)) from
        cons_comp_frontExtend_swap01 (b i) (b j) c r, covStep_ricciSwapField_apply]
  have h3 : ricciSwapField g (k + 1) (covStep g k A) x
      (Fin.cons (b i) (Fin.cons c (Fin.cons (b j) r))) =
        iterCov g k A 3 x (Fin.cons (b i) (Fin.cons c (Fin.cons (b j) r))) -
          iterCov g k A 3 x (Fin.cons c (Fin.cons (b i) (Fin.cons (b j) r))) :=
    ricciSwapField_apply g (covStep g k A) x (b i) c (Fin.cons (b j) r)
  have e1 : iterCov g (k + 1) (covStep g k A) 2 = iterCov g k A 3 := rfl
  have e2 : covStep g (k + 2) (iterCov g k A 2) = iterCov g k A 3 := rfl
  rw [h3, e1, e2]
  ring

omit [T2Space M] in
theorem domDomCongr_product_apply {a b n : ℕ} (P : TF a) (A : TF b) (e : Fin (a + b) ≃ Fin n)
    (x : M) (u : Fin n → TangentSpace I x) :
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e (tensor0SFieldProduct (∞ : WithTop ℕ∞) P A) x u =
      P x (fun i => u (e (Fin.castAdd b i))) * A x (fun j => u (e (Fin.natAdd a j))) := by
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  rfl

theorem finCongr_two_castAdd_zero (k : ℕ) :
    finCongr (Nat.add_comm 2 k) (Fin.castAdd k (0 : Fin 2)) = (0 : Fin (k + 2)) := by
  ext; simp

theorem finCongr_two_castAdd_one (k : ℕ) :
    finCongr (Nat.add_comm 2 k) (Fin.castAdd k (1 : Fin 2)) = (Fin.succ 0 : Fin (k + 2)) := by
  ext; simp

theorem finCongr_two_natAdd (k : ℕ) (j : Fin k) :
    finCongr (Nat.add_comm 2 k) (Fin.natAdd 2 j) = (j.succ.succ : Fin (k + 2)) := by
  ext; simp [Fin.val_succ]

def curvSwapPermX {k : ℕ} (q : Fin k) : Fin (2 + k) ≃ Fin (k + 2) :=
  (finCongr (Nat.add_comm 2 k)).trans
    ((Equiv.swap (0 : Fin (k + 2)) (Fin.succ 0)).trans (Equiv.swap (0 : Fin (k + 2)) q.succ.succ))

def curvSwapPermY {k : ℕ} (q : Fin k) : Fin (2 + k) ≃ Fin (k + 2) :=
  (finCongr (Nat.add_comm 2 k)).trans (Equiv.swap (Fin.succ (0 : Fin (k + 1))) q.succ.succ)

def curvSwapField (g : SmoothRiemannianMetric I M) (k : ℕ) (A : TF k) : TF (k + 2) :=
  (-(1 / 2 : ℝ)) • ∑ q : Fin k,
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermX q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) A) -
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermY q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) A))

omit [T2Space M] in
theorem curvSwapPermX_apply {α : Type*} {k : ℕ} (q : Fin k) (X Y : α) (s : Fin k → α) :
    (fun i => (Fin.cons X (Fin.cons Y s) : Fin (k + 2) → α) (curvSwapPermX q (Fin.castAdd k i)))
        = ![Y, s q] ∧
      (fun j => (Fin.cons X (Fin.cons Y s) : Fin (k + 2) → α) (curvSwapPermX q (Fin.natAdd 2 j)))
        = Function.update s q X := by
  have h0q : (0 : Fin (k + 2)) ≠ q.succ.succ := (Fin.succ_ne_zero _).symm
  have h1q : (Fin.succ 0 : Fin (k + 2)) ≠ q.succ.succ := fun h =>
    Fin.succ_ne_zero _ (Fin.succ_injective _ h).symm
  have h10 : (Fin.succ 0 : Fin (k + 2)) ≠ 0 := Fin.succ_ne_zero _
  constructor
  · funext i
    fin_cases i
    · simp only [curvSwapPermX, Equiv.trans_apply, Fin.zero_eta, finCongr_two_castAdd_zero,
        Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h10 h1q]
      rfl
    · simp only [curvSwapPermX, Equiv.trans_apply, Fin.mk_one, finCongr_two_castAdd_one,
        Equiv.swap_apply_right, Equiv.swap_apply_left]
      rfl
  · funext j
    simp only [curvSwapPermX, Equiv.trans_apply, finCongr_two_natAdd]
    have hj0 : (j.succ.succ : Fin (k + 2)) ≠ 0 := Fin.succ_ne_zero _
    have hj1 : (j.succ.succ : Fin (k + 2)) ≠ Fin.succ 0 := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1]
    by_cases hjq : j = q
    · subst hjq
      rw [Equiv.swap_apply_right, Function.update_self]
      rfl
    · have hne : (j.succ.succ : Fin (k + 2)) ≠ q.succ.succ := fun h =>
        hjq (Fin.succ_injective _ (Fin.succ_injective _ h))
      rw [Equiv.swap_apply_of_ne_of_ne hj0 hne, Function.update_of_ne hjq]
      rfl

omit [T2Space M] in
theorem curvSwapPermY_apply {α : Type*} {k : ℕ} (q : Fin k) (X Y : α) (s : Fin k → α) :
    (fun i => (Fin.cons X (Fin.cons Y s) : Fin (k + 2) → α) (curvSwapPermY q (Fin.castAdd k i)))
        = ![X, s q] ∧
      (fun j => (Fin.cons X (Fin.cons Y s) : Fin (k + 2) → α) (curvSwapPermY q (Fin.natAdd 2 j)))
        = Function.update s q Y := by
  have h0q : (0 : Fin (k + 2)) ≠ q.succ.succ := (Fin.succ_ne_zero _).symm
  have h01 : (0 : Fin (k + 2)) ≠ Fin.succ 0 := (Fin.succ_ne_zero _).symm
  constructor
  · funext i
    fin_cases i
    · simp only [curvSwapPermY, Equiv.trans_apply, Fin.zero_eta, finCongr_two_castAdd_zero,
        Equiv.swap_apply_of_ne_of_ne h01 h0q]
      rfl
    · simp only [curvSwapPermY, Equiv.trans_apply, Fin.mk_one, finCongr_two_castAdd_one,
        Equiv.swap_apply_left]
      rfl
  · funext j
    simp only [curvSwapPermY, Equiv.trans_apply, finCongr_two_natAdd]
    have hj1 : (j.succ.succ : Fin (k + 2)) ≠ Fin.succ 0 := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    by_cases hjq : j = q
    · subst hjq
      rw [Equiv.swap_apply_right, Function.update_self]
      rfl
    · have hne : (j.succ.succ : Fin (k + 2)) ≠ q.succ.succ := fun h =>
        hjq (Fin.succ_injective _ (Fin.succ_injective _ h))
      rw [Equiv.swap_apply_of_ne_of_ne hj1 hne, Function.update_of_ne hjq]
      rfl

theorem ricciSwapField_eq_of_finrank_two [I.Boundaryless] (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) {k : ℕ}
    (A : TF k) :
    ricciSwapField g k A =
      tensor0SFieldSmulByFun (∞ : WithTop ℕ∞) (metricScalarAt g) hR (curvSwapField g k A) := by
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext (k + 2) x fun v => ?_
  rw [← Fin.cons_self_tail v, ← Fin.cons_self_tail (Fin.tail v)]
  set X := v 0
  set Y := Fin.tail v 0
  set s := Fin.tail (Fin.tail v)
  rw [ricciSwapField_apply, tensor0SField_smulByFun_apply, Tensor0SSpace.smul_apply,
    smul_eq_mul, curvSwapField, ContMDiffSection.coe_smul, Pi.smul_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  have hL := iterCov_two_swap_sub g A x X Y s
  rw [curvatureAction0SAt_metricRm13_of_finrank_eq_two hdim] at hL
  change iterCov g k A 2 x (Fin.cons X (Fin.cons Y s)) -
      iterCov g k A 2 x (Fin.cons Y (Fin.cons X s)) = _ at hL
  rw [hL]
  have hsum : (∑ q : Fin k, (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermX q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) A) -
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermY q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) A))) x
        (Fin.cons X (Fin.cons Y s)) =
      ∑ q : Fin k, (g.inner x Y (s q) * A x (Function.update s q X) -
        g.inner x X (s q) * A x (Function.update s q Y)) := by
    rw [ContMDiffSection.finset_sum_apply, tensor0S_sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      domDomCongr_product_apply, domDomCongr_product_apply,
      (curvSwapPermX_apply q X Y s).1, (curvSwapPermX_apply q X Y s).2,
      (curvSwapPermY_apply q X Y s).1, (curvSwapPermY_apply q X Y s).2,
      metricTensorField_apply, metricTensorField_apply]
    rfl
  rw [hsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hlin : A x (Function.update s q ((metricScalarAt g x / 2) •
      (g.inner x Y (s q) • X - g.inner x X (s q) • Y))) =
        metricScalarAt g x / 2 * (g.inner x Y (s q) * A x (Function.update s q X) -
          g.inner x X (s q) * A x (Function.update s q Y)) := by
    have key : ∀ w : TangentSpace I x,
        A x (Function.update s q w) = (A x).toContinuousLinearMap s q w := fun w => rfl
    rw [key, key, key, map_smul, map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
  rw [hlin]
  ring

def gradField (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) :
    TF 1 :=
  covStep g 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (metricScalarAt g) hR)

theorem covStep_fromScalarField_apply (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : Fin 1 → TangentSpace I x) :
    covStep g 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f hf) x v =
      mvfderiv I f x (v 0) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x (v 0)
  have hv : v = Fin.cons (X x) (fun q : Fin 0 => (Fin.elim0 q :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) x) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    rw [Fin.cons_zero, hX]
  rw [hv, covStep_eval_smooth_slots, Fin.cons_zero, hX]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  congr 1

theorem gradField_apply (g : SmoothRiemannianMetric I M)
    (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) (x : M) (v : Fin 1 → TangentSpace I x) :
    gradField g hR x v = mvfderiv I (metricScalarAt g) x (v 0) :=
  covStep_fromScalarField_apply g _ hR x v

def gammaPermB {k : ℕ} (i : Fin k) : Fin (1 + k) ≃ Fin (k + 1) :=
  (finCongr (Nat.add_comm 1 k)).trans (Equiv.swap (0 : Fin (k + 1)) i.succ)

def gammaPermC {k : ℕ} (i : Fin k) : Fin (2 + 1 + k) ≃ Fin (k + 1 + 2) :=
  (finCongr (by omega : 2 + 1 + k = k + 1 + 2)).trans
    ((Equiv.swap (0 : Fin (k + 1 + 2)) i.succ.succ.succ).trans
      ((Equiv.swap (0 : Fin (k + 1 + 2)) (Fin.succ 0)).trans
        (Equiv.swap (0 : Fin (k + 1 + 2)) (Fin.succ (Fin.succ 0)))))

def gammaField (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g))
    (k : ℕ) (A : TF k) : TF (k + 1) :=
  (-(1 / 2 : ℝ)) • ∑ i : Fin k,
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (finCongr (Nat.add_comm 1 k))
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (gradField g hR) A) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (gammaPermB i)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) (gradField g hR) A) -
      metricTraceFirstTwoField g (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (gammaPermC i)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) (gradField g hR)) A)))

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem apply_update_eq_sum_inner (g : SmoothRiemannianMetric I M) {x : M} {s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (b : Module.Basis Idx ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s → TangentSpace I x) (i : Fin s) (u : TangentSpace I x) :
    T (Function.update v i u) = ∑ a, g.inner x u (b a) * T (Function.update v i (b a)) := by
  have hrepr : ∀ a, b.repr u a = g.inner x u (b a) := by
    intro a
    conv_rhs => rw [← b.sum_repr u]
    rw [map_sum, sum_apply]
    simp only [map_smul, smul_apply, smul_eq_mul, hb, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have key : ∀ y : TangentSpace I x,
      T (Function.update v i y) = T.toContinuousLinearMap v i y := fun y => rfl
  rw [key]
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, hrepr, key]

theorem gammaPermA_apply {α : Type*} {k : ℕ} (w : α) (v : Fin k → α) :
    (Fin.cons w v : Fin (k + 1) → α) (finCongr (Nat.add_comm 1 k) (Fin.castAdd k 0)) = w ∧
      (fun j => (Fin.cons w v : Fin (k + 1) → α) (finCongr (Nat.add_comm 1 k) (Fin.natAdd 1 j)))
        = v := by
  constructor
  · rw [show finCongr (Nat.add_comm 1 k) (Fin.castAdd k (0 : Fin 1)) = 0 by ext; simp]
    rfl
  · funext j
    rw [show finCongr (Nat.add_comm 1 k) (Fin.natAdd 1 j) = j.succ by ext; simp [Fin.val_succ]]
    rfl

theorem gammaPermB_apply {α : Type*} {k : ℕ} (i : Fin k) (w : α) (v : Fin k → α) :
    (Fin.cons w v : Fin (k + 1) → α) (gammaPermB i (Fin.castAdd k 0)) = v i ∧
      (fun j => (Fin.cons w v : Fin (k + 1) → α) (gammaPermB i (Fin.natAdd 1 j)))
        = Function.update v i w := by
  constructor
  · rw [gammaPermB, Equiv.trans_apply,
      show finCongr (Nat.add_comm 1 k) (Fin.castAdd k (0 : Fin 1)) = 0 by ext; simp,
      Equiv.swap_apply_left]
    rfl
  · funext j
    rw [gammaPermB, Equiv.trans_apply,
      show finCongr (Nat.add_comm 1 k) (Fin.natAdd 1 j) = j.succ by ext; simp [Fin.val_succ]]
    have hj0 : (j.succ : Fin (k + 1)) ≠ 0 := Fin.succ_ne_zero _
    by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_right, Function.update_self]
      rfl
    · have hne : (j.succ : Fin (k + 1)) ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
      rw [Equiv.swap_apply_of_ne_of_ne hj0 hne, Function.update_of_ne hji]
      rfl

theorem gammaPermC_apply {α : Type*} {k : ℕ} (i : Fin k) (e e' w : α) (v : Fin k → α) :
    let u : Fin (k + 1 + 2) → α := Fin.cons e (Fin.cons e' (Fin.cons w v))
    u (gammaPermC i (Fin.castAdd k (Fin.castAdd 1 0))) = v i ∧
      u (gammaPermC i (Fin.castAdd k (Fin.castAdd 1 1))) = w ∧
      u (gammaPermC i (Fin.castAdd k (Fin.natAdd 2 0))) = e ∧
      (fun j => u (gammaPermC i (Fin.natAdd (2 + 1) j))) = Function.update v i e' := by
  intro u
  have hi0 : (i.succ.succ.succ : Fin (k + 1 + 2)) ≠ 0 := Fin.succ_ne_zero _
  have hi1 : (i.succ.succ.succ : Fin (k + 1 + 2)) ≠ Fin.succ 0 := fun h =>
    Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  have hi2 : (i.succ.succ.succ : Fin (k + 1 + 2)) ≠ Fin.succ (Fin.succ 0) := fun h =>
    Fin.succ_ne_zero _ (Fin.succ_injective _ (Fin.succ_injective _ h))
  have h10 : (Fin.succ 0 : Fin (k + 1 + 2)) ≠ 0 := Fin.succ_ne_zero _
  have h20 : (Fin.succ (Fin.succ 0) : Fin (k + 1 + 2)) ≠ 0 := Fin.succ_ne_zero _
  have h12 : (Fin.succ 0 : Fin (k + 1 + 2)) ≠ Fin.succ (Fin.succ 0) := fun h =>
    Fin.succ_ne_zero (0 : Fin (k + 1)) (Fin.succ_injective _ h).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gammaPermC, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
      show finCongr (by omega : 2 + 1 + k = k + 1 + 2) (Fin.castAdd k (Fin.castAdd 1 0)) = 0 by
        ext; simp,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hi0 hi1,
      Equiv.swap_apply_of_ne_of_ne hi0 hi2]
    rfl
  · rw [gammaPermC, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
      show finCongr (by omega : 2 + 1 + k = k + 1 + 2) (Fin.castAdd k (Fin.castAdd 1 1)) =
        Fin.succ 0 by ext; simp,
      Equiv.swap_apply_of_ne_of_ne h10 hi1.symm, Equiv.swap_apply_right, Equiv.swap_apply_left]
    rfl
  · rw [gammaPermC, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
      show finCongr (by omega : 2 + 1 + k = k + 1 + 2) (Fin.castAdd k (Fin.natAdd 2 0)) =
        Fin.succ (Fin.succ 0) by
          ext
          simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ,
            Fin.val_zero],
      Equiv.swap_apply_of_ne_of_ne h20 hi2.symm, Equiv.swap_apply_of_ne_of_ne h20 h12.symm,
      Equiv.swap_apply_right]
    rfl
  · funext j
    rw [gammaPermC, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
      show finCongr (by omega : 2 + 1 + k = k + 1 + 2) (Fin.natAdd (2 + 1) j) =
        j.succ.succ.succ by ext; simp [Fin.val_succ]]
    have hj0 : (j.succ.succ.succ : Fin (k + 1 + 2)) ≠ 0 := Fin.succ_ne_zero _
    have hj1 : (j.succ.succ.succ : Fin (k + 1 + 2)) ≠ Fin.succ 0 := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    have hj2 : (j.succ.succ.succ : Fin (k + 1 + 2)) ≠ Fin.succ (Fin.succ 0) := fun h =>
      Fin.succ_ne_zero _ (Fin.succ_injective _ (Fin.succ_injective _ h))
    by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h10 h12,
        Function.update_self]
      rfl
    · have hne : (j.succ.succ.succ : Fin (k + 1 + 2)) ≠ i.succ.succ.succ := fun h =>
        hji (Fin.succ_injective _ (Fin.succ_injective _ (Fin.succ_injective _ h)))
      rw [Equiv.swap_apply_of_ne_of_ne hj0 hne, Equiv.swap_apply_of_ne_of_ne hj0 hj1,
        Equiv.swap_apply_of_ne_of_ne hj0 hj2, Function.update_of_ne hji]
      rfl

theorem sum_identityInvMetric_mul {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (f : Idx → Idx → ℝ) :
    ∑ a, ∑ b, identityInvMetric (Idx := Idx) a b * f a b = ∑ a, f a a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [identityInvMetric]
  · intro b _ hba
    simp [identityInvMetric, diagonalInvMetric, Ne.symm hba]
  · simp

theorem slotVariation_eq_gammaField (g : SmoothRiemannianMetric I M)
    (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) {k : ℕ} (A : TF k) (x : M)
    (Γ : TangentSpace I x → TangentSpace I x → TangentSpace I x)
    (hΓ : ∀ a b z : TangentSpace I x, g.inner x (Γ a b) z =
      (-(mvfderiv I (metricScalarAt g) x b * g.inner x a z) -
        mvfderiv I (metricScalarAt g) x a * g.inner x b z +
        mvfderiv I (metricScalarAt g) x z * g.inner x b a) / 2)
    (w : TangentSpace I x) (v : Fin k → TangentSpace I x) :
    ∑ i, A x (Function.update v i (Γ (v i) w)) = gammaField g hR k A x (Fin.cons w v) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  set dR := mvfderiv I (metricScalarAt g) x with hdR
  rw [gammaField, ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
    ContMDiffSection.finset_sum_apply, tensor0S_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hT3 : metricTraceFirstTwoField g (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (gammaPermC i)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField g) (gradField g hR)) A)) x
        (Fin.cons w v) =
      ∑ a, g.inner x (v i) w * (dR (b a) * A x (Function.update v i (b a))) := by
    rw [metricTraceFirstTwoField_apply_basis g _ x b _ hinv]
    rw [← sum_identityInvMetric_mul (fun a a' =>
      g.inner x (v i) w * (dR (b a) * A x (Function.update v i (b a'))))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    congr 1
    rw [domDomCongr_product_apply, tensor0SField_product_apply, metricTensorField_apply,
      gradField_apply]
    obtain ⟨c1, c2, c3, c4⟩ := gammaPermC_apply i (b a) (b a') w v
    simp only [Function.comp_apply]
    rw [c1, c2, c3, c4]
    ring
  have hT1 := domDomCongr_product_apply (gradField g hR) A (finCongr (Nat.add_comm 1 k)) x
    (Fin.cons w v)
  have hT2 := domDomCongr_product_apply (gradField g hR) A (gammaPermB i) x (Fin.cons w v)
  rw [gradField_apply, (gammaPermA_apply w v).2] at hT1
  rw [gradField_apply, (gammaPermB_apply i w v).2] at hT2
  simp only [(gammaPermA_apply w v).1] at hT1
  simp only [(gammaPermB_apply i w v).1] at hT2
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply, hT1, hT2, hT3]
  have e1 : A x v = ∑ a, g.inner x (v i) (b a) * A x (Function.update v i (b a)) := by
    conv_lhs => rw [← Function.update_eq_self i v]
    exact apply_update_eq_sum_inner g b hb (A x) v i (v i)
  have e2 := apply_update_eq_sum_inner g b hb (A x) v i w
  rw [apply_update_eq_sum_inner g b hb (A x) v i (Γ (v i) w), e1, e2]
  simp only [hΓ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [g.symm x w (v i)]
  ring

theorem fromScalarField_eq_neg_trace_rm04 [I.Boundaryless] (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) :
    Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (metricScalarAt g) hR =
      (-1 : ℝ) • metricTraceFirstTwoField g (metricTraceFirstTwoField g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv (swap01 1))
          (metricRm04 g))) := by
  classical
  refine DFunLike.ext _ _ fun x => tensor0SSpace_ext 0 x fun v => ?_
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  have hn : Module.finrank ℝ (TangentSpace I x) = 2 := hdim
  rw [Tensor0SField.fromScalarField_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul, metricTraceFirstTwoField_apply_basis g _ x b _ hinv,
    sum_identityInvMetric_mul]
  have hin : ∀ c, metricTraceFirstTwoField g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv (swap01 1)) (metricRm04 g)) x
        (Fin.cons (b c) (Fin.cons (b c) v)) =
      ∑ a, metricScalarAt g x / 2 * ((if a = c then 1 else 0) - 1) := by
    intro c
    rw [metricTraceFirstTwoField_apply_basis g _ x b _ hinv, sum_identityInvMetric_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      show (fun i => (Fin.cons (b a) (Fin.cons (b a) (Fin.cons (b c) (Fin.cons (b c) v))) :
          Fin (1 + 2 + 1) → TangentSpace I x) (frontExtendEquiv (swap01 1) i)) =
        Fin.cons (b a) (Fin.cons (b c) (Fin.cons (b a) (Fin.cons (b c) v))) from
          cons_comp_frontExtend_swap01 (b a) (b a) (b c) (Fin.cons (b c) v)]
    have hv4 : (Fin.cons (b a) (Fin.cons (b c) (Fin.cons (b a) (Fin.cons (b c) v))) :
        Fin 4 → TangentSpace I x) = vec4 (b a) (b c) (b a) (b c) := by
      funext i; fin_cases i <;> rfl
    rw [hv4, metricRm04_apply]
    change metricRm04StandardAt g x (b a) (b c) (b a) (b c) = _
    rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim, hb, hb, hb, hb]
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac, Ne.symm hac]
  have hsum : ∀ c : Fin (Module.finrank ℝ (TangentSpace I x)),
      ∑ a, metricScalarAt g x / 2 * ((if a = c then (1 : ℝ) else 0) - 1) =
        metricScalarAt g x / 2 * (1 - 2) := by
    intro c
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [hn]
    norm_num
  simp only [hin, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hn]
  norm_num
  ring

end GC.Geometry
