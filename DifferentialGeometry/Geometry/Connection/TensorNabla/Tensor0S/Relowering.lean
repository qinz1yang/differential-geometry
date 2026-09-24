import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Relowering
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.MetricConnectionDifference
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

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
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) x)
        (Fin.cons X w) =
      Tensor0SSpace.eval (nablaA x) (Fin.cons X (fun a : Fin s => w (Fin.castAdd q a))) *
          Tensor0SSpace.eval (B x) (fun a : Fin q => w (Fin.natAdd s a)) +
        Tensor0SSpace.eval (A x) (fun a : Fin s => w (Fin.castAdd q a)) *
          Tensor0SSpace.eval (nablaB x)
            (Fin.cons X (fun a : Fin q => w (Fin.natAdd s a))) := by
  classical
  let Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose
  have hXsec : Xsec x = X :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose_spec
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose
  have hV : ∀ a : Fin (s + q), V a x = w a := fun a =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose_spec
  have h1 := totalNabla0SFun_eval_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s + q) cov Xsec
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) x
    (fun a : Fin (s + q) => V a x)
  have h2 := nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB Xsec V x
  simp only [hV, hXsec] at h1 h2
  change Tensor0SSpace.eval
      (nabla0SFun (s + q) cov Xsec (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B) x)
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
  have hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_isInverse (I := I) g₂ x basis
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
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
  let P := tensor0SFieldProduct (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
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
  rw [harg, show P = tensor0SFieldProduct (∞ : WithTop ℕ∞)
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
      (basisInvMetric_isInverse (I := I) g x basis) u]
  have hz : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    rw [metricNabla0S_self (I := I) g]
    rfl
  simp [hz]


end DifferentialGeometry.PDE.RicciFlow
