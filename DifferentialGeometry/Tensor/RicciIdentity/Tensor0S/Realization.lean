import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Tensor.RicciIdentity

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def Nabla0SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (slots : Fin s → TangentSpace I x),
    nablaAlpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X alpha x slots

def Nabla0SSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)) : Prop :=
  ∀ x : M, Nabla0SRealizesAt (I := I) s cov alpha (fun y => nablaAlpha y) x

def Nabla20SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
        (slots : Fin (s + 1) → TangentSpace I x),
      nabla2Alpha (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + 1) cov X nablaAlpha x slots

theorem Nabla0SSectionRealizes.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      mvfderiv (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = mvfderiv (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x

theorem Nabla0SSectionRealizes.eval_point_vector_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [T2Space M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    {x : M}
    (W : TangentSpace I x)
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nablaAlpha x (Fin.cons W (fun q : Fin s => V q x)) =
      mvfderiv (I := I)
        (fun y : M => alpha y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        alpha x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := Nabla0SSectionRealizes.eval_smooth_slots
    (I := I) h Wsec V x
  simpa [hWsec] using h0

theorem Nabla0SSectionRealizes.eval_C1_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      mvfderiv (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (V a) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = mvfderiv (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (V a) x) (X x))) := by
          exact nabla0SFun_eval_C1_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x hV_at

theorem Nabla20SRealizesAt.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    {x : M}
    {nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x}
    (h : Nabla20SRealizesAt (I := I) s cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x)) =
      mvfderiv (I := I) (fun p : M => nablaAlpha p
          (fun a : Fin (s + 1) => V a p)) x (X x) -
        ∑ a : Fin (s + 1),
          nablaAlpha x
            (Function.update (fun b : Fin (s + 1) => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (s + 1) cov X nablaAlpha x
            (fun a : Fin (s + 1) => V a x) := by
          exact h.2 X (fun a : Fin (s + 1) => V a x)
    _ = mvfderiv (I := I) (fun p : M => nablaAlpha p
            (fun a : Fin (s + 1) => V a p)) x (X x) -
          ∑ a : Fin (s + 1),
            nablaAlpha x
              (Function.update (fun b : Fin (s + 1) => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V nablaAlpha x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      change MDifferentiableAt I 𝓘(Real, Real) (fun _ : M ↦ (0 : Real)) x
      exact mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real))
        (c := (0 : Real)) (x := x)
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_finset_sum_at
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x :=
        mdiffAt_finset_sum (I := I) t f hft
      calc
        mvfderiv (I := I) ((insert i t).sum f) x v
            = mvfderiv (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = mvfderiv (I := I) (f i) x v +
              mvfderiv (I := I) (t.sum f) x v := by
              have hadd := congr($(mvfderiv_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => mvfderiv (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_neg_at
    {f : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mvfderiv (I := I) (fun y : M => -f y) x v =
      -mvfderiv (I := I) f x v := by
  let _ := hf
  have hneg := congr($(mvfderiv_neg (I := I) (g := f) (x := x)) v)
  change mvfderiv (I := I) (-f) x v = -mvfderiv (I := I) f x v
  simpa only [neg_apply] using hneg

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_sub_at
    {f g : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    mvfderiv (I := I) (fun y : M => f y - g y) x v =
      mvfderiv (I := I) f x v - mvfderiv (I := I) g x v := by
  have hsub := congr($(mvfderiv_sub
    (I := I) (g := f) (g' := g) (x := x) hf hg) v)
  change mvfderiv (I := I) (f - g) x v =
    mvfderiv (I := I) f x v - mvfderiv (I := I) g x v
  simpa only [sub_apply] using hsub

omit [FiniteDimensional ℝ E] in
lemma tensor0S_update_curvature_diag
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s)
    (DXY DYX DB : TangentSpace I x) :
    -alpha (Function.update slots q DXY) +
        alpha (Function.update slots q DYX) +
        alpha (Function.update slots q DB) =
      -alpha (Function.update slots q (DXY - DYX - DB)) := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => alpha (Function.update slots q T)
      map_add' := by
        intro U V
        exact alpha.map_update_add slots q U V
      map_smul' := by
        intro c U
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }
  change -L DXY + L DYX + L DB = -L (DXY - DYX - DB)
  rw [map_sub, map_sub]
  abel

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma metricTraceInput_eq_finCons {s : ℕ} {x : M}
    (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    metricTraceInput (I := I) X Y tail =
      Fin.cons X (Fin.cons Y tail) := by
  rfl

omit [FiniteDimensional ℝ E] in
lemma first_slot_torsionCorrection_eq
    {s : ℕ} {x : M}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (A B C : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    nablaAlpha (Fin.cons C slots) - nablaAlpha (Fin.cons A slots) +
        nablaAlpha (Fin.cons B slots) =
      -torsionCorrection0SAt (I := I) nablaAlpha (A - B - C) slots := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => nablaAlpha (Fin.cons T slots)
      map_add' := by
        intro U V
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base] using nablaAlpha.map_update_add base 0 U V
      map_smul' := by
        intro c U
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base, smul_eq_mul] using nablaAlpha.map_update_smul base 0 c U }
  change L C - L A + L B = -L (A - B - C)
  rw [map_sub, map_sub]
  abel

end DifferentialGeometry.Tensor.RicciIdentity
