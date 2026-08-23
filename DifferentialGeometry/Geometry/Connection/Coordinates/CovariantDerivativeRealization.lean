import DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeComponents
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
section FrameTuple

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def frameTuple {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    Fin r → TangentSpace I x :=
  fun q => frame (m q) x

def frameComp0S {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) :
    M → (Fin r → Idx) → Real :=
  fun x m => A x (frameTuple (I := I) frame x m)

omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem frameComp0S_apply {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    frameComp0S (I := I) A frame x m = A x (fun q => frame (m q) x) := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M]
    [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx]
    [DecidableEq Idx] in
theorem frameTuple_eq_cons {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (n : Fin (r + 1) → Idx) :
    frameTuple (I := I) frame x n =
      Fin.cons (frame (n 0) x) (frameTuple (I := I) frame x (Fin.tail n)) := by
  funext q
  refine Fin.cases ?_ ?_ q
  · simp [frameTuple]
  · intro q
    simp [frameTuple, Fin.tail]

end FrameTuple

section StepBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}

omit [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem covDerivStepComp_frameComp_eq {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) (n : Fin (s + 1) → Idx) :
    covDerivStepComp
        (frameExtData (I := I) frame (frameComp0S (I := I) A frame) x)
        (christoffelSymbolInFrame cov frame hframe x)
        (frameComp0S (I := I) A frame x) n =
      nablaA x (frameTuple (I := I) frame x n) := by
  classical
  set V : Fin s → (y : M) → TangentSpace I y :=
    fun q y => frame (Fin.tail n q) y with hV_def
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (frame (n 0) x)
  have hV_at : ∀ q : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro q
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame (Fin.tail n q) y⟩ :
              TotalSpace E (TangentSpace I : M → Type _))) x :=
      (hframe.contMDiffAt hu hx (Fin.tail n q))
    simpa [hV_def] using htop
  have heval :=
    (hreal X x (fun q : Fin s => V q x)).trans
      (nabla0SFun_eval_C1_slots
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov X V A x hV_at)
  unfold covDerivStepComp
  rw [frameTuple_eq_cons (I := I) frame x n]
  rw [show
      nablaA x (Fin.cons (frame (n 0) x)
          (frameTuple (I := I) frame x (Fin.tail n))) =
        nablaA x (Fin.cons (X x) (fun q : Fin s => V q x)) by
        rw [hX]; rfl]
  rw [heval, hX]
  have hext :
      extDerivFun (I := I)
          (fun p : M => A p (fun q : Fin s => V q p)) x (frame (n 0) x) =
        frameExtData (I := I) frame (frameComp0S (I := I) A frame) x
          (Fin.tail n) (n 0) := by
    rfl
  rw [hext]
  congr 1
  have hslot : ∀ q : Fin s,
      A x
          (Function.update (fun b : Fin s => V b x) q ((cov (V q) x) (frame (n 0) x))) =
        ∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p *
            frameComp0S (I := I) A frame x
              (Function.update (Fin.tail n) q p) := by
    intro q
    have hVq : V q = frame (Fin.tail n q) := by funext y; rfl
    have hcov :
        (cov (V q) x) (frame (n 0) x) =
          ∑ p : Idx,
            christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
              frame p x := by
      rw [hVq]
      exact covariantDerivative_eq_sum_christoffel
        (𝕜 := Real) (I := I) (cov := cov) (frame := frame) (hframe := hframe) hx
        (n 0) (Fin.tail n q)
    rw [hcov]
    rw [show
        A x
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) =
          (A x).toMultilinearMap
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) from rfl]
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MultilinearMap.map_update_smul]
    have hupd :
        Function.update (fun b : Fin s => V b x) q (frame p x) =
          frameTuple (I := I) frame x (Function.update (Fin.tail n) q p) := by
      funext r
      by_cases hr : r = q
      · subst hr; simp [frameTuple, Function.update_self]
      · simp [frameTuple, Function.update_of_ne hr, hV_def]
    rw [show
        (A x).toMultilinearMap (Function.update (fun b : Fin s => V b x) q (frame p x)) =
          A x (Function.update (fun b : Fin s => V b x) q (frame p x)) from rfl]
    rw [hupd]
    simp [frameComp0S, smul_eq_mul]
  exact Finset.sum_congr rfl fun q _ => (hslot q).symm

end StepBridge
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M]
    [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem extDerivFun_eventuallyEq_congr
    {f g : M → Real} {x : M} (V : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x V = extDerivFun (I := I) g x V := by
  rw [extDerivFun_real_eq_mfderiv (I := I) f x V,
    extDerivFun_real_eq_mfderiv (I := I) g x V]
  rw [Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h]
  rfl


end DifferentialGeometry.PDE.RicciFlow
