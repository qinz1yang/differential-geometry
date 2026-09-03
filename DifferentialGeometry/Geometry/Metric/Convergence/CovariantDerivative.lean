import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]

noncomputable def metricCovDerivStep
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 3) := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 2) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 2) cov A hreg

noncomputable def metricCovDeriv
    (h gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (by
      have : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact Tensor0SBundle.metricTensorField (I := I) (M := M) h)
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_apply_section
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (slots : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) h gRef 1 x (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        X (metricCovDeriv (I := I) h gRef 0) x slots := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricCovDeriv (I := I) h gRef 0
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) 2 cov hcov A
  change
    (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov A hreg x) (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov X A x slots
  exact Tensor0SBundle.totalNabla0SFun_apply_section
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X A x slots

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (X x) (fun a : Fin 2 => V a x)) =
      mvfderiv (I := I)
          (fun p : M => h.inner p (V 0 p) (V 1 p)) x (X x) -
        ∑ a : Fin 2,
          h.inner x
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
                gRef)
                  (fun p : M => V a p) x) (X x))) 0)
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
                gRef)
                  (fun p : M => V a p) x) (X x))) 1) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  have hzero :
      metricCovDeriv (I := I) h gRef 0 =
        Tensor0SBundle.metricTensorField (I := I) h := by
    rfl
  have hdir :=
    metricCovDeriv_one_apply_section (I := I) h gRef X x
      (fun a : Fin 2 => V a x)
  have heval :=
    Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := Real)
      (E := E) (H := H) (I := I) (M := M)
      cov X V (metricCovDeriv (I := I) h gRef 0) x
  rw [hdir, heval]
  simp [hzero, cov, Tensor0SBundle.metricTensorField_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] in
private theorem mvfderiv_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold mvfderiv
  rw [hmf, hx]

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_localFrame
    {Idx : Type*} {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (frame d x)
          (fun q : Fin 2 => if q = 0 then frame a x else frame b x)) =
      mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := sec d
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun q => if q = 0 then sec a else sec b
  have hsec_ev (i : Idx) :
      ∀ᶠ y in 𝓝 x, sec i y = frame i y :=
    hsec.mono fun y hy => hy i
  have hsec_x (i : Idx) : sec i x = frame i x :=
    (hsec_ev i).self_of_nhds
  have hpair_ev :
      (fun y : M => h.inner y (V 0 y) (V 1 y)) =ᶠ[𝓝 x]
        (fun y : M => h.inner y (frame a y) (frame b y)) := by
    filter_upwards [hsec_ev a, hsec_ev b] with y ha hb
    simp [V, ha, hb]
  have hXx : X x = frame d x := by
    simpa [X] using hsec_x d
  have hV0x : V 0 x = frame a x := by
    simp [V, hsec_x a]
  have hV1x : V 1 x = frame b x := by
    simp [V, hsec_x b]
  have hcov_a :
      ((cov (fun y : M => V 0 y) x) (X x)) =
        ((cov (frame a) x) (frame d x)) := by
    have hconn :
        cov (fun y : M => V 0 y) x = cov (frame a) x := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((V 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((hframe.contMDiffAt hu hx a).mdifferentiableAt (by simp))
        (by simp)
        (by
          filter_upwards [hsec_ev a] with y hy
          simpa [V] using hy)
    rw [hconn, hXx]
  have hcov_b :
      ((cov (fun y : M => V 1 y) x) (X x)) =
        ((cov (frame b) x) (frame d x)) := by
    have hconn :
        cov (fun y : M => V 1 y) x = cov (frame b) x := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((V 1).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((hframe.contMDiffAt hu hx b).mdifferentiableAt (by simp))
        (by simp)
        (by
          filter_upwards [hsec_ev b] with y hy
          simpa [V] using hy)
    rw [hconn, hXx]
  have hcov_a' :
      (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec a y) x) (X x)) =
        (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame a) x) (frame d x)) := by
    simpa [cov, V] using hcov_a
  have hcov_b' :
      (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec b y) x) (X x)) =
        (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame b) x) (frame d x)) := by
    simpa [cov, V] using hcov_b
  have hcov_a_candidate :
      ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec a y) x) (X x)) =
        ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame a) x) (frame d x)) := by
    simpa [DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric] using hcov_a'
  have hcov_b_candidate :
      ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec b y) x) (X x)) =
        ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame b) x) (frame d x)) := by
    simpa [DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric] using hcov_b'
  have hmain :=
    metricCovDeriv_one_eval_smooth_slots (I := I) h gRef X V x
  have hderiv :
      mvfderiv (I := I)
          (fun y : M => h.inner y (V 0 y) (V 1 y)) x (X x) =
        mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x
          (frame d x) := by
    rw [hXx]
    exact mvfderiv_congr_eventually_real (I := I) (x := x)
      (frame d x) hpair_ev
  calc
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (frame d x)
          (fun q : Fin 2 => if q = 0 then frame a x else frame b x))
        =
      metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (X x) (fun q : Fin 2 => V q x)) := by
          congr
          · exact hXx.symm
          · funext q
            fin_cases q
            · simpa [V] using hV0x.symm
            · simpa [V] using hV1x.symm
    _ =
      mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
          rw [hmain, hderiv, Fin.sum_univ_two]
          simp [V, hsec_x a, hsec_x b, hcov_a_candidate, hcov_b_candidate]

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_component_localFrame
    {Idx : Type*} {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
  classical
  rw [Tensor0SBundle.component0S_apply]
  simp only [IsLocalFrameOn.toBasisAt_coe]
  have hslots :
      (fun a_1 : Fin 3 =>
        frame
          ((Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
            Fin 3 -> Idx) a_1) x) =
      Fin.cons (frame d x)
        (fun q : Fin 2 => if q = 0 then frame a x else frame b x) := by
    funext q
    fin_cases q <;> rfl
  exact
    (congrArg
        (fun slots : Fin 3 -> TangentSpace I x =>
          metricCovDeriv (I := I) h gRef 1 x slots) hslots).trans
      (metricCovDeriv_one_eval_localFrame (I := I) h gRef frame hframe hu hx
        d a b)

end FixedManifoldMetricConvergence

end HCGCompactness
end DifferentialGeometry
