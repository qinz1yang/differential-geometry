import RicciFlower.HCGCompactness.Basic
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import RicciFlower.VectorBundle.Frame
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointed Cheeger--Gromov Convergence Data

The maps and convergence predicates mirror MSM135 Chapter 3: exhaustions of the
limit, basepoint-preserving diffeomorphisms onto their images, and smooth
convergence on compact sets.
-/

noncomputable section

universe u

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]

/-- One covariant-derivative step in the recursive definition of
`metricCovDeriv`.  Keeping the `a + 2` to `a + 3` index adjustment here makes
the recursion less sensitive to future refactors of `totalNabla0S`. -/
noncomputable def metricCovDerivStep
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 3) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 2) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 2) cov A hreg

/-- The `a`-fold covariant derivative of a metric tensor, using the
Levi-Civita connection of the reference metric `gRef`.  The derivative slots
are placed first, so the output has covariant valence `a + 2`. -/
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
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact Tensor0SBundle.metricTensorField (I := I) (M := M) h)
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

/-- Evaluation of the first canonical background covariant derivative of a
metric tensor.  The leading slot is the derivative direction; evaluating it on
a smooth vector field recovers the existing directional `nabla0SFun` API. -/
theorem metricCovDeriv_one_apply_section
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (slots : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) h gRef 1 x (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
        X (metricCovDeriv (I := I) h gRef 0) x slots := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricCovDeriv (I := I) h gRef 0
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
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

/-- Smooth-slot expansion of the first background covariant derivative of a
metric tensor.  This is the invariant form of the first displayed formula in
the second part of MSM135 Lemma 3.11. -/
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
      extDerivFun (I := I)
          (fun p : M => h.inner p (V 0 p) (V 1 p)) x (X x) -
        ∑ a : Fin 2,
          h.inner x
            ((Function.update (fun b : Fin 2 => V b x) a
              (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) 0)
            ((Function.update (fun b : Fin 2 => V b x) a
              (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) 1) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
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

private theorem extDerivFun_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

/-- Local-frame evaluation of the first background covariant derivative of a
metric tensor.

This is the local-frame form of the first displayed formula in the second part
of MSM135 Lemma 3.11:
`(nabla_gRef h)_{d a b}` is the directional derivative of `h_{a b}` minus the
two Christoffel corrections for the background connection. -/
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
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let cov :=
    LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := sec d
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun q => if q = 0 then sec a else sec b
  have hsec_ev (i : Idx) :
      (fun y : M => sec i y) =ᶠ[𝓝 x] frame i :=
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
        (by simpa [V] using hsec_ev a)
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
        (by simpa [V] using hsec_ev b)
    rw [hconn, hXx]
  have hcov_a' :
      (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec a y) x) (X x)) =
        (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame a) x) (frame d x)) := by
    simpa [cov, V] using hcov_a
  have hcov_b' :
      (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec b y) x) (X x)) =
        (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame b) x) (frame d x)) := by
    simpa [cov, V] using hcov_b
  have hcov_a_candidate :
      ((LeviCivita.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec a y) x) (X x)) =
        ((LeviCivita.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame a) x) (frame d x)) := by
    simpa [LeviCivita.leviCivitaConnectionOfMetric] using hcov_a'
  have hcov_b_candidate :
      ((LeviCivita.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec b y) x) (X x)) =
        ((LeviCivita.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame b) x) (frame d x)) := by
    simpa [LeviCivita.leviCivitaConnectionOfMetric] using hcov_b'
  have hmain :=
    metricCovDeriv_one_eval_smooth_slots (I := I) h gRef X V x
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => h.inner y (V 0 y) (V 1 y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x
          (frame d x) := by
    rw [hXx]
    exact extDerivFun_congr_eventually_real (I := I) (x := x)
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
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
          rw [hmain, hderiv, Fin.sum_univ_two]
          simp [V, hsec_x a, hsec_x b, hcov_a_candidate, hcov_b_candidate]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Component form of `metricCovDeriv_one_eval_localFrame`. -/
theorem metricCovDeriv_one_component_localFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
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

/-- The pointwise tensor `∇^a(g_k - g_infty)`, represented as the difference of
the iterated covariant derivatives of the two metric tensors. -/
noncomputable def metricDiffCovDerivAt
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x :=
  metricCovDeriv (I := I) gk gRef a x -
    metricCovDeriv (I := I) gInf gRef a x

/-- The pointwise quantity `|∇^a(g_k - g_infty)|_g` from MSM135 Definition
3.1.  The covariant derivatives are taken using the Levi-Civita connection of
`gRef`, and the tensor norm is the one induced by `gRef`. -/
noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef x))

/-- The displayed `sup_{0 <= a <= p} sup_{x in K}` norm from MSM135
Definition 3.1.  This is a raw low-level supremum; it is only intended to be
used through `MetricCPConvOn`, where compactness of `K` is an explicit
hypothesis. -/
noncomputable def metricDerivNormSupOn
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricDerivNorm (I := I) a gk gInf gRef x = r}

/-- MSM135 Definition 3.1: `g_k` converges to `g∞` in `C^p`, uniformly on
`K`, with the covariant derivatives and norms measured using the reference
metric `g`.  Since `p : Nat`, the range `0 ≤ a ≤ p` is represented by
`a ≤ p`. -/
def MetricCPConvOn
    (K : Set M) (_hK : IsCompact K) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef < ε

/-- `C^∞` convergence uniformly on a fixed compact set, expressed as `C^p`
convergence for every finite `p`. -/
def MetricCInfConvOn
    (K : Set M) (hK : IsCompact K)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall p : Nat, MetricCPConvOn (I := I) K hK p gSeq gInf gRef

/-- Compact-open `C^∞` convergence on one fixed manifold: every compact set has
uniform `C^p` convergence for every finite `p`. -/
def MetricCInfConvOnCompacts
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall K : Set M, forall hK : IsCompact K,
    MetricCInfConvOn (I := I) K hK gSeq gInf gRef

/-- Data package for compact-open `C^∞` convergence of metrics on one fixed
manifold. -/
structure MetricCInfConvData
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] where
  gSeq : Nat -> SmoothRiemannianMetric I M
  gInf : SmoothRiemannianMetric I M
  gRef : SmoothRiemannianMetric I M
  converges : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef

end FixedManifoldMetricConvergence

/-- A monotone exhaustion by open sets, as in the paragraph after MSM135
Definition 3.1 and in Hamilton's pointed compactness setup. -/
structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

namespace ExhaustsByOpen

theorem monotone {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) :
    Monotone U := by
  intro i j hij
  induction hij with
  | refl => intro x hx; exact hx
  | step hle ih =>
      exact Set.Subset.trans ih (hU.mono_step _)

theorem subset_of_le {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {i j : Nat} (hij : i <= j) :
    U i ⊆ U j :=
  hU.monotone hij

end ExhaustsByOpen

/-- Exhaustion and comparison maps for pointed Cheeger--Gromov convergence.

The comparison maps are actual smooth partial diffeomorphisms from the limit
manifold onto open images in the sequence manifolds.  Their total functions
exist globally because `PartialDiffeomorph` is implemented through a
`PartialEquiv`, but all geometric content below is restricted to `source k`. -/
structure PointedCGHMaps
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      PartialDiffeomorph I I L.M (X.term (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.term (subseq k)).basepoint

namespace PointedCGHMaps

def source
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.term (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.term (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

theorem source_open
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

theorem target_open
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsOpen (Φ.target k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

theorem source_mono
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    Φ.source k ⊆ Φ.source (k + 1) := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.mono_step k

theorem source_subset
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.subset K hK

end PointedCGHMaps

/-- The source domain of the `k`th comparison map as a subtype.  The manifold
structure and restricted/pulled-back metrics on this subtype are supplied by
`SourceDomainMetricData`; this keeps the missing open-domain backend explicit
instead of silently extending metrics to all of the limit manifold. -/
abbrev SourceDomain
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :=
  {x : L.M // x ∈ Φ.source k}

def sourceCompactSet
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (SourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}

/-- Metrics on a source domain together with the formulas saying that they are
the restricted limit metric and the pullback of the corresponding sequence
metric along the partial diffeomorphism. -/
structure SourceDomainMetricData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) where
  topology : TopologicalSpace (SourceDomain (I := I) Φ k)
  charted : ChartedSpace H (SourceDomain (I := I) Φ k)
  t2 : T2Space (SourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (SourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (SourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  compact_preimage :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace L.M := L.topology
    forall K : Set L.M, IsCompact K ->
      IsCompact (sourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
      change IsManifold I ∞ L.M
      infer_instance
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (limitMetric t).inner x v w =
          (L.S.family.metric t).inner (x : L.M)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : L.M)) x) v)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : L.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
      change IsManifold I ∞ L.M
      infer_instance
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
      by
        change IsManifold I ∞ (X.term (subseq k)).M
        infer_instance
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (pullbackMetric t).inner x v w =
          ((X.term (subseq k)).S.family.metric t).inner
            (Φ.map k (x : L.M))
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)

namespace SourceDomainMetricData

noncomputable def derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedCGHMaps (I := I) X L subseq}
    (D : SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M) (p : Nat) (t : Real) : Real := by
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (SourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (sourceCompactSet (I := I) Φ k K) p
    (D.pullbackMetric t) (D.limitMetric t) (D.referenceMetric t)

end SourceDomainMetricData

def SourceMetricCPConvOn
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat) (t : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        (D k).derivNormSupOn (I := I) K p t < ε

def SourceMetricCPConvOnWindow
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat)
    (a b : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε

/-- Compact-open smooth convergence of the pulled-back spatial metrics on the
source domains.  This is theorem-facing data: constructing the source subtype
manifold structures and proving the pullback formulas is the current
open-domain metric frontier. -/
structure SourceMetricConvergenceData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) where
  domain : forall k : Nat, SourceDomainMetricData (I := I) Φ k
  converges :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        SourceMetricCPConvOn (I := I) Φ domain K hK p t

/-- Compact-open smooth convergence on spacetime windows. -/
structure SourceSpacetimeConvergenceData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k) where
  converges_on_windows :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        SourceMetricCPConvOnWindow (I := I) Φ D K hK p a b

/-- Pointwise pullback convergence for real-valued spacetime functions along
the Cheeger--Gromov comparison maps.  This is the typed interface needed by
Hamilton Section 12 whenever the argument only uses scalar-valued convergence,
for example scalar curvature or scale-invariant pinching ratios. -/
def FunctionPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X L subseq)
    (uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real)
    (uInf : Real -> L.M -> Real) : Prop :=
  forall t : Real, forall x : L.M,
    Filter.Tendsto (fun k : Nat => uSeq k t (Phi.map k x))
      Filter.atTop (nhds (uInf t x))

/-- If pulled-back real functions converge pointwise and are eventually bounded
above by quantities tending to `0`, then the limit is bounded above by every
positive number.

This is the order-closure step used by the Section 12 pinching transfer after
the rescaled estimate supplies a decaying upper bound. -/
theorem FunctionPullbackTendsto.le_of_bound0
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    {Phi : PointedCGHMaps (I := I) X L subseq}
    {uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real}
    {uInf : Real -> L.M -> Real}
    (hconv : FunctionPullbackTendsto (I := I) Phi uSeq uInf)
    (bound : Real -> L.M -> Nat -> Real)
    (hbound :
      forall t : Real, forall x : L.M,
        Filter.Tendsto (bound t x) Filter.atTop (nhds 0) /\
          (∀ᶠ k in Filter.atTop,
            uSeq k t (Phi.map k x) <= bound t x k)) :
    forall t : Real, forall x : L.M, forall η : Real, 0 < η ->
      uInf t x <= η := by
  intro t x η hη
  have hle0 : uInf t x <= 0 := by
    exact le_of_tendsto_of_tendsto (hconv t x) (hbound t x).1 (hbound t x).2
  exact le_trans hle0 (le_of_lt hη)

/-- Pointwise pullback convergence of scalar curvature along the comparison
maps of a smooth Cheeger--Gromov--Hamilton limit. -/
def ScalarPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X L subseq) : Prop :=
  FunctionPullbackTendsto (I := I) Phi
    (fun k t x =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      (X.term (subseq k)).S.scalar t x)
    (fun t x =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
        change IsManifold I ∞ L.M
        infer_instance
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : T2Space L.M := L.t2
      L.S.scalar t x)

/-- Smooth pointed Cheeger--Gromov convergence of the spatial metrics at one
time, packaged around the comparison maps. -/
structure PointedCGConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  maps : PointedCGHMaps (I := I) X L subseq
  metrics : SourceMetricConvergenceData (I := I) maps

/-- Smooth pointed Cheeger--Gromov--Hamilton convergence of Ricci flows on the
common time interval. -/
structure SmoothCGHConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  spatial : PointedCGConverges (I := I) X L subseq
  scalar_converges : ScalarPullbackTendsto (I := I) spatial.maps
  spacetime :
    SourceSpacetimeConvergenceData (I := I) spatial.maps
      spatial.metrics.domain

end HCGCompactness
end RicciFlower
