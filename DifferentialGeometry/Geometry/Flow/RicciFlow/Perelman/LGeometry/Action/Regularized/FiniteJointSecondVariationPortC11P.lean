import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.MovingEndpointSecondVariation
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationChain

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariation`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (about 10 errors in
`hasDerivAt_deriv_finiteJointAction_line`; first, `open scoped Topology` inside the namespace
is read as `_root_.DifferentialGeometry.Topology`, so `𝓝` is unknown).
Elaboration-level repairs:
* `open scoped _root_.Topology` instead of `open scoped Topology` (namespace clash).
* statement and `hconcl`: the bound variables of `HasDerivAt (fun u => deriv (fun z => ..) u)`
  get the ascription `(u z : ℝ)`; unannotated, `z • ξ` is elaborated with `z : ℕ` and
  `NontriviallyNormedField ℕ` fails (same elaborated statement).
* `hend`: `have h : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun u => beta i u r) := ...` (the constant `r`
  of `contMDiff_const` was an unassigned metavariable).
* `hline`: `hcont : Continuous (fun u : ℝ => u • ξ)` stated first, then `hcont.tendsto 0` (the
  type ascription on the term did not stop `simp` from seeing `id • fun _ => ξ`).
* `hjoinBeta`: `hline.eventually hjoin` for `hjoin.comp_tendsto hline` (`Filter.Eventually`
  has no `comp_tendsto`; `Tendsto.eventually` is the same statement).
* `hvelocityBeta`: `simpa only [beta, zero_smul, lVelocity] using ..` becomes
  `simp only [beta]; rw [zero_smul]; have h := hvelocity i; simp only [lVelocity] at h; exact h`
  (`zero_smul` cannot be a `simp` step inside the dependent `mfderiv` arguments; `rw` abstracts
  all occurrences at once).
* `hexpBeta`, `hboundary`: `simpa only [..] using e` becomes `have h := e; simp only [..] at h ⊢;
  exact h` (the `simpa` closing check is reducible-only and sees the `TangentSpace`/`E` instance
  paths as different; `exact` unifies at default transparency); `hexpBeta` also adds
  `Function.comp_def`.
* final step: `simpa only [index, beta, zero_smul] using hconcl` becomes
  `have h := hconcl; simp only [index, beta] at h; rw [zero_smul] at h; exact h`.
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariation` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH uP

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
  {D : Fin (n + 1) → RealTimeInterval}

/-- Second variation of the actual finite joint action along a parameter line.
Only the central curves satisfy the geodesic equation. Endpoint germs and the
actual metric and velocity transmission cancel the internal acceleration terms;
the terminal exponential germ cancels variation acceleration, without imposing
zero final velocity on the central curve. -/
theorem hasDerivAt_deriv_finiteJointAction_line
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i))
    (a b : Fin (n + 1) → ℝ)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T
      (fun r => f i (0, r)) (uIcc (a i) (b i)))
    (Phi : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (Phi i).source →
      ∀ V W : TangentSpace I x,
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner x V W =
        ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (Phi i x)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (Phi i : M i.castSucc → M i.succ) x W))
    (hjoin : ∀ᶠ z in 𝓝 (0 : P), ∀ i : Fin n,
      f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
      Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (Phi i : M i.castSucc → M i.succ)
        (f i.castSucc (0, b i.castSucc))
        (lVelocity (I := I) (fun r => f i.castSucc (0, r)) (b i.castSucc)) : E) =
          lVelocity (I := I) (fun r => f i.succ (0, r)) (a i.succ))
    (p : M 0)
    (hfirst : (fun z => f 0 (z, a 0)) =ᶠ[𝓝 (0 : P)] fun _ => p)
    (q : M (Fin.last n)) (B : P →L[ℝ] E)
    (hexp : (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace I q from B z)))
    (ξ : P) :
    HasDerivAt
      (fun u : ℝ => deriv (fun z : ℝ =>
        finiteJointAction S T f a b (z • ξ, b (Fin.last n))) u)
      (2 * ∑ i : Fin (n + 1), lRegularizedIndex (S i) T
        (fun r => f i (0, r))
        (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0)
        (fun r => lVelocity (I := I) (fun u => f i (u • ξ, r)) 0)
        (a i) (b i)) 0 := by
  let beta : (i : Fin (n + 1)) → ℝ → ℝ → M i :=
    fun i u r => f i (u • ξ, r)
  have hbeta (i : Fin (n + 1)) : IsSmoothVariation (I := I) (beta i) := by
    exact (hf i).comp
      ((contMDiff_fst.smul contMDiff_const).prodMk contMDiff_snd)
  have hgeoBeta (i : Fin (n + 1)) :
      IsLRegularizedGeodesicOn (S i) T (beta i 0) (uIcc (a i) (b i)) := by
    simpa only [beta, zero_smul] using hgeo i
  have hend (i : Fin (n + 1)) (r : ℝ) :
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u => beta i u r) 0 := by
    have h : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun u => beta i u r) :=
      (hbeta i : ContMDiff _ _ (8 : ℕ) _).comp (contMDiff_id.prodMk contMDiff_const)
    exact h.contMDiffAt.of_le (by norm_num)
  have hline : Tendsto (fun u : ℝ => u • ξ) (𝓝 0) (𝓝 (0 : P)) := by
    have hcont : Continuous (fun u : ℝ => u • ξ) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hcont.tendsto 0
  have hjoinBeta : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i : Fin n,
      beta i.castSucc u (b i.castSucc) ∈ (Phi i).source ∧
      Phi i (beta i.castSucc u (b i.castSucc)) = beta i.succ u (a i.succ) :=
    hline.eventually hjoin
  have hvelocityBeta (i : Fin n) :
      (mfderiv I I (Phi i : M i.castSucc → M i.succ)
        (beta i.castSucc 0 (b i.castSucc))
        (mfderiv 𝓘(ℝ, ℝ) I (beta i.castSucc 0) (b i.castSucc) 1) : E) =
          mfderiv 𝓘(ℝ, ℝ) I (beta i.succ 0) (a i.succ) 1 := by
    simp only [beta]
    rw [zero_smul]
    have h := hvelocity i
    simp only [lVelocity] at h
    exact h
  have hfirstBeta : (fun u => beta 0 u (a 0)) =ᶠ[𝓝 (0 : ℝ)] fun _ => p :=
    hfirst.comp_tendsto hline
  have hexpBeta : (fun u => beta (Fin.last n) u (b (Fin.last n))) =ᶠ[𝓝 (0 : ℝ)]
      (fun u => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (u • (show TangentSpace I q from B ξ))) := by
    have h := hexp.comp_tendsto hline
    simp only [beta, map_smul, Function.comp_def] at h ⊢
    exact h
  let pair (i : Fin (n + 1)) (r : ℝ) :=
    ((S i).base.metric (T - r ^ 2)).inner (beta i 0 r)
      (covDerivAlong (I := I) ((S i).base.metric (T - r ^ 2))
        (fun u => beta i u r)
        (fun u => lVelocity (I := I) (fun z => beta i z r) u) 0)
      (lVelocity (I := I) (beta i 0) r)
  let index (i : Fin (n + 1)) := lRegularizedIndex (S i) T (beta i 0)
    (fun r => lVelocity (I := I) (fun u => beta i u r) 0)
    (fun r => lVelocity (I := I) (fun u => beta i u r) 0) (a i) (b i)
  have hboundary : (∑ i : Fin (n + 1), (pair i (b i) - pair i (a i))) = 0 := by
    have h := sum_variation_acceleration_boundary_eq_zero_of_terminal_exp
        (fun i r => (S i).base.metric (T - r ^ 2)) a b beta
        (fun i => hend i.castSucc (b i.castSucc)) Phi hmetric hjoinBeta hvelocityBeta
        p hfirstBeta q (show TangentSpace I q from B ξ)
        (hend (Fin.last n) (b (Fin.last n))) hexpBeta
    simp only [pair, lVelocity] at h ⊢
    exact h
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    lRegularizedAction_second_variation_moving_endpoints
      (S i) (hS i) T (beta i) (hbeta i) (a i) (b i) (hgeoBeta i))
  have hderiv (u : ℝ) :
      deriv (fun z : ℝ => ∑ i : Fin (n + 1),
        lRegularizedAction (S i) T (beta i z) (a i) (b i)) u =
      ∑ i : Fin (n + 1), deriv (fun z : ℝ =>
        lRegularizedAction (S i) T (beta i z) (a i) (b i)) u := by
    apply deriv_fun_sum
    intro i _
    exact (contDiff_lRegularizedAction (S i) (hS i) T (beta i) (hbeta i)
      (a i) (b i) (fun r hr => (hgeoBeta i r hr).1)).differentiable
        (by norm_num) u
  have haction :
      (fun u : ℝ => finiteJointAction S T f a b (u • ξ, b (Fin.last n))) =
      (fun u => ∑ i : Fin (n + 1),
        lRegularizedAction (S i) T (beta i u) (a i) (b i)) := by
    funext u
    rw [Fin.sum_univ_castSucc]
    rfl
  have hconcl :
      HasDerivAt (fun u : ℝ => deriv (fun z : ℝ =>
        finiteJointAction S T f a b (z • ξ, b (Fin.last n))) u)
        (2 * ∑ i : Fin (n + 1), index i) 0 := by
    rw [haction]
    simp_rw [hderiv]
    apply hsum.congr_deriv
    change (∑ i : Fin (n + 1), (2 * index i + pair i (b i) - pair i (a i))) =
      2 * ∑ i : Fin (n + 1), index i
    calc
      (∑ i : Fin (n + 1), (2 * index i + pair i (b i) - pair i (a i))) =
          ∑ i : Fin (n + 1), (2 * index i + (pair i (b i) - pair i (a i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * (∑ i : Fin (n + 1), index i) +
          ∑ i : Fin (n + 1), (pair i (b i) - pair i (a i)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ i : Fin (n + 1), index i := by rw [hboundary, add_zero]
  have h := hconcl
  simp only [index, beta] at h
  rw [zero_smul] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman
