import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5GaugeFlow
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Identities
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.MetricPairing
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Operator.HessianDivergence
import DifferentialGeometry.Geometry.Metric.RicciSoliton.TensorForm
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace

/-!
# The rough Laplacian of the Hessian on a surface

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii),
review 18 §1.2: the general commutator first, for an arbitrary smooth `f`).

All covariant derivatives are the Levi-Civita `iterCov`/`covStep` of a metric `g`, new slots
first.
* `iterCov_two_swap_sub`: the Ricci identity for `iterCov g s A 2`
  (`tensor0S_ricciIdentity_of_leviCivita`); `curvatureAction0SAt_metricRm13_of_finrank_eq_two`:
  in dimension two `R(X, Y)Z = (R / 2)(⟨Y, Z⟩X - ⟨X, Z⟩Y)`.
* `oneForm_iterCov_two_swap`, `oneForm_iterCov_three_swap`: for a one-form `θ`, the antisymmetric
  part of `∇²θ` and its covariant derivative, computed on smooth vector fields.
* `covStep_two_of_eq_smul_metric`, `covStep_three_of_eq_dsmul_metric`: `∇(φ g) = dφ ⊗ g` and
  `∇(dφ ⊗ g) = ∇²φ ⊗ g`.
* `covStep_trace_iterCov_duSec`: `∇(div ∇²f) = ∇²Δf + dR ⊗ df / 2 + (R / 2) ∇²f`, from
  `hessian_divergence` (`div ∇²f = dΔf + Ric(∇f)`).
* `roughLap_iterCov_hessian`: for `H = ∇²f = covStep g 1 (duSec f)`,
  `ΔH = ∇²Δf + 2 R H - R (Δf) g + ½ (dR ⊗ df + df ⊗ dR - ⟨∇R, ∇f⟩ g)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.RicciIdentity
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
theorem tensorField_apply_mdifferentiableAt {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y (fun q : Fin s => V q y)) x := by
  have h := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M) (n := s) (x₀ := x)
    (T := fun y : M => A y) (A.contMDiff x) (v := fun q : Fin s => V q)
    (hv := fun q => (V q).contMDiff.contMDiffAt)
  exact h.mdifferentiableAt (by simp)

omit [I.Boundaryless] [T2Space M] in
theorem inner_sections_mdifferentiableAt (g : SmoothRiemannianMetric I M)
    (B C : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => g.inner y (B y) (C y)) x := by
  have h := tensorField_apply_mdifferentiableAt (metricTensorField g) ![B, C] x
  convert h using 2 with y
  rw [metricTensorField_apply]
  rfl

omit [I.Boundaryless] in
theorem covStep_two_eval (g : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (A B C : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    covStep g 2 P x ![A x, B x, C x] =
      mvfderiv (I := I) (fun y => P y ![B y, C y]) x (A x) -
        (P x ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x), C x] +
          P x ![B x, leviCivitaConnectionOfMetric g (fun y => C y) x (A x)]) := by
  have h := covStep_eval_smooth_slots g 2 P A ![B, C] x
  rw [Fin.sum_univ_two] at h
  have e1 : (Fin.cons (A x) (fun q : Fin 2 => (![B, C] : Fin 2 → _) q x) : Fin 3 → _) =
      ![A x, B x, C x] := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun y : M => P y (fun q : Fin 2 => (![B, C] : Fin 2 → _) q y)) =
      fun y : M => P y ![B y, C y] := by
    funext y; congr 1; funext i; fin_cases i <;> rfl
  have u0 : Function.update (fun b : Fin 2 => (![B, C] : Fin 2 → _) b x) 0
      (leviCivitaConnectionOfMetric g (fun y => (![B, C] : Fin 2 → _) 0 y) x (A x)) =
      ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x), C x] := by
    funext i; fin_cases i <;> rfl
  have u1 : Function.update (fun b : Fin 2 => (![B, C] : Fin 2 → _) b x) 1
      (leviCivitaConnectionOfMetric g (fun y => (![B, C] : Fin 2 → _) 1 y) x (A x)) =
      ![B x, leviCivitaConnectionOfMetric g (fun y => C y) x (A x)] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, u0, u1] at h
  exact h

omit [I.Boundaryless] in
theorem covStep_three_eval (g : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (A B C D : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    covStep g 3 P x ![A x, B x, C x, D x] =
      mvfderiv (I := I) (fun y => P y ![B y, C y, D y]) x (A x) -
        (P x ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x), C x, D x] +
          P x ![B x, leviCivitaConnectionOfMetric g (fun y => C y) x (A x), D x] +
          P x ![B x, C x, leviCivitaConnectionOfMetric g (fun y => D y) x (A x)]) := by
  have h := covStep_eval_smooth_slots g 3 P A ![B, C, D] x
  rw [Fin.sum_univ_three] at h
  have e1 : (Fin.cons (A x) (fun q : Fin 3 => (![B, C, D] : Fin 3 → _) q x) : Fin 4 → _) =
      ![A x, B x, C x, D x] := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun y : M => P y (fun q : Fin 3 => (![B, C, D] : Fin 3 → _) q y)) =
      fun y : M => P y ![B y, C y, D y] := by
    funext y; congr 1; funext i; fin_cases i <;> rfl
  have u0 : Function.update (fun b : Fin 3 => (![B, C, D] : Fin 3 → _) b x) 0
      (leviCivitaConnectionOfMetric g (fun y => (![B, C, D] : Fin 3 → _) 0 y) x (A x)) =
      ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x), C x, D x] := by
    funext i; fin_cases i <;> rfl
  have u1 : Function.update (fun b : Fin 3 => (![B, C, D] : Fin 3 → _) b x) 1
      (leviCivitaConnectionOfMetric g (fun y => (![B, C, D] : Fin 3 → _) 1 y) x (A x)) =
      ![B x, leviCivitaConnectionOfMetric g (fun y => C y) x (A x), D x] := by
    funext i; fin_cases i <;> rfl
  have u2 : Function.update (fun b : Fin 3 => (![B, C, D] : Fin 3 → _) b x) 2
      (leviCivitaConnectionOfMetric g (fun y => (![B, C, D] : Fin 3 → _) 2 y) x (A x)) =
      ![B x, C x, leviCivitaConnectionOfMetric g (fun y => D y) x (A x)] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, u0, u1, u2] at h
  exact h

omit [I.Boundaryless] in
theorem covStep_one_eval (g : SmoothRiemannianMetric I M)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (A B : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    mvfderiv (I := I) (fun y : M => θ y ![B y]) x (A x) =
      covStep g 1 θ x ![A x, B x] +
        θ x ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x)] := by
  have h := covStep_eval_smooth_slots g 1 θ A ![B] x
  rw [Fin.sum_univ_one] at h
  have e1 : (Fin.cons (A x) (fun q : Fin 1 => (![B] : Fin 1 → _) q x) : Fin 2 → _) =
      ![A x, B x] := by
    funext i; fin_cases i <;> rfl
  have e2 : Function.update (fun b : Fin 1 => (![B] : Fin 1 → _) b x) 0
      (leviCivitaConnectionOfMetric g (fun y => (![B] : Fin 1 → _) 0 y) x (A x)) =
      ![leviCivitaConnectionOfMetric g (fun y => B y) x (A x)] := by
    funext i; fin_cases i; rfl
  have e3 : (fun y : M => θ y (fun q : Fin 1 => (![B] : Fin 1 → _) q y)) =
      fun y : M => θ y ![B y] := by
    funext y; congr 1; funext i; fin_cases i; rfl
  rw [e1, e2, e3] at h
  linarith

omit [I.Boundaryless] [T2Space M] in
theorem metricCompatible_mvfderiv (g : SmoothRiemannianMetric I M)
    (A B C : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    mvfderiv (I := I) (fun y => g.inner y (B y) (C y)) x (A x) =
      g.inner x (leviCivitaConnectionOfMetric g (fun y => B y) x (A x)) (C x) +
        g.inner x (B x) (leviCivitaConnectionOfMetric g (fun y => C y) x (A x)) :=
  leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
    ((B.contMDiff x).mdifferentiableAt (by simp))
    ((C.contMDiff x).mdifferentiableAt (by simp)) (mem_univ x) (A x)

omit [I.Boundaryless] in
theorem covStep_two_of_eq_smul_metric (g : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hP : ∀ y (v w : TangentSpace I y), P y ![v, w] = φ y * g.inner y v w)
    (x : M) (a b c : TangentSpace I x) :
    covStep g 2 P x ![a, b, c] = mvfderiv (I := I) φ x a * g.inner x b c := by
  obtain ⟨A, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨B, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x b
  obtain ⟨C, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x c
  rw [covStep_two_eval, hP, hP]
  have hfun : (fun y => P y ![B y, C y]) = fun y => φ y * g.inner y (B y) (C y) := by
    funext y; exact hP y (B y) (C y)
  rw [hfun, mvfderiv_fun_mul ((hφ x).mdifferentiableAt (by simp))
    (inner_sections_mdifferentiableAt g B C x)]
  simp only [add_apply, smul_apply, smul_eq_mul, metricCompatible_mvfderiv]
  ring

omit [I.Boundaryless] in
theorem covStep_three_of_eq_dsmul_metric (g : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hP : ∀ y (a v w : TangentSpace I y),
      P y ![a, v, w] = mvfderiv (I := I) φ y a * g.inner y v w)
    (x : M) (a' a b c : TangentSpace I x) :
    covStep g 3 P x ![a', a, b, c] = covStep g 1 (duSec φ hφ) x ![a', a] * g.inner x b c := by
  obtain ⟨A', rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x a'
  obtain ⟨A, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨B, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x b
  obtain ⟨C, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x c
  have hd : ∀ y (v : TangentSpace I y), duSec φ hφ y ![v] = mvfderiv (I := I) φ y v := by
    intro y v
    rw [duSec_apply]
    have e : (![v] : Fin 1 → TangentSpace I y) = fun _ => v := by
      funext i; fin_cases i; rfl
    rw [e, differential1FormFun_apply_eq_mvfderiv]
  rw [covStep_three_eval, hP, hP, hP]
  have hfun : (fun y => P y ![A y, B y, C y]) =
      fun y => duSec φ hφ y ![A y] * g.inner y (B y) (C y) := by
    funext y; rw [hP, hd]
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => duSec φ hφ y ![A y]) x := by
    have h := tensorField_apply_mdifferentiableAt (duSec φ hφ) ![A] x
    convert h using 3 with y
    funext i; fin_cases i; rfl
  rw [hfun, mvfderiv_fun_mul hmd (inner_sections_mdifferentiableAt g B C x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [covStep_one_eval g (duSec φ hφ) A' A x]
  simp only [metricCompatible_mvfderiv, hd]
  ring


omit [I.Boundaryless] [T2Space M] in
theorem metricTraceFirstTwo0SAt_eq_sum_orthonormal (g : SmoothRiemannianMetric I M) {x : M}
    {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : ℝ) else 0) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt g T tail = ∑ i, T (metricTraceInput (b i) (b i) tail) := by
  classical
  rw [metricTraceFirstTwo0SAt_eq_sum_basis g b _ (metricInverseInBasis_of_orthonormal g b hb)]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [identityInvMetric]
  · intro j _ hji
    simp [identityInvMetric, diagonalInvMetric, Ne.symm hji]
  · simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem sum_inner_orthonormal_mul (g : SmoothRiemannianMetric I M) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (L : TangentSpace I x →ₗ[ℝ] ℝ) (v : TangentSpace I x) :
    ∑ i, g.inner x (b i) v * L (b i) = L v := by
  classical
  have hrepr : ∀ i, b.repr v i = g.inner x (b i) v := by
    intro i
    conv_rhs => rw [← b.sum_repr v]
    rw [map_sum, Finset.sum_eq_single i]
    · rw [map_smul, smul_eq_mul, hb]
      simp
    · intro j _ hji
      rw [map_smul, smul_eq_mul, hb]
      simp [Ne.symm hji]
    · simp
  conv_rhs => rw [← b.sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, hrepr]

omit [I.Boundaryless] [T2Space M] in
theorem duSec_apply_vec (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M)
    (v : TangentSpace I y) : duSec f hf y ![v] = mvfderiv (I := I) f y v := by
  rw [duSec_apply]
  have e : (![v] : Fin 1 → TangentSpace I y) = fun _ => v := by
    funext i; fin_cases i; rfl
  rw [e, differential1FormFun_apply_eq_mvfderiv]

theorem covStep_duSec_apply_vec (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) (v w : TangentSpace I y) :
    covStep g 1 (duSec f hf) y ![v, w] = hessFun g f y v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have e : (![v, w] : Fin 2 → TangentSpace I y) = vec2 v w := by
    funext i; fin_cases i <;> rfl
  rw [e]
  exact hessianSec_metricCov_eq_hessFun g hf y v w

theorem trace_iterCov_duSec_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (y : M) (v : TangentSpace I y) :
    metricTraceFirstTwo0SAt g (iterCov g 1 (duSec f f.contMDiff) 2 y) ![v] =
      mvfderiv (I := I) (ΔG g f) y v +
        metricScalarAt g y / 2 * mvfderiv (I := I) f y v := by
  have e : (![v] : Fin 1 → TangentSpace I y) = fun _ => v := by
    funext i; fin_cases i; rfl
  rw [e]
  have h := hessian_divergence g f y v
  have hlap : (laplacian (metricCov g) g f) = ΔG g f := by
    funext z; exact laplacian_levi_eq g f.contMDiff z
  rw [hlap, differential1FormFun_apply_eq_mvfderiv,
    metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two g hdim,
    Tensor0SSpace.smul_apply, metricTensor0S_apply, smul_eq_mul] at h
  refine h.trans ?_
  congr 1
  congr 1
  change g.inner y v (gradientFun g f y) = _
  rw [g.symm]
  exact inner_gradFun g f y v


theorem covStep_trace_iterCov_duSec (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) (c d : TangentSpace I x) :
    covStep g 1 (metricTraceFirstTwoField g (iterCov g 1 (duSec f f.contMDiff) 2)) x ![c, d] =
      hessFun g (ΔG g f) x c d +
        mvfderiv (I := I) (fun y => metricScalarAt g y) x c / 2 * mvfderiv (I := I) f x d +
        metricScalarAt g x / 2 * hessFun g f x c d := by
  obtain ⟨C, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x c
  obtain ⟨D, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x d
  set tr := metricTraceFirstTwoField g (iterCov g 1 (duSec f f.contMDiff) 2) with htr
  set R : M → ℝ := fun y => metricScalarAt g y with hR
  have hΔ := Δ_g_contMDiff g f
  have htr_apply : ∀ y (v : TangentSpace I y), tr y ![v] =
      duSec (ΔG g f) hΔ y ![v] + (1 / 2 * R y) * duSec f f.contMDiff y ![v] := by
    intro y v
    rw [htr, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      trace_iterCov_duSec_two hdim, duSec_apply_vec, duSec_apply_vec]
    ring
  have h := covStep_one_eval g tr C D x
  have hfun : (fun y => tr y ![D y]) = fun y =>
      duSec (ΔG g f) hΔ y ![D y] + (1 / 2 * R y) * duSec f f.contMDiff y ![D y] := by
    funext y; exact htr_apply y (D y)
  have md1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => duSec (ΔG g f) hΔ y ![D y]) x := by
    have h := tensorField_apply_mdifferentiableAt (duSec (ΔG g f) hΔ) ![D] x
    convert h using 3 with y
    funext i; fin_cases i; rfl
  have md2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => duSec f f.contMDiff y ![D y]) x := by
    have h := tensorField_apply_mdifferentiableAt (duSec f f.contMDiff) ![D] x
    convert h using 3 with y
    funext i; fin_cases i; rfl
  have mdR : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => 1 / 2 * R y) x :=
    mdifferentiableAt_const.mul ((metricScalar_smooth g x).mdifferentiableAt (by simp))
  have md3 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => (1 / 2 * R y) * duSec f f.contMDiff y ![D y]) x := mdR.mul md2
  rw [hfun, mvfderiv_fun_add md1 md3, mvfderiv_fun_mul mdR md2,
    mvfderiv_const_mul I _ ((metricScalar_smooth g x).mdifferentiableAt (by simp))] at h
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  rw [covStep_one_eval g (duSec (ΔG g f) hΔ) C D x,
    covStep_one_eval g (duSec f f.contMDiff) C D x,
    htr_apply, covStep_duSec_apply_vec, covStep_duSec_apply_vec] at h
  simp only [hR, duSec_apply_vec] at h ⊢
  linarith

omit [I.Boundaryless] in
theorem sum_iterCov_duSec_three (g : SmoothRiemannianMetric I M)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (c d : TangentSpace I x) :
    ∑ i, iterCov g 1 θ 3 x ![c, b i, b i, d] =
      covStep g 1 (metricTraceFirstTwoField g (iterCov g 1 θ 2)) x ![c, d] := by
  classical
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have h := nabla_metricTraceFirstTwo0S (s := 1) (leviCivitaConnectionOfMetric g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible g) (iterCov g 1 θ 2) b identityInvMetric
    (metricInverseInBasis_of_orthonormal g b hb) c ![d]
  change covStep g 1 (metricTraceFirstTwoField g (iterCov g 1 θ 2)) x ![c, d] = _ at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [identityInvMetric, diagonalInvMetric, ite_true, one_mul]
    change _ = iterCov g 1 θ 3 x (Fin.cons c (metricTraceInput (b i) (b i) ![d]))
    congr 1
  · intro j _ hji
    simp [identityInvMetric, diagonalInvMetric, Ne.symm hji]
  · simp

omit [I.Boundaryless] in
theorem iterCov_two_swap_sub (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (X Y : TangentSpace I x)
    (slots : Fin s → TangentSpace I x) :
    iterCov g s A 2 x (metricTraceInput X Y slots) -
        iterCov g s A 2 x (metricTraceInput Y X slots) =
      curvatureAction0SAt (metricRm13 g) (A x) X Y slots := by
  have hR0 := DifferentialGeometry.PDE.RicciFlow.iterCov_realizes g A 0
  have hR1 := DifferentialGeometry.PDE.RicciFlow.iterCov_realizes g A 1
  have hnabla2 : Nabla20SRealizesAt (I := I) s (leviCivitaConnectionOfMetric (I := I) g) A
      (iterCov g s A 1) x (iterCov g s A 2 x) := by
    constructor
    · intro y X slots
      exact hR0 X y slots
    · intro X slots
      exact hR1 X x slots
  exact tensor0S_ricciIdentity_of_leviCivita g (metricRm13 g) A (iterCov g s A 1) (A x)
    (iterCov g s A 1 x) (iterCov g s A 2 x) (metricCurvatureSections g).rm13Realizes rfl rfl
    hnabla2 X Y slots

theorem curvatureAction0SAt_metricRm13_of_finrank_eq_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M}
    (α : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    curvatureAction0SAt (metricRm13 g) α X Y slots =
      -∑ q : Fin s, α (Function.update slots q ((metricScalarAt g x / 2) •
        (g.inner x Y (slots q) • X - g.inner x X (slots q) • Y))) := by
  unfold curvatureAction0SAt
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [metricRm13_apply, metricRm13At_eq_riemannCurvatureAt,
    CovariantDerivative.riemannCurvatureAt_apply_const,
    connectionRiemannCurvatureField_tangentConst_eq_riemannOp (LeviCivita g)
      (leviCivita_contMDiffCovariantDerivativeLocally g),
    riemannOp_eq_scalar_div_two_of_finrank_eq_two g hdim, cotangentToDual_apply,
    oneFormAtSlot0S_apply]


theorem oneForm_iterCov_two_swap (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) (y : M) (X Y Z : TangentSpace I y) :
    iterCov g 1 θ 2 y ![X, Y, Z] - iterCov g 1 θ 2 y ![Y, X, Z] =
      -(metricScalarAt g y / 2) *
        (g.inner y Y Z * θ y ![X] - g.inner y X Z * θ y ![Y]) := by
  have h := iterCov_two_swap_sub g θ y X Y ![Z]
  rw [curvatureAction0SAt_metricRm13_of_finrank_eq_two hdim] at h
  have e1 : metricTraceInput X Y ![Z] = ![X, Y, Z] := by
    funext i; fin_cases i <;> rfl
  have e2 : metricTraceInput Y X ![Z] = ![Y, X, Z] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2] at h
  rw [h, Fin.sum_univ_one]
  have e3 : Function.update ![Z] 0 ((metricScalarAt g y / 2) •
      (g.inner y Y (![Z] 0) • X - g.inner y X (![Z] 0) • Y)) =
      fun _ : Fin 1 =>
        (metricScalarAt g y / 2) • (g.inner y Y Z • X - g.inner y X Z • Y) := by
    funext i; fin_cases i; rfl
  rw [e3]
  have hlin : ∀ (c : ℝ) (u w : TangentSpace I y), θ y (fun _ : Fin 1 => c • u - w) =
      c * θ y (fun _ : Fin 1 => u) - θ y (fun _ : Fin 1 => w) := by
    intro c u w
    have h1 := (θ y).map_update_sub (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 (c • u) w
    have h2 := (θ y).map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 c u
    have hu : ∀ v : TangentSpace I y,
        Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 v = fun _ => v := by
      intro v; funext i; fin_cases i; rfl
    simp only [hu] at h1 h2
    rw [smul_eq_mul] at h2
    exact h1.trans (congrArg (· - _) h2)
  have hsm : ∀ (c : ℝ) (u : TangentSpace I y), θ y (fun _ : Fin 1 => c • u) =
      c * θ y (fun _ : Fin 1 => u) := by
    intro c u
    have h2 := (θ y).map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 c u
    have hu : ∀ v : TangentSpace I y,
        Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 v = fun _ => v := by
      intro v; funext i; fin_cases i; rfl
    simp only [hu] at h2
    rw [smul_eq_mul] at h2
    exact h2
  rw [hsm, hlin, hsm]
  have e4 : ∀ v : TangentSpace I y, (fun _ : Fin 1 => v) = ![v] := by
    intro v; funext i; fin_cases i; rfl
  rw [e4, e4]
  ring


theorem oneForm_iterCov_three_swap (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) (x : M) (a b c d : TangentSpace I x) :
    iterCov g 1 θ 3 x ![a, b, c, d] - iterCov g 1 θ 3 x ![a, c, b, d] =
      -(mvfderiv (I := I) (fun y => metricScalarAt g y) x a / 2) *
          (g.inner x c d * θ x ![b] - g.inner x b d * θ x ![c]) -
        metricScalarAt g x / 2 *
          (g.inner x c d * iterCov g 1 θ 1 x ![a, b] -
            g.inner x b d * iterCov g 1 θ 1 x ![a, c]) := by
  obtain ⟨A, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨B, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x b
  obtain ⟨C, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x c
  obtain ⟨D, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x d
  set T3 := iterCov g 1 θ 2 with hT3
  set cov := leviCivitaConnectionOfMetric (I := I) g with hcov
  set R : M → ℝ := fun y => metricScalarAt g y with hR
  have hev : ∀ (P Q W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)),
      iterCov g 1 θ 3 x ![A x, P x, Q x, W x] =
        mvfderiv (I := I) (fun y => T3 y ![P y, Q y, W y]) x (A x) -
          (T3 x ![cov (fun y => P y) x (A x), Q x, W x] +
            T3 x ![P x, cov (fun y => Q y) x (A x), W x] +
            T3 x ![P x, Q x, cov (fun y => W y) x (A x)]) := by
    intro P Q W
    have h := covStep_eval_smooth_slots g 3 T3 A ![P, Q, W] x
    rw [Fin.sum_univ_three] at h
    have e1 : (Fin.cons (A x) (fun q : Fin 3 => (![P, Q, W] : Fin 3 → _) q x) : Fin 4 → _) =
        ![A x, P x, Q x, W x] := by
      funext i; fin_cases i <;> rfl
    have e2 : (fun y : M => T3 y (fun q : Fin 3 => (![P, Q, W] : Fin 3 → _) q y)) =
        fun y : M => T3 y ![P y, Q y, W y] := by
      funext y; congr 1; funext i; fin_cases i <;> rfl
    have u0 : Function.update (fun b : Fin 3 => (![P, Q, W] : Fin 3 → _) b x) 0
        (cov (fun y => (![P, Q, W] : Fin 3 → _) 0 y) x (A x)) =
        ![cov (fun y => P y) x (A x), Q x, W x] := by
      funext i; fin_cases i <;> rfl
    have u1 : Function.update (fun b : Fin 3 => (![P, Q, W] : Fin 3 → _) b x) 1
        (cov (fun y => (![P, Q, W] : Fin 3 → _) 1 y) x (A x)) =
        ![P x, cov (fun y => Q y) x (A x), W x] := by
      funext i; fin_cases i <;> rfl
    have u2 : Function.update (fun b : Fin 3 => (![P, Q, W] : Fin 3 → _) b x) 2
        (cov (fun y => (![P, Q, W] : Fin 3 → _) 2 y) x (A x)) =
        ![P x, Q x, cov (fun y => W y) x (A x)] := by
      funext i; fin_cases i <;> rfl
    rw [e1, e2, u0, u1, u2] at h
    exact h
  have hS1 := oneForm_iterCov_two_swap hdim g θ
  have hfun : (fun y => T3 y ![B y, C y, D y] - T3 y ![C y, B y, D y]) =
      fun y => (-(1 / 2) * R y) * (g.inner y (C y) (D y) * θ y ![B y] -
        g.inner y (B y) (D y) * θ y ![C y]) := by
    funext y
    rw [hS1 y (B y) (C y) (D y)]
    ring
  have mdT : ∀ (P Q W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => T3 y ![P y, Q y, W y]) x := by
    intro P Q W
    have h := tensorField_apply_mdifferentiableAt T3 ![P, Q, W] x
    convert h using 3 with y
    funext i; fin_cases i <;> rfl
  have mdθ : ∀ P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => θ y ![P y]) x := by
    intro P
    have h := tensorField_apply_mdifferentiableAt θ ![P] x
    convert h using 3 with y
    funext i; fin_cases i; rfl
  have mdR : MDifferentiableAt I 𝓘(ℝ, ℝ) R x :=
    (metricScalar_smooth g x).mdifferentiableAt (by simp)
  have mdG := inner_sections_mdifferentiableAt g
  have hmc := leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hG : ∀ P Q : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      mvfderiv (I := I) (fun y => g.inner y (P y) (Q y)) x (A x) =
        g.inner x (cov (fun y => P y) x (A x)) (Q x) +
          g.inner x (P x) (cov (fun y => Q y) x (A x)) := by
    intro P Q
    exact hmc ((P.contMDiff x).mdifferentiableAt (by simp))
      ((Q.contMDiff x).mdifferentiableAt (by simp)) (mem_univ x) (A x)
  have hθ := covStep_one_eval g θ A
  have hD : mvfderiv (I := I) (fun y => T3 y ![B y, C y, D y]) x (A x) -
      mvfderiv (I := I) (fun y => T3 y ![C y, B y, D y]) x (A x) =
      -(mvfderiv (I := I) R x (A x) / 2) *
          (g.inner x (C x) (D x) * θ x ![B x] - g.inner x (B x) (D x) * θ x ![C x]) -
        R x / 2 * ((g.inner x (cov (fun y => C y) x (A x)) (D x) +
            g.inner x (C x) (cov (fun y => D y) x (A x))) * θ x ![B x] +
          g.inner x (C x) (D x) * (iterCov g 1 θ 1 x ![A x, B x] +
            θ x ![cov (fun y => B y) x (A x)]) -
          ((g.inner x (cov (fun y => B y) x (A x)) (D x) +
            g.inner x (B x) (cov (fun y => D y) x (A x))) * θ x ![C x] +
          g.inner x (B x) (D x) * (iterCov g 1 θ 1 x ![A x, C x] +
            θ x ![cov (fun y => C y) x (A x)]))) := by
    have md1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => -(1 / 2 : ℝ) * R y) x :=
      mdifferentiableAt_const.mul mdR
    have md2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => g.inner y (C y) (D y) * θ y ![B y]) x := (mdG C D x).mul (mdθ B)
    have md3 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => g.inner y (B y) (D y) * θ y ![C y]) x := (mdG B D x).mul (mdθ C)
    have md4 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => g.inner y (C y) (D y) * θ y ![B y] -
          g.inner y (B y) (D y) * θ y ![C y]) x := md2.sub md3
    rw [show iterCov g 1 θ 1 = covStep g 1 θ from rfl]
    rw [← sub_apply, ← mvfderiv_fun_sub (mdT B C D) (mdT C B D), hfun]
    rw [mvfderiv_fun_mul md1 md4, mvfderiv_fun_sub md2 md3,
      mvfderiv_fun_mul (mdG C D x) (mdθ B), mvfderiv_fun_mul (mdG B D x) (mdθ C)]
    have hRd : mvfderiv (I := I) (fun y => -(1 / 2) * R y) x (A x) =
        -(mvfderiv (I := I) R x (A x) / 2) := by
      rw [mvfderiv_const_mul I _ mdR]
      simp only [smul_apply, smul_eq_mul]
      ring
    simp only [add_apply, sub_apply,
      smul_apply, smul_eq_mul, hRd, hG, hθ]
    ring
  have h1 := hev B C D
  have h2 := hev C B D
  have s1 := hS1 x (cov (fun y => B y) x (A x)) (C x) (D x)
  have s2 := hS1 x (B x) (cov (fun y => C y) x (A x)) (D x)
  have s3 := hS1 x (B x) (C x) (cov (fun y => D y) x (A x))
  rw [h1, h2]
  linear_combination hD - s1 - s2 - s3


theorem roughLap_iterCov_hessian (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) (c d : TangentSpace I x) :
    roughLap0STensor g (iterCov g 2 (covStep g 1 (duSec f f.contMDiff)) 2 x) ![c, d] =
      hessFun g (ΔG g f) x c d + 2 * metricScalarAt g x * hessFun g f x c d -
        metricScalarAt g x * ΔG g f x * g.inner x c d +
        (mvfderiv (I := I) (fun y => metricScalarAt g y) x c * mvfderiv (I := I) f x d +
          mvfderiv (I := I) f x c * mvfderiv (I := I) (fun y => metricScalarAt g y) x d -
          mvfderiv (I := I) (fun y => metricScalarAt g y) x (gradFun g f x) *
            g.inner x c d) / 2 := by
  classical
  set θ := duSec f f.contMDiff with hθ
  set Rx := metricScalarAt g x with hRx
  set dR := mvfderiv (I := I) (fun y => metricScalarAt g y) x with hdR
  set h := hessFun g f x with hh
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [roughLap0STensor_apply, metricTraceFirstTwo0SAt_eq_sum_orthonormal g b hb]
  change ∑ i, iterCov g 1 θ 3 x (metricTraceInput (b i) (b i) ![c, d]) = _
  have hin : ∀ i, metricTraceInput (b i) (b i) ![c, d] = ![b i, b i, c, d] := by
    intro i; funext k; fin_cases k <;> rfl
  simp only [hin]
  have hH : ∀ v w : TangentSpace I x, covStep g 1 θ x ![v, w] = h v w := fun v w =>
    covStep_duSec_apply_vec g f f.contMDiff x v w
  have hH1 : ∀ v w : TangentSpace I x, iterCov g 1 θ 1 x ![v, w] = h v w := hH
  have hθx : ∀ v : TangentSpace I x, θ x ![v] = mvfderiv (I := I) f x v := fun v =>
    duSec_apply_vec f f.contMDiff x v
  have hper : ∀ e : TangentSpace I x, iterCov g 1 θ 3 x ![e, e, c, d] =
      iterCov g 1 θ 3 x ![c, e, e, d] +
        (-(dR e / 2) * (g.inner x c d * mvfderiv (I := I) f x e -
            g.inner x e d * mvfderiv (I := I) f x c) -
          Rx / 2 * (g.inner x c d * h e e - g.inner x e d * h e c) -
          Rx / 2 * (g.inner x c e * h e d - g.inner x e e * h c d) -
          Rx / 2 * (g.inner x c d * h e e - g.inner x e d * h e c)) := by
    intro e
    have s2 := oneForm_iterCov_three_swap hdim g θ x e e c d
    have s3 := iterCov_two_swap_sub g (covStep g 1 θ) x e c ![e, d]
    rw [curvatureAction0SAt_metricRm13_of_finrank_eq_two hdim, Fin.sum_univ_two] at s3
    have i1 : metricTraceInput e c ![e, d] = ![e, c, e, d] := by
      funext k; fin_cases k <;> rfl
    have i2 : metricTraceInput c e ![e, d] = ![c, e, e, d] := by
      funext k; fin_cases k <;> rfl
    have u0 : ∀ w : TangentSpace I x, Function.update ![e, d] 0 w = ![w, d] := by
      intro w; funext k; fin_cases k <;> rfl
    have u1 : ∀ w : TangentSpace I x, Function.update ![e, d] 1 w = ![e, w] := by
      intro w; funext k; fin_cases k <;> rfl
    rw [i1, i2, u0, u1, hH, hH] at s3
    change iterCov g 1 θ 3 x ![e, c, e, d] - iterCov g 1 θ 3 x ![c, e, e, d] = _ at s3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul] at s3
    rw [hθx, hθx, hH1, hH1] at s2
    linear_combination s2 + s3
  rw [Finset.sum_congr rfl (fun i _ => hper (b i)), Finset.sum_add_distrib,
    sum_iterCov_duSec_three g θ b hb c d, covStep_trace_iterCov_duSec hdim g f x c d]
  have hsym : ∀ v w : TangentSpace I x, h v w = h w v := fun v w =>
    hessFun_symm_of_boundaryless g f.contMDiff x v w
  have sum1 : ∑ i, dR (b i) * mvfderiv (I := I) f x (b i) = dR (gradFun g f x) := by
    refine Eq.trans ?_ (sum_inner_orthonormal_mul g b hb dR.toLinearMap (gradFun g f x))
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g.symm, inner_gradFun]
    change _ = mvfderiv (I := I) f x (b i) * dR (b i)
    ring
  have sum2 : ∑ i, g.inner x (b i) d * dR (b i) = dR d :=
    sum_inner_orthonormal_mul g b hb dR.toLinearMap d
  have sum3 : ∑ i, h (b i) (b i) = ΔG g f x := by
    refine (laplacian_eq_sum_hessFun g f f.contMDiff x b hb).symm.trans ?_
    exact laplacian_levi_eq g f.contMDiff x
  have sum4 : ∑ i, g.inner x (b i) d * h (b i) c = h c d := by
    rw [hsym c d]
    exact sum_inner_orthonormal_mul g b hb (h.flip c) d
  have sum5 : ∑ i, g.inner x c (b i) * h (b i) d = h c d := by
    refine Eq.trans ?_ (sum_inner_orthonormal_mul g b hb (h.flip d) c)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g.symm]
    rfl
  have sum6 : ∑ i, g.inner x (b i) (b i) = 2 := by
    simp only [hb, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    have : Module.finrank ℝ (TangentSpace I x) = 2 := hdim
    rw [this]
    norm_num
  have hexp : ∑ i, (-(dR (b i) / 2) * (g.inner x c d * mvfderiv (I := I) f x (b i) -
            g.inner x (b i) d * mvfderiv (I := I) f x c) -
          Rx / 2 * (g.inner x c d * h (b i) (b i) - g.inner x (b i) d * h (b i) c) -
          Rx / 2 * (g.inner x c (b i) * h (b i) d - g.inner x (b i) (b i) * h c d) -
          Rx / 2 * (g.inner x c d * h (b i) (b i) - g.inner x (b i) d * h (b i) c)) =
      -(g.inner x c d / 2) * ∑ i, dR (b i) * mvfderiv (I := I) f x (b i) +
        mvfderiv (I := I) f x c / 2 * ∑ i, g.inner x (b i) d * dR (b i) -
        Rx * g.inner x c d * ∑ i, h (b i) (b i) +
        Rx * ∑ i, g.inner x (b i) d * h (b i) c -
        Rx / 2 * ∑ i, g.inner x c (b i) * h (b i) d +
        Rx / 2 * h c d * ∑ i, g.inner x (b i) (b i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp, sum1, sum2, sum3, sum4, sum5, sum6]
  ring

end GC.Geometry
