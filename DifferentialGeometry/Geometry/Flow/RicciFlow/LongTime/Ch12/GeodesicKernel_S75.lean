import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.TensorDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Interpolation_S66

set_option autoImplicit false

/-!
# CH12-S75 / G1b: Landau along a geodesic in a parallel frame (kernel of `hstep`)

For a smooth covariant tensor field `A` of rank `s`, a geodesic `γ` and parallel fields `V a` along
`γ`, the function `f r = A (γ r) (V · r)` has `f' = (∇A)(γ', V)` and `f'' = (∇²A)(γ', γ', V)`
(`tensor_eval_deriv` twice, parallel slots contribute nothing).  `landau_1d_S66` then bounds
`|(∇A)(γ' 0, V 0)|` by `4 (√(α β) + α / ℓ)`, where `α` bounds `|f|` and `β` bounds `|f''|` on
`[0, ℓ]`.  No chart expansion, no Christoffel lower-order term.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- first derivative of a tensor evaluated on parallel slots along a curve. -/
theorem hasDerivAt_eval_parallel_S75 {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (γ : ℝ → M) (t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (V : Fin s → (r : ℝ) → TangentSpace I (γ r))
    (hV : ∀ a, DifferentiableAt ℝ (chartRepAt (I := I) γ (V a) t) t)
    (hpar : ∀ a, covDerivAlong (I := I) g γ (V a) t = 0) :
    HasDerivAt (fun r => A (γ r) (fun a => V a r))
      (totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (LeviCivita (I := I) g) A
        (γ t) (Fin.cons ((mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ)) (fun a => V a t))) t := by
  have h := tensor_eval_deriv (I := I) g A γ V t hγ hV
  have hz : ∀ a : Fin s, A (γ t) (Function.update (fun b => V b t) a
      (covDerivAlong (I := I) g γ (V a) t)) = 0 := by
    intro a
    rw [hpar a]
    exact (A (γ t)).map_update_zero _ a
  rw [Finset.sum_eq_zero (fun a _ => hz a), add_zero] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- **Landau along a geodesic in a parallel frame.**  `A` a smooth rank-`s` covariant tensor field,
`B = ∇A` (as a field), `γ` a geodesic on `[0, ℓ]`, `V a` parallel along `γ`.  If
`|A(V)| ≤ α` and `|(∇²A)(γ', γ', V)| ≤ β` along `[0, ℓ]` then
`|(∇A)(γ' 0, V 0)| ≤ 4 (√(α β) + α / ℓ)`. -/
theorem landau_geodesic_S75 {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hB : ∀ x, B x = totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
      (LeviCivita (I := I) g) A x)
    (γ : ℝ → M) {ℓ α β : ℝ} (hℓ : 0 < ℓ)
    (hγ : ∀ t ∈ Icc 0 ℓ, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : ∀ t ∈ Icc 0 ℓ, HasGeodesicEquationAt (I := I) g γ t)
    (V : Fin s → (r : ℝ) → TangentSpace I (γ r))
    (hV : ∀ a, ∀ t ∈ Icc 0 ℓ, DifferentiableAt ℝ (chartRepAt (I := I) γ (V a) t) t)
    (hpar : ∀ a, ∀ t ∈ Icc 0 ℓ, covDerivAlong (I := I) g γ (V a) t = 0)
    (h0 : ∀ t ∈ Icc 0 ℓ, |A (γ t) (fun a => V a t)| ≤ α)
    (h2 : ∀ t ∈ Icc 0 ℓ, |totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
      (LeviCivita (I := I) g) B (γ t) (Fin.cons ((mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ))
        (Fin.cons ((mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ)) (fun a => V a t)))| ≤ β) :
    |totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (LeviCivita (I := I) g) A
        (γ 0) (Fin.cons ((mfderiv 𝓘(ℝ, ℝ) I γ 0) (1 : ℝ)) (fun a => V a 0))| ≤
      4 * (√(α * β) + α / ℓ) := by
  classical
  let W : (r : ℝ) → TangentSpace I (γ r) := fun r => (mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ)
  let X : Fin (s + 1) → (r : ℝ) → TangentSpace I (γ r) :=
    Fin.cons (α := fun _ => (r : ℝ) → TangentSpace I (γ r)) W V
  have hmd : ∀ t ∈ Icc 0 ℓ, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := fun t ht =>
    ((hγ t ht).mdifferentiableAt (by norm_num))
  have hWpar : ∀ t ∈ Icc 0 ℓ, covDerivAlong (I := I) g γ W t = 0 := fun t ht =>
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t (hγ t ht) (hgeo t ht)
  have hX : ∀ a, ∀ t ∈ Icc 0 ℓ, DifferentiableAt ℝ (chartRepAt (I := I) γ (X a) t) t := by
    intro a t ht
    refine Fin.cases ?_ (fun b => ?_) a
    · exact MFDerivAlongCurve.velocity_coord_diff (I := I) γ t (hγ t ht)
    · exact hV b t ht
  have hXpar : ∀ a, ∀ t ∈ Icc 0 ℓ, covDerivAlong (I := I) g γ (X a) t = 0 := by
    intro a t ht
    refine Fin.cases ?_ (fun b => ?_) a
    · exact hWpar t ht
    · exact hpar b t ht
  have hXt : ∀ t, (fun a => X a t) = Fin.cons (W t) (fun a => V a t) := by
    intro t
    funext a
    refine Fin.cases ?_ (fun b => ?_) a <;> simp [X]
  have hfeq : (fun r => totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
      (LeviCivita (I := I) g) A (γ r) (Fin.cons (W r) (fun a => V a r))) =
      fun r => B (γ r) (fun a => X a r) := by
    funext r
    rw [hXt r, hB]
  have hf : ∀ t ∈ Icc (0 : ℝ) ℓ, HasDerivWithinAt (fun r => A (γ r) (fun a => V a r))
      (totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (LeviCivita (I := I) g) A
        (γ t) (Fin.cons (W t) (fun a => V a t))) (Icc 0 ℓ) t := fun t ht =>
    (hasDerivAt_eval_parallel_S75 g A γ t (hmd t ht) V (fun a => hV a t ht)
      (fun a => hpar a t ht)).hasDerivWithinAt
  have hf' : ∀ t ∈ Icc (0 : ℝ) ℓ, HasDerivWithinAt
      (fun r => totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
        (LeviCivita (I := I) g) A (γ r) (Fin.cons (W r) (fun a => V a r)))
      (totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
        (LeviCivita (I := I) g) B (γ t) (Fin.cons (W t) (Fin.cons (W t) (fun a => V a t))))
      (Icc 0 ℓ) t := by
    intro t ht
    rw [hfeq]
    have h := tensor_eval_deriv (I := I) g B γ X t (hmd t ht) (fun a => hX a t ht)
    have hz : ∀ a : Fin (s + 1), B (γ t) (Function.update (fun b => X b t) a
        (covDerivAlong (I := I) g γ (X a) t)) = 0 := by
      intro a
      rw [hXpar a t ht]
      exact (B (γ t)).map_update_zero _ a
    rw [Finset.sum_eq_zero (fun a _ => hz a), add_zero, hXt t] at h
    exact h.hasDerivWithinAt
  have key := landau_1d_S66 (E := ℝ) hℓ hf hf' (M0 := α) (M2 := β)
    (fun t ht => by simpa [Real.norm_eq_abs] using h0 t ht)
    (fun t ht => by simpa [Real.norm_eq_abs] using h2 t ht) 0 ⟨le_rfl, hℓ.le⟩
  simpa [Real.norm_eq_abs] using key

end GC.LongTime.Ch12
