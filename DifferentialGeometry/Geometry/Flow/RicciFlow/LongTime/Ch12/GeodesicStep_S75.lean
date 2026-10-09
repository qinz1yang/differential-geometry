import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GeodesicKernel_S75
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false

/-!
# CH12-S75 / G1c: component bounds in an orthonormal tuple, and the pointwise Landau step on a tensor

`abs_eval_orthonormal_le_S75`: an `h`-orthonormal tuple `P : Fin n → T_yM` (`n = dim`) is a basis, so
`|A (P ∘ slots)| ≤ √(normSq0S h y s A)`.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
/-- an orthonormal tuple of `n = dim` tangent vectors is a basis. -/
theorem linearIndependent_of_orthonormal_S75 (g : SmoothRiemannianMetric I M) (y : M)
    (P : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hP : ∀ i j, g.inner y (P i) (P j) = if i = j then 1 else 0) : LinearIndependent ℝ P := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun v => g.inner y v (P j)) hc
  simp [hP] at h
  simpa using h

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- component of a covariant tensor in an orthonormal tuple is bounded by its norm. -/
theorem abs_eval_orthonormal_le_S75 (g : SmoothRiemannianMetric I M) (y : M) {s : ℕ}
    (P : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hP : ∀ i j, g.inner y (P i) (P j) = if i = j then 1 else 0)
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s y)
    (slots : Fin s → Fin (Module.finrank ℝ E)) :
    |A (fun k => P (slots k))| ≤ Real.sqrt (normSq0S (I := I) g y s A) := by
  classical
  have hli := linearIndependent_of_orthonormal_S75 g y P hP
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)
  have hb : ∀ i, b i = P i := fun i => by simp [b]
  have hON : ∀ i j, g.inner y (b i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [hb, hb]; exact hP i j
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g b hON
  have := DifferentialGeometry.Geometry.Curvature.abs_component0S_le_sqrt_normSq0S (I := I) g b hinv A slots
  simpa [component0S, hb] using this

omit [SigmaCompactSpace M] in
/-- **Pointwise Landau step on a tensor field (modulo the geodesic frames `hgeo`).**
`A : Tensor0SField s`, `B = ∇A`, `C = ∇B`.  If `|A| ≤ α` and `|∇²A| ≤ β` on `K'`, and every
`h`-orthonormal basis `e` at every `x ∈ K` and every direction `a` has a geodesic `γ_a` on `[0, ℓ]`
inside `K'` with `γ_a' = P a`, `P` a parallel orthonormal frame, `P 0 = e`, then
`|∇A (x)|² ≤ n^(s+1) (4 (√(α β) + α / ℓ))²` at every `x ∈ K`. -/
theorem landau_step_S75 {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (C : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hB : ∀ x, B x = totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
      (LeviCivita (I := I) g) A x)
    (hC : ∀ x, C x = totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
      (LeviCivita (I := I) g) B x)
    (K K' : Set M) {ℓ α β : ℝ} (hℓ : 0 < ℓ)
    (hgeo : ∀ x ∈ K, ∀ e : Fin (Module.finrank ℝ E) → TangentSpace I x,
      (∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ E), ∃ (γ : ℝ → M) (hγ0 : γ 0 = x)
        (P : Fin (Module.finrank ℝ E) → (r : ℝ) → TangentSpace I (γ r)),
        (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
        (∀ t ∈ Icc 0 ℓ, γ t ∈ K' ∧ ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t ∧
          HasGeodesicEquationAt (I := I) g γ t ∧
          (∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (P i) t) t) ∧
          (∀ i, covDerivAlong (I := I) g γ (P i) t = 0) ∧
          (∀ i j, g.inner (γ t) (P i t) (P j t) = if i = j then 1 else 0) ∧
          (mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ) = P a t))
    (hα : ∀ y ∈ K', Real.sqrt (normSq0S (I := I) g y s (A y)) ≤ α)
    (hβ : ∀ y ∈ K', Real.sqrt (normSq0S (I := I) g y (s + 2) (C y)) ≤ β) :
    ∀ x ∈ K, normSq0S (I := I) g x (s + 1) (B x) ≤
      (Module.finrank ℝ E : ℝ) ^ (s + 1) * (4 * (Real.sqrt (α * β) + α / ℓ)) ^ 2 := by
  classical
  intro x hx
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g b hb
  rw [normSq0S_identity_eq_sum_sq (I := I) g x (s + 1) b hinv (B x)]
  have hentry : ∀ slots : Fin (s + 1) → Fin (Module.finrank ℝ E),
      (component0S (I := I) b (B x) slots) ^ 2 ≤ (4 * (Real.sqrt (α * β) + α / ℓ)) ^ 2 := by
    intro slots
    have hM : |component0S (I := I) b (B x) slots| ≤ 4 * (Real.sqrt (α * β) + α / ℓ) := by
      obtain ⟨γ, hγ0, P, hP0, hPd⟩ := hgeo x hx (fun i => b i) (fun i j => hb i j) (slots 0)
      subst hγ0
      have hmem : (0 : ℝ) ∈ Icc 0 ℓ := ⟨le_rfl, hℓ.le⟩
      set a : Fin (Module.finrank ℝ E) := slots 0 with ha
      let V : Fin s → (r : ℝ) → TangentSpace I (γ r) := fun k => P (slots k.succ)
      have hW : ∀ t ∈ Icc 0 ℓ, (mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ) = P a t := fun t ht =>
        (hPd t ht).2.2.2.2.2.2
      have hcomp : component0S (I := I) b (B (γ 0)) slots =
          totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (LeviCivita (I := I) g) A
            (γ 0) (Fin.cons ((mfderiv 𝓘(ℝ, ℝ) I γ 0) (1 : ℝ)) (fun k => V k 0)) := by
        rw [← hB]
        unfold component0S
        congr 1
        funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · simp only [Fin.cons_zero]
          rw [hW 0 hmem, hP0 a]
        · simp only [Fin.cons_succ, V]
          rw [hP0 (slots j.succ)]
      rw [hcomp]
      refine landau_geodesic_S75 g A B hB γ hℓ (fun t ht => (hPd t ht).2.1)
        (fun t ht => (hPd t ht).2.2.1) V (fun i t ht => (hPd t ht).2.2.2.1 _)
        (fun i t ht => (hPd t ht).2.2.2.2.1 _) ?_ ?_
      · intro t ht
        exact (abs_eval_orthonormal_le_S75 g (γ t) (fun i => P i t) (hPd t ht).2.2.2.2.2.1
          (A (γ t)) (fun k => slots k.succ)).trans (hα (γ t) (hPd t ht).1)
      · intro t ht
        have hslots : (Fin.cons (P a t) (Fin.cons (P a t) (fun k => V k t)) :
            Fin (s + 2) → TangentSpace I (γ t)) =
            fun k => P ((Fin.cons a (Fin.cons a (fun k : Fin s => slots k.succ)) :
              Fin (s + 2) → Fin (Module.finrank ℝ E)) k) t := by
          funext k
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) k <;> simp [V]
        rw [hW t ht, ← hC, hslots]
        exact (abs_eval_orthonormal_le_S75 g (γ t) (fun i => P i t) (hPd t ht).2.2.2.2.2.1
          (C (γ t)) _).trans (hβ (γ t) (hPd t ht).1)
    calc _ = |component0S (I := I) b (B x) slots| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hM 2
  calc _ ≤ ∑ _slots : Fin (s + 1) → Fin (Module.finrank ℝ E),
        (4 * (Real.sqrt (α * β) + α / ℓ)) ^ 2 := Finset.sum_le_sum (fun slots _ => hentry slots)
    _ = _ := by simp

/-- real algebra turning the squared step bound of `landau_step_S75` into the `hstep`-shaped bound
`√X ≤ C (√(α β) + α)` (`C = 4 N (1 + 1/ℓ)`, `N = n^(s+1) ≥ 1`). -/
theorem sqrt_step_bound_S75 {X N α β ℓ : ℝ} (hα : 0 ≤ α) (hℓ : 0 < ℓ) (hN : 1 ≤ N)
    (hX : X ≤ N * (4 * (Real.sqrt (α * β) + α / ℓ)) ^ 2) :
    Real.sqrt X ≤ (4 * N * (1 + 1 / ℓ)) * (Real.sqrt (α * β) + α) := by
  have hN0 : 0 ≤ N := by linarith
  have hs0 : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ 4 * (Real.sqrt (α * β) + α / ℓ) := by positivity
  have h1 : Real.sqrt X ≤ Real.sqrt N * (4 * (Real.sqrt (α * β) + α / ℓ)) := by
    calc Real.sqrt X ≤ Real.sqrt (N * (4 * (Real.sqrt (α * β) + α / ℓ)) ^ 2) :=
          Real.sqrt_le_sqrt hX
      _ = _ := by rw [Real.sqrt_mul hN0, Real.sqrt_sq hM0]
  have h2 : Real.sqrt N ≤ N := (Real.sqrt_le_iff).2 ⟨hN0, by nlinarith⟩
  have h3 : α / ℓ ≤ (1 / ℓ) * α := by rw [one_div, inv_mul_eq_div]
  have h4 : Real.sqrt (α * β) + α / ℓ ≤ (1 + 1 / ℓ) * (Real.sqrt (α * β) + α) := by
    have : 0 ≤ 1 / ℓ := by positivity
    nlinarith [mul_nonneg this hs0]
  calc Real.sqrt X ≤ Real.sqrt N * (4 * (Real.sqrt (α * β) + α / ℓ)) := h1
    _ ≤ N * (4 * ((1 + 1 / ℓ) * (Real.sqrt (α * β) + α))) :=
        mul_le_mul h2 (by linarith) hM0 hN0
    _ = _ := by ring

end GC.LongTime.Ch12
