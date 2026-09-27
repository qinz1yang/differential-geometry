import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifferenceBounds
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.TraceBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.Difference
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.VectorField.SmoothGlobalExtension
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Frame

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem innerSelfNonneg (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · exact (g.pos x v hv).le

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem frankEq (x : M) :
    (Module.finrank Real (TangentSpace I x) : Real) = (Module.finrank Real E : Real) := rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem metricCS (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  set α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangent (I := I) (tangentFlatLinear (I := I) g x u) with hα
  have hαnorm : normSq0S (I := I) g x 1 α = g.inner x u u := by
    rw [hα, normSq0S_eq_inner, inner0S_one_eq_cotangent]
    exact cotangentInner_dualToCotangent_tangentFlat (I := I) g x u u
  have hαv : Tensor0SSpace.eval α (fun _ : Fin 1 => v) = g.inner x u v := by
    rw [hα]
    change tangentFlatLinear (I := I) g x u v = g.inner x u v
    exact tangentFlatLinear_apply (I := I) g x u v
  have h := abs_apply_le_sqrt_normSq0S (I := I) g x 1 basis hON α (fun _ : Fin 1 => v)
  change |Tensor0SSpace.eval α (fun _ : Fin 1 => v)| ≤ _ at h
  rw [hαv, hαnorm] at h
  simpa using h

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_coord {Idx : Type*} [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i : Idx) (v : TangentSpace I x) :
    basis.coord i v = g.inner x (basis i) v := by
  classical
  have hlin : basis.coord i = (g.inner x (basis i)).toLinearMap := by
    refine basis.ext fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    change (if j = i then (1 : Real) else 0) = g.inner x (basis i) (basis j)
    rw [hON i j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm)]
  exact congrArg (fun L : (TangentSpace I x) →ₗ[Real] Real => L v) hlin

omit [SigmaCompactSpace M] [T2Space M] in
private theorem absBasis_le {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {k : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) k x)
    (u : Fin k -> TangentSpace I x) (hu : ∀ b, ∃ i, u b = basis i) :
    |T u| ≤ Real.sqrt (normSq0S (I := I) g x k T) := by
  have _ : Fintype Idx := Fintype.ofFinite Idx
  have h := abs_apply_le_sqrt_normSq0S (I := I) g x k basis hON T u
  have hprod : (∏ a : Fin k, Real.sqrt (g.inner x (u a) (u a))) = 1 := by
    refine Finset.prod_eq_one fun a _ => ?_
    obtain ⟨i, hi⟩ := hu a
    rw [hi, hON i i]; simp
  rw [hprod, mul_one] at h
  exact h

omit [SigmaCompactSpace M] [T2Space M] in
private theorem normSqAdd_le {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {k : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) k x) :
    normSq0S (I := I) g x k (A + B) ≤
      2 * normSq0S (I := I) g x k A + 2 * normSq0S (I := I) g x k B := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv A,
    normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv B,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun φ _ => ?_
  have hsplit : component0S (I := I) basis (A + B) φ =
      component0S (I := I) basis A φ + component0S (I := I) basis B φ := by
    rw [component0S_apply, component0S_apply, component0S_apply]
    exact Tensor0SSpace.add_apply (I := I) k x A B _
  rw [hsplit]
  nlinarith [sq_nonneg (component0S (I := I) basis A φ - component0S (I := I) basis B φ)]

end Frame

section InverseMetric

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invDiag_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (k : Idx) :
    0 ≤ basisInvMetric (I := I) g₂ x basis k k ∧
      basisInvMetric (I := I) g₂ x basis k k ≤ Λ := by
  classical
  set u : TangentSpace I x :=
    (tangentFlatEquiv (I := I) g₂ x).symm (basis.coord k) with hu
  have hflat : ∀ w : TangentSpace I x, g₂.inner x u w = basis.coord k w := by
    intro w
    change (tangentFlatEquiv (I := I) g₂ x u) w = basis.coord k w
    rw [hu, (tangentFlatEquiv (I := I) g₂ x).apply_symm_apply]
  have hQ : basisInvMetric (I := I) g₂ x basis k k = g₂.inner x u u := by
    simp only [basisInvMetric]
    rw [← hu]
    exact (hflat u).symm
  have hQ1 : basisInvMetric (I := I) g₂ x basis k k = g₁.inner x (basis k) u := by
    simp only [basisInvMetric]
    rw [← hu]
    exact onFrame_coord (I := I) g₁ basis hON k u
  have hnn : 0 ≤ g₂.inner x u u := innerSelfNonneg (I := I) g₂ x u
  refine ⟨by rw [hQ]; exact hnn, ?_⟩
  have hcs : g₁.inner x (basis k) u ≤ Real.sqrt (g₁.inner x u u) := by
    have h := metricCS (I := I) g₁ x (basis k) u
    rw [hON k k] at h
    simpa using le_trans (le_abs_self _) h
  have hle : Real.sqrt (g₁.inner x u u) ≤ Real.sqrt (Λ * g₂.inner x u u) :=
    Real.sqrt_le_sqrt (hΛ u)
  have heq : g₂.inner x u u = g₁.inner x (basis k) u := by rw [← hQ, hQ1]
  have hkey : g₂.inner x u u ≤ Real.sqrt (Λ * g₂.inner x u u) :=
    calc g₂.inner x u u = g₁.inner x (basis k) u := heq
      _ ≤ Real.sqrt (g₁.inner x u u) := hcs
      _ ≤ Real.sqrt (Λ * g₂.inner x u u) := hle
  have hsqrt : Real.sqrt (Λ * g₂.inner x u u) ^ 2 = Λ * g₂.inner x u u :=
    Real.sq_sqrt (mul_nonneg hΛ0 hnn)
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [hQ, ← h0]; exact hΛ0
  · rw [hQ]
    nlinarith [hkey, hsqrt, hpos, Real.sqrt_nonneg (Λ * g₂.inner x u u)]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invEntry_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i j : Idx) :
    |basisInvMetric (I := I) g₂ x basis i j| ≤ Λ := by
  classical
  set ui : TangentSpace I x :=
    (tangentFlatEquiv (I := I) g₂ x).symm (basis.coord i) with hui
  set uj : TangentSpace I x :=
    (tangentFlatEquiv (I := I) g₂ x).symm (basis.coord j) with huj
  have hflat : ∀ (m : Idx) (w : TangentSpace I x),
      g₂.inner x ((tangentFlatEquiv (I := I) g₂ x).symm (basis.coord m)) w
        = basis.coord m w := by
    intro m w
    change (tangentFlatEquiv (I := I) g₂ x
      ((tangentFlatEquiv (I := I) g₂ x).symm (basis.coord m))) w = basis.coord m w
    rw [(tangentFlatEquiv (I := I) g₂ x).apply_symm_apply]
  have hval : basisInvMetric (I := I) g₂ x basis i j = g₂.inner x uj ui := by
    simp only [basisInvMetric]
    rw [← hui, huj]
    exact (hflat j ui).symm
  have hdi := invDiag_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i
  have hdj := invDiag_le (I := I) g₁ g₂ hΛ0 hΛ basis hON j
  have hQi : basisInvMetric (I := I) g₂ x basis i i = g₂.inner x ui ui := by
    simp only [basisInvMetric]; rw [← hui]; exact (hflat i ui).symm
  have hQj : basisInvMetric (I := I) g₂ x basis j j = g₂.inner x uj uj := by
    simp only [basisInvMetric]; rw [← huj]; exact (hflat j uj).symm
  rw [hQi] at hdi
  rw [hQj] at hdj
  rw [hval]
  calc |g₂.inner x uj ui|
      ≤ Real.sqrt (g₂.inner x uj uj) * Real.sqrt (g₂.inner x ui ui) :=
        metricCS (I := I) g₂ x uj ui
    _ ≤ Real.sqrt Λ * Real.sqrt Λ :=
        mul_le_mul (Real.sqrt_le_sqrt hdj.2) (Real.sqrt_le_sqrt hdi.2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Λ := Real.mul_self_sqrt hΛ0

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invDiff_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i j : Idx) :
    |(if i = j then (1 : Real) else 0) - basisInvMetric (I := I) g₂ x basis i j| ≤
      (Fintype.card Idx : Real) * Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
  classical
  have hrow := (basisInvMetric_isInverse (I := I) g₂ x basis i j).1
  have hH : ∀ k : Idx, g₂.inner x (basis k) (basis j)
      = (if k = j then (1 : Real) else 0) -
        metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    intro k
    rw [metricDiffAt_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hON k j]; ring
  have hstep : ∀ k : Idx,
      basisInvMetric (I := I) g₂ x basis i k * g₂.inner x (basis k) (basis j)
        = basisInvMetric (I := I) g₂ x basis i k * (if k = j then (1 : Real) else 0) -
          basisInvMetric (I := I) g₂ x basis i k *
            metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    intro k; rw [hH k]; ring
  have h1 : (∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
      (if k = j then (1 : Real) else 0)) = basisInvMetric (I := I) g₂ x basis i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h
  have h2 : (if i = j then (1 : Real) else 0)
      = basisInvMetric (I := I) g₂ x basis i j -
        ∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    rw [← hrow, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_sub_distrib, h1]
  rw [h2, show basisInvMetric (I := I) g₂ x basis i j -
        (∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]) -
        basisInvMetric (I := I) g₂ x basis i j
      = -∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] by ring, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k : Idx,
      |basisInvMetric (I := I) g₂ x basis i k *
        metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|
        ≤ Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
    intro k
    rw [abs_mul]
    have hH2 : |metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|
        ≤ Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
      rw [metricDiffSq_def]
      refine absBasis_le (I := I) g₁ basis hON (metricDiffAt (I := I) g₁ g₂ x) _ ?_
      intro b
      refine Fin.cases ?_ ?_ b
      · exact ⟨k, rfl⟩
      · intro c; exact ⟨j, by fin_cases c; rfl⟩
    exact mul_le_mul (invEntry_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i k) hH2
      (abs_nonneg _) hΛ0
  calc (∑ k : Idx, |basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|)
      ≤ ∑ _k : Idx, Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (Fintype.card Idx : Real) * Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [nsmul_eq_mul]; ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceDiffNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) {s : ℕ} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    normSq0S (I := I) g₁ x s
        (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) ≤
      (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
        metricDiffSq (I := I) g₁ g₂ x * normSq0S (I := I) g₁ x (s + 2) W := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  have hinv1 := onFrame_inv (I := I) g₁ basis hON
  have hinv2 := basisInvMetric_isInverse (I := I) g₂ x basis
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnRnn : 0 ≤ nR := by rw [hnR]; positivity
  set NW := Real.sqrt (normSq0S (I := I) g₁ x (s + 2) W) with hNW
  have hNWnn : 0 ≤ NW := Real.sqrt_nonneg _
  set NH := Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) with hNH
  have hNHnn : 0 ≤ NH := Real.sqrt_nonneg _
  set B : Real := nR ^ 3 * Λ * NH * NW with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcardIdx : (Fintype.card (Fin (Module.finrank Real (TangentSpace I x))) : Real) = nR := by
    rw [Fintype.card_fin, hnR]
    exact frankEq (I := I) x
  have hcomp : ∀ φ : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis
        (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) φ| ≤ B := by
    intro φ
    rw [component0S_apply]
    have hval : (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) (fun a : Fin s => basis (φ a)) =
        ∑ i, ∑ j, ((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a))) := by
      rw [Tensor0SSpace.sub_apply (I := I) s x _ _ _,
        metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₁ basis
          (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv1,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₂ basis _ hinv2]
      unfold metricTrace0S2InBasis
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hid : identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x))) i j
          = if i = j then (1 : Real) else 0 := by
        simp [identityInvMetric, diagonalInvMetric]
      rw [hid]; ring
    rw [hval]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hrow : ∀ i, |∑ j, ((if i = j then (1 : Real) else 0) -
          basisInvMetric (I := I) g₂ x basis i j) *
        W (metricTraceInput (I := I) (basis i) (basis j)
          (fun a : Fin s => basis (φ a)))| ≤ nR * (nR * Λ * NH * NW) := by
      intro i
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ j, |((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))| ≤ nR * Λ * NH * NW := by
        intro j
        rw [abs_mul]
        have hW : |W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))| ≤ NW := by
          rw [hNW]
          refine absBasis_le (I := I) g₁ basis hON W _ ?_
          intro b
          refine Fin.cases ?_ ?_ b
          · exact ⟨i, rfl⟩
          · intro c
            refine Fin.cases ?_ ?_ c
            · exact ⟨j, rfl⟩
            · intro d; exact ⟨φ d, rfl⟩
        have hQ := invDiff_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i j
        rw [hcardIdx, ← hNH] at hQ
        exact mul_le_mul hQ hW (abs_nonneg _) (by positivity)
      calc (∑ j, |((if i = j then (1 : Real) else 0) -
              basisInvMetric (I := I) g₂ x basis i j) *
            W (metricTraceInput (I := I) (basis i) (basis j)
              (fun a : Fin s => basis (φ a)))|)
          ≤ ∑ _j : Fin (Module.finrank Real (TangentSpace I x)), nR * Λ * NH * NW :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = nR * (nR * Λ * NH * NW) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp only [nsmul_eq_mul]
            rw [frankEq (I := I) x, ← hnR]
    calc (∑ i, |∑ j, ((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))|)
        ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)), nR * (nR * Λ * NH * NW) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp only [nsmul_eq_mul]
          rw [frankEq (I := I) x, ← hnR]
          ring
  have hcard := normSq0S_le_card_of_component_bound (I := I) g₁ x s basis hinv1
    (metricTraceFirstTwo0STensor (I := I) g₁ W -
      metricTraceFirstTwo0STensor (I := I) g₂ W) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin s -> Fin (Module.finrank Real (TangentSpace I x))) : Real)
        = nR ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hnR]
    push_cast
    rfl
  rw [hcard_eq] at hcard
  refine hcard.trans (le_of_eq ?_)
  have hH2 : NH ^ 2 = metricDiffSq (I := I) g₁ g₂ x := by
    rw [hNH, metricDiffSq_def]
    exact Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x 2 _)
  have hW2 : NW ^ 2 = normSq0S (I := I) g₁ x (s + 2) W :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x (s + 2) _)
  rw [hB, show (nR ^ 3 * Λ * NH * NW) ^ 2 = nR ^ 6 * Λ ^ 2 * NH ^ 2 * NW ^ 2 by ring,
    hH2, hW2, pow_add]
  ring

end InverseMetric

section Remainder

omit [SigmaCompactSpace M] in
theorem remNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) {Λ B₁ B₂ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₁ : normSq0S (I := I) g₁ x (s + 1) (metricNabla0S (I := I) g₂ T x) ≤ B₁)
    (hB₂ : normSq0S (I := I) g₁ x (s + 2)
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T) x) ≤ B₂) :
    normSq0S (I := I) g₁ x s (lapDiffRem (I := I) g₁ g₂ T x) ≤
      2 * ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ +
        2 * (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ basis hON
  set W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
    metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T) with hW
  set U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
    lapDiffFlux (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) with hU
  have hsplit : lapDiffRem (I := I) g₁ g₂ T x =
      metricTraceFirstTwo0STensor (I := I) g₁ (U x) +
        (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
          metricTraceFirstTwo0STensor (I := I) g₂ (W x)) := rfl
  rw [hsplit]
  refine le_trans (normSqAdd_le (I := I) g₁ basis hinv _ _) ?_
  have hnn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  have hfirst : normSq0S (I := I) g₁ x s
      (metricTraceFirstTwo0STensor (I := I) g₁ (U x)) ≤
        ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ := by
    refine le_trans (traceNormSq_le (I := I) g₁ x (U x)) ?_
    have hflux := fluxNormSq_le (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x
    rw [← hU] at hflux
    have hcd : 0 ≤ connectionDifferenceSq (I := I) g₁ g₂ x := by
      rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) g₁ x 3 _
    have hchain : normSq0S (I := I) g₁ x (s + 2) (U x) ≤
        ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (s + 2) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ := by
      refine le_trans hflux ?_
      have hfac : (0 : Real) ≤ ((s : Real) + 1) ^ 2 *
          (Module.finrank Real E : Real) ^ (s + 2) * connectionDifferenceSq (I := I) g₁ g₂ x := by
        positivity
      have hcast : (((s : ℕ) + 1 : ℕ) : Real) = (s : Real) + 1 := by push_cast; ring
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hB₁ hfac
    refine le_trans (mul_le_mul_of_nonneg_left hchain (by positivity)) (le_of_eq ?_)
    rw [show 2 * s + 4 = (s + 2) + (s + 2) by ring, pow_add]
    ring
  have hsecond : normSq0S (I := I) g₁ x s
      (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
        metricTraceFirstTwo0STensor (I := I) g₂ (W x)) ≤
        (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
    refine le_trans (traceDiffNormSq_le (I := I) g₁ g₂ x hΛ0 hΛ (W x)) ?_
    have hfac : (0 : Real) ≤ (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
        metricDiffSq (I := I) g₁ g₂ x := by
      have : 0 ≤ metricDiffSq (I := I) g₁ g₂ x := by
        rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) g₁ x 2 _
      positivity
    exact mul_le_mul_of_nonneg_left hB₂ hfac
  calc 2 * normSq0S (I := I) g₁ x s (metricTraceFirstTwo0STensor (I := I) g₁ (U x)) +
        2 * normSq0S (I := I) g₁ x s
          (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
            metricTraceFirstTwo0STensor (I := I) g₂ (W x))
      ≤ 2 * (((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
            connectionDifferenceSq (I := I) g₁ g₂ x * B₁) +
          2 * ((Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
            metricDiffSq (I := I) g₁ g₂ x * B₂) :=
        add_le_add (by linarith [hfirst]) (by linarith [hsecond])
    _ = _ := by ring

end Remainder

section Curvature

omit [SigmaCompactSpace M] in
theorem rmFluxNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {B : Real} (hB : normSq0S (I := I) g₁ x 4 (Rm2 x) ≤ B) :
    normSq0S (I := I) g₁ x 5 (rmDiffFlux (I := I) g₁ g₂ Rm2 x) ≤
      16 * (Module.finrank Real E : Real) ^ 5 * connectionDifferenceSq (I := I) g₁ g₂ x * B := by
  have hmain := fluxNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x
  have hfac : (0 : Real) ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
      connectionDifferenceSq (I := I) g₁ g₂ x := by
    have := normSq0S_nonneg (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x)
    rw [connectionDifferenceSq_def]
    positivity
  refine hmain.trans ?_
  have : (16 : Real) = (4 : Real) ^ 2 := by norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_left hB hfac

omit [SigmaCompactSpace M] in
theorem rmRemNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {Λ B₁ B₂ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₁ : normSq0S (I := I) g₁ x 5 (metricNabla0S (I := I) g₂ Rm2 x) ≤ B₁)
    (hB₂ : normSq0S (I := I) g₁ x 6
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ Rm2) x) ≤ B₂) :
    normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ Rm2 x) ≤
      50 * (Module.finrank Real E : Real) ^ 12 * connectionDifferenceSq (I := I) g₁ g₂ x * B₁ +
        2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
  have h := remNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x hΛ0 hΛ hB₁ hB₂
  refine h.trans (le_of_eq ?_)
  norm_num

end Curvature

end DifferentialGeometry.PDE.RicciFlow

end
