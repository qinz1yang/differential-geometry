import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import DifferentialGeometry.Geometry.Curvature.Algebraic.Polarization
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

/-!
# The Riemann operator from a pointwise bound on sectional numerators

If `|Rm(u,w,w,u)| ≤ κ |u|² |w|²` at a point, polarization of the algebraic curvature form bounds
every component of `Rm` in an orthonormal basis by `18 κ`, hence `|Rm| ≤ n² · 18 κ` and the
Riemann operator by the same constant (`n = dim`). This supplies the model bound `hmodel` of the
perturbation estimates for a metric of constant sectional curvature.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- A pointwise bound `|Rm(u,w,w,u)| ≤ κ |u|²|w|²` bounds the full curvature norm by `n² · 18 κ`. -/
theorem sqrt_normSq0S_metricRm04At_le_of_abs_sectional_le (G : SmoothRiemannianMetric I M)
    (x : M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hk : ∀ u w : TangentSpace I x,
      |metricRm04StandardAt G x u w w u| ≤ κ * G.inner x u u * G.inner x w w) :
    Real.sqrt (normSq0S G x 4 (metricRm04At G x)) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (18 * κ) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis G x
  have hinv := metricInverseInBasis_of_orthonormal G basis hON
  have hB : IsAlgCurvForm (fun a b c d : TangentSpace I x => metricRm04StandardAt G x a b c d) := by
    change IsAlgCurvForm (tensor04StandardAt (metricRm04At G x))
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule G x)
  let N : TangentSpace I x → ℝ := fun u => Real.sqrt (G.inner x u u)
  have hN : ∀ u, 0 ≤ N u := fun u => Real.sqrt_nonneg _
  have hNadd : ∀ u u', N (u + u') ≤ N u + N u' := fun u u' =>
    Riemannian.sqrt_inner_add_le G x u u'
  have hk' : ∀ u w : TangentSpace I x,
      |metricRm04StandardAt G x u w w u| ≤ κ * N u ^ 2 * N w ^ 2 := by
    intro u w
    simp only [N, Real.sq_sqrt (metric_inner_self_nonneg G x _)]
    exact hk u w
  have hr : ∀ a, N (basis a) ≤ 1 := by
    intro a
    simp [N, hON a a]
  have hcomp : ∀ slots : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x)),
      |component0S basis (metricRm04At G x) slots| ≤ 18 * κ := by
    intro slots
    have hvec : (fun a => basis (slots a)) = vec4
        (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
      funext a
      fin_cases a <;> rfl
    have hval : component0S basis (metricRm04At G x) slots =
        metricRm04StandardAt G x
          (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
      rw [component0S, hvec]
      rfl
    rw [hval]
    have h := hB.abs_le_of_abs_sectional_le N hN hNadd hκ hk' (hr (slots 0)) (hr (slots 1))
      (hr (slots 2)) (hr (slots 3))
    simpa using h
  have hbound := sqrt_normSq0S_le_card_of_component_bound G x 4 basis hinv (metricRm04At G x)
    (18 * κ) (by positivity) hcomp
  have hcard : Real.sqrt (Fintype.card (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      (Module.finrank ℝ E : ℝ) ^ 2 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have : ((Module.finrank ℝ (TangentSpace I x) ^ 4 : ℕ) : ℝ) =
        ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 := by
      change ((Module.finrank ℝ E ^ 4 : ℕ) : ℝ) = _
      push_cast
      ring
    rw [this, Real.sqrt_sq (by positivity)]
  rwa [hcard] at hbound

/-- **Model bound from sectional numerators.** On a manifold without boundary, a pointwise bound
`|Rm(u,w,w,u)| ≤ κ |u|²|w|²` bounds the Riemann operator: `|R(u,v)w| ≤ n² · 18 κ |u||v||w|`. -/
theorem sqrt_inner_riemannOp_le_of_abs_sectional_le [BoundarylessManifold I M]
    (G : SmoothRiemannianMetric I M) (x : M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hk : ∀ u w : TangentSpace I x,
      |metricRm04StandardAt G x u w w u| ≤ κ * G.inner x u u * G.inner x w w)
    (u v w : TangentSpace I x) :
    let r := riemannOp (LeviCivita G) x u v w
    Real.sqrt (G.inner x r r) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (18 * κ) * Real.sqrt (G.inner x u u) *
        Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w) := by
  intro r
  refine (sqrt_inner_riemannOp_le G x u v w).trans ?_
  have h := sqrt_normSq0S_metricRm04At_le_of_abs_sectional_le G x hκ hk
  gcongr

end DifferentialGeometry.Geometry.Curvature
