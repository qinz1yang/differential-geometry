import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem scalar_le_two_mul_initial_of_time_sub_le
    {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : G.flow.scalar a x ≤ A) {t : ℝ} (ht : t ∈ Ico a s)
    (htime : 2 * C * A * (t - a) ≤ 1) : G.flow.scalar t x ≤ 2 * A := by
  have hlip := G.lipschitzOnWith_inv_max_scalar_at hA x
    (fun r hr hAr => hbound r hr (hqA.trans_lt hAr))
  have hh := hlip.dist_le_mul t ht a ⟨le_rfl,G.lt⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1), max_eq_left hinit] at hh
  have hhalf : C * (t - a) ≤ (2 * A)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have htwo : A⁻¹ = 2 * (2 * A)⁻¹ := by field_simp
  have hlow : (2 * A)⁻¹ ≤ (max A (G.flow.scalar t x))⁻¹ := by
    have hab := (abs_le.mp hh).1
    rw [htwo] at hab
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hA.trans_le (le_max_left _ _))).mp hlow)

theorem TerminalLimitMetric.scalar_le_two_mul_initial_of_time_sub_le
    (L : G.TerminalLimitMetric) {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hinit : G.flow.scalar a x.val ≤ A)
    (htime : 2 * C * A * (s - a) ≤ 1) : metricScalarAt L.metric x ≤ 2 * A := by
  apply le_of_tendsto (L.tendsto_metricScalarAt x)
  filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
  apply G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x.val hbound hinit ⟨ht.1.le,ht.2⟩
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) (by positivity)).trans htime


theorem curvature_bound_of_initial_scalar_bound
    {q A a₀ : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A) (ha₀ : 0 < a₀)
    (K : Set P.Carrier)
    (hbound : ∀ x ∈ K, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : ∀ x ∈ K, G.flow.scalar a x ≤ A)
    (hpinch : ∀ t ∈ Ico a s, ∀ x ∈ K,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ x)
    {b : ℝ} (hbs : b < s)
    (htime : 2 * C * A * (b - a) ≤ 1) :
    ∀ t ∈ Icc a b, ∀ x ∈ K,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (G.flow.base.metric t) x 4
        (metricRm04 (G.flow.base.metric t) x)) ≤
        2 * Real.sqrt 3 * (A + max (2 * A) (Real.exp 4 / a₀)) := by
  intro t ht x hx
  have htc : t ∈ Ico a s := ⟨ht.1, ht.2.trans_lt hbs⟩
  have hscalar : G.flow.scalar t x ≤ 2 * A :=
    G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x (hbound x hx) (hinit x hx) htc
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (by positivity)).trans htime)
  have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x ha₀ le_rfl
    (hpinch t htc x hx) hscalar
  have hA2 : max (2 * A) 0 = 2 * A := max_eq_left (by positivity)
  have heq : (2 * A) / 2 = A := by ring
  rw [hA2, heq] at hr
  exact hr

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

theorem exists_uniform_curvature_bound_of_normalized_initial_scalar_bound
    (B P : ℝ) (hB : 0 < B) (hP : 0 < P) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : OrientedThreeStage.{u}} {a s : ℝ} (G : X.IncomingSlab a s)
        (Ω : Set X.Carrier) (Q q τ : ℝ) (C : ℝ≥0) (h : ℝ → ℝ),
        0 < Q → q ≤ B * Q →
        (∀ x ∈ Ω, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
          |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
        (∀ x ∈ Ω, G.flow.scalar a x ≤ B * Q) →
        (∀ t ∈ Ico a s, ∀ x ∈ Ω,
          InFixedHamiltonIveyRegion (G.flow.base.metric t) (h t) x) →
        (∀ t ∈ Ico a s, P ≤ h t * Q) →
        2 * C * B * τ ≤ 1 →
        ∀ b : ℝ, b < s → b - a ≤ τ / Q →
          ∀ t ∈ Icc a b, ∀ x ∈ Ω,
            Real.sqrt (normSq0S (G.flow.base.metric t) x 4
              (metricRm04 (G.flow.base.metric t) x)) ≤ K * Q := by
  let K := 2 * Real.sqrt 3 * (B + max (2 * B) (Real.exp 4 / P))
  have hK : 0 < K := by
    have hm : 0 < max (2 * B) (Real.exp 4 / P) :=
      (div_pos (Real.exp_pos _) hP).trans_le (le_max_right _ _)
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro X a s G Ω Q q τ C h hQ hq hbound hinit hpinch hparameter hbudget b hbs htime t ht x hx
  have htc : t ∈ Ico a s := ⟨ht.1, ht.2.trans_lt hbs⟩
  have htime' : 2 * C * (B * Q) * (t - a) ≤ 1 := by
    have hta : t - a ≤ τ / Q := (sub_le_sub_right ht.2 a).trans htime
    have hmul := mul_le_mul_of_nonneg_left hta
      (show 0 ≤ 2 * (C : ℝ) * (B * Q) by positivity)
    have he : 2 * (C : ℝ) * (B * Q) * (τ / Q) = 2 * C * B * τ := by
      field_simp
    exact (hmul.trans_eq he).trans hbudget
  have hscalar := G.scalar_le_two_mul_initial_of_time_sub_le (mul_pos hB hQ) hq x
    (hbound x hx) (hinit x hx) htc htime'
  have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x
    (div_pos hP hQ) ((div_le_iff₀ hQ).mpr (hparameter t htc))
    (hpinch t htc x hx) hscalar
  have hm : max (2 * (B * Q)) 0 = 2 * (B * Q) := max_eq_left (by positivity)
  have he : Real.exp 4 / (P / Q) = (Real.exp 4 / P) * Q := by field_simp
  rw [hm, he, show 2 * (B * Q) = (2 * B) * Q by ring,
    ← max_mul_of_nonneg _ _ hQ.le] at hr
  change Real.sqrt (normSq0S (G.flow.base.metric t) x 4
    (metricRm04At (G.flow.base.metric t) x)) ≤ K * Q
  exact hr.trans_eq (by dsimp only [K]; ring)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
