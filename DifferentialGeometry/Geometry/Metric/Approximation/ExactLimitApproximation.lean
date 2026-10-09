import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.PerturbApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false

namespace GC.MetricGeometry.PointedGHConverges

open Filter

universe u v w z

variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] {p : ∀ i, X i} {q : Y}

theorem eventually_kleinerLott_approx_isometric_target
    (h : PointedGHConverges p q) {Z : Type w} [MetricSpace Z]
    (e : Y ≃ᵢ Z) {ν : ℝ} (hν : 0 < ν) (hνone : ν < 1) :
    ∀ᶠ i in atTop, Nonempty (KleinerLottApprox (p i) (e q) ν) := by
  have hsmall : 0 < ν / 4 := by linarith
  have hR : ν / 4 < ν⁻¹ + ν := by linarith [inv_pos.mpr hν]
  filter_upwards [h.eventually_approx hsmall hR] with i hi
  obtain ⟨f⟩ := hi
  exact ⟨(f.mapTargetIsometry e).toKleinerLott hν hνone⟩

theorem not_exists_product_isometry_of_frequently_no_kleinerLott
    (h : PointedGHConverges p q) {E : Type w} [MetricSpace E] (e₀ : E)
    {ν : ℝ} (hν : 0 < ν) (hνone : ν < 1)
    (hno : ∃ᶠ i in atTop, ¬ ∃ (W : Type z) (m : MetricSpace W), letI := m
      ∃ (w₀ : W), Nonempty (KleinerLottApprox (p i) (WithLp.toLp 2 (e₀, w₀)) ν)) :
    ¬ ∃ (W : Type z) (m : MetricSpace W), letI := m
      ∃ (w₀ : W) (e : Y ≃ᵢ WithLp 2 (E × W)), e q = WithLp.toLp 2 (e₀, w₀) := by
  rintro ⟨W, m, w₀, e, he⟩
  let := m
  have happ := h.eventually_kleinerLott_approx_isometric_target e hν hνone
  rw [he] at happ
  obtain ⟨i, hni, hi⟩ := (hno.and_eventually happ).exists
  exact hni ⟨W, m, w₀, hi⟩


theorem not_exists_small_product_isometry_of_frequently_no_kleinerLott
    (h : PointedGHConverges p q) {E : Type w} [MetricSpace E] (e₀ : E)
    {ν : ℝ} (hν : 0 < ν) (hνone : ν < 1)
    (hno : ∃ᶠ i in atTop, ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ (w₀ : W), Nonempty (KleinerLottApprox (p i) (WithLp.toLp 2 (e₀, w₀)) ν)) :
    ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w₀ : W) (e : Y ≃ᵢ WithLp 2 (E × W)), e q = WithLp.toLp 2 (e₀, w₀) := by
  rintro ⟨W, m, w₀, e, he⟩
  let := m
  let up : W ≃ᵢ ULift.{u} W :=
    { Equiv.ulift.symm with isometry_toFun := fun _ _ => rfl }
  let eUp := e.trans (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl E) up)
  have heUp : eUp q = WithLp.toLp 2 (e₀, ULift.up w₀) := by
    change WithLp.toLp 2 ((e q).fst, up (e q).snd) = _
    rw [he]
    rfl
  have happ := h.eventually_kleinerLott_approx_isometric_target eUp hν hνone
  rw [heUp] at happ
  obtain ⟨i, hni, hi⟩ := (hno.and_eventually happ).exists
  exact hni ⟨ULift.{u} W, inferInstance, ULift.up w₀, hi⟩

end GC.MetricGeometry.PointedGHConverges
