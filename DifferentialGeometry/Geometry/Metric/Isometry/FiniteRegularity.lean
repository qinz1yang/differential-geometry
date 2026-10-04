import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import DifferentialGeometry.Analysis.Calculus.ContDiff.ConnectionBootstrap
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition

/-!
# Finite regularity of a metric pullback map

The coefficient transformation identity supplies the second-order equation used by the
connection bootstrap. A twice differentiable local metric isometry gains the extra order.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Geometry.MetricIsometry

theorem contDiffOn_of_metric_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {m : ℕ∞} {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hb : ContDiffOn ℝ ((m : ℕ∞ω) + 1) b U)
    (hc : ContDiffOn ℝ ((m : ℕ∞ω) + 1) c V)
    (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z))
    (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E,
      b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ContDiffOn ℝ ((m : ℕ∞ω) + 2) Φ U := by
  have hc1 : ContDiffOn ℝ 1 c V := hc.of_le (le_add_of_nonneg_left zero_le)
  have hbco : ∀ y ∈ U, IsCoercive (b y) :=
    DifferentialGeometry.Analysis.isCoercive_of_pullback hcco hΦUV hΦinv hpull
  have hΓb := DifferentialGeometry.MetricKoszul.raisedOp_contDiffOn_succ hU hb hbco
  have hΓc := DifferentialGeometry.MetricKoszul.raisedOp_contDiffOn_succ hV hc hcco
  apply DifferentialGeometry.Analysis.contDiffOn_of_fderiv_fderiv_eq_enat
    hU hΦ hΦUV hΓb hΓc
  intro y hy X u
  exact DifferentialGeometry.Analysis.fderiv_fderiv_eq_raisedKoszulOp_of_pullback
    hU hV hc1 hcsymm hcco hΦ hΦUV hΦinv hpull hy X u

theorem contDiff_identity_from_metric_pullback (m : ℕ∞) :
    ContDiff ℝ ((m : ℕ∞ω) + 2) (id : ℝ → ℝ) := by
  let b : ℝ → ℝ →L[ℝ] ℝ →L[ℝ] ℝ := fun z => ContinuousLinearMap.mul ℝ ℝ
  have hco : ∀ z ∈ (Set.univ : Set ℝ), IsCoercive (b z) := by
    intro z hz
    exact ContinuousLinearMap.isCoercive_of_posDef (F := ℝ) (b z)
      (fun v hv => by simpa only [b, ContinuousLinearMap.mul_apply', ← pow_two]
        using sq_pos_of_ne_zero hv)
  have hs : ∀ z ∈ (Set.univ : Set ℝ), ∀ u v : ℝ, b z u v = b z v u := by
    intro z hz u v
    exact mul_comm u v
  have hi : ∀ y ∈ (Set.univ : Set ℝ), (fderiv ℝ (id : ℝ → ℝ) y).IsInvertible := by
    intro y hy
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, by simp⟩
  have hp : ∀ y ∈ (Set.univ : Set ℝ), ∀ u v : ℝ,
      b y u v = b (id y) (fderiv ℝ (id : ℝ → ℝ) y u)
        (fderiv ℝ (id : ℝ → ℝ) y v) := by
    intro y hy u v
    simp
  exact contDiffOn_univ.mp (contDiffOn_of_metric_pullback isOpen_univ isOpen_univ
    (m := m) contDiffOn_const contDiffOn_const hs hco contDiffOn_id
    (fun y hy => mem_univ _) hi hp)

end DifferentialGeometry.Geometry.MetricIsometry
