import DifferentialGeometry.Geometry.Metric.Approximation.DirectedSplittingCompatibility
import DifferentialGeometry.Analysis.InnerProductSpace.AnchorAlignment
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Raw alignment of two equal-rank splittings (TCP02, circle rows)

Blueprint `master207B.tex`, TCP02 (`lem:fibration-first-raw-alignment`, lines 5311–5368): for a listed
circle chart, AC76 (reference rank two, no three-splitting) makes the recentred, rescaled circle
splitting `φ` compatible with the reference splitting `ψ`, and FC20–FC21 replace the Euclidean factor map
by an orthogonal map. Kernel form: AC76's witness `SplittingCompatible φ ψ τ` for ranks `(n, n)` and
FC20 (W4-FCa's `InnerProductSpace.exists_linearIsometryEquiv_anchor_alignment_euclidean`, on the ball of
radius `τ⁻¹/2`, which needs `40 n τ² ≤ 1`) give one linear isometry `A` of `ℝⁿ` with
`‖φ₁ - A ψ₁‖ ≤ (24 n + 1) τ` wherever `‖ψ₁‖ ≤ τ⁻¹/2`. For `n = 2` this is (TR) with `A_j = A`
(a coisometry `ℝ² → ℝ²`); the rank-one rows are `exists_unit_row_alignment_of_splittingCompatible`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]

/-- TCP02's circle rows: equal-rank compatible splittings are aligned by one orthogonal map. -/
theorem exists_orthogonal_alignment_of_splittingCompatible_equal_rank {p : X} {a₀ : A} {b₀ : B}
    {n : ℕ} {δ ε τ : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), a₀)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) (hτn : 40 * (n : ℝ) * τ ^ 2 ≤ 1) :
    ∃ Aₒ : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), ∀ x ∈ ball p τ⁻¹,
      ‖(ψ.toFun x).fst‖ ≤ τ⁻¹ / 2 →
        ‖(φ.toFun x).fst - Aₒ (ψ.toFun x).fst‖ ≤ (24 * n + 1) * τ := by
  obtain ⟨-, Q, E, Fac, hQ⟩ := hcomp
  have hτ : 0 < τ := E.error_pos
  -- the first factor of `Q` is a linear isometry (its second factor is `ℝ⁰`)
  have hsnd (u : EuclideanSpace ℝ (Fin n)) : (Q u).snd = 0 := by
    ext i
    exact absurd i.isLt (by simp)
  have hnorm (u : EuclideanSpace ℝ (Fin n)) : ‖(Q u).fst‖ = ‖u‖ := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (Q u)
    rw [hsnd, norm_zero, LinearIsometryEquiv.norm_map] at h
    have h' : ‖(Q u).fst‖ ^ 2 = ‖u‖ ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'
  let G : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toLinearMap := (LinearMap.fst ℝ _ _).comp
        ((WithLp.linearEquiv 2 ℝ _).toLinearMap.comp Q.toLinearEquiv.toLinearMap)
      norm_map' := hnorm }
  have hG (u : EuclideanSpace ℝ (Fin n)) : G u = (Q u).fst := rfl
  -- FC20 for the factor map `E`
  have ha : 0 < τ⁻¹ / 2 := by positivity
  have hδa : 20 * (n : ℝ) * τ ≤ τ⁻¹ / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hτ]
    nlinarith
  obtain ⟨Q', hQ'⟩ := InnerProductSpace.exists_linearIsometryEquiv_anchor_alignment_euclidean ha
    hτ.le hδa E.toFun E.basepoint (fun v w hv hw => by
      have hv' : v ∈ ball (0 : EuclideanSpace ℝ (Fin n)) τ⁻¹ := by
        rw [mem_ball, dist_zero_right]; linarith
      have hw' : w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) τ⁻¹ := by
        rw [mem_ball, dist_zero_right]; linarith
      have h := E.distortion v hv' w hw'
      rwa [dist_eq_norm, dist_eq_norm] at h)
  refine ⟨Q'.toLinearIsometry.comp G, fun x hx hsmall => ?_⟩
  have hu : ‖G (ψ.toFun x).fst‖ ≤ τ⁻¹ / 2 := by rw [G.norm_map]; exact hsmall
  have hclose : ‖(φ.toFun x).fst - E.toFun (G (ψ.toFun x).fst)‖ ≤ τ := by
    have h1 := hQ x hx
    have h2 := WithLp.dist_fst_le
      (WithLp.toLp 2 (E.toFun (Q (ψ.toFun x).fst).fst,
        Fac.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))) (φ.toFun x)
    rw [dist_eq_norm] at h2
    simp only [WithLp.toLp_fst] at h2
    rw [norm_sub_rev, hG]
    exact h2.trans h1
  have hfc := hQ' (G (ψ.toFun x).fst) hu
  have heq : (φ.toFun x).fst - (Q'.toLinearIsometry.comp G) (ψ.toFun x).fst =
      ((φ.toFun x).fst - E.toFun (G (ψ.toFun x).fst)) +
        (E.toFun (G (ψ.toFun x).fst) - Q' (G (ψ.toFun x).fst)) := by
    simp only [LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry]
    abel
  rw [heq]
  calc _ ≤ ‖(φ.toFun x).fst - E.toFun (G (ψ.toFun x).fst)‖ +
        ‖E.toFun (G (ψ.toFun x).fst) - Q' (G (ψ.toFun x).fst)‖ := norm_add_le _ _
    _ ≤ τ + 24 * n * τ := add_le_add hclose hfc
    _ = (24 * n + 1) * τ := by ring

end GC.MetricGeometry
