import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# LFR37: buffered stability of the vector adapted conditions and of rank two (kernels)

Blueprint 207A, LFR37 (`lem:collapse-buffered-vector-adapted-stability`, A:28210–28241), and the
operator-norm step of LFR38 (A:28293–28298). The adapted contract (LFR35.1, A:27928–27942) of a map
`J : B(x,100) → ℝ²` relative to a two-splitting `Φ` has three clauses: ambient Lipschitz constant
`≤ 1 + γ`; image within Hausdorff distance `100γ` of `B(J(x), 100)` (both inclusions, by infimum
distances); and the derivative test against `(Φ_{ℝ²}(z) - Φ_{ℝ²}(y))/d(y,z)`. As in the rank-one
kernels (`AdaptedCoordinateTransfer.lean`) no definition of adaptedness is introduced: the clauses
are written out.

* `adjoint_lower_bound_of_gram` / `surjective_of_gram_perturbation` (rank two): if
  `‖A A* - 1‖ < γ/4` and `‖B - A‖ < γ/100` with `γ < 1/100`, then
  `‖B* a‖ ≥ (√(1 - γ/4) - γ/100) ‖a‖ > 0`, so `B` is onto `ℝ²`.
* `vector_adapted_metric_clauses_of_perturbation`: the Lipschitz and image clauses pass from `χ`
  (quality `γ/4`, `χ(x) = 0`) to `J` (quality `γ`, centred at `J(x)`) when `J - χ` is
  `γ/100`-Lipschitz on `B(x, 100)`.
* `norm_sub_lt_of_derivative_perturbation`: the derivative clause, `γ/4 + γ/100 < γ`.
* `opNorm_le_of_components` (LFR38): if both components of `L : V →L ℝ²` have norm `≤ c`, then
  `‖L‖ ≤ √2 c`.

The Riemannian step (integration of `D(J - χ)` along minimizing segments inside `B(x, 300)`) is the
binding, not part of these kernels.
-/

set_option autoImplicit false

open Set Metric ContinuousLinearMap
open scoped InnerProductSpace

namespace DifferentialGeometry.Geometry.Comparison

section Rank

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Lower bound for the adjoint of a perturbation of an almost co-isometry. -/
theorem adjoint_lower_bound_of_gram {A B : V →L[ℝ] EuclideanSpace ℝ (Fin 2)} {γ : ℝ}
    (hA : ‖A ∘L adjoint A - 1‖ < γ / 4) (hB : ‖B - A‖ < γ / 100)
    (a : EuclideanSpace ℝ (Fin 2)) :
    (Real.sqrt (1 - γ / 4) - γ / 100) * ‖a‖ ≤ ‖adjoint B a‖ := by
  have hsq : (1 - γ / 4) * ‖a‖ ^ 2 ≤ ‖adjoint A a‖ ^ 2 := by
    rw [apply_norm_sq_eq_inner_adjoint_left, adjoint_adjoint]
    have h1 : (A ∘L adjoint A) a = a + (A ∘L adjoint A - 1) a := by simp
    rw [h1, inner_add_left, real_inner_self_eq_norm_sq]
    have h2 : |⟪(A ∘L adjoint A - 1) a, a⟫_ℝ| ≤ γ / 4 * ‖a‖ ^ 2 := by
      calc |⟪(A ∘L adjoint A - 1) a, a⟫_ℝ| ≤ ‖(A ∘L adjoint A - 1) a‖ * ‖a‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖A ∘L adjoint A - 1‖ * ‖a‖ * ‖a‖ :=
            mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg _)
        _ ≤ γ / 4 * ‖a‖ ^ 2 := by
            rw [mul_assoc, ← pow_two]
            exact mul_le_mul_of_nonneg_right hA.le (by positivity)
    simp only [RCLike.re_to_real]
    linarith [(abs_le.mp h2).1]
  have hA' : Real.sqrt (1 - γ / 4) * ‖a‖ ≤ ‖adjoint A a‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (adjoint A a)), ← Real.sqrt_sq (norm_nonneg a),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  have hdiff : ‖adjoint B a - adjoint A a‖ ≤ γ / 100 * ‖a‖ := by
    rw [← sub_apply, ← map_sub]
    calc ‖adjoint (B - A) a‖ ≤ ‖adjoint (B - A)‖ * ‖a‖ := le_opNorm _ _
      _ = ‖B - A‖ * ‖a‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ γ / 100 * ‖a‖ := mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)
  have htri := norm_sub_norm_le (adjoint A a) (adjoint A a - adjoint B a)
  rw [sub_sub_cancel, norm_sub_rev] at htri
  nlinarith

/-- **LFR37, rank two.** -/
theorem surjective_of_gram_perturbation [FiniteDimensional ℝ V]
    {A B : V →L[ℝ] EuclideanSpace ℝ (Fin 2)} {γ : ℝ}
    (hγ : γ < 1 / 100) (hA : ‖A ∘L adjoint A - 1‖ < γ / 4) (hB : ‖B - A‖ < γ / 100) :
    Function.Surjective B := by
  have hpos : 0 < Real.sqrt (1 - γ / 4) - γ / 100 := by
    have h1 : (99 / 100 : ℝ) ≤ Real.sqrt (1 - γ / 4) := by
      rw [show (99 / 100 : ℝ) = Real.sqrt ((99 / 100) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hker : LinearMap.ker ((adjoint B : EuclideanSpace ℝ (Fin 2) →L[ℝ] V) :
      EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] V) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have h := adjoint_lower_bound_of_gram hA hB a
    have ha' : adjoint B a = 0 := ha
    rw [ha', norm_zero] at h
    have : ‖a‖ ≤ 0 := by nlinarith [norm_nonneg a]
    exact norm_le_zero_iff.mp this
  have hrange : LinearMap.range (B : V →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, orthogonal_range]
    exact hker
  intro y
  have hy : y ∈ LinearMap.range (B : V →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
    rw [hrange]
    exact Submodule.mem_top
  obtain ⟨v, hv⟩ := hy
  exact ⟨v, hv⟩

omit [CompleteSpace V] in
/-- **LFR38, operator norm from components.** -/
theorem opNorm_le_of_components {L : V →L[ℝ] EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ v, |L v 0| ≤ c * ‖v‖) (h1 : ∀ v, |L v 1| ≤ c * ‖v‖) :
    ‖L‖ ≤ Real.sqrt 2 * c := by
  refine opNorm_le_bound _ (by positivity) fun v => ?_
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  have hv := norm_nonneg v
  have e0 := h0 v
  have e1 := h1 v
  rw [show Real.sqrt 2 * c * ‖v‖ = Real.sqrt (2 * (c * ‖v‖) ^ 2) by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]; ring]
  apply Real.sqrt_le_sqrt
  have a0 : |(L v).ofLp 0| ^ 2 ≤ (c * ‖v‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) e0 2
  have a1 : |(L v).ofLp 1| ^ 2 ≤ (c * ‖v‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) e1 2
  linarith

end Rank

section Clauses

variable {X : Type*} [MetricSpace X] {F : Type*} [NormedAddCommGroup F]

/-- **LFR37, Lipschitz and image clauses.** -/
theorem vector_adapted_metric_clauses_of_perturbation {x : X} {J χ : X → F} {γ : ℝ}
    (hχx : χ x = 0)
    (hχL : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (χ y) (χ z) ≤ (1 + γ / 4) * dist y z)
    (hχI : ∀ y ∈ ball x 100, infDist (χ y) (ball (0 : F) 100) ≤ 100 * (γ / 4))
    (hχI' : ∀ w ∈ ball (0 : F) 100, infDist w (χ '' ball x 100) ≤ 100 * (γ / 4))
    (hdiff : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100,
      ‖(J y - χ y) - (J z - χ z)‖ ≤ γ / 100 * dist y z) :
    (∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (J y) (J z) ≤ (1 + γ) * dist y z) ∧
      (∀ y ∈ ball x 100, infDist (J y) (ball (J x) 100) ≤ 100 * γ) ∧
      ∀ w ∈ ball (J x) 100, infDist w (J '' ball x 100) ≤ 100 * γ := by
  have hx : x ∈ ball x 100 := mem_ball_self (by norm_num)
  have hγ : 0 ≤ γ := by
    have h := hχI' 0 (mem_ball_self (by norm_num))
    have h0 : (0 : ℝ) ≤ infDist (0 : F) (χ '' ball x 100) := infDist_nonneg
    linarith
  -- `J - J(x) - χ` is small on the ball
  have hsmall (y : X) (hy : y ∈ ball x 100) : ‖J y - (J x + χ y)‖ ≤ γ := by
    have h := hdiff y hy x hx
    rw [hχx, sub_zero] at h
    have hyx : dist y x < 100 := hy
    have e : J y - (J x + χ y) = (J y - χ y) - J x := by abel
    rw [e]
    calc ‖(J y - χ y) - J x‖ ≤ γ / 100 * dist y x := h
      _ ≤ γ / 100 * 100 := mul_le_mul_of_nonneg_left hyx.le (by positivity)
      _ = γ := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro y hy z hz
    have e : J y - J z = (χ y - χ z) + ((J y - χ y) - (J z - χ z)) := by abel
    rw [dist_eq_norm, e]
    calc ‖(χ y - χ z) + ((J y - χ y) - (J z - χ z))‖
        ≤ ‖χ y - χ z‖ + ‖(J y - χ y) - (J z - χ z)‖ := norm_add_le _ _
      _ ≤ (1 + γ / 4) * dist y z + γ / 100 * dist y z := by
          rw [← dist_eq_norm]
          exact add_le_add (hχL y hy z hz) (hdiff y hy z hz)
      _ ≤ (1 + γ) * dist y z := by nlinarith [dist_nonneg (x := y) (y := z)]
  · intro y hy
    have h1 : infDist (J x + χ y) (ball (J x) 100) = infDist (χ y) (ball (0 : F) 100) := by
      have hb : ball (J x) 100 = IsometryEquiv.addLeft (J x) '' ball (0 : F) 100 := by
        rw [IsometryEquiv.image_ball, IsometryEquiv.addLeft_apply, add_zero]
      rw [hb]
      exact infDist_image (IsometryEquiv.addLeft (J x)).isometry
    have h2 := infDist_le_infDist_add_dist (x := J y) (y := J x + χ y) (s := ball (J x) 100)
    rw [h1, dist_eq_norm] at h2
    linarith [hχI y hy, hsmall y hy]
  · intro w hw
    have hw' : w - J x ∈ ball (0 : F) 100 := by
      rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact hw
    have hne : (χ '' ball x 100).Nonempty := ⟨χ x, mem_image_of_mem _ hx⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨c, ⟨y, hy, rfl⟩, hc⟩ := (infDist_lt_iff hne).mp
      (show infDist (w - J x) (χ '' ball x 100) < 100 * (γ / 4) + ε by linarith [hχI' _ hw'])
    have hJy : dist w (J y) ≤ dist (w - J x) (χ y) + ‖J y - (J x + χ y)‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      have e : w - J y = (w - J x - χ y) - (J y - (J x + χ y)) := by abel
      rw [e]
      exact norm_sub_le _ _
    calc infDist w (J '' ball x 100) ≤ dist w (J y) := infDist_le_dist_of_mem (mem_image_of_mem _ hy)
      _ < 100 * γ + ε := by linarith [hsmall y hy]

/-- **LFR37, derivative clause**: `γ/4 + γ/100 < γ`. -/
theorem norm_sub_lt_of_derivative_perturbation {a c t : F} {γ : ℝ} (hγ : 0 < γ)
    (hac : ‖a - c‖ ≤ γ / 100) (hct : ‖c - t‖ < γ / 4) : ‖a - t‖ < γ := by
  have e : a - t = (a - c) + (c - t) := by abel
  rw [e]
  calc ‖(a - c) + (c - t)‖ ≤ ‖a - c‖ + ‖c - t‖ := norm_add_le _ _
    _ < γ := by linarith

end Clauses

end DifferentialGeometry.Geometry.Comparison
