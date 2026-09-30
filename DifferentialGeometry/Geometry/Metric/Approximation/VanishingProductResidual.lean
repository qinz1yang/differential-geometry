import DifferentialGeometry.Geometry.Metric.Approximation.ProductResidualBound
import DifferentialGeometry.Geometry.Metric.Approximation.ControlledProductLimit
import DifferentialGeometry.Geometry.Comparison.OriginalFactorGeometry

set_option autoImplicit false

open Set Metric Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w z

theorem eventually_residual_lt_of_coordinate_control
    {X : ℕ → Type u} {A : ℕ → Type v} {Y : Type w} {E : Type z}
    [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (A i)] [MetricSpace Y] [MetricSpace E]
    {p : ∀ i, X i} {b : ∀ i, A i} {q : Y} {a : E} {β R ε : ℕ → ℝ}
    (F : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (β i))
    (g : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (e : Y ≃ᵢ E) (he : e q = a)
    (hβ : Tendsto β atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hR : Tendsto R atTop atTop)
    (hcontrol : ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        dist ((F i).toFun x.val).fst (e ((g i).toFun x)) < η)
    (S r : ℝ) (hr : 0 < r) :
    ∀ᶠ i in atTop, ∀ x : X i, dist x (p i) ≤ S → dist ((F i).toFun x).snd (b i) < r := by
  let B := max S 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right S 0]
  have hSB : S < B := by dsimp [B]; linarith [le_max_left S 0]
  let τ := r ^ 2 / (12 * B)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : 12 * B * τ = r ^ 2 := by dsimp [τ]; field_simp
  filter_upwards [hβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hβ.eventually (gt_mem_nhds (inv_pos.mpr hB)), hβ.eventually (gt_mem_nhds hτ),
    hε.eventually (gt_mem_nhds hτ), hR.eventually (eventually_ge_atTop B),
    hcontrol S τ hτ] with i hβone hβinv hβτ hετ hRi hci
  intro x hx
  have hxR : dist x (p i) ≤ R i := hx.trans (hSB.le.trans hRi)
  have hBinv : B < (β i)⁻¹ := by
    simpa only [inv_inv] using (inv_lt_inv₀ (inv_pos.mpr hB) (F i).error_pos).mpr hβinv
  have hbound := (F i).snd_dist_sq_le_of_coordinate_control (g i) e he ⟨x, hxR⟩
    (hx.trans_lt (hSB.trans hBinv)) (hci ⟨x, hxR⟩ hx).le
  have hdB : dist x (p i) + β i ≤ B := by
    dsimp [B]
    linarith [le_max_left S 0]
  have hsum : 0 ≤ β i + ε i + τ := by linarith [(F i).error_pos, (g i).error_pos]
  have hmul := mul_le_mul_of_nonneg_right (show 2 * (dist x (p i) + β i) ≤ 2 * B by linarith) hsum
  have hsmall := mul_lt_mul_of_pos_left (show β i + ε i + τ < 3 * τ by linarith) (show 0 < 2 * B by positivity)
  have hsq : dist ((F i).toFun x).snd (b i) ^ 2 < r ^ 2 := by
    dsimp only at hbound
    nlinarith [sq_pos_of_pos hr]
  exact (sq_lt_sq₀ dist_nonneg hr.le).mp hsq

theorem PointedGHConverges.exists_subsequence_with_vanishing_tested_residual
    {X : ℕ → Type u} {A : ℕ → Type v} {Y : Type w}
    [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (A i)] [MetricSpace Y]
    [CompleteSpace Y] [ProperSpace Y] {p : ∀ i, X i} {b : ∀ i, A i} {q : Y}
    {β : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h : PointedGHConverges p q)
    (F : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), b i)) (β i))
    (hβ : Tendsto β atTop (𝓝 0))
    (hsegments : ∀ x y : Y, ∃ f : unitInterval → Y,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hdim : dimH (univ : Set Y) ≤ n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ S r : ℝ, 0 < r →
      ∀ᶠ i in atTop, ∀ x : X (φ i), dist x (p (φ i)) ≤ S →
        dist ((F (φ i)).toFun x).snd (b (φ i)) < r := by
  obtain ⟨W, mW, w, φ, hφ, hpW, hcW, _, _, e, he, R, ε, hR, hε, g, hcontrol⟩ :=
    h.exists_controlled_product_limit_of_approximate_products F hβ
  let := mW
  let := hpW
  let := hcW
  let : Subsingleton W := e.subsingleton_euclidean_factor_of_polynomial_nets q w he hsegments
    (polynomial_nets_of_nonnegative_comparison
      (arbitrarily_short_curves_of_metric_segments hsegments) hcomp hn hdim q)
  let : Unique W := ⟨⟨w⟩, fun y => Subsingleton.elim y w⟩
  let f := e.trans (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin n)) W)
  have hf : f q = 0 := by change (e q).fst = 0; rw [he]; rfl
  exact ⟨φ, hφ, eventually_residual_lt_of_coordinate_control
    (fun i => F (φ i)) g f hf (hβ.comp hφ.tendsto_atTop) hε hR hcontrol⟩

end GC.MetricGeometry
