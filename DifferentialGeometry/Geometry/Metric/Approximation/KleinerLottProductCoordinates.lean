import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottBallTransport

/-!
# Kleiner–Lott approximations with BOTH product coordinates prescribed (lane BCUSP-1)

`PointedBallApprox.exists_kleinerLott_with_first_coordinate_BCG1` (lane BCG-1) turns a bi-Lipschitz
product map `x ↦ (Φ x, φT (τ x))` into `ℝ ×₂ Y` with coverage into a Kleiner–Lott approximation whose
FIRST coordinate is `Φ` everywhere; it does not record the second coordinate. The same construction
also has second coordinate `φT (τ x)` on the whole test ball of radius `β⁻¹ + β` (which contains the
Kleiner–Lott ball of radius `β⁻¹`): the residual factor is read through the given map `φT ∘ τ`, not
replaced.

* `PointedBallApprox.toKleinerLottWithFirstCoordinate_toFun_BCUSP1`: on the ball of radius `R` the
  Kleiner–Lott map of `toKleinerLottWithFirstCoordinate` is the given ball map;
* `PointedBallApprox.exists_kleinerLott_with_product_coordinates_BCUSP1`: the product form.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function

namespace GC.MetricGeometry

universe u v

namespace PointedBallApprox

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]
variable {p : X} {a : E} {b : Y} {R ε δ : ℝ}

/-- On the ball of radius `R`, the Kleiner–Lott map of `toKleinerLottWithFirstCoordinate` is the
ball map of the pointed approximation. -/
theorem toKleinerLottWithFirstCoordinate_toFun_BCUSP1
    (f : PointedBallApprox p (WithLp.toLp 2 (a, b)) R ε) (h : X → E)
    (hδ : 0 < δ) (hδone : δ < 1) (hε : ε < δ / 2) (hR : δ⁻¹ ≤ R) (x : BallCarrier p R) :
    (f.toKleinerLottWithFirstCoordinate h hδ hδone hε hR).toFun x.val = f.toFun x := by
  classical
  change (if hx : dist x.val p ≤ R then f.toFun ⟨x.val, hx⟩ else WithLp.toLp 2 (h x.val, b)) = _
  rw [dite_eq_left x.property]

/-- **Both coordinates prescribed.** For `x ↦ (Φ x, φT (τ x))` `(1 ± a)`-bi-Lipschitz on the closed
ball of radius `β⁻¹ + β` about `p₀` and `β/4`-covering (measured with `√(ΔΦ² + (c d_T)²)`, `φT` a
surjective metric model of `c d_T`), there is a Kleiner–Lott `β`-approximation of `(X, p₀)` to
`(ℝ ×₂ Y, (0, φT (τ p₀)))` whose first coordinate is `Φ` everywhere and whose second coordinate is
`φT (τ x)` on the whole closed ball of radius `β⁻¹ + β`. -/
theorem exists_kleinerLott_with_product_coordinates_BCUSP1 {Xs : Type u} [MetricSpace Xs]
    {p₀ : Xs} {β a c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (herr : 2 * a * (β⁻¹ + β) < β / 4) {T : Type v} (Φ : Xs → ℝ) (τ : Xs → T)
    (dT : T → T → ℝ) (hbase : Φ p₀ = 0)
    (hdist : ∀ x x', dist x p₀ ≤ β⁻¹ + β → dist x' p₀ ≤ β⁻¹ + β →
      (1 - a) * dist x x' ≤ Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ∧
        Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ≤ (1 + a) * dist x x')
    (hcov : ∀ (s : ℝ) (t : T),
      Real.sqrt (s ^ 2 + (c * dT t (τ p₀)) ^ 2) ≤ β⁻¹ + β - β / 4 →
        ∃ x, dist x p₀ ≤ β⁻¹ + β ∧ Real.sqrt ((s - Φ x) ^ 2 + (c * dT t (τ x)) ^ 2) < β / 4)
    {Y : Type v} [MetricSpace Y] (φT : T → Y) (hφT : Surjective φT)
    (hdY : ∀ t t', dist (φT t) (φT t') = c * dT t t') :
    ∃ f : KleinerLottApprox p₀ (WithLp.toLp 2 ((0 : ℝ), φT (τ p₀))) β,
      (∀ x, (f.toFun x).fst = Φ x) ∧
        ∀ x, dist x p₀ ≤ β⁻¹ + β → (f.toFun x).snd = φT (τ x) := by
  have hd : ∀ (u u' : ℝ) (t t' : T),
      dist (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y)) (WithLp.toLp 2 (u', φT t')) =
        Real.sqrt ((u - u') ^ 2 + (c * dT t t') ^ 2) := by
    intro u u' t t'
    have h := WithLp.prod_dist_sq_eq_add_sq (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y))
      (WithLp.toLp 2 (u', φT t'))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs, hdY] at h
    rw [← h, Real.sqrt_sq dist_nonneg]
  have hε : 0 < β / 4 := by positivity
  have hεR : β / 4 < β⁻¹ + β := by
    have := inv_pos.mpr hβ
    linarith
  let F : Xs → WithLp 2 (ℝ × Y) := fun x => WithLp.toLp 2 (Φ x, φT (τ x))
  have hbaseF : F p₀ = WithLp.toLp 2 ((0 : ℝ), φT (τ p₀)) := by
    simp only [F, hbase]
  let f : PointedBallApprox p₀ (WithLp.toLp 2 ((0 : ℝ), φT (τ p₀))) (β⁻¹ + β) (β / 4) :=
    PointedBallApprox.ofBilipschitz ⟨ha, ha1⟩ hε hεR herr (fun x => F x.val) hbaseF
      (fun x x' => by
        change (1 - a) * dist x.val x'.val ≤ dist (F x.val) (F x'.val) ∧
          dist (F x.val) (F x'.val) ≤ (1 + a) * dist x.val x'.val
        simp only [F]
        rw [hd]
        exact hdist x.val x'.val x.property x'.property)
      (fun y hy => by
        obtain ⟨t, ht⟩ := hφT y.snd
        have hy' : y = WithLp.toLp 2 (y.fst, φT t) := by
          rw [ht]
          rfl
        rw [hy', hd, sub_zero] at hy
        obtain ⟨x, hx, hxy⟩ := hcov y.fst t hy
        refine ⟨⟨x, hx⟩, ?_⟩
        change dist y (F x) < β / 4
        rw [hy']
        simp only [F]
        rw [hd]
        exact hxy)
  have hεδ : β / 4 < β / 2 := by linarith
  have hRδ : β⁻¹ ≤ β⁻¹ + β := by linarith
  refine ⟨f.toKleinerLottWithFirstCoordinate Φ hβ hβ1 hεδ hRδ, fun x => ?_, fun x hx => ?_⟩
  · exact f.toKleinerLottWithFirstCoordinate_fst Φ (fun x => rfl) hβ hβ1 _ _ x
  · rw [f.toKleinerLottWithFirstCoordinate_toFun_BCUSP1 Φ hβ hβ1 hεδ hRδ ⟨x, hx⟩]
    rfl

end PointedBallApprox

end GC.MetricGeometry
