import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateFactorCompactness
import DifferentialGeometry.Geometry.Metric.Approximation.CommonSourceControl
import DifferentialGeometry.Geometry.Metric.Approximation.ProductCoordinateApproximation

open Filter
open scoped Topology

namespace GC.MetricGeometry.PointedGHConverges

universe u v w z
variable {X : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable [∀ i, MetricSpace (X i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace Y]
variable {p : ∀ i, X i} {a : E} {q : Y} {b : ∀ i, Z i} {δ : ℕ → ℝ}

theorem exists_controlled_product_limit_of_approximate_products
    (h : PointedGHConverges p q)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) ∧
          ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i),
              ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
                ∀ x : BallCarrier (p (φ i)) (R i), dist x.val (p (φ i)) ≤ S →
                  dist (((f (φ i)).toFun x.val).fst) ((e ((g i).toFun x)).fst) < η := by
  classical
  obtain ⟨W, m, w, α, hα, hp, hc, hz, hx⟩ :=
    h.exists_factor_limit_of_approximate_products f hδ
  let := m
  let := hp
  let := hc
  let J : ℕ → ℝ := fun i => (i : ℝ) + 1
  let ε : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hJone (i : ℕ) : 1 ≤ J i := by dsimp [J]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hJ : Tendsto J atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hepos (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have heJ (i : ℕ) : 10 * ε i < J i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [ε, J]
    linarith
  have hezero : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  have htail (j : ℕ) : ∀ᶠ i in atTop,
      Nonempty (PointedBallApprox (p (α i)) q (4 * J j + 4) (ε j)) ∧
      ∃ G : PointedBallApprox (p (α i)) (WithLp.toLp 2 (a, w)) (4 * J j + 4) (ε j),
        ∀ x : BallCarrier (p (α i)) (4 * J j + 4),
          (G.toFun x).fst = ((f (α i)).toFun x.val).fst := by
    exact (hx.eventually_approx (hepos j) (by linarith [heJ j, hJone j])).and
      (hz.eventually_product_coordinate_approximation (fun i => f (α i))
        (hδ.comp hα.tendsto_atTop) (hepos j) (by linarith [heJ j, hJone j]))
  obtain ⟨β, hβ, hmaps⟩ := extraction_forall_of_eventually htail
  let A (j : ℕ) : PointedBallApprox (p (α (β j))) q (4 * J j + 4) (ε j) :=
    Classical.choice (hmaps j).1
  choose B hB using fun j => (hmaps j).2
  obtain ⟨e, ψ, he, hψ, hcontrol⟩ :=
    exists_controlled_common_limit_isometry hJone hJ hezero heJ A B
  let φ : ℕ → ℕ := fun i => α (β (ψ i))
  have hφ : StrictMono φ := hα.comp (hβ.comp hψ)
  have hrad : Tendsto (fun i => 4 * J (ψ i) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 ((hJ.comp hψ.tendsto_atTop).const_mul_atTop (by norm_num))
  refine ⟨W, m, w, φ, hφ, hp, hc, (hz.subsequence hβ).subsequence hψ,
    (hx.subsequence hβ).subsequence hψ, e, he,
    (fun i => 4 * J (ψ i) + 4), (fun i => ε (ψ i)), hrad,
    hezero.comp hψ.tendsto_atTop, (fun i => A (ψ i)), ?_⟩
  intro S η hη
  filter_upwards [hcontrol S η hη] with i hi
  intro x hx
  have hh := (WithLp.dist_fst_le ((B (ψ i)).toFun x) (e ((A (ψ i)).toFun x))).trans_lt
    (hi x hx)
  rw [hB (ψ i) x] at hh
  exact hh

end GC.MetricGeometry.PointedGHConverges
