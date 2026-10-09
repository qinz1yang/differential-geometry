import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Geometry.Metric.Approximation.ProductCollapse

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace MetricSpace

variable {Y F : Type*}

@[instance_reducible]
noncomputable def scaledProduct (mY : MetricSpace Y) (mF : MetricSpace F) (t : ℝ) (ht : 0 < t) :
    MetricSpace (WithLp 2 (Y × F)) :=
  let : MetricSpace Y := mY
  let : MetricSpace F := mF.rescale t ht
  inferInstance

theorem scaledProduct_dist (mY : MetricSpace Y) (mF : MetricSpace F)
    (t : ℝ) (ht : 0 < t) (a b : WithLp 2 (Y × F)) :
    @dist (WithLp 2 (Y × F)) (scaledProduct mY mF t ht).toDist a b =
      Real.sqrt ((@dist Y mY.toDist a.fst b.fst) ^ 2 +
        t ^ 2 * (@dist F mF.toDist a.snd b.snd) ^ 2) := by
  let : MetricSpace Y := mY
  let : MetricSpace F := mF.rescale t ht
  rw [show @dist (WithLp 2 (Y × F)) (scaledProduct mY mF t ht).toDist a b = dist a b
    from rfl, WithLp.prod_dist_eq_sqrt_sq_add_sq]
  change Real.sqrt ((dist a.fst b.fst) ^ 2 +
      (t * @dist F mF.toDist a.snd b.snd) ^ 2) = _
  rw [mul_pow]

end MetricSpace

namespace GromovHausdorff

variable {Y F : Type*} [mY : MetricSpace Y] [mF : MetricSpace F]

theorem ghDist_scaledProduct_le_half_diam [CompactSpace Y] [CompactSpace F]
    [Nonempty Y] [Nonempty F] (t : ℝ) (ht : 0 < t) :
    letI : MetricSpace (WithLp 2 (Y × F)) := MetricSpace.scaledProduct mY mF t ht
    ghDist (WithLp 2 (Y × F)) Y ≤ t * Metric.diam (univ : Set F) / 2 := by
  have hdiam := MetricSpace.rescale_diam mF t ht (univ : Set F)
    isCompact_univ.isBounded
  let : MetricSpace F := mF.rescale t ht
  have h := ghDist_prod_le_half_diam (X := Y) (Y := F)
  rw [hdiam] at h
  exact h

theorem tendsto_ghDist_scaledProduct [CompactSpace Y] [CompactSpace F]
    [Nonempty Y] [Nonempty F] {t : ℕ → ℝ} (ht : ∀ n, 0 < t n)
    (hlim : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n =>
      letI : MetricSpace (WithLp 2 (Y × F)) := MetricSpace.scaledProduct mY mF (t n) (ht n)
      ghDist (WithLp 2 (Y × F)) Y) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => dist_nonneg)
    (fun n => ghDist_scaledProduct_le_half_diam (Y := Y) (F := F) (t n) (ht n))
  simpa only [zero_mul, zero_div] using
    (hlim.mul_const (Metric.diam (univ : Set F))).div_const 2

end GromovHausdorff

namespace GC.MetricGeometry

theorem pointedGHConverges_scaledProduct
    {Y F : Type*} [mY : MetricSpace Y] [mF : MetricSpace F]
    [CompleteSpace Y] [CompactSpace F] (p : Y) (q : F)
    {t : ℕ → ℝ} (ht : ∀ n, 0 < t n) (hlim : Tendsto t atTop (𝓝 0)) :
    @PointedGHConverges (fun _ : ℕ => WithLp 2 (Y × F))
      (fun n => MetricSpace.scaledProduct mY mF (t n) (ht n)) Y mY
      (fun _ => WithLp.toLp 2 (p, q)) p := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  have hdlim : Tendsto (fun n => t n * Metric.diam (univ : Set F)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const (Metric.diam (univ : Set F))
  filter_upwards [hdlim.eventually (eventually_lt_nhds hε)] with n hn
  have hdiam := MetricSpace.rescale_diam mF (t n) (ht n) (univ : Set F)
    isCompact_univ.isBounded
  let : MetricSpace F := mF.rescale (t n) (ht n)
  exact ⟨productFstApprox p q hε hεR (hdiam.trans_lt hn)⟩

end GC.MetricGeometry
