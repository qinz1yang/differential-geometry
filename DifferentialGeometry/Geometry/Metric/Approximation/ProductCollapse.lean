import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.Normed.Lp.ProdLp
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

open Set Filter
open scoped Topology

namespace WithLp

instance instNonempty {p : ENNReal} {X : Type*} [Nonempty X] : Nonempty (WithLp p X) :=
  (WithLp.equiv p X).nonempty

instance instCompactSpaceProd {p : ENNReal} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y] :
    CompactSpace (WithLp p (X × Y)) := (WithLp.homeomorphProd p X Y).symm.compactSpace

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem prod_dist_eq_sqrt_sq_add_sq (a b : WithLp 2 (X × Y)) :
    dist a b = Real.sqrt (dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2) := by
  rw [prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_two]

theorem prod_dist_sub_dist_fst_le (a b : WithLp 2 (X × Y)) :
    |dist a b - dist a.fst b.fst| ≤ dist a.snd b.snd := by
  rw [abs_of_nonneg (sub_nonneg.mpr (dist_fst_le a b))]
  rw [prod_dist_eq_sqrt_sq_add_sq]
  have hsum : 0 ≤ dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hsum
  have hnonneg := Real.sqrt_nonneg (dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2)
  nlinarith [dist_nonneg (x := a.fst) (y := b.fst),
    dist_nonneg (x := a.snd) (y := b.snd)]

end WithLp

namespace GromovHausdorff

theorem ghDist_prod_le_half_diam {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] :
    ghDist (WithLp 2 (X × Y)) X ≤ Metric.diam (univ : Set Y) / 2 := by
  classical
  let y₀ : Y := Classical.choice inferInstance
  have h := ghDist_le_of_approx_subsets
    (s := (univ : Set (WithLp 2 (X × Y)))) (fun a => a.val.fst)
    (ε₁ := 0) (ε₂ := Metric.diam (univ : Set Y)) (ε₃ := 0)
    (fun a => ⟨a, mem_univ a, by simp⟩)
    (fun x => ⟨⟨WithLp.toLp 2 (x, y₀), mem_univ _⟩, by simp⟩)
    (fun a b => (WithLp.prod_dist_sub_dist_fst_le a.val b.val).trans
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)))
  simpa using h

theorem ghDist_prod_le_of_diam_le {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] {δ : ℝ}
    (hdiam : Metric.diam (univ : Set Y) ≤ δ) :
    ghDist (WithLp 2 (X × Y)) X ≤ δ / 2 :=
  ghDist_prod_le_half_diam.trans (div_le_div_of_nonneg_right hdiam (by norm_num))

theorem tendsto_ghDist_prod_of_tendsto_diam
    {X : Type*} {Y : ℕ → Type*} [MetricSpace X] [∀ n, MetricSpace (Y n)]
    [CompactSpace X] [∀ n, CompactSpace (Y n)] [Nonempty X] [∀ n, Nonempty (Y n)]
    (h : Tendsto (fun n => Metric.diam (univ : Set (Y n))) atTop (𝓝 0)) :
    Tendsto (fun n => ghDist (WithLp 2 (X × Y n)) X) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ghDist_prod_le_half_diam)
  simpa only [zero_div] using h.div_const 2

end GromovHausdorff

namespace GC.MetricGeometry

def productFstApprox {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace Y] (p : X) (q : Y) {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε < R) (hdiam : Metric.diam (univ : Set Y) < ε) :
    PointedBallApprox (WithLp.toLp 2 (p, q)) p R ε where
  error_pos := hε
  error_lt_radius := hεR
  toFun x := x.val.fst
  basepoint := rfl
  distortion x y := by
    rw [abs_sub_comm]
    exact (WithLp.prod_dist_sub_dist_fst_le x.val y.val).trans_lt
      ((Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans_lt hdiam)
  coverage x hx := by
    have hd : dist (WithLp.toLp 2 (x, q)) (WithLp.toLp 2 (p, q)) = dist x p := by
      rw [WithLp.prod_dist_eq_sqrt_sq_add_sq]
      simp
    refine ⟨⟨WithLp.toLp 2 (x, q), ?_⟩, by simpa using hε⟩
    rw [hd]
    exact hx.trans (sub_le_self _ hε.le)

theorem pointedGHConverges_product_of_tendsto_diam
    {X : Type*} {Y : ℕ → Type*} [MetricSpace X] [∀ n, MetricSpace (Y n)]
    [CompleteSpace X] [∀ n, CompactSpace (Y n)] (p : X) (q : ∀ n, Y n)
    (h : Tendsto (fun n => Metric.diam (univ : Set (Y n))) atTop (𝓝 0)) :
    PointedGHConverges (fun n => WithLp.toLp 2 (p, q n)) p := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  filter_upwards [h.eventually (eventually_lt_nhds hε)] with n hn
  exact ⟨productFstApprox p (q n) hε hεR hn⟩

end GC.MetricGeometry
