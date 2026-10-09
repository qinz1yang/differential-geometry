import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

section

variable {I : Type*} {l : Filter I}
variable {A : I → Type*} [∀ i, MetricSpace (A i)]
variable {Y : Type*} [MetricSpace Y]
variable {o : ∀ i, A i} {p : Y} {R ε : I → ℝ}

theorem PointedBallApprox.tendsto_dist_of_tendsto_images
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε l (𝓝 0))
    (x y : ∀ i, BallCarrier (o i) (R i)) {a b : Y}
    (hx : Tendsto (fun i => (f i).toFun (x i)) l (𝓝 a))
    (hy : Tendsto (fun i => (f i).toFun (y i)) l (𝓝 b)) :
    Tendsto (fun i => dist (x i).val (y i).val) l (𝓝 (dist a b)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (i : I) : dist (dist (x i).val (y i).val) (dist a b) ≤
      ε i + dist (dist ((f i).toFun (x i)) ((f i).toFun (y i))) (dist a b) := by
    have herr : dist (dist (x i).val (y i).val)
        (dist ((f i).toFun (x i)) ((f i).toFun (y i))) ≤ ε i := by
      rw [Real.dist_eq, abs_sub_comm]
      exact (f i).distortion (x i) (y i) |>.le
    exact (dist_triangle _ (dist ((f i).toFun (x i)) ((f i).toFun (y i))) _).trans
      (add_le_add herr le_rfl)
  exact squeeze_zero (fun i => dist_nonneg) hbound
    (by simpa only [zero_add] using hε.add (tendsto_iff_dist_tendsto_zero.mp (hx.dist hy)))

end

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y]
variable {o : ∀ i, A i} {p : Y} {R ε : ℕ → ℝ}

theorem tendsto_dist_IccExtend_of_converging_signed_prefixes
    {L : ℕ → ι → ℝ} (hL : ∀ i j, 0 ≤ L i j)
    (Q : ∀ i j, Icc (-(L i j)) (L i j) → A i)
    (hLip : ∀ i j, LipschitzWith 1 (Q i j))
    (hbase : ∀ i j, Q i j ⟨0, ⟨by linarith [hL i j], hL i j⟩⟩ = o i)
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) (γ : ι → ℝ → Y)
    (hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ j, S ≤ L i j ∧
      ∀ t : Icc (-(L i j)) (L i j), |t.val| ≤ S →
        ∀ ht : dist (Q i j t) (o i) ≤ R i,
          dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ)
    (j k : ι) (s t : ℝ) :
    Tendsto (fun i => dist
      (IccExtend (by linarith [hL i j] : -(L i j) ≤ L i j) (Q i j) s)
      (IccExtend (by linarith [hL i k] : -(L i k) ≤ L i k) (Q i k) t))
      atTop (𝓝 (dist (γ j s) (γ k t))) := by
  classical
  have hrad (i : ℕ) (j : ι) (u : Icc (-(L i j)) (L i j)) :
      dist (Q i j u) (o i) ≤ |u.val| := by
    have hh := (hLip i j).dist_le_mul u ⟨0, ⟨by linarith [hL i j], hL i j⟩⟩
    rw [hbase] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, sub_zero] using hh
  let x (i : ℕ) (j : ι) (u : ℝ) : BallCarrier (o i) (R i) :=
    if hu : |u| ≤ min (L i j) (R i) then
      ⟨Q i j ⟨u, abs_le.mp (hu.trans (min_le_left _ _))⟩,
        (hrad i j _).trans (hu.trans (min_le_right _ _))⟩
    else ⟨o i, by simpa only [dist_self] using (f i).error_pos.le.trans (f i).error_lt_radius.le⟩
  have hx (j : ι) (u : ℝ) : Tendsto (fun i => (f i).toFun (x i j u)) atTop (𝓝 (γ j u)) := by
    apply Metric.tendsto_nhds.mpr
    intro ζ hζ
    filter_upwards [hconv |u| ζ hζ] with i hi
    have hu : |u| ≤ min (L i j) (R i) := le_min (hi.2 j).1 hi.1
    simp only [x, dite_eq_left hu]
    exact (hi.2 j).2 ⟨u, abs_le.mp (hu.trans (min_le_left _ _))⟩ le_rfl _
  have hd := PointedBallApprox.tendsto_dist_of_tendsto_images f hε
    (fun i => x i j s) (fun i => x i k t) (hx j s) (hx k t)
  apply hd.congr'
  filter_upwards [hconv (max |s| |t|) 1 zero_lt_one] with i hi
  have hs : |s| ≤ min (L i j) (R i) :=
    le_min ((le_max_left _ _).trans (hi.2 j).1) ((le_max_left _ _).trans hi.1)
  have ht : |t| ≤ min (L i k) (R i) :=
    le_min ((le_max_right _ _).trans (hi.2 k).1) ((le_max_right _ _).trans hi.1)
  simp only [x, dite_eq_left hs, dite_eq_left ht,
    IccExtend_of_mem (by linarith [hL i j] : -(L i j) ≤ L i j) (Q i j)
      (abs_le.mp (hs.trans (min_le_left _ _))),
    IccExtend_of_mem (by linarith [hL i k] : -(L i k) ≤ L i k) (Q i k)
      (abs_le.mp (ht.trans (min_le_left _ _)))]

theorem tendsto_comparisonAngle_IccExtend_of_converging_signed_prefixes
    {L : ℕ → ι → ℝ} (hL : ∀ i j, 0 ≤ L i j)
    (Q : ∀ i j, Icc (-(L i j)) (L i j) → A i)
    (hLip : ∀ i j, LipschitzWith 1 (Q i j))
    (hbase : ∀ i j, Q i j ⟨0, ⟨by linarith [hL i j], hL i j⟩⟩ = o i)
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) (γ : ι → ℝ → Y)
    (hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ j, S ≤ L i j ∧
      ∀ t : Icc (-(L i j)) (L i j), |t.val| ≤ S →
        ∀ ht : dist (Q i j t) (o i) ≤ R i,
          dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ)
    {κ : ℕ → ℝ} (hκ : Tendsto κ atTop (𝓝 0))
    (hκnonneg : ∀ᶠ i in atTop, 0 ≤ κ i)
    (j k : ι) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    Tendsto (fun i => DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature
      (κ i) |s| |t| (dist
        (IccExtend (by linarith [hL i j] : -(L i j) ≤ L i j) (Q i j) s)
        (IccExtend (by linarith [hL i k] : -(L i k) ≤ L i k) (Q i k) t)))
      atTop (𝓝 (DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature
        0 |s| |t| (dist (γ j s) (γ k t)))) := by
  simpa only [DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_zero] using
    DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngleNegCurvature_zero
      hκ tendsto_const_nhds tendsto_const_nhds
      (tendsto_dist_IccExtend_of_converging_signed_prefixes hL Q hLip hbase f hε γ hconv j k s t)
      hκnonneg (abs_pos.mpr hs) (abs_pos.mpr ht)

end GC.MetricGeometry
