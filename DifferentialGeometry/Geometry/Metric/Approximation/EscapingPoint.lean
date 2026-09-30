import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.Correspondence

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace GC.MetricGeometry.EscapingPoint

abbrev Carrier (n : ℕ) := {x : ℝ // x ∈ ({0, (n : ℝ) + 1} : Set ℝ)}

instance instFinite (n : ℕ) : Finite (Carrier n) :=
  ((Set.finite_singleton ((n : ℝ) + 1)).insert 0).to_subtype

def basepoint (n : ℕ) : Carrier n := ⟨0, by simp⟩

def farPoint (n : ℕ) : Carrier n := ⟨(n : ℝ) + 1, by simp⟩

instance instNonempty (n : ℕ) : Nonempty (Carrier n) := ⟨basepoint n⟩

theorem dist_farPoint_basepoint (n : ℕ) :
    dist (farPoint n) (basepoint n) = (n : ℝ) + 1 := by
  change |((n : ℝ) + 1) - 0| = (n : ℝ) + 1
  rw [sub_zero, abs_of_nonneg (by positivity)]

theorem dist_le_separation (n : ℕ) (x y : Carrier n) : dist x y ≤ (n : ℝ) + 1 := by
  have hx := x.property
  have hy := y.property
  simp only [mem_insert_iff, mem_singleton_iff] at hx hy
  change |x.val - y.val| ≤ (n : ℝ) + 1
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;>
    apply abs_le.mpr <;> constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]

theorem diam_eq_separation (n : ℕ) : Metric.diam (univ : Set (Carrier n)) = (n : ℝ) + 1 := by
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le (by positivity)
      (fun x _ y _ => dist_le_separation n x y)
  · calc
      (n : ℝ) + 1 = dist (farPoint n) (basepoint n) := (dist_farPoint_basepoint n).symm
      _ ≤ Metric.diam (univ : Set (Carrier n)) :=
        Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

theorem not_exists_uniform_diam_bound :
    ¬ ∃ D : ℝ, ∀ n : ℕ, Metric.diam (univ : Set (Carrier n)) ≤ D := by
  rintro ⟨D, hD⟩
  obtain ⟨n, hn⟩ := exists_nat_gt D
  have h := hD n
  rw [diam_eq_separation] at h
  linarith

theorem eq_basepoint_of_mem_ball {n : ℕ} {R : ℝ} (hR : R < (n : ℝ) + 1)
    (x : Carrier n) (hx : dist x (basepoint n) ≤ R) : x = basepoint n := by
  apply Subtype.ext
  have hmem := x.property
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with hzero | hfar
  · exact hzero
  · have heq : x = farPoint n := Subtype.ext hfar
    rw [heq, dist_farPoint_basepoint] at hx
    exact False.elim (by linarith)

def approximation (n : ℕ) {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hR : R < (n : ℝ) + 1) : PointedBallApprox (basepoint n) Unit.unit R ε where
  error_pos := hε
  error_lt_radius := hεR
  toFun _ := Unit.unit
  basepoint := rfl
  distortion x y := by
    rw [eq_basepoint_of_mem_ball hR x.val x.property,
      eq_basepoint_of_mem_ball hR y.val y.property]
    simpa using hε
  coverage y _ := ⟨⟨basepoint n, by simpa using (hε.trans hεR).le⟩, by simpa using hε⟩

theorem pointed_convergence : PointedGHConverges basepoint Unit.unit := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact ⟨approximation n hε hεR (by linarith)⟩

theorem ghDist_eq_half_separation (n : ℕ) :
    GromovHausdorff.ghDist (Carrier n) Unit = ((n : ℝ) + 1) / 2 := by
  apply le_antisymm
  · apply GromovHausdorff.ghDist_le_half_of_correspondence (fun (_ : Carrier n) (_ : Unit) => True)
      (fun _ => ⟨Unit.unit, trivial⟩) (fun _ => ⟨basepoint n, trivial⟩)
    intro x y x' y' _ _
    have hyy : dist y y' = 0 := dist_eq_zero.mpr (Subsingleton.elim y y')
    simpa only [hyy, sub_zero, abs_of_nonneg dist_nonneg] using
      dist_le_separation n x x'
  · obtain ⟨r, hl, _, hd⟩ :=
      GromovHausdorff.exists_correspondence_distortion_le_twice_ghDist
        (X := Carrier n) (Y := Unit)
    obtain ⟨y, hy⟩ := hl (farPoint n)
    obtain ⟨y', hy'⟩ := hl (basepoint n)
    have h := hd (farPoint n) y (basepoint n) y' hy hy'
    have hyy : dist y y' = 0 := dist_eq_zero.mpr (Subsingleton.elim y y')
    rw [hyy, sub_zero, abs_of_nonneg dist_nonneg,
      dist_farPoint_basepoint] at h
    linarith

theorem tendsto_ghDist_atTop :
    Tendsto (fun n => GromovHausdorff.ghDist (Carrier n) Unit) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * b)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [ghDist_eq_half_separation]
  linarith

theorem not_tendsto_ghDist_zero :
    ¬ Tendsto (fun n => GromovHausdorff.ghDist (Carrier n) Unit) atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (1 / 4) (by norm_num)
  have hh := hN N le_rfl
  rw [ghDist_eq_half_separation, Real.dist_eq, sub_zero,
    abs_of_nonneg (by positivity)] at hh
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

end GC.MetricGeometry.EscapingPoint
