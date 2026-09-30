import DifferentialGeometry.Topology.MetricSpace.DistanceMatrixLimit
import DifferentialGeometry.Geometry.Comparison.DistanceMatrixLimit
import DifferentialGeometry.Geometry.Comparison.DistanceMatrixRadial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

universe u

open Set Filter Real Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_uniform_radial_defect_distance_matrix {a D t ε : ℝ}
    (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ d : Fin 5 → Fin 5 → ℝ,
      (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
      (∀ i j k, d i k ≤ d i j + d j k) →
      (∀ q x y z, 0 < d q x → 0 < d q y → 0 < d q z →
        comparisonAngleNegCurvature 1 (d q x) (d q y) (d x y) +
          comparisonAngleNegCurvature 1 (d q y) (d q z) (d y z) +
          comparisonAngleNegCurvature 1 (d q z) (d q x) (d z x) ≤ 2 * Real.pi) →
      d 0 1 ∈ Icc a D → d 0 2 ∈ Icc a D → ε ≤ d 1 2 →
      d 0 3 = t * d 0 1 → (1 - t) * d 0 1 ≤ d 3 1 → d 3 1 ≤ (1 - t) * d 0 1 + η →
      d 0 4 = t * d 0 2 → (1 - t) * d 0 2 ≤ d 4 2 → d 4 2 ≤ (1 - t) * d 0 2 + η →
      ((t * D / sinh D) / 2) * d 1 2 ≤ d 3 4 := by
  classical
  by_contra hnone
  push Not at hnone
  have hη (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose d hself hsymm htri hcomp hr hs hsep hqu huxlo huxhi hqv hvylo hvyhi hbad using
    fun (n : ℕ) => hnone (1 / ((n : ℝ) + 1)) (hη n)
  have hD : 0 < D := ha.trans_le haD
  have hnonneg (n : ℕ) (i j : Fin 5) : 0 ≤ d n i j := by
    have hh := htri n i j i
    rw [hself n i, hsymm n j i] at hh
    linarith
  have hrad (n : ℕ) (i : Fin 5) : d n 0 i ≤ D := by
    fin_cases i
    · change d n 0 0 ≤ D
      rw [hself]
      exact hD.le
    · exact (hr n).2
    · exact (hs n).2
    · change d n 0 3 ≤ D
      rw [hqu]
      exact (mul_le_of_le_one_left (hnonneg n 0 1) ht.2.le).trans (hr n).2
    · change d n 0 4 ≤ D
      rw [hqv]
      exact (mul_le_of_le_one_left (hnonneg n 0 2) ht.2.le).trans (hs n).2
  have hbounded (n : ℕ) (i j : Fin 5) : d n i j ∈ Icc 0 (2 * D) := by
    refine ⟨hnonneg n i j, ?_⟩
    have hh := htri n i 0 j
    rw [hsymm n i 0] at hh
    linarith [hrad n i, hrad n j]
  let P (n : ℕ) : PseudoMetricSpace (Fin 5) := {
    dist := d n
    dist_self := hself n
    dist_comm := hsymm n
    dist_triangle := htri n }
  obtain ⟨φ, hφ, dlim, hlim⟩ := @exists_pseudometric_subseq_tendsto_dist (Fin 5) inferInstance
    (fun _ : ℕ => Fin 5) P (fun _ i => i) (fun _ _ => 2 * D) (fun n i j => (hbounded n i j).2)
  let d₀ := dlim.dist
  have hd (i j : Fin 5) : Tendsto (fun n => d (φ n) i j) atTop (𝓝 (d₀ i j)) := hlim i j
  have hself₀ := dlim.dist_self
  have hsymm₀ := dlim.dist_comm
  have htri₀ := dlim.dist_triangle
  have hcomp₀ := fourPoint_distance_matrix_limit (by norm_num : (0 : ℝ) < 1) hd
    (fun n => hcomp (φ n))
  have hrlo : a ≤ d₀ 0 1 := le_of_tendsto_of_tendsto tendsto_const_nhds (hd 0 1)
    (Eventually.of_forall (fun n => (hr (φ n)).1))
  have hrhi : d₀ 0 1 ≤ D := le_of_tendsto (hd 0 1)
    (Eventually.of_forall (fun n => (hr (φ n)).2))
  have hslo : a ≤ d₀ 0 2 := le_of_tendsto_of_tendsto tendsto_const_nhds (hd 0 2)
    (Eventually.of_forall (fun n => (hs (φ n)).1))
  have hshi : d₀ 0 2 ≤ D := le_of_tendsto (hd 0 2)
    (Eventually.of_forall (fun n => (hs (φ n)).2))
  have hsep₀ : ε ≤ d₀ 1 2 := le_of_tendsto_of_tendsto tendsto_const_nhds (hd 1 2)
    (Eventually.of_forall (fun n => hsep (φ n)))
  have hqu₀ : d₀ 0 3 = t * d₀ 0 1 := by
    apply tendsto_nhds_unique (hd 0 3)
    convert (hd 0 1).const_mul t using 1
    funext n
    exact hqu (φ n)
  have hqv₀ : d₀ 0 4 = t * d₀ 0 2 := by
    apply tendsto_nhds_unique (hd 0 4)
    convert (hd 0 2).const_mul t using 1
    funext n
    exact hqv (φ n)
  have hηlim : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hux₀ : d₀ 3 1 = (1 - t) * d₀ 0 1 := by
    apply le_antisymm
    · have hh := le_of_tendsto_of_tendsto (hd 3 1) (((hd 0 1).const_mul (1 - t)).add hηlim)
        (Eventually.of_forall (fun n => huxhi (φ n)))
      simpa only [add_zero] using hh
    · exact le_of_tendsto_of_tendsto ((hd 0 1).const_mul (1 - t)) (hd 3 1)
        (Eventually.of_forall (fun n => huxlo (φ n)))
  have hvy₀ : d₀ 4 2 = (1 - t) * d₀ 0 2 := by
    apply le_antisymm
    · have hh := le_of_tendsto_of_tendsto (hd 4 2) (((hd 0 2).const_mul (1 - t)).add hηlim)
        (Eventually.of_forall (fun n => hvyhi (φ n)))
      simpa only [add_zero] using hh
    · exact le_of_tendsto_of_tendsto ((hd 0 2).const_mul (1 - t)) (hd 4 2)
        (Eventually.of_forall (fun n => hvylo (φ n)))
  have hbad₀ := le_of_tendsto_of_tendsto (hd 3 4) ((hd 1 2).const_mul ((t * D / sinh D) / 2))
    (Eventually.of_forall (fun n => (hbad (φ n)).le))
  have hlower := radial_lower_of_distance_matrix d₀ hself₀ hsymm₀ htri₀ hcomp₀
    (ha.trans_le hrlo) (ha.trans_le hslo) hrhi hshi ht hqu₀ hux₀ hqv₀ hvy₀
  have hpositive : 0 < (t * D / sinh D) * d₀ 1 2 :=
    mul_pos (div_pos (mul_pos ht.1 hD) (sinh_pos_iff.mpr hD)) (hε.trans_le hsep₀)
  nlinarith

theorem exists_uniform_radial_defect {a D t ε : ℝ}
    (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {X : Type u} [MetricSpace X] {Ω : Set X},
      fourPointComparison 1 Ω → ∀ {q x y u v : X},
      q ∈ Ω → x ∈ Ω → y ∈ Ω → u ∈ Ω → v ∈ Ω →
      dist q x ∈ Icc a D → dist q y ∈ Icc a D → ε ≤ dist x y →
      dist q u = t * dist q x →
      (1 - t) * dist q x ≤ dist u x → dist u x ≤ (1 - t) * dist q x + η →
      dist q v = t * dist q y →
      (1 - t) * dist q y ≤ dist v y → dist v y ≤ (1 - t) * dist q y + η →
      ((t * D / sinh D) / 2) * dist x y ≤ dist u v := by
  obtain ⟨η, hη, hmatrix⟩ := exists_uniform_radial_defect_distance_matrix ha haD ht hε
  refine ⟨η, hη, ?_⟩
  intro X inst Ω hcomp q x y u v hq hx hy hu hv hr hs hsep hqu huxlo huxhi hqv hvylo hvyhi
  let p : Fin 5 → X := ![q, x, y, u, v]
  have hp (i : Fin 5) : p i ∈ Ω := by
    fin_cases i <;> simp [p, hq, hx, hy, hu, hv]
  have hmatrixComp : ∀ i j k l : Fin 5, 0 < dist (p i) (p j) →
      0 < dist (p i) (p k) → 0 < dist (p i) (p l) →
      comparisonAngleNegCurvature 1 (dist (p i) (p j)) (dist (p i) (p k)) (dist (p j) (p k)) +
        comparisonAngleNegCurvature 1 (dist (p i) (p k)) (dist (p i) (p l)) (dist (p k) (p l)) +
        comparisonAngleNegCurvature 1 (dist (p i) (p l)) (dist (p i) (p j)) (dist (p l) (p j)) ≤ 2 * Real.pi := by
    intro i j k l hij hik hil
    exact hcomp (p i) (hp i) (p j) (hp j) (p k) (hp k) (p l) (hp l)
      (dist_pos.mp hij).symm (dist_pos.mp hik).symm (dist_pos.mp hil).symm
  exact hmatrix (fun i j => dist (p i) (p j)) (fun i => dist_self (p i))
    (fun i j => dist_comm (p i) (p j)) (fun i j k => dist_triangle (p i) (p j) (p k))
    hmatrixComp hr hs hsep hqu huxlo huxhi hqv hvylo hvyhi

end DifferentialGeometry.Geometry.Comparison.Toponogov
