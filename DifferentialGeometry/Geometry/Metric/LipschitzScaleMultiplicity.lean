import DifferentialGeometry.Geometry.Metric.SupportScalePacking
import DifferentialGeometry.Analysis.Integration.Measure.FinitePacking
import DifferentialGeometry.Topology.MetricSpace.LipschitzBallSelection
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem card_le_of_lipschitz_scale_ball_overlap
    (μ : Measure X) (I : Finset X) {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ i ∈ I, 0 < ρ i)
    {a C b : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hsmall : (Λ : ℝ) * C ≤ 1 / 4)
    (hdisjoint : (I : Set X).PairwiseDisjoint (fun i => ball i (a * ρ i)))
    (hpos : ∀ i ∈ I, 0 < μ.real (ball i (a * ρ i)))
    (hfinite : ∀ i ∈ I, μ (ball i ((3 * C + 2 * a) * ρ i)) ≠ ∞)
    (hcomparison : ∀ i ∈ I, μ.real (ball i ((3 * C + 2 * a) * ρ i)) ≤
      b * μ.real (ball i (a * ρ i)))
    (x : X) (hx : ∀ i ∈ I, x ∈ ball i (C * ρ i)) : (I.card : ℝ) ≤ b := by
  apply card_le_of_disjoint_measure_comparison μ I
    (fun i => ball i (a * ρ i)) (fun i => ball i ((3 * C + 2 * a) * ρ i))
    hb hdisjoint (fun _ _ => isOpen_ball.measurableSet) hpos hfinite ?_ hcomparison
  intro i hi j hj y hy
  obtain ⟨hr, hd⟩ := scale_ratio_of_support_meeting hρ (hρpos i hi) (hρpos j hj) hC
    (by simpa only [max_self] using hsmall)
    (show (closedBall j (C * ρ j) ∩ ball i (C * ρ i)).Nonempty from
      ⟨x, ball_subset_closedBall (hx j hj), hx i hi⟩)
  have hscale : ρ j ≤ 2 * ρ i := (div_le_iff₀ (hρpos i hi)).mp hr.2
  have hmul := mul_le_mul_of_nonneg_left hscale ha
  have htri := dist_triangle y j i
  change dist y j < a * ρ j at hy
  change dist y i < (3 * C + 2 * a) * ρ i
  nlinarith

theorem exists_finite_scale_cover_with_multiplicity [CompactSpace X]
    (μ : Measure X) (E : Set X) {ρ : X → ℝ} {Λ : NNReal} {Δ C b : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hpos : ∀ i ∈ E, 0 < μ.real (ball i (Δ * ρ i / 3)))
    (hfinite : ∀ i ∈ E, μ (ball i ((3 * C + 2 * (Δ / 3)) * ρ i)) ≠ ∞)
    (hcomparison : ∀ i ∈ E, μ.real (ball i ((3 * C + 2 * (Δ / 3)) * ρ i)) ≤
      b * μ.real (ball i (Δ * ρ i / 3))) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      (∀ p ∈ E, ∃ i ∈ I, ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i)) ∧
      ∀ x : X, ((I ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤ b := by
  classical
  obtain ⟨I, hIE, hfin, hdisj, hcover⟩ :=
    exists_finite_disjoint_lipschitz_scale_selection E hρ hρpos hΔ hselection
  refine ⟨I, hIE, hfin, hdisj, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, _, _, hc⟩ := hcover p hp
    exact ⟨i, hi, hc⟩
  · intro x
    let T := I ∩ {i | x ∈ ball i (C * ρ i)}
    have hT : T.Finite := hfin.subset inter_subset_left
    have ht (i : X) : i ∈ hT.toFinset ↔ i ∈ I ∧ x ∈ ball i (C * ρ i) := by
      simp only [Set.Finite.mem_toFinset, T, mem_inter_iff, mem_ofPred_eq]
    have hid : ∀ i, (Δ / 3) * ρ i = Δ * ρ i / 3 := by intro i; ring
    have hh := card_le_of_lipschitz_scale_ball_overlap μ hT.toFinset hρ
      (fun i _ => hρpos i) (a := Δ / 3) (C := C) (b := b) (by positivity) hC hb hoverlap
      (by
        intro i hi j hj hij
        simp only [hid]
        exact hdisj (ht i |>.mp hi).1 (ht j |>.mp hj).1 hij)
      (by intro i hi; rw [hid]; exact hpos i (hIE (ht i |>.mp hi).1))
      (fun i hi => hfinite i (hIE (ht i |>.mp hi).1))
      (by intro i hi; rw [hid]; exact hcomparison i (hIE (ht i |>.mp hi).1))
      x (fun i hi => (ht i |>.mp hi).2)
    change (T.ncard : ℝ) ≤ b
    rw [Set.ncard_eq_toFinset_card T hT]
    exact hh

end GC.MetricGeometry
