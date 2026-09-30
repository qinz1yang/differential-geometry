# Pointwise local openness: compiled self-review

This is assistant self-review, not independent human/agent approval.
All four public statements use actual angles, distances, sets and maps. The
localization proof needs finite anchors and strict margins; it retains one
neighborhood and proves positive distance bounds there. Anchor exclusion is
proved from the packet, not an unproved noncoincidence assumption in AC23.
The final theorem calls the geometric correction/open-map chain and applies
the Lipschitz open-image dimension theorem to that same map and neighborhood.
No injectivity or local compactness is inferred. Empty index localization is
allowed; positive rank is explicit for geometric openness.

The two new leaves and both source-copy linter drivers compile silently
(unusedArguments, simpNF, synTaut). defLemma is unavailable in this pin;
declaration kinds were checked manually. The 85-module gate passes (2873
jobs, 643 owned declarations), including generated helpers and transitive
axioms. New closures use only propext, Classical.choice and Quot.sound.
The inherited AreaUpperBarrier warning lies outside these closures; the
migrated root is not built. Earlier mathematical leaves are unchanged.
The static blueprint audit returns BLUEPRINT_STATIC_OK; blueprint207 is
unchanged. No PDF or Overleaf build is claimed.

The following compiled driver proves the real-line geometric inputs and
checks the full pointwise theorem at zero with anchors +2 and -2, yielding
one open neighborhood with an open Euclidean distance map and Hausdorff
rank bound. It also checks actual angle continuity and empty-index packet
localization. The real-line cross-pair condition is vacuous, so this is
not a separate higher-dimensional packet example.

```lean
import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature 1 (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub (by norm_num) (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison : fourPointComparison 1 (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc 1 (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 1 (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 1 (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith

private theorem real_short_curves (p u : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
      eVariationOn c univ < ENNReal.ofReal (dist p u + η) := by
  have hmid (a b ε : ℝ) (hε : 0 < ε) :
      ∃ z : ℝ, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε := by
    refine ⟨(a + b) / 2, ?_, ?_⟩
    · have heq : a - (a + b) / 2 = (a - b) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div]
      norm_num
      rw [Real.dist_eq a b]
      linarith
    · have heq : b - (a + b) / 2 = (b - a) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div, abs_sub_comm b a]
      norm_num
      rw [Real.dist_eq a b]
      linarith
  obtain ⟨c, hc, hc0, hc1, _, hlen⟩ := exists_curve_eVariationOn_lt_of_approximate_midpoints
    hmid p u hη
  exact ⟨c, hc, hc0, hc1, hlen⟩

private theorem real_anchor_bounds (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) (c : ℝ)
    (hc : c ∈ ({2, -2} : Set ℝ)) : dist z c ∈ Icc (1 : ℝ) 3 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0)]
    constructor <;> linarith [hz.1, hz.2]
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
    constructor <;> linarith [hz.1, hz.2]

private theorem real_packet : PairedComparisonPacket (1 / 200) (Ioo (-1 : ℝ) 1)
    (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (-2 : ℝ)) := by
  constructor
  · intro z hz i
    have heq : dist (2 : ℝ) (-2) = dist z 2 + dist z (-2) := by
      rw [Real.dist_eq (2 : ℝ) (-2), Real.dist_eq z 2, Real.dist_eq z (-2),
        abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0),
        abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
      norm_num
      ring
    rw [heq, comparisonAngleNegCurvature_add (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz 2 (by simp)).1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz (-2) (by simp)).1)]
    linarith
  · intro z hz i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

example : ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧
    IsOpenMap (fun z : V => distanceCoordinates 2 (fun _ : Fin 1 => (2 : ℝ)) (z : ℝ)) ∧
    (1 : ℝ≥0∞) ≤ dimH V := by
  have hp : PairedComparisonPacket ((1 / 100 : ℝ) / 2) {(0 : ℝ)}
      (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (-2 : ℝ)) := by
    have h := real_packet.mono (show {(0 : ℝ)} ⊆ Ioo (-1 : ℝ) 1 by norm_num)
    convert h using 1; norm_num
  obtain ⟨V, ho, hq, _, _, _, _, h2, _, _, hd⟩ :=
    exists_open_distanceCoordinates_of_pointwise_packet real_short_curves hp
      real_comparison (Filter.univ_mem) (subset_univ _) (by norm_num) (by norm_num)
      (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
  exact ⟨V, ho, hq, h2, by simpa using hd⟩

example : ContinuousAt (fun z : ℝ =>
    comparisonAngleNegCurvature 1 (dist z 2) (dist z (-2)) (dist (2 : ℝ) (-2))) 0 :=
  continuousAt_comparisonAngleNegCurvature_one_dist (by norm_num) (by norm_num)

example {δ : ℝ} {q : ℝ} (hδ : 0 < δ) :
    ∃ V : Set ℝ, IsOpen V ∧ q ∈ V ∧
      PairedComparisonPacket δ V (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) := by
  have hp : PairedComparisonPacket (δ / 2) {q}
      (fun i : Fin 0 => (Fin.elim0 i : ℝ)) (fun i : Fin 0 => (Fin.elim0 i : ℝ)) := by
    constructor
    · intro z hz i; exact Fin.elim0 i
    · intro z hz i; exact Fin.elim0 i
  obtain ⟨V, ho, hq, _, hV, _⟩ := hp.exists_uniform_nhds hδ
    (by simp) (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 q)
  exact ⟨V, ho, hq, hV⟩

#print axioms exists_open_distanceCoordinates_of_pointwise_packet
#print axioms PairedComparisonPacket.exists_uniform_nhds
#print axioms PairedComparisonPacket.not_mem_anchors
```
