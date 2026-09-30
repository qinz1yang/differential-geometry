# Compiled self-review: same-factor endpoint products

Four public theorems in two leaves pass the 146-module/814-owned-declaration
gate. Source-copy unusedArguments, simpNF and synTaut linters are silent.
defLemma is unavailable; declaration kinds were inspected manually. New
closures use only propext, Classical.choice and Quot.sound. Earlier leaves
are unchanged. The inherited AreaUpperBarrier warning is outside these
closures; no full migrated-root or PDF build is claimed. Static audit passes.

The compiled driver constructs the constant sequence of closed rays with
basepoint at HEIGHT ONE, proves its actual polynomial covering premise
using the Euclidean packing bound and finite nets, and supplies an exact
rank-zero Euclidean-product splitting with nontrivial ray factor. It proves
all segment/comparison/endpoint premises and applies the same-limit theorem.
The resulting global product isometry has transverse basepoint coordinate
EXACTLY ONE, exercising the preservation of positive height. The covering
premise is witnessed in this example, not assumed. The general theorem
retains it, as required. The nontrivial factor, completeness inherited from
convergence, dimension drop and actual product composition are all checked.
This is self-review, not human approval. Endpoint-free classification and
uniform covering production remain open.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.FactorEndpointRecognition
import DifferentialGeometry.Topology.MetricSpace.EuclideanPacking
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import DifferentialGeometry.Geometry.Comparison.EndpointRecognition
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
import DifferentialGeometry.Geometry.Metric.Approximation.FactorRecognition
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature 0 (dist x a) (dist x b) (dist a b) = 0 := by
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

private theorem real_comparison : fourPointComparison 0 (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc 0 (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 0 (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 0 (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) : ∃ f : Icc (0 : ℝ) 1 → ℝ,
    Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
    ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : Icc (0 : ℝ) 1 → ℝ := fun t => x + (y-x) * t
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(x + (y-x)*(s : ℝ)) - (x + (y-x)*(t : ℝ))| = |x-y| * |(s : ℝ)-t|
  have heq : (x + (y-x)*(s : ℝ)) - (x + (y-x)*(t : ℝ)) = (y-x)*((s : ℝ)-t) := by ring
  rw [heq, abs_mul, abs_sub_comm y x]

private theorem ray_segments (x y : Ici (0 : ℝ)) : ∃ f : Icc (0 : ℝ) 1 → Ici (0 : ℝ),
    Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
    ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : Icc (0 : ℝ) 1 → Ici (0 : ℝ) := fun t =>
    ⟨(1-(t : ℝ)) * x + (t : ℝ) * y,
      add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property)
        (mul_nonneg t.property.1 y.property)⟩
  refine ⟨f, by fun_prop, ?_, ?_, ?_⟩
  · apply Subtype.ext; simp [f]
  · apply Subtype.ext; simp [f]
  · intro s t
    change |((1-(s : ℝ)) * x + (s : ℝ) * y) - ((1-(t : ℝ)) * x + (t : ℝ) * y)| =
      |(x : ℝ)-y| * |(s : ℝ)-t|
    have heq : ((1-(s : ℝ)) * x + (s : ℝ) * y) - ((1-(t : ℝ)) * x + (t : ℝ) * y) =
        ((y : ℝ)-x)*((s : ℝ)-t) := by ring
    rw [heq, abs_mul, abs_sub_comm (y : ℝ) x]

private theorem ray_endpoint : ∀ x y : Ici (0 : ℝ),
    dist x (⟨0, by norm_num⟩ : Ici (0 : ℝ)) + dist (⟨0, by norm_num⟩ : Ici (0 : ℝ)) y = dist x y →
      x = ⟨0, by norm_num⟩ ∨ y = ⟨0, by norm_num⟩ := by
  intro x y h
  change |(x : ℝ) - 0| + |0 - (y : ℝ)| = |(x : ℝ) - y| at h
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (show 0 ≤ (x : ℝ) from x.property), abs_of_nonneg (show 0 ≤ (y : ℝ) from y.property)] at h
  rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Or.inl (Subtype.ext (by change (x : ℝ) = 0; linarith))
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at h
    exact Or.inr (Subtype.ext (by change (y : ℝ) = 0; linarith))

private noncomputable def lineEmbedding (x : ℝ) : PiLp 2 (fun _ : Fin 1 => ℝ) :=
  WithLp.toLp 2 (fun _ => x)

private theorem lineEmbedding_dist (x y : ℝ) : dist (lineEmbedding x) (lineEmbedding y) = dist x y := by
  simp [PiLp.dist_eq_of_L2, lineEmbedding]

private theorem lineEmbedding_norm (x : ℝ) : ‖lineEmbedding x‖ = |x| := by
  simp [PiLp.norm_eq_of_L2, lineEmbedding, Real.sqrt_sq_eq_abs]

private theorem ray_nets (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ F : Finset (Ici (0 : ℝ)), (F.card : ℝ) ≤ C * η ^ (-(1 : ℝ)) ∧
        (∀ x ∈ F, dist x (⟨1, by norm_num⟩ : Ici (0 : ℝ)) ≤ R) ∧
        ∀ x : Ici (0 : ℝ), dist x ⟨1, by norm_num⟩ ≤ R → ∃ y ∈ F, dist x y ≤ η := by
  let q : Ici (0 : ℝ) := ⟨1, by norm_num⟩
  let B := R + 1
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨1 + 4 * B, by positivity, ?_⟩
  intro η hη hηone
  let S := closedBall q R
  let f : S → PiLp 2 (fun _ : Fin 1 => ℝ) := fun x => lineEmbedding (x.val : ℝ)
  have hn (x : S) : ‖f x‖ ≤ B := by
    change ‖lineEmbedding (x.val : ℝ)‖ ≤ B
    rw [lineEmbedding_norm, abs_of_nonneg (show 0 ≤ (x.val : ℝ) from x.val.property)]
    have hx := x.property
    change |(x.val : ℝ) - 1| ≤ R at hx
    have h := (le_abs_self ((x.val : ℝ) - 1)).trans hx
    dsimp [B]
    linarith
  have hl (x y : S) : (1 : ℝ) * dist x y ≤ dist (f x) (f y) := by
    simp [f, lineEmbedding_dist, Subtype.dist_eq]
  have hp (A : Finset (Ici (0 : ℝ))) (hA : (A : Set (Ici (0 : ℝ))) ⊆ S)
      (hsep : (A : Set (Ici (0 : ℝ))).Pairwise (fun x y => η ≤ dist x y)) :
      A.card ≤ ⌊1 + 4 * B / η⌋₊ := by
    have hc := card_le_of_bounded_lower_dist_map (m := 1) (by norm_num) hB.le
      (K := 1) (by norm_num) hη hn hl A hA hsep
    simp only [Nat.cast_one, Real.sqrt_one, mul_one, one_mul, pow_one] at hc
    exact Nat.le_floor hc
  obtain ⟨F, hcard, hFS, hnet⟩ := exists_finset_net_card_le_of_packing hη ⌊1 + 4 * B / η⌋₊ hp
  refine ⟨F, ?_, fun x hx => hFS hx, fun x hx => ?_⟩
  · rw [Real.rpow_neg_one]
    change (F.card : ℝ) ≤ (1 + 4 * B) / η
    calc
      (F.card : ℝ) ≤ (⌊1 + 4 * B / η⌋₊ : ℝ) := by exact_mod_cast hcard
      _ ≤ 1 + 4 * B / η := Nat.floor_le (by positivity)
      _ ≤ (1 + 4 * B) / η := by
        apply (le_div_iff₀ hη).mpr
        rw [add_mul, one_mul, div_mul_cancel₀ _ hη.ne']
        linarith
  · obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩

example :
    (∃ L : ℝ, 0 < L ∧ ∃ F : Ici (0 : ℝ) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Icc (0 : ℝ) L),
      ((F ⟨1, by norm_num⟩).snd : ℝ) = 1) ∨
    (∃ F : Ici (0 : ℝ) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Ici (0 : ℝ)),
      ((F ⟨1, by norm_num⟩).snd : ℝ) = 1) := by
  let : CompleteSpace (Ici (0 : ℝ)) := isClosed_Ici.completeSpace_coe
  let : Nontrivial (Ici (0 : ℝ)) := ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
    intro h; have hh := congrArg (fun z : Ici (0 : ℝ) => (z : ℝ)) h; norm_num at hh⟩⟩
  let e : Ici (0 : ℝ) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Ici (0 : ℝ)) :=
    (IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin 0)) (Ici (0 : ℝ))).symm
  have hconv := GC.MetricGeometry.PointedGHConverges.const (⟨1, by norm_num⟩ : Ici (0 : ℝ))
  have hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i : ℕ in Filter.atTop, ∃ F : Finset (Ici (0 : ℝ)), (F.card : ℝ) ≤ C * η ^ (-(1 : ℝ)) ∧
          (∀ x ∈ F, dist x (⟨1, by norm_num⟩ : Ici (0 : ℝ)) ≤ R) ∧
          ∀ x : Ici (0 : ℝ), dist x ⟨1, by norm_num⟩ ≤ R → ∃ y ∈ F, dist x y ≤ η := by
    intro R hR
    obtain ⟨C, hC, hnet⟩ := ray_nets R hR
    exact ⟨C, hC, fun η hη hηone => Filter.Eventually.of_forall (fun _ => hnet η hη hηone)⟩
  have h := hconv.exists_interval_or_ray_product_of_factor_endpoint (k := 0) (n := 1)
    (by norm_num) (by norm_num) (by simpa only [Nat.cast_one] using hcover)
    ray_segments (real_comparison.of_isometry isometry_subtype_coe) e ray_endpoint
  have hbase : dist (⟨0, by norm_num⟩ : Ici (0 : ℝ)) (e ⟨1, by norm_num⟩).snd = 1 := by
    change |(0 : ℝ) - 1| = 1
    norm_num
  rcases h with ⟨L, hL, F, hF⟩ | ⟨F, hF⟩
  · exact Or.inl ⟨L, hL, F, (hF ⟨1, by norm_num⟩).2.trans hbase⟩
  · exact Or.inr ⟨F, (hF ⟨1, by norm_num⟩).2.trans hbase⟩

#print axioms IsometryEquiv.exists_interval_or_ray_product_of_factor_endpoint
#print axioms GC.MetricGeometry.PointedGHConverges.exists_interval_or_ray_product_of_factor_endpoint
#print axioms GC.MetricGeometry.PointedGHConverges.exists_interval_or_ray_product_of_factor_half_interval_chart

```
