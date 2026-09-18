import DifferentialGeometry.Geometry.Metric.ChartGluing

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} {T : Type*}

theorem exists_metric_family_of_compatible_open_covers
    (U : ι → Opens M) (J : ι → Set T) (A : Set T) (hA : A.Nonempty)
    (g : ∀ i, T → SmoothRiemannianMetric I (U i))
    (hcover : ∀ t ∈ A, ∀ x : M, ∃ i, t ∈ J i ∧ x ∈ U i)
    (hcompat : ∀ i j t, t ∈ A → t ∈ J i → t ∈ J j →
      (g i t).restrictOpenOfSubset (inf_le_left : U i ⊓ U j ≤ U i) =
        (g j t).restrictOpenOfSubset (inf_le_right : U i ⊓ U j ≤ U j)) :
    ∃ G : T → SmoothRiemannianMetric I M,
      ∀ i t, t ∈ A → t ∈ J i → (G t).restrictOpen (U i) = g i t := by
  classical
  have hexists (t : A) : ∃ G : SmoothRiemannianMetric I M,
      ∀ i, (t : T) ∈ J i → G.restrictOpen (U i) = g i t := by
    let V (i : {i : ι // (t : T) ∈ J i}) := U i.val
    obtain ⟨G, hG, _⟩ := exists_unique_metric_of_open_cover
      V (fun i => g i.val t) (by
        intro x
        obtain ⟨i, hi, hx⟩ := hcover t t.property x
        exact ⟨⟨i, hi⟩, hx⟩) (by
        intro i j x hi hj v w
        have h := congrArg
          (fun k : SmoothRiemannianMetric I ↥(U i.val ⊓ U j.val) =>
            k.inner ⟨x, hi, hj⟩ v w)
          (hcompat i.val j.val t t.property i.property j.property)
        exact h)
    exact ⟨G, fun i hi => hG ⟨i, hi⟩⟩
  let G : A → SmoothRiemannianMetric I M := fun t => (hexists t).choose
  let base : A := ⟨hA.choose, hA.choose_spec⟩
  refine ⟨fun t => if ht : t ∈ A then G ⟨t, ht⟩ else G base, ?_⟩
  intro i t ht hJ
  dsimp only
  rw [dif_pos ht]
  exact (hexists ⟨t, ht⟩).choose_spec i hJ

end DifferentialGeometry.Geometry.Metric
