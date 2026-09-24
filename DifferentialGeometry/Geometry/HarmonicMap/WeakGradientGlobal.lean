import DifferentialGeometry.Geometry.HarmonicMap.WeakGradientBound
import Mathlib.Topology.Compactness.Lindelof

noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {ι : Type*} [Fintype ι]

theorem exists_weak_gradient_norm_sq_le_pullback_metric
    (g : SmoothRiemannianMetric I M) {Φ : M → EuclideanSpace ℝ ι}
    (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ ι) ∞ Φ)
    {r : EuclideanSpace ℝ ι → M} {U : Set (EuclideanSpace ℝ ι)}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ ι) I ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))),
      IsOpen Ω → ∀ (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
        (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω),
      (∀ᵐ x ∂volume.restrict Ω, f x ∈ range Φ) →
      ∀ᵐ x ∂volume.restrict Ω, ∀ j : Fin d,
        ‖(WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ ι)‖ ^ 2 ≤
          (C : ℝ) ^ 2 * pullbackMetricCoefficients g r (f x)
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_weak_gradient_norm_sq_le_pullback_metric_on_ball
    g hΦ hU hr hΦU hleft
  refine ⟨C, hC, ?_⟩
  intro d Ω hΩ f hf hfK
  have hball : ∀ x : Ω, ∃ a : ℝ, 0 < a ∧
      Metric.closedBall (x : EuclideanSpace ℝ (Fin d)) a ⊆ Ω := by
    intro x
    obtain ⟨a, ha, haΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds x.property)
    exact ⟨a / 2, half_pos ha,
      (Metric.closedBall_subset_ball (half_lt_self ha)).trans haΩ⟩
  choose a ha haΩ using hball
  let V : Ω → Set (EuclideanSpace ℝ (Fin d)) := fun x => Metric.ball x (a x)
  have hV : ∀ x, IsOpen (V x) := fun _ => Metric.isOpen_ball
  have hcover : Ω ⊆ ⋃ x : Ω, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (ha ⟨x, hx⟩)⟩
  obtain ⟨T, hT, hTcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover V hV hcover
  apply ae_all_iff.mpr
  intro j
  have hlocal : ∀ x : Ω, ∀ᵐ y ∂volume.restrict (V x),
      ‖(WithLp.toLp 2 (fun i => (hf i).weakGrad y j) : EuclideanSpace ℝ ι)‖ ^ 2 ≤
        (C : ℝ) ^ 2 * pullbackMetricCoefficients g r (f y)
          (WithLp.toLp 2 (fun i => (hf i).weakGrad y j))
          (WithLp.toLp 2 (fun i => (hf i).weakGrad y j)) :=
    fun x => hbound d Ω hΩ f hf hfK x (a x) (haΩ x) j
  exact ae_restrict_of_ae_restrict_of_subset hTcover
    ((ae_restrict_biUnion_iff V hT _).mpr fun x _ => hlocal x)

end DifferentialGeometry.Geometry

end
