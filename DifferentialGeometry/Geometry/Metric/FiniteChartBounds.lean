import DifferentialGeometry.Geometry.Metric.SourceCoefficients
import DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



open Set Bundle Manifold DifferentialGeometry
open scoped ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem exists_uniform_metric_chart_bounds
    {ι J : Type*} [Finite ι] [Nonempty ι] [Finite J]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (c : ι → OpenPartialHomeomorph V M)
    (hc : ∀ i, ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (c i).symm (c i).target)
    (K : ι → Set V) (hK : ∀ i, IsCompact (K i)) (hKs : ∀ i, K i ⊆ (c i).source)
    (v : J → V) :
    (∃ m A : ℝ, 0 < m ∧ m ≤ A ∧ ∀ i x, x ∈ K i → ∀ ξ : V,
      m * ‖ξ‖ ^ 2 ≤ g.inner (c i x)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) x ξ) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) x ξ) ∧
      g.inner (c i x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) x ξ)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) x ξ) ≤ A * ‖ξ‖ ^ 2) ∧
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i j l x, x ∈ K i →
      ‖iteratedFDeriv ℝ k (fun y => g.inner (c i y)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) y (v j))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (c i) y (v l))) x‖ ≤ C := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite J
  have hb (i : ι) := exists_compact_source_metric_ellipticity g (c i).open_source
    ((hc i).of_le (by simp)) (hK i) (hKs i) (fun x hx =>
      (show (c i).MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, E) from
        ⟨(hc i).mdifferentiableOn (by simp), (hi i).mdifferentiableOn (by simp)⟩).mfderiv_injective
          (hKs i hx))
  choose m A hm hmA hb using hb
  let m₀ := Finset.univ.inf' Finset.univ_nonempty m
  let A₀ := Finset.univ.sup' Finset.univ_nonempty A
  have hlow (i : ι) : m₀ ≤ m i := Finset.inf'_le _ (Finset.mem_univ i)
  have hupp (i : ι) : A i ≤ A₀ := Finset.le_sup' _ (Finset.mem_univ i)
  constructor
  · refine ⟨m₀, A₀, ?_, ?_, fun i x hx ξ => ?_⟩
    · exact (Finset.lt_inf'_iff _).mpr (fun i _ => hm i)
    · exact (hlow (Classical.arbitrary ι)).trans
        ((hmA _).trans (hupp _))
    · exact ⟨(mul_le_mul_of_nonneg_right (hlow i) (sq_nonneg ‖ξ‖)).trans (hb i x hx ξ).1,
        (hb i x hx ξ).2.trans (mul_le_mul_of_nonneg_right (hupp i) (sq_nonneg ‖ξ‖))⟩
  · intro k
    have hd (i : ι) (j l : J) := exists_bound_iteratedFDeriv_sourceMetricPairing g
      (c i).open_source (hc i) (hK i) (hKs i) (v j) (v l) k
    choose C hC hbound using hd
    refine ⟨∑ i, ∑ j, ∑ l, C i j l, Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => hC i j l))), ?_⟩
    intro i j l x hx
    apply (hbound i j l x hx).trans
    exact (Finset.single_le_sum (fun q _ => hC i j q) (Finset.mem_univ l)).trans
      ((Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun r _ => hC i q r))
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun r _ =>
          Finset.sum_nonneg (fun s _ => hC q r s))) (Finset.mem_univ i)))

end DifferentialGeometry.Geometry
