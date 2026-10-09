import DifferentialGeometry.Topology.Manifold.UniformChartCover
import DifferentialGeometry.Geometry.Metric.FiniteChartBounds
import DifferentialGeometry.Geometry.Metric.AffineChartCoefficients








open Set Bundle Manifold DifferentialGeometry
open scoped ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]





theorem exists_uniform_metric_charts {J : Type*} [Finite J]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : V ≃L[ℝ] E) (R : ℝ) (v : J → V) :
    ∃ m A : ℝ, 0 < m ∧ m ≤ A ∧ ∃ ψ : M → OpenPartialHomeomorph V M,
      (∀ p, Metric.closedBall (0 : V) R ⊆ (ψ p).source ∧ ψ p 0 = p ∧
        ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (ψ p) (ψ p).source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (ψ p).symm (ψ p).target ∧
        ∀ x ∈ Metric.closedBall (0 : V) R, ∀ ξ : V,
          m * ‖ξ‖ ^ 2 ≤ g.inner (ψ p x)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) x ξ) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) x ξ) ∧
          g.inner (ψ p x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) x ξ)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) x ξ) ≤ A * ‖ξ‖ ^ 2) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p i j x, x ∈ Metric.closedBall (0 : V) R →
        ‖iteratedFDeriv ℝ k (fun y => g.inner (ψ p y)
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) y (v i))
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ p) y (v j))) x‖ ≤ C := by
  classical
  obtain ⟨t, htn, c, K, hc, j, b, hb⟩ := exists_finite_translated_chart_cover (M := M) e R
  obtain ⟨q, hq⟩ := htn
  let : Nonempty t := ⟨⟨q, hq⟩⟩
  obtain ⟨⟨m, A, hm, hmA, hbounds⟩, hderiv⟩ := exists_uniform_metric_chart_bounds g c
    (fun i => (hc i).1) (fun i => (hc i).2.1) K
    (fun i => (hc i).2.2.1) (fun i => (hc i).2.2.2) v
  let ψ : M → OpenPartialHomeomorph V M := fun p =>
    affineChart (c (j p)) (b p) (ContinuousLinearEquiv.refl ℝ V)
  have hsource (p : M) (x : V) (hx : x ∈ Metric.closedBall (0 : V) R) :
      b p + x ∈ (c (j p)).source := (hc (j p)).2.2.2 ((hb p).2 hx)
  refine ⟨m, A, hm, hmA, ψ, ?_, ?_⟩
  · intro p
    have hs := contMDiffOn_affineChart (hc (j p)).1 (hc (j p)).2.1 (b p)
      (ContinuousLinearEquiv.refl ℝ V)
    refine ⟨?_, ?_, hs.1, hs.2, ?_⟩
    · intro x hx
      simpa [ψ] using hsource p x hx
    · simpa [ψ] using (hb p).1
    · intro x hx ξ
      have hd := (((hc (j p)).1 _ (hsource p x hx)).contMDiffAt
        ((c (j p)).open_source.mem_nhds (hsource p x hx))).mdifferentiableAt (by simp)
      have h := hbounds (j p) (b p + x) ((hb p).2 hx) ξ
      dsimp only [ψ]
      erw [affineChart_mfderiv (b p) (ContinuousLinearEquiv.refl ℝ V) hd ξ]
      exact h
  · intro k
    obtain ⟨C, hC, hbound⟩ := hderiv k
    refine ⟨C, hC, fun p i l x hx => ?_⟩
    have hd := iteratedFDeriv_affineChart_metricPairing g (hc (j p)).1 (b p)
      (ContinuousLinearEquiv.refl ℝ V) (hsource p x hx) (v i) (v l) k
    have hid (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
        B.compContinuousLinearMap (fun _ =>
          (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V)) = B := by
      ext z
      rfl
    rw [hid] at hd
    exact (congrArg norm hd).le.trans (hbound (j p) i l (b p + x) ((hb p).2 hx))

end DifferentialGeometry.Geometry
