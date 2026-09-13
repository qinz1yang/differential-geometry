import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Convolution

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure V} [μ.IsAddHaarMeasure]

theorem ContDiffBump.tendstoUniformly_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : V)}
    (hr : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {u : V → F} (hu : UniformContinuous u) :
    TendstoUniformly (fun i => (φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) u l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (half_pos hε)
  filter_upwards [hr.eventually (gt_mem_nhds hδ)] with n hn
  intro x
  have hh : dist (((φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) (u x) ≤ ε / 2 := by
    apply (φ n).dist_normed_convolution_le hu.continuous.aestronglyMeasurable
    intro y hy
    exact (hδu (lt_trans hy hn)).le
  rw [dist_comm]
  exact hh.trans_lt (half_lt_self hε)
