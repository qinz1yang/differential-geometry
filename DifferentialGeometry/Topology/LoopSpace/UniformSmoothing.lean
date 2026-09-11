import DifferentialGeometry.Topology.LoopSpace.Basic
import DifferentialGeometry.Analysis.Calculus.Periodic.SmoothingFamilies
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.HeineCantor









noncomputable section

open ContinuousMap Function Metric Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

variable {K F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem loopFamily_uniform_parameter_modulus {f : K × loopCircle → F}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k (x y : ℝ), dist x y < δ →
      dist (f (k, (x : loopCircle))) (f (k, (y : loopCircle))) < ε := by
  let A : C(loopCircle, C(K, F)) := (⟨f ∘ Prod.swap, hf.comp continuous_swap⟩ :
    C(loopCircle × K, F)).curry
  have hA : UniformContinuous A := CompactSpace.uniformContinuous_of_continuous A.continuous
  have hq : UniformContinuous (fun t : ℝ => (t : loopCircle)) :=
    (AddSubgroup.zmultiples (1 : ℝ)).normedMk.uniformContinuous
  obtain ⟨δ, hδ, hδA⟩ := Metric.uniformContinuous_iff.mp (hA.comp hq) ε hε
  refine ⟨δ, hδ, fun k x y hxy => ?_⟩
  exact (ContinuousMap.dist_apply_le_dist k).trans_lt (hδA hxy)

variable [CompleteSpace F]



theorem smoothPeriodic_uniform_approximation {f : K × loopCircle → F}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∀ k t, dist (DifferentialGeometry.Analysis.smoothPeriodic φ
        (fun s : ℝ => f (k, (s : loopCircle))) t) (f (k, (t : loopCircle))) < ε := by
  obtain ⟨δ, hδ, hmod⟩ := loopFamily_uniform_parameter_modulus hf (half_pos hε)
  refine ⟨δ, hδ, fun φ hφ k t => ?_⟩
  have hfc : Continuous (fun s : ℝ => f (k, (s : loopCircle))) :=
    hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' (1 : ℝ)))
  apply lt_of_le_of_lt (DifferentialGeometry.Analysis.dist_smoothPeriodic_le φ hfc ?_) (half_lt_self hε)
  intro s hs
  exact (hmod k s t (hs.trans hφ)).le

end DifferentialGeometry.Topology
