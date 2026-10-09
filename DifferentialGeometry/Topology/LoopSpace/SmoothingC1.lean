import DifferentialGeometry.Topology.LoopSpace.SmoothingDerivatives



noncomputable section

open Function ContinuousMap Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

variable {K F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]




theorem smoothPeriodic_uniform_C1_approximation (Γ : C(K, freeLoop F))
    (hΓ : ∀ k, ContDiff ℝ 1 (fun t : ℝ => Γ k (t : loopCircle)))
    (hd : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => Γ p.1 (t : loopCircle)) p.2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ → ∀ k t,
      dist (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t)
        (Γ k (t : loopCircle)) < ε ∧
      dist (deriv (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle))) t)
        (deriv (fun s : ℝ => Γ k (s : loopCircle)) t) < ε := by
  let D : K → freeLoop F := fun k => regularLoopDerivative (id : F → F) contMDiff_id
    ⟨Γ k, (hΓ k).contMDiff⟩
  have hD : Continuous D := continuous_periodicLoop_family hd _
  obtain ⟨a, ha, haΓ⟩ := smoothPeriodic_uniform_approximation Γ.uncurry.continuous hε
  obtain ⟨b, hb, hbD⟩ := smoothPeriodic_uniform_approximation
    (FreeLoop.continuous_family_iff D |>.mp hD) hε
  refine ⟨min a b, lt_min ha hb, fun φ hφ k t => ?_⟩
  refine ⟨haΓ φ (hφ.trans_le (min_le_left _ _)) k t, ?_⟩
  rw [deriv_smoothPeriodic φ (Γ k) (hΓ k)]
  exact hbD φ (hφ.trans_le (min_le_right _ _)) k t

end DifferentialGeometry.Topology
