import DifferentialGeometry.Topology.LoopSpace.FiniteRegular



noncomputable section

open Function ContinuousMap Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

set_option backward.isDefEq.respectTransparency false in


theorem finiteRegularLoopTopology_one (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) :
    finiteRegularLoopTopology e he 1 =
      regularLoopTopology e (he.of_le (by exact_mod_cast le_top)) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  have hzero (γ : finiteRegularLoop 1 E M) : finiteLoopJet e he 1 γ 0 = regularLoopValue e he₁ γ := by
    apply ContinuousMap.ext
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rfl
  have hone (γ : finiteRegularLoop 1 E M) : finiteLoopJet e he 1 γ 1 = regularLoopDerivative e he₁ γ := by
    apply ContinuousMap.ext
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change iteratedDeriv 1 (fun s : ℝ => e (γ.val (s : loopCircle))) t = _
    rw [iteratedDeriv_one]
    rfl
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    let : TopologicalSpace (finiteRegularLoop 1 E M) := finiteRegularLoopTopology e he 1
    have h : Continuous[finiteRegularLoopTopology e he 1, inferInstance] (finiteLoopJet e he 1) := continuous_induced_dom
    apply continuous_induced_rng.mpr
    change Continuous (fun γ : finiteRegularLoop 1 E M => (regularLoopValue e he₁ γ, regularLoopDerivative e he₁ γ))
    simp_rw [← hzero, ← hone]
    exact ((continuous_apply 0).comp h).prodMk ((continuous_apply 1).comp h)
  · apply continuous_id_iff_le.mp
    let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
    have h : Continuous[regularLoopTopology e he₁, inferInstance] (regularLoopJet e he₁) := continuous_induced_dom
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    fin_cases i
    · exact h.fst.congr (fun γ => (hzero γ).symm)
    · exact h.snd.congr (fun γ => (hone γ).symm)

end DifferentialGeometry.Topology
