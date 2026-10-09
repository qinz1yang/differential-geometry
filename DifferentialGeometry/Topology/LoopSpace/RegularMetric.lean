import DifferentialGeometry.Topology.LoopSpace.Regular



noncomputable section

open Function ContinuousMap Set Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



def regularLoopDist (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ η : regularLoop E M) : ℝ :=
  dist (regularLoopValue e he γ) (regularLoopValue e he η) +
    dist (regularLoopDerivative e he γ) (regularLoopDerivative e he η)

theorem regularLoopDist_nonneg (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ η : regularLoop E M) : 0 ≤ regularLoopDist e he γ η := add_nonneg dist_nonneg dist_nonneg

@[simp] theorem regularLoopDist_self (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ : regularLoop E M) : regularLoopDist e he γ γ = 0 := by simp [regularLoopDist]

theorem regularLoopDist_comm (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ η : regularLoop E M) : regularLoopDist e he γ η = regularLoopDist e he η γ := by
  simp only [regularLoopDist, dist_comm]

theorem regularLoopDist_triangle (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ η ζ : regularLoop E M) :
    regularLoopDist e he γ ζ ≤ regularLoopDist e he γ η + regularLoopDist e he η ζ := by
  have h₀ := dist_triangle (regularLoopValue e he γ) (regularLoopValue e he η) (regularLoopValue e he ζ)
  have h₁ := dist_triangle (regularLoopDerivative e he γ) (regularLoopDerivative e he η)
    (regularLoopDerivative e he ζ)
  dsimp only [regularLoopDist]
  linarith

theorem regularLoopDist_eq_zero_iff (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hi : Injective e) (γ η : regularLoop E M) :
    regularLoopDist e he γ η = 0 ↔ γ = η := by
  constructor
  · intro h
    have hv : regularLoopValue e he γ = regularLoopValue e he η := by
      apply dist_eq_zero.mp
      have hn := @dist_nonneg (freeLoop F) _ (regularLoopDerivative e he γ) (regularLoopDerivative e he η)
      have hn₀ := @dist_nonneg (freeLoop F) _ (regularLoopValue e he γ) (regularLoopValue e he η)
      dsimp only [regularLoopDist] at h
      linarith
    apply Subtype.ext
    apply ContinuousMap.ext
    intro θ
    exact hi (congrArg (fun f : freeLoop F => f θ) hv)
  · rintro rfl
    exact regularLoopDist_self e he γ




theorem regularLoopTopology_isOpen_iff (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (s : Set (regularLoop E M)) :
    @IsOpen _ (regularLoopTopology e he) s ↔
      ∀ γ ∈ s, ∃ ε > 0, ∀ η, regularLoopDist e he γ η < ε → η ∈ s := by
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he
  let : PseudoMetricSpace (regularLoop E M) := PseudoMetricSpace.induced (regularLoopJet e he) inferInstance
  have hmax (γ η : regularLoop E M) : dist γ η ≤ regularLoopDist e he γ η := by
    change max _ _ ≤ _ + _
    exact max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg)
  have hsum (γ η : regularLoop E M) : regularLoopDist e he γ η ≤ 2 * dist γ η := by
    change _ + _ ≤ 2 * max _ _
    have h₀ := le_max_left (dist (regularLoopValue e he γ) (regularLoopValue e he η))
      (dist (regularLoopDerivative e he γ) (regularLoopDerivative e he η))
    have h₁ := le_max_right (dist (regularLoopValue e he γ) (regularLoopValue e he η))
      (dist (regularLoopDerivative e he γ) (regularLoopDerivative e he η))
    dsimp only [regularLoopJet]
    linarith
  change IsOpen s ↔ _
  rw [Metric.isOpen_iff]
  constructor
  · intro h γ hγ
    obtain ⟨ε, hε, hball⟩ := h γ hγ
    refine ⟨ε, hε, fun η hη => hball ?_⟩
    rw [Metric.mem_ball, dist_comm]
    exact (hmax γ η).trans_lt hη
  · intro h γ hγ
    obtain ⟨ε, hε, hball⟩ := h γ hγ
    refine ⟨ε / 2, half_pos hε, fun η hη => hball η ?_⟩
    rw [Metric.mem_ball, dist_comm] at hη
    exact (hsum γ η).trans_lt (by linarith)

end DifferentialGeometry.Topology
