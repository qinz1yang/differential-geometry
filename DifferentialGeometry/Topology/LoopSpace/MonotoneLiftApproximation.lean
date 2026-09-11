import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Analysis.Calculus.Periodic.MonotoneLiftApproximation
import DifferentialGeometry.Topology.Homeomorph.AffinePeriodic



noncomputable section

open Function
open scoped ContDiff NNReal

namespace DifferentialGeometry.Topology




theorem exists_affineCircleHomeomorph_approximation {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hm : Monotone ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ ≃ₜ ℝ) (hpF : ∀ t, F (t + 1) = F t + 1) (K L : ℝ≥0),
      ContDiff ℝ ∞ F ∧ StrictMono F ∧
      LipschitzWith K (affineCircleHomeomorph F hpF) ∧
      LipschitzWith L (affineCircleHomeomorph F hpF).symm ∧
      (∀ θ, dist (affineCircleHomeomorph F hpF θ) (affineCircleMap ψ hc hp θ) < ε) := by
  obtain ⟨f, τ, K, hfc, hfp, hτ, hl, hK, herr⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_affinePeriodic_approximation hc hm hp hε
  obtain ⟨F, L, hF, hL⟩ := DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope
    hfc.continuous hfp hτ hl
  have heq : (F : ℝ → ℝ) = f := funext hF
  have hpF (t : ℝ) : F (t + 1) = F t + 1 := by simpa only [hF] using hfp t
  have hFc : ContDiff ℝ ∞ F := heq.symm ▸ hfc
  have hFK : LipschitzWith K F := heq.symm ▸ hK
  obtain ⟨hCK, hCL⟩ := affineCircleHomeomorph_lipschitz F hpF hFK hL
  refine ⟨F, hpF, K, L, hFc, ?_, hCK, hCL, ?_⟩
  · intro x y hxy
    have h := hl x y hxy.le
    have hpos := mul_pos hτ (sub_pos.mpr hxy)
    rw [hF, hF]
    linarith
  · intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change dist (F t : loopCircle) (ψ t : loopCircle) < ε
    have h := loopCircle_projection_lipschitz.dist_le_mul (F t) (ψ t)
    simp only [NNReal.coe_one, one_mul] at h
    exact h.trans_lt (by simpa only [hF] using herr t)

end DifferentialGeometry.Topology
