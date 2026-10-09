import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfP6ObsC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12SuppliesNonempty_C11S

set_option autoImplicit false

/-!
# O-CH11-ASM (G4 consumer)：观察层参数前提的非空真

常值链 `p n := sampleParameters_C11S`（δ = 1/(2(t+1))，ρ = 1/(t+1)）同时满足 G4 主定理
`exists_surgery_with_decaying_accuracy_of_P6_obs_C11A` 的六个参数级前提
`hstatic / hcompat / hδanti / hρanti / hδsmall / hscale`——这些前提彼此相容、不空真。
flow 级前提（`hwin / hobs / hlev`、S8）没有平凡 flow 可实例化（同 SKEL G3 的说明）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set

namespace GC.LongTime.Ch11

/-- 常值样本链满足 G4 的六个参数级前提。 -/
theorem sampleChain_obs_params_C11A :
    let p : ℕ → CutoffParameters := fun _ => sampleParameters_C11S
    (∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant) ∧
    (∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t) ∧
    (∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ))) ∧
    (∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ))) ∧
    (∀ η : ℝ, 0 < η → ∃ n : ℕ, (p n).delta n < η) ∧
    (∀ (n : ℕ) (u : ℝ), 0 ≤ u → 2 * u ≤ (n : ℝ) →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (u + 1)) := by
  intro p
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩,
    fun n => sampleParameters_delta_antitone_C11S.mono fun t ht => ht.1,
    fun n => sampleParameters_radiusAntitone_C11S.mono fun t ht => ht.1,
    fun η hη => ?_, fun n u hu _ => ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
    refine ⟨n, ?_⟩
    change 1 / (2 * ((n : ℝ) + 1)) < η
    rw [one_div_lt (by positivity) hη]
    linarith
  · change (1 / (2 * (u + 1))) ^ 2 * (1 / (u + 1)) < 1 / (2 * u + 1) / (u + 1)
    have hu1 : 0 < u + 1 := by linarith
    have hkey : (1 / (2 * (u + 1))) ^ 2 * (1 / (u + 1)) = 1 / (4 * (u + 1) ^ 3) := by
      field_simp
      ring
    rw [hkey, div_div]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [sq_nonneg u, mul_pos hu1 hu1]

end GC.LongTime.Ch11
