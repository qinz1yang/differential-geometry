import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Filter Topology

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_closedBall_in_norm_band {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E} (hx : ‖x‖ ∈ Icc a b) :
    ∃ c : E, x ∈ closedBall c ((b - a) / 2) ∧
      closedBall c ((b - a) / 2) ⊆ {y : E | ‖y‖ ∈ Icc a b} := by
  have hnx : 0 < ‖x‖ := lt_of_lt_of_le ha hx.1
  let m := (a + b) / 2
  let r := (b - a) / 2
  let v := ‖x‖⁻¹ • x
  let c := m • v
  have hm : 0 < m := by dsimp [m]; linarith
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (norm_ne_zero_iff.mp hnx.ne')
  have hnormc : ‖c‖ = m := by simp [c, norm_smul, hv, abs_of_pos hm]
  have hrec : ‖x‖ • v = x := by simp [v, smul_smul, hnx.ne']
  refine ⟨c, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    change ‖x - c‖ ≤ r
    have heq : x - c = (‖x‖ - m) • v := by rw [sub_smul, hrec]
    rw [heq, norm_smul, Real.norm_eq_abs, hv, mul_one]
    rw [abs_le]
    constructor <;> dsimp [r, m] <;> linarith [hx.1, hx.2]
  · intro y hy
    have hy' : ‖y - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hu := norm_sub_norm_le y c
    have hl := norm_sub_norm_le c y
    rw [norm_sub_rev c y] at hl
    rw [hnormc] at hu hl
    constructor <;> dsimp [r, m] at * <;> linarith

theorem uniqueDiffOn_norm_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    UniqueDiffOn ℝ {x : E | ‖x‖ ∈ Icc a b} := by
  intro x hx
  obtain ⟨c, hxc, hc⟩ := exists_closedBall_in_norm_band ha hab hx
  have hr : 0 < (b - a) / 2 := by linarith
  have hi : (interior (closedBall c ((b - a) / 2))).Nonempty := by
    refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr)) ball_subset_closedBall
  exact ((uniqueDiffOn_convex (convex_closedBall c ((b - a) / 2)) hi) x hxc).mono hc

theorem isConnected_norm_band (hrank : 1 < Module.rank ℝ E)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IsConnected {x : E | ‖x‖ ∈ Icc a b} := by
  have hprod := (isConnected_sphere hrank (0 : E) (show (0 : ℝ) ≤ 1 from zero_le_one)).prod
    (isConnected_Icc hab)
  have himage : (fun q : E × ℝ ↦ q.2 • q.1) '' (sphere (0 : E) 1 ×ˢ Icc a b) =
      {x : E | ‖x‖ ∈ Icc a b} := by
    ext x
    constructor
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
      have hvn : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
      simpa [norm_smul, hvn, abs_of_pos (lt_of_lt_of_le ha hr.1)] using hr
    · intro hx
      have hnx : 0 < ‖x‖ := lt_of_lt_of_le ha hx.1
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hx⟩, ?_⟩
      · exact mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (norm_ne_zero_iff.mp hnx.ne'))
      · simp [smul_smul, hnx.ne']
  rw [← himage]
  exact hprod.image _ (continuous_snd.smul continuous_fst).continuousOn

end Poincare.Analysis
