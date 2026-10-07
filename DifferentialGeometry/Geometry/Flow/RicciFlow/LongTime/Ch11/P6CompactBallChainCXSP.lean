import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedComponentCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage

set_option autoImplicit false

/-!
# CX-SPINE G11：统一有限步数的实际 compact-stage 球链

先按 S/δ 选 N，再任取 stage、metric、中心和内闭球点。
复用实际 minimizing segment；N 个等长时间子段均留在原 S 闭球，相邻距离≤δ。
不假设整个 stage connected，也不把给定的 segment 或球链作为输入。
-/

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 步数先于全部几何数据的实际内球 chain，端点可以重合。 -/
theorem exists_uniform_compact_ball_chain_CXSP {S δ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p x : P.Carrier),
      x ∈ riemannianClosedBallOf g p S → ∃ points : ℕ → P.Carrier,
        points 0 = p ∧ points N = x ∧
        (∀ k ≤ N, points k ∈ riemannianClosedBallOf g p S) ∧
        ∀ k < N, riemannianEDistOf g (points k) (points (k + 1)) ≤ ENNReal.ofReal δ := by
  let N := Nat.ceil (S / δ) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstepS : S / (N : ℝ) ≤ δ := by
    have hceil := Nat.le_ceil (S / δ)
    have hbound : S / δ ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith
    have hmul := (div_le_iff₀ hδ).mp hbound
    exact (div_le_iff₀ hNr).mpr (by nlinarith)
  refine ⟨N, hN, ?_⟩
  intro P g p x hx
  by_cases hpx : p = x
  · subst x
    refine ⟨fun _ => p, rfl, rfl, ?_, ?_⟩
    · intro k hk
      change riemannianEDistOf g p p ≤ ENNReal.ofReal S
      rw [riemannianEDistOf_self]
      exact bot_le
    · intro k hk
      rw [riemannianEDistOf_self]
      exact bot_le
  have hxopen : x ∈ riemannianBallOf g p (S + 1) :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  obtain ⟨L, γ, hL, -, hstart, hend, -, -, hdist⟩ :=
    exists_seed_segment_of_compact_CXSP g p x hxopen hpx
  have hdistpx : riemannianEDistOf g p x = ENNReal.ofReal L := by
    rw [← hstart, ← hend, hdist 0 ⟨le_rfl, hL⟩ L ⟨hL, le_rfl⟩,
      zero_sub, abs_neg, abs_of_nonneg hL]
  have hLS : L ≤ S := by
    change riemannianEDistOf g p x ≤ ENNReal.ofReal S at hx
    rw [hdistpx] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hS).mp hx
  have hparam (k : ℕ) (hk : k ≤ N) : (k : ℝ) * L / (N : ℝ) ∈ Icc 0 L := by
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ hNr).mpr
    have hkn : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    nlinarith
  let points : ℕ → P.Carrier := fun k => γ ((k : ℝ) * L / (N : ℝ))
  have htimeN : (N : ℝ) * L / (N : ℝ) = L := by field_simp
  refine ⟨points, ?_, ?_, ?_, ?_⟩
  · simpa only [points, Nat.cast_zero, zero_mul, zero_div] using hstart
  · simpa only [points, htimeN] using hend
  · intro k hk
    change riemannianEDistOf g p (γ ((k : ℝ) * L / (N : ℝ))) ≤ ENNReal.ofReal S
    rw [← hstart, hdist 0 ⟨le_rfl, hL⟩ _ (hparam k hk), zero_sub, abs_neg,
      abs_of_nonneg (hparam k hk).1]
    exact ENNReal.ofReal_le_ofReal ((hparam k hk).2.trans hLS)
  · intro k hk
    change riemannianEDistOf g (γ _) (γ _) ≤ ENNReal.ofReal δ
    rw [hdist _ (hparam k hk.le) _ (hparam (k + 1) (Nat.succ_le_of_lt hk))]
    have hdiff : (k : ℝ) * L / (N : ℝ) - ((k + 1 : ℕ) : ℝ) * L / (N : ℝ) =
        -(L / (N : ℝ)) := by push_cast; ring
    rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg hL hNr.le)]
    exact ENNReal.ofReal_le_ofReal
      ((div_le_div_of_nonneg_right hLS hNr.le).trans hstepS)

end GC.LongTime.Ch11
