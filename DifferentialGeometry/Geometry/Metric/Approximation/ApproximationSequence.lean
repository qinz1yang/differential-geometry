import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open Filter
open scoped Topology

namespace GC.MetricGeometry

theorem PointedGHConverges.exists_approximation_sequence
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)] {Y : Type*} [MetricSpace Y]
    {p : ∀ i, X i} {q : Y} (h : PointedGHConverges p q) :
    ∃ (φ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono φ ∧ Tendsto R atTop atTop ∧
      Tendsto ε atTop (𝓝 0) ∧ Nonempty (∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i)) := by
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  let e : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hepos (i : ℕ) : 0 < e i := by
    dsimp [e]
    positivity
  have her (i : ℕ) : e i < r i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [e, r]
    linarith
  have hezero : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  obtain ⟨β, hβ, hf⟩ := extraction_forall_of_eventually
    (fun i => h.eventually_approx (hepos i) (her i))
  exact ⟨β, r, e, hβ, hr, hezero, ⟨fun i => Classical.choice (hf i)⟩⟩

end GC.MetricGeometry
