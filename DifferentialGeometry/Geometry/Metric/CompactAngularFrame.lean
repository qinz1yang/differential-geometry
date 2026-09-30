import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Topology Metric

namespace Metric

theorem exists_subsequence_antipodal_orthogonal_frame
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] {ι : Type*} [Finite ι]
    (hdiam : ∀ x y : Y, dist x y ≤ Real.pi)
    (hthree : ∀ x y z : Y, dist x y + dist y z + dist z x ≤ 2 * Real.pi)
    (A : ℕ → (ι × Bool) → Y) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hopp : ∀ᶠ n in atTop, ∀ i, Real.pi - ε n ≤ dist (A n (i, true)) (A n (i, false)))
    (hcross : ∀ᶠ n in atTop, ∀ i j, i ≠ j → ∀ s t,
      Real.pi / 2 - ε n ≤ dist (A n (i, s)) (A n (j, t))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : (ι × Bool) → Y,
      Tendsto (A ∘ φ) atTop (𝓝 v) ∧
      (∀ i, dist (v (i, true)) (v (i, false)) = Real.pi) ∧
      ∀ i j, i ≠ j → ∀ s t, dist (v (i, s)) (v (j, t)) = Real.pi / 2 := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, φ, hφ, hv⟩ := CompactSpace.tendsto_subseq A
  have hlim (i j : ι × Bool) :
      Tendsto (fun n => dist (A (φ n) i) (A (φ n) j)) atTop (𝓝 (dist (v i) (v j))) :=
    (hv.apply_nhds i).dist (hv.apply_nhds j)
  have hop (i : ι) : dist (v (i, true)) (v (i, false)) = Real.pi := by
    apply le_antisymm (hdiam _ _)
    have h := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub (hε.comp hφ.tendsto_atTop))
      (hlim (i, true) (i, false))
      ((hφ.tendsto_atTop.eventually hopp).mono (fun _ hn => hn i))
    simpa only [sub_zero] using h
  have hcr (i j : ι) (hij : i ≠ j) (s t : Bool) :
      Real.pi / 2 ≤ dist (v (i, s)) (v (j, t)) := by
    have h := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub (hε.comp hφ.tendsto_atTop))
      (hlim (i, s) (j, t))
      ((hφ.tendsto_atTop.eventually hcross).mono (fun _ hn => hn i j hij s t))
    simpa only [sub_zero] using h
  refine ⟨φ, hφ, v, hv, hop, ?_⟩
  intro i j hij s t
  apply le_antisymm _ (hcr i j hij s t)
  have h := hthree (v (i, true)) (v (i, false)) (v (j, t))
  rw [hop i, dist_comm (v (j, t)) (v (i, true))] at h
  have hp := hcr i j hij true t
  have hm := hcr i j hij false t
  cases s <;> linarith

end Metric
