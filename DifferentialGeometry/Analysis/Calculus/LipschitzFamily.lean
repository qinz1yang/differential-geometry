import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.NormNum

open scoped Topology NNReal

namespace ContDiff

theorem eventually_lipschitzWith_sub_slice
    {P V F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : P × V → F} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (p₀ : P) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, LipschitzWith ε (fun y => G (p, y) - G (p₀, y)) := by
  let H : P × V → F := fun q => G q - G (p₀, q.2)
  have hH : ContDiff ℝ 1 H :=
    hG.sub (hG.comp (contDiff_const.prodMk contDiff_snd))
  let D : P × V → V →L[ℝ] F := fun q => fderiv ℝ (fun y => H (q.1, y)) q.2
  have hD : Continuous D :=
    Continuous.fderiv (hH.comp (contDiff_fst.fst.prodMk contDiff_snd))
      continuous_snd le_rfl
  have hD₀ (y : V) : D (p₀, y) = 0 := by
    simp [D, H]
  let S : Set V := Prod.snd '' tsupport G
  have hS : IsCompact S := hGc.image continuous_snd
  have hzero (p : P) {y : V} (hy : y ∉ S) : G (p, y) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hpy => hy ⟨(p, y), hpy, rfl⟩)
  have hDoff (p : P) {y : V} (hy : y ∉ S) : D (p, y) = 0 := by
    have hloc : (fun z => H (p, z)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hy] with z hz
      change G (p, z) - G (p₀, z) = 0
      rw [hzero p hz, hzero p₀ hz, sub_self]
    change fderiv ℝ (fun z => H (p, z)) y = 0
    rw [hloc.fderiv_eq, fderiv_zero, Pi.zero_apply]
  have hbound : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ S, ‖D (p, y)‖₊ < ε := by
    apply hS.eventually_forall_of_forall_eventually
    intro y hy
    exact (isOpen_lt hD.nnnorm continuous_const).mem_nhds (by simpa [hD₀] using hε)
  filter_upwards [hbound] with p hp
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num))
  intro y
  change ‖D (p, y)‖₊ ≤ ε
  by_cases hy : y ∈ S
  · exact (hp y hy).le
  · rw [hDoff p hy, nnnorm_zero]
    exact zero_le

end ContDiff
