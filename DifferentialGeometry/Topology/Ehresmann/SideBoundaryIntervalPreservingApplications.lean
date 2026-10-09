import DifferentialGeometry.Topology.Ehresmann.SideBoundaryIntervalPreserving

/-!
# Consumer of the side-function-preserving trivialization: the rims are slices

`exists_sideBoundary_interval_trivialization_rim`: for the trivialization of
`exists_sideBoundary_interval_trivialization_preserving`, the rim `{P = t, B = 0}` of every level
`t ∈ (a₀, b₀)` is exactly the slice `Θ (∂F₀ × {t})`, `∂F₀ = {B = 0}` (the side boundary is
carried to itself level by level, not only as a set).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

open DifferentialGeometry.Manifold.RegularLevel

/-- **Consumer.** The rims of the levels are the slices of the boundary of the fibre. -/
theorem exists_sideBoundary_interval_trivialization_rim {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ ℝ)
    {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B) {a b : ℝ}
    (hreg : ∀ y, P y ∈ Ioo a b → 0 ≤ B y → Surjective (mfderiv I 𝓘(ℝ, ℝ) P y))
    (hregb : ∀ y, P y ∈ Ioo a b → B y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y}))
    {a₀ b₀ : ℝ} (ha₀ : a < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < b) :
    letI := regularSublevelChartedSpace (Ψ := P) (B := B) hdim hP hB
      (fun y hy hBy => hreg y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
      (fun y hy hBy => hregb y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
    let Q : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
    ∃ Θ : {y : Y // P y = 0 ∧ 0 ≤ B y} × Q → Y,
      ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ Θ ∧ (∀ p, P (Θ p) = p.2) ∧
      (∀ p, B p.1 = 0 → B (Θ p) = 0) ∧
      ∀ (t : Q) (y : Y), P y = t → B y = 0 →
        ∃ x : {y : Y // P y = 0 ∧ 0 ≤ B y}, B x = 0 ∧ Θ (x, t) = y := by
  let _ := regularSublevelChartedSpace (Ψ := P) (B := B) hdim hP hB
    (fun y hy hBy => hreg y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
    (fun y hy hBy => hregb y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
  obtain ⟨Θ, hΘs, hΘP, -, -, ⟨r', hr', hΘB, U, hU, D, -, hD0, hDtr, hΘD, -, hDB⟩, -, -, -, R, -,
      hR⟩ := exists_sideBoundary_interval_trivialization_preserving hdim hP hB hreg hregb hprop
    ha₀ h0 hb₀
  refine ⟨Θ, hΘs, fun p => (hΘP p).1, fun p hp => ?_, fun t y hyt hy0 => ?_⟩
  · rw [hΘB p (by rw [hp]; exact hr'), hp]
  · have hyI : P y ∈ Ioo a₀ b₀ := by rw [hyt]; exact t.2
    obtain ⟨hRy, hΘR⟩ := hR y hyI hy0.ge
    set x : {y : Y // P y = 0 ∧ 0 ≤ B y} := ⟨R y, hRy⟩ with hxdef
    have ht' : (⟨P y, hyI⟩ : (⟨Ioo a₀ b₀, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ)) = t :=
      Subtype.ext hyt
    rw [ht'] at hΘR
    refine ⟨x, ?_, hΘR⟩
    obtain ⟨hxU, hΘx⟩ := hΘD (x, t)
    have hDapp : ∀ (s s' : ℝ) (z : (⟨U, hU⟩ : TopologicalSpace.Opens Y)),
        D s' (D s z) = D (s + s') z := fun s s' z =>
      congrArg (fun F : (⟨U, hU⟩ : TopologicalSpace.Opens Y) ≃ₘ⟮I, I⟯
        (⟨U, hU⟩ : TopologicalSpace.Opens Y) => F z) (hDtr s s')
    set yU : (⟨U, hU⟩ : TopologicalSpace.Opens Y) := D (t : ℝ) ⟨x, hxU⟩ with hyUdef
    have hyU : (yU : Y) = y := by rw [hyUdef, ← hΘx, hΘR]
    have hback : D (-(t : ℝ)) yU = ⟨x, hxU⟩ := by
      rw [hyUdef, hDapp, add_neg_cancel, hD0]
      rfl
    have hB0 : |B yU| < r' := by rw [hyU, hy0, abs_zero]; exact hr'
    have h := hDB yU (-(t : ℝ)) hB0
    rw [hback, hyU, hy0] at h
    exact h

end DifferentialGeometry.Topology.Ehresmann
