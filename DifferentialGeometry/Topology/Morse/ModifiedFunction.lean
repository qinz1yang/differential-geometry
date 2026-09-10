import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment
open DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

namespace Poincare.Morse

variable {n k : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [T2Space M]

theorem contMDiff_morseModifiedFunction (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2)
    (hRpos : 0 < R) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (χ : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = morseNormalForm hk c y)
    (hsource : ∀ y, morseNorm n y ≤ R → y ∈ χ.source) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (morseModifiedFunction hk c ε δ R χ.toOpenPartialHomeomorph f) := by
  classical
  let g := morseModifiedFunction hk c ε δ R χ.toOpenPartialHomeomorph f
  have hon (x : M) (hx : x ∈ χ.target) :
      g x = modifiedNormalForm hk c ε δ (χ.symm x) := by
    change (if x ∈ χ.target then
      if morseNorm n (χ.symm x) ≤ R then modifiedNormalForm hk c ε δ (χ.symm x)
      else f x else f x) = _
    rw [if_pos hx]
    split_ifs with hb
    · rfl
    · have hgt : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n (χ.symm x) ^ 2 := by
        have hnorm : R < morseNorm n (χ.symm x) := lt_of_not_ge hb
        nlinarith
      rw [modifiedNormalForm_eq_of_modulation_zero hk c ε δ
        (modMu_mul_modGamma_eq_zero_of_norm_gt hk ε δ hε hδ hgt)]
      have hn := hnormal (χ.symm x) (χ.map_target hx)
      have he : χ.toPartialEquiv (χ.symm.toPartialEquiv x) = x := χ.right_inv hx
      rw [he] at hn
      exact hn
  have hcompact : IsCompact {y : MorseModel n | morseNorm n y ≤ R} := by
    cases n with
    | zero => exact (Set.toFinite _).isCompact
    | succ m => exact isCompact_morseCollarClosedBall m R
  have hclosed : IsClosed (χ '' {y | morseNorm n y ≤ R}) :=
    (hcompact.image_of_continuousOn (χ.toOpenPartialHomeomorph.continuousOn_toFun.mono
      hsource)).isClosed
  intro x
  by_cases hx : x ∈ χ.target
  · have hs := (contDiff_modifiedNormalForm hk c ε δ hδ).contMDiff.contMDiffAt.comp x
      (χ.symm.contMDiffOn.contMDiffAt (χ.open_target.mem_nhds hx))
    apply hs.congr_of_eventuallyEq
    filter_upwards [χ.open_target.mem_nhds hx] with y hy
    exact hon y hy
  · have hxout : x ∉ χ '' {y | morseNorm n y ≤ R} := by
      rintro ⟨y, hy, rfl⟩
      exact hx (χ.map_source (hsource y hy))
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [hclosed.isOpen_compl.mem_nhds hxout] with y hy
    change g y = f y
    change (if y ∈ χ.target then
      if morseNorm n (χ.symm y) ≤ R then modifiedNormalForm hk c ε δ (χ.symm y)
      else f y else f y) = f y
    split_ifs with hyt hball
    · exact False.elim (hy ⟨χ.symm y, hball, χ.right_inv hyt⟩)
    · rfl
    · rfl

end Poincare.Morse
