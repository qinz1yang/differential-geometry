import DifferentialGeometry.Topology.Morse.SmoothNormalForm
import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment
open DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
open scoped Manifold ContDiff Topology

namespace Poincare.Morse

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [IsManifold I ∞ M]

theorem exists_interior_morse_chart (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (p : M) (hp : I.IsInteriorPoint p) (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y ↦ f ((extChartAt I p).symm y))
      (extChartAt I p p)) = k) :
    ∃ data : MorseChart n k hk (f p) I f,
      data.p = p ∧ 0 ∈ data.χ.source ∧ p ∈ data.χ.target ∧
      Metric.ball (0 : MorseModel n) data.smoothRadius ⊆ data.χ.source ∧
      ContMDiffOn 𝓘(ℝ, MorseModel n) I ∞ data.χ data.χ.source ∧
      ContMDiffOn I 𝓘(ℝ, MorseModel n) ∞ data.χ.symm data.χ.target ∧
      (∀ y ∈ data.χ.source, f (data.χ y) = morseNormalForm hk (f p) y) ∧
      ∀ x ∈ data.χ.target, I.IsInteriorPoint x := by
  obtain ⟨χ, hχsrc, hχ0, hnormal, htarget⟩ :=
    exists_interior_morse_normal_form I f hf p hp k hk hnd hindex
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp χ.open_source 0 hχsrc
  let R := r / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRr : R < r := by dsimp [R]; linarith
  have hclosed (y : MorseModel n) (hy : morseNorm n y ≤ R) : y ∈ χ.source := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (supNorm_le_morseNorm y).trans hy |>.trans_lt hRr
  have hsmall : Metric.ball (0 : MorseModel n) R ⊆ χ.source :=
    (Metric.ball_subset_ball hRr.le).trans hball
  let ε := R ^ 2 / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsqrt : Real.sqrt (2 * ε) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hR.le, ?_⟩
    dsimp [ε]
    nlinarith [sq_nonneg R]
  let data : MorseChart n k hk (f p) I f := {
    p := p
    R := R
    smoothRadius := R
    ε := ε
    χ := χ.toOpenPartialHomeomorph
    map_zero := hχ0
    radius_pos := hR
    smoothRadius_pos := hR
    epsilon_pos := hε
    sqrt_two_epsilon_le_radius := hsqrt
    normalForm_on := fun y hy ↦ hnormal y (hclosed y hy)
    closedBall_subset_source := hclosed
    contMDiffOn := χ.contMDiffOn.mono hsmall
    symm_contMDiffOn := χ.symm.contMDiffOn.mono (fun _ hy ↦ by
      obtain ⟨y, hy, rfl⟩ := hy
      exact χ.map_source (hsmall hy)) }
  refine ⟨data, rfl, hχsrc, ?_, hsmall, χ.contMDiffOn, χ.symm.contMDiffOn, hnormal, htarget⟩
  change p ∈ χ.target
  exact hχ0 ▸ χ.map_source hχsrc

end Poincare.Morse
