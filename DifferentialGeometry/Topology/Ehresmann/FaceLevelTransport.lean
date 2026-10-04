import DifferentialGeometry.Topology.Ehresmann.FaceTransportProducer

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y]

/-- Level-only transversality yields a uniform band and an ambient transport of the WHOLE level. -/
theorem exists_ambient_levelTransport_and_band_margin
    (h : Y × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) (a : F)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → y ∈ Q) :
    ∃ ε > 0,
      (∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Q, ‖h (y, τ) - a‖ < ε →
        Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y)) ∧
      ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y,
        (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
        Ψ '' {y | h (y, 0) = a} = {y | h (y, 1) = a} := by
  obtain ⟨ε, hε, hmargin⟩ := exists_band_margin_of_level_surjective h hh a hreg hQ
  have hpair : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → |(0 : ℝ) - 1| < 1 / 2 →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), (0 : ℝ))) y) := by
    intro _τ _hτ _y _hy hfalse
    norm_num at hfalse
  obtain ⟨Ψ, hsupp, himage, _hboundary⟩ := exists_diffeomorph_face_of_compact_transport
    h (fun _x => 0) hh contMDiff_const a 1 (by norm_num : (0 : ℝ) < 1 / 2)
    (fun τ hτ y hy _hT => hreg τ hτ y hy) hpair hQ
    (fun τ hτ y hy _hT => hloc τ hτ y hy)
  refine ⟨ε, hε, hmargin, Ψ, hsupp, ?_⟩
  simpa only [zero_le_one, and_true] using himage

end DifferentialGeometry.Topology.Ehresmann
