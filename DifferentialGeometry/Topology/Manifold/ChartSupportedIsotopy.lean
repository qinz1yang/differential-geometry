import DifferentialGeometry.Topology.Manifold.ChartSupportedDiffeomorph
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.CompactPlanarIsotopy

noncomputable section
open Set Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ F H}

theorem exists_isotopy_of_support_in_planar_chart
    (e : OpenPartialHomeomorph M ℂ) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ e.symm e.target)
    (f : Diffeomorph I I M M ∞) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hfix : ∀ x, x ∉ K → f x = x) :
    ∃ J : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl I M ∞ ∧
      ∃ C : Set M, IsCompact C ∧ C ⊆ e.source ∧
        ∀ p x, x ∉ C → J p x = x ∧ (J p).symm x = x := by
  obtain ⟨g, _, _, hgsupport, hgf⟩ :=
    exists_compactly_supported_chart_representative e htarget he hei f hK hKs hfix
  obtain ⟨D, hD, hDi, hD0, hD1, L, hL, hDfix⟩ :=
    exists_compactly_supported_planar_isotopy g hgsupport
  obtain ⟨J, hJ, hJi, hJe, hJL, hJLs, hJfix⟩ :=
    exists_diffeomorph_extension_of_chart_family e htarget he hei D hD hDi hL hDfix
  refine ⟨J, hJ, hJi, ?_, ?_, e.symm '' L, hJL, hJLs, hJfix⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hD0]
    by_cases hx : x ∈ e.source
    · exact (show extendChartById e g x = e.symm (g (e x)) from if_pos hx).trans (hgf x hx)
    · exact (show extendChartById e g x = x from if_neg hx).trans
        (hfix x (fun hk ↦ hx (hKs hk))).symm
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 1 x).1, hD1]
    change extendChartById e (id : ℂ → ℂ) x = x
    by_cases hx : x ∈ e.source
    · exact (show extendChartById e id x = e.symm (e x) from if_pos hx).trans (e.left_inv hx)
    · exact if_neg hx

end Poincare.Topology.Manifold
