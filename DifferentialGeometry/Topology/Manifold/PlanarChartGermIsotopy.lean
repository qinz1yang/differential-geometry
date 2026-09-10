import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import DifferentialGeometry.Analysis.ODE.Flow.Planar.PositivePlanarGerm

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

theorem exists_isotopy_realizing_positive_chart_germ
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ F H}
    (e : OpenPartialHomeomorph M ℂ) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ e.symm e.target)
    (f : Diffeomorph I I M M ∞) (x : M) (hx : x ∈ e.source)
    (hex : e x = 0) (hfx : f x = x)
    (hpos : 0 < (fderiv ℝ (fun z ↦ e (f (e.symm z))) 0).toLinearMap.det) :
    ∃ B : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ B q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ (B q.1).symm q.2) ∧
      B 0 = Diffeomorph.refl I M ∞ ∧ (B 1 : M → M) =ᶠ[𝓝 x] f ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ e.source ∧
        ∀ p y, y ∉ K → B p y = y ∧ (B p).symm y = y := by
  have hix : e.symm 0 = x := by rw [← hex]; exact e.left_inv hx
  have hi : ContMDiff 𝓘(ℝ, ℂ) I ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  let g : ℂ → ℂ := fun z ↦ e (f (e.symm z))
  let U : Set ℂ := (fun z ↦ f (e.symm z)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (f.continuous.comp hi.continuous)
  have h0U : (0 : ℂ) ∈ U := by
    change f (e.symm 0) ∈ e.source
    rw [hix, hfx]
    exact hx
  have hg : ContDiffOn ℝ ∞ g U :=
    (he.comp (f.contMDiff.comp hi).contMDiffOn (fun _ hz ↦ hz)).contDiffOn
  have hg0 : g 0 = 0 := by simp only [g, hix, hfx, hex]
  obtain ⟨D, hD, hDi, hD0, hDg, hDfix⟩ :=
    Poincare.Analysis.exists_compact_isotopy_realizing_positive_planar_germ hU h0U hg hg0
      (fderiv ℝ g 0) ((hg.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt
      hpos 1 (by norm_num)
  obtain ⟨B, hB, hBi, hBe, hK, hKs, hBfix⟩ :=
    exists_diffeomorph_extension_of_chart_family e htarget he hei D hD hDi
      (isCompact_closedBall (0 : ℂ) (2 * 1)) hDfix
  refine ⟨B, hB, hBi, ?_, ?_, e.symm '' closedBall 0 (2 * 1), hK, hKs, hBfix⟩
  · apply Diffeomorph.ext
    intro y
    rw [(hBe 0 y).1, hD0]
    change extendChartById e (id : ℂ → ℂ) y = y
    by_cases hy : y ∈ e.source
    · exact (show extendChartById e id y = e.symm (e y) from if_pos hy).trans (e.left_inv hy)
    · exact if_neg hy
  · have hte : Tendsto e (𝓝 x) (𝓝 0) := by
      rw [← hex]
      exact (he.contMDiffAt (e.open_source.mem_nhds hx)).continuousAt
    have hfn : f ⁻¹' e.source ∈ 𝓝 x :=
      (e.open_source.preimage f.continuous).mem_nhds (by simpa only [mem_preimage, hfx] using hx)
    filter_upwards [hDg.comp_tendsto hte, e.open_source.mem_nhds hx, hfn] with y hy hys hyfs
    change D 1 (e y) = e (f (e.symm (e y))) at hy
    rw [e.left_inv hys] at hy
    rw [(hBe 1 y).1]
    have hext : extendChartById e (D 1) y = e.symm (D 1 (e y)) := if_pos hys
    rw [hext, hy, e.left_inv hyfs]

end Poincare.Topology.Manifold
