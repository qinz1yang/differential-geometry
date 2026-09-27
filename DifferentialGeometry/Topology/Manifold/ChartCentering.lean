import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_chart_centered
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H}
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (x : M) (hx : x ∈ e.source) :
    ∃ c : OpenPartialHomeomorph M E, c.source = e.source ∧ c.target = univ ∧
      c x = 0 ∧ c.symm 0 = x ∧
      ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target := by
  let c := e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph
  have hs : c.source = e.source := by simp [c]
  have ht : c.target = univ := by simp [c, htarget]
  have hc : c x = 0 := by change e x - e x = 0; exact sub_self _
  have hci : c.symm 0 = x := by rw [← hc]; exact c.left_inv (hs ▸ hx)
  refine ⟨c, hs, ht, hc, hci, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ e.source := hs ▸ hy
    exact ((contDiff_id.sub contDiff_const).contMDiff.contMDiffAt.comp y
      (he.contMDiffAt (e.open_source.mem_nhds hy'))).contMDiffWithinAt
  · intro z _
    have hi : ContMDiff 𝓘(ℝ, E) I ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
    exact (hi.contMDiffAt.comp z
      (contDiff_id.add contDiff_const).contMDiff.contMDiffAt).contMDiffWithinAt

end DifferentialGeometry.Topology.Manifold
