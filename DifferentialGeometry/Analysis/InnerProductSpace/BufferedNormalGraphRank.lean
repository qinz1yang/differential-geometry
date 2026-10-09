import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphDerivative
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphMapRank

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finrank_range_fderiv_nearest_map_eq
    (L : Submodule ℝ H) [FiniteDimensional ℝ L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (W : Set H) (P : H → H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ 2 g (ball (0 : L) (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R),
      ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R),
      ∃ t ∈ ball (0 : L) (4 * R), y = o + orthogonalCoordinateSum L (t, g t))
    (hnearest : ∀ y ∈ ball o R,
      P y ∈ W ∧ IsMinOn (fun w => dist y w) W (P y))
    (z : H) (hz : z ∈ ball o R) (hP : DifferentiableAt ℝ P z) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ P z).toLinearMap) =
      Module.finrank ℝ L := by
  let T : H → L := fun y => L.orthogonalProjectionOnto (P y - o)
  have hrepresentation (y : H) (hy : y ∈ ball o R) :
      T y ∈ ball (0 : L) (4 * R) ∧
        P y = o + orthogonalCoordinateSum L (T y, g (T y)) := by
    obtain ⟨_, _, t, ht, heq⟩ := minimizer_mem_buffered_normal_graph L o g W R a hR ha
      hvalue hgraph hsheet y (P y) hy (hnearest y hy).1 (hnearest y hy).2
    have htT : T y = t := by
      have hsub : P y - o = (t : H) + (g t : H) := by
        rw [heq]
        change (o + ((t : H) + (g t : H))) - o = _
        abel
      change L.orthogonalProjectionOnto (P y - o) = t
      rw [hsub, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property,
        add_zero]
    have ht4 : t ∈ ball (0 : L) (4 * R) := by
      have hh : dist t 0 < 5 * R / 2 := ht
      change dist t 0 < 4 * R
      linarith
    exact ⟨htT.symm ▸ ht4, by simpa only [htT] using heq⟩
  have hT : DifferentiableAt ℝ T z :=
    L.orthogonalProjectionOnto.differentiableAt.comp z (hP.sub_const o)
  have hgT : DifferentiableAt ℝ g (T z) :=
    (hg.contDiffAt (isOpen_ball.mem_nhds (hrepresentation z hz).1)).differentiableAt
      (by norm_num)
  have hevent : P =ᶠ[𝓝 z]
      (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (hrepresentation y hy).2
  have hderiv := hevent.fderiv_eq (𝕜 := ℝ)
  have hbound := norm_fderiv_nearest_map_sub_starProjection_le L o g W P R a
    hR ha hg hvalue hfirst hsecond hgraph hsheet hnearest z hz hP
  have hclose : ‖fderiv ℝ P z - L.starProjection‖ < 1 :=
    hbound.trans_lt (by linarith)
  have hgraphclose :
      ‖fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z -
        L.starProjection‖ < 1 := by
    rw [← hderiv]
    exact hclose
  rw [hderiv]
  exact finrank_range_fderiv_normal_graph_map_eq L o g T z hgT hT hgraphclose

end DifferentialGeometry.Analysis
