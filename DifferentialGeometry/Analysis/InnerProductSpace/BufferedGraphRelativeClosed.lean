import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import Mathlib.Topology.LocalAtTarget

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem buffered_graph_isClosed_on_core
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (R : ℝ) (hR : 0 < R) (g : L → Lᗮ) (W : Set H)
    (hg : ContinuousOn g (ball (0 : L) (4 * R)))
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R),
      ∃ t ∈ ball (0 : L) (4 * R), y = o + orthogonalCoordinateSum L (t, g t)) :
    IsClosed {y : ball o R | (y : H) ∈ W} := by
  let t : ball o R → L := fun y => L.orthogonalProjectionOnto ((y : H) - o)
  have ht : Continuous t :=
    L.orthogonalProjectionOnto.continuous.comp (continuous_subtype_val.sub continuous_const)
  have htball (y : ball o R) : t y ∈ ball (0 : L) (4 * R) := by
    rw [mem_ball, dist_zero_right]
    have hp := L.norm_orthogonalProjectionOnto_apply_le ((y : H) - o)
    have hy : ‖(y : H) - o‖ < R := by
      simpa only [mem_ball, dist_eq_norm] using y.property
    change ‖L.orthogonalProjectionOnto ((y : H) - o)‖ < 4 * R
    linarith
  have hgt : Continuous (fun y => g (t y)) := hg.comp_continuous ht htball
  have hq : Continuous (fun y : ball o R =>
      o + orthogonalCoordinateSum L (t y, g (t y))) :=
    ((orthogonalCoordinateSum L).continuous.comp (ht.prodMk hgt)).const_add o
  have heq : {y : ball o R | (y : H) ∈ W} =
      {y : ball o R | (y : H) = o + orthogonalCoordinateSum L (t y, g (t y))} := by
    ext y
    change (y : H) ∈ W ↔
      (y : H) = o + orthogonalCoordinateSum L (t y, g (t y))
    constructor
    · intro hy
      have hy3 : (y : H) ∈ ball o (3 * R) := by
        have hyR : dist (y : H) o < R := y.property
        change dist (y : H) o < 3 * R
        linarith
      obtain ⟨s, _hs, hys⟩ := hsheet y ⟨hy, hy3⟩
      have hprojection : t y = s := by
        have hsub : (y : H) - o = (s : H) + (g s : H) := by
          rw [hys]
          change (o + ((s : H) + (g s : H))) - o = _
          abel
        change L.orthogonalProjectionOnto ((y : H) - o) = s
        rw [hsub, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
          Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g s).property,
          add_zero]
      simpa only [hprojection] using hys
    · intro hy
      change (y : H) = o + orthogonalCoordinateSum L (t y, g (t y)) at hy
      rw [hy]
      exact hgraph (t y) (htball y)
  rw [heq]
  exact isClosed_eq continuous_subtype_val hq

theorem isClosed_buffered_graph_in_core_union
    {ι : Type*} (o : ι → H) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (L : ι → Submodule ℝ H) [∀ i, (L i).HasOrthogonalProjection]
    (g : ∀ i, L i → (L i)ᗮ) (W : Set H)
    (hg : ∀ i, ContinuousOn (g i) (ball (0 : L i) (4 * R i)))
    (hgraph : ∀ i t, t ∈ ball (0 : L i) (4 * R i) →
      o i + orthogonalCoordinateSum (L i) (t, g i t) ∈ W)
    (hsheet : ∀ i y, y ∈ W ∩ ball (o i) (3 * R i) →
      ∃ t ∈ ball (0 : L i) (4 * R i),
        y = o i + orthogonalCoordinateSum (L i) (t, g i t)) :
    IsClosed {y : (⋃ i, ball (o i) (R i)) | (y : H) ∈ W} := by
  let Ω : Set H := ⋃ i, ball (o i) (R i)
  let V : ι → Opens Ω := fun i =>
    ⟨Subtype.val ⁻¹' ball (o i) (R i), isOpen_ball.preimage continuous_subtype_val⟩
  have hcover : IsOpenCover V := by
    refine IsOpenCover.of_sets
      (fun i => isOpen_ball.preimage (continuous_subtype_val : Continuous (Subtype.val : Ω → H))) ?_
    ext y
    simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
    exact mem_iUnion.mp y.property
  apply hcover.isClosed_iff_coe_preimage.mpr
  intro i
  have hc : Continuous (fun y : V i =>
      (⟨(y.val : H), y.property⟩ : ball (o i) (R i))) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact (buffered_graph_isClosed_on_core (L i) (o i) (R i) (hR i)
    (g i) W (hg i) (hgraph i) (hsheet i)).preimage hc

theorem isProperMap_buffered_graph_core_inclusion
    {ι : Type*} (o : ι → H) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (L : ι → Submodule ℝ H) [∀ i, (L i).HasOrthogonalProjection]
    (g : ∀ i, L i → (L i)ᗮ) (W : Set H)
    (hg : ∀ i, ContinuousOn (g i) (ball (0 : L i) (4 * R i)))
    (hgraph : ∀ i t, t ∈ ball (0 : L i) (4 * R i) →
      o i + orthogonalCoordinateSum (L i) (t, g i t) ∈ W)
    (hsheet : ∀ i y, y ∈ W ∩ ball (o i) (3 * R i) →
      ∃ t ∈ ball (0 : L i) (4 * R i),
        y = o i + orthogonalCoordinateSum (L i) (t, g i t)) :
    IsProperMap (Subtype.val :
      {y : (⋃ i, ball (o i) (R i)) | (y : H) ∈ W} → (⋃ i, ball (o i) (R i))) :=
  (isClosed_buffered_graph_in_core_union o R hR L g W hg hgraph hsheet).isProperMap_subtypeVal

end DifferentialGeometry.Analysis
