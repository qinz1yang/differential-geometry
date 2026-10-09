import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidBijective

/-!
# The fold data of the flat compact triangles

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §7, the interface `CompactShape.FoldData` of
`SF/CompactFoldSpec.lean`). For a flat `CompactShape` (`(2,3,6)`, `(2,4,4)`, `(3,3,3)` in any
order) the fold is the core-replaced map `F` of `exists_foldCore` for `toEuclidShape`
(`exists_foldData_flat`):
* `U` is the open set of `exists_foldCore` (the core disc, a neighbourhood of the core circle and
  the part of `goodSet` outside the core, minus `0`);
* the wall neighbourhoods are `wallNbhd i` of `CompactFoldEuclidWalls`, which lie in strips of
  width `cornerShrink` about the walls, hence outside the core, where `F = preFold` and the
  reflection identities `preFold_refl_*` hold (`preFold_refl`);
* `bijOn_f` comes from `bijOn_of_local` with the wall reality derived from these identities, the
  vertex values `F(v₁) = 3/2`, `F(v₂) = -3/2` and the outer germ near `v₃ = 0`;
* all three apex radii are `cornerShrink = ρ/64`, inside the germ discs of `preFold` and at side
  distance less than `cornerShrink` from a wall, hence outside the core.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace EuclidShape

variable (σ : EuclidShape)

def wallNbhd : Fin 3 → Set ℂ
  | 0 => σ.wallNbhdZero
  | 1 => σ.wallNbhdOne
  | 2 => σ.wallNbhdTwo

theorem isOpen_wallNbhd (i : Fin 3) : IsOpen (σ.wallNbhd i) := by
  fin_cases i
  · exact σ.isOpen_wallNbhdZero
  · exact σ.isOpen_wallNbhdOne
  · exact σ.isOpen_wallNbhdTwo

theorem wall_mem_wallNbhd (i : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide i z = 0) : z ∈ σ.wallNbhd i := by
  fin_cases i
  · exact σ.wall_mem_wallNbhdZero hz h0 hw
  · exact σ.wall_mem_wallNbhdOne hz h0 hw
  · exact σ.wall_mem_wallNbhdTwo hz h0 hw

theorem refl_mapsTo_wallNbhd (i : Fin 3) : MapsTo (σ.refl i) (σ.wallNbhd i) (σ.wallNbhd i) := by
  fin_cases i
  · exact σ.refl_mapsTo_wallNbhdZero
  · exact σ.refl_mapsTo_wallNbhdOne
  · exact σ.refl_mapsTo_wallNbhdTwo

theorem preFold_refl (i : Fin 3) {z : ℂ} (hz : z ∈ σ.wallNbhd i) :
    σ.preFold (σ.refl i z) = conj (σ.preFold z) := by
  fin_cases i
  · exact σ.preFold_refl_zero hz
  · exact σ.preFold_refl_one hz
  · exact σ.preFold_refl_two hz

theorem coreRadius_lt_of_strip {i : Fin 3} {z : ℂ} (h : |σ.wallSide i z| < σ.cornerShrink) :
    σ.coreRadius < ‖z - σ.incenter‖ := by
  have hm : 0 < σ.coreMargin := σ.core_consts.1
  have : σ.coreRadius + σ.coreMargin < ‖z - σ.incenter‖ := by
    fin_cases i
    · exact σ.core_lt_of_strip_zero h
    · exact σ.core_lt_of_strip_one h
    · exact σ.core_lt_of_strip_two h
  linarith

theorem far_of_wallNbhd (i : Fin 3) {z : ℂ} (hz : z ∈ σ.wallNbhd i) :
    z ≠ 0 ∧ z ∈ σ.goodSet ∧ σ.coreRadius < ‖z - σ.incenter‖ := by
  fin_cases i
  · obtain ⟨⟨a1, a2, a3, -⟩, -⟩ := hz
    refine ⟨fun h0 => ?_, a3, σ.coreRadius_lt_of_strip (i := 0) a1⟩
    rw [h0, norm_zero, zero_re, add_zero] at a2
    exact lt_irrefl _ a2
  · obtain ⟨⟨a1, a2, a3, -⟩, -⟩ := hz
    refine ⟨fun h0 => ?_, a3, σ.coreRadius_lt_of_strip (i := 1) a1⟩
    rw [h0, norm_zero, zero_re, add_zero] at a2
    exact lt_irrefl _ a2
  · obtain ⟨⟨a1, a3, -⟩, -⟩ := hz
    refine ⟨fun h0 => ?_, a3, σ.coreRadius_lt_of_strip (i := 2) a1⟩
    have := σ.norm_of_strip_two a1
    rw [h0, norm_zero] at this
    linarith [σ.params.2.2.2.2.2.2.1]

theorem strip_of_near (i : Fin 3) {z v : ℂ} (hv : σ.wallSide i v = 0)
    (h : ‖z - v‖ < σ.cornerShrink) : |σ.wallSide i z| < σ.cornerShrink := by
  have := σ.abs_wallSide_sub_le i z v
  rw [hv, sub_zero] at this
  linarith

theorem cornerShrink_lt_germRadius : σ.cornerShrink < σ.germRadius := by
  unfold cornerShrink germRadius
  linarith [σ.inradius_pos]

theorem cornerShrink_lt_outerGermRadius : σ.cornerShrink < σ.outerGermRadius := by
  unfold cornerShrink outerGermRadius
  linarith [σ.inradius_pos]

theorem cornerShrink_lt_half : σ.cornerShrink < 1 / 2 := by
  have := σ.inradius_lt_half
  have := σ.inradius_pos
  unfold cornerShrink
  linarith

theorem ne_zero_of_near_vertexOne {z : ℂ} (h : ‖z - σ.vertexOne‖ < σ.cornerShrink) : z ≠ 0 := by
  rintro rfl
  rw [zero_sub, norm_neg, σ.norm_vertexOne] at h
  linarith [σ.half_le_sin_θ₂, σ.cornerShrink_lt_half]

theorem ne_zero_of_near_vertexTwo {z : ℂ} (h : ‖z - σ.vertexTwo‖ < σ.cornerShrink) : z ≠ 0 := by
  rintro rfl
  rw [zero_sub, norm_neg, σ.norm_vertexTwo] at h
  linarith [σ.half_le_sin_θ₁, σ.cornerShrink_lt_half]

end EuclidShape

namespace CompactShape

theorem exists_foldData_flat (σ : CompactShape) (h : σ.curv = .flat) : Nonempty σ.FoldData := by
  set τ := σ.toEuclidShape h with hτ
  obtain ⟨F, U, hUo, h0U, hTU, hUmem, hF, hdet, hagree, hinj, hmaps⟩ := τ.exists_foldCore
  have hfar : ∀ z, τ.coreRadius < ‖z - τ.incenter‖ → F z = τ.preFold z := fun z hz =>
    hagree z hz.le
  have hstripU : ∀ (i : Fin 3) (z : ℂ), z ≠ 0 → z ∈ τ.goodSet →
      |τ.wallSide i z| < τ.cornerShrink → z ∈ U ∧ F z = τ.preFold z := by
    intro i z hz0 hg hs
    have hc := τ.coreRadius_lt_of_strip hs
    exact ⟨hUmem z hz0 hg hc, hfar z hc⟩
  have hgood : ∀ i (z : ℂ), z ∈ τ.wallNbhd i → z ∈ U ∧ F z = τ.preFold z := by
    intro i z hz
    obtain ⟨hz0, hg, hc⟩ := τ.far_of_wallNbhd i hz
    exact ⟨hUmem z hz0 hg hc, hfar z hc⟩
  have hreal : ∀ i, ∀ z ∈ τ.triangle, z ≠ 0 → τ.wallSide i z = 0 → (F z).im = 0 := by
    intro i z hz hz0 hw
    have hV := τ.wall_mem_wallNbhd i hz hz0 hw
    have e := τ.preFold_refl i hV
    rw [τ.refl_of_wallSide_eq_zero hw, ← (hgood i z hV).2] at e
    exact Complex.conj_eq_iff_im.1 e.symm
  have hv1 : F τ.vertexOne = 3 / 2 := by
    have hs := τ.strip_of_near 2 τ.wallSide_two_vertexOne
      (by rw [sub_self, norm_zero]; exact τ.cornerShrink_pos)
    rw [hfar _ (τ.coreRadius_lt_of_strip hs), τ.preFold_eq_apexOne (by
      change ‖_ - _‖ < _
      rw [sub_self, norm_zero]
      exact τ.params.2.2.2.2.2.2.2.2.2.2.2.2.1), EuclidShape.apexOne, τ.rotOne_vertexOne,
      zero_pow (by have := τ.two_le_p₁; omega)]
    norm_num
  have hv2 : F τ.vertexTwo = -(3 / 2) := by
    have hs := τ.strip_of_near 2 τ.wallSide_two_vertexTwo
      (by rw [sub_self, norm_zero]; exact τ.cornerShrink_pos)
    rw [hfar _ (τ.coreRadius_lt_of_strip hs), τ.preFold_eq_apexTwo (by
      change ‖_ - _‖ < _
      rw [sub_self, norm_zero]
      exact τ.params.2.2.2.2.2.2.2.2.2.2.2.2.1), EuclidShape.apexTwo, τ.rotTwo_vertexTwo,
      zero_pow (by have := τ.two_le_p₂; omega)]
    norm_num
  have houter : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < τ.cornerShrink →
      z ∈ U ∧ F z = compactOuterGerm σ.p₃ z := by
    intro z hz0 hz
    have hpo : z ∈ τ.pieceOuter := ⟨hz0, hz.trans τ.cornerShrink_lt_outerGermRadius⟩
    have hs := τ.strip_of_near 0 τ.wallSide_zero_zero (by rwa [sub_zero])
    obtain ⟨hU, hFz⟩ := hstripU 0 z (norm_pos_iff.1 hz0)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hpo))))))) hs
    exact ⟨hU, hFz.trans (τ.preFold_eq_outer hpo)⟩
  have hbij := EuclidShape.bijOn_of_local hUo hTU hF (fun z hz h1 h2 => (hdet z hz h1 h2).ne')
    hreal hinj hmaps hv1 hv2 τ.cornerShrink_pos fun z hz0 hz => (houter z hz0 hz).2
  rw [← triangle_flat h] at hTU hinj hmaps hbij
  refine ⟨{
    U := U
    f := F
    isOpen_U := hUo
    U_subset_plane := by rw [plane_flat h]; exact subset_univ U
    zero_not_mem_U := h0U
    triangle_diff_subset_U := hTU
    contDiffOn_f := hF
    det_fderiv_pos := fun z hz h1 h2 => by
      rw [vertexOne_flat h] at h1
      rw [vertexTwo_flat h] at h2
      exact hdet z hz h1 h2
    V := τ.wallNbhd
    isOpen_V := τ.isOpen_wallNbhd
    V_subset_U := fun i z hz => (hgood i z hz).1
    V_subset_reflChart := fun i => by rw [reflChart_flat h]; exact subset_univ _
    foldWall_diff_subset_V := fun i z hz => by
      rw [foldWall_flat h] at hz
      exact τ.wall_mem_wallNbhd i hz.1.1 hz.2 hz.1.2
    refl_mapsTo_V := fun i z hz => by
      rw [refl_flat h]
      exact τ.refl_mapsTo_wallNbhd i hz
    f_refl := fun i z hz => by
      rw [refl_flat h, (hgood i _ (τ.refl_mapsTo_wallNbhd i hz)).2, (hgood i z hz).2]
      exact τ.preFold_refl i hz
    bijOn_f := hbij
    apexRadius := fun _ => τ.cornerShrink
    apexRadius_pos := fun _ => τ.cornerShrink_pos
    f_apexOne := fun z hz => by
      rw [apexDisc_flat h, vertexOne_flat h] at hz
      change ‖z - τ.vertexOne‖ < τ.cornerShrink at hz
      have hpa : z ∈ τ.pieceApexOne := hz.trans τ.cornerShrink_lt_germRadius
      obtain ⟨hU, hFz⟩ := hstripU 2 z (τ.ne_zero_of_near_vertexOne hz)
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hpa))))))))
        (τ.strip_of_near 2 τ.wallSide_two_vertexOne hz)
      refine ⟨hU, ?_⟩
      rw [hFz, τ.preFold_eq_apexOne hpa, EuclidShape.apexOne, rotOne_flat h]
      rfl
    f_apexTwo := fun z hz => by
      rw [apexDisc_flat h, vertexTwo_flat h] at hz
      change ‖z - τ.vertexTwo‖ < τ.cornerShrink at hz
      have hpa : z ∈ τ.pieceApexTwo := hz.trans τ.cornerShrink_lt_germRadius
      obtain ⟨hU, hFz⟩ := hstripU 2 z (τ.ne_zero_of_near_vertexTwo hz)
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hpa))))))))
        (τ.strip_of_near 2 τ.wallSide_two_vertexTwo hz)
      refine ⟨hU, ?_⟩
      rw [hFz, τ.preFold_eq_apexTwo hpa, EuclidShape.apexTwo, rotTwo_flat h]
      rfl
    f_outer := fun z hz0 hz => houter z hz0 hz }⟩

end CompactShape

theorem EuclidShape.nonempty_foldData (σ : EuclidShape) : Nonempty σ.toCompactShape.FoldData :=
  σ.toCompactShape.exists_foldData_flat σ.toCompactShape_curv

end GC.Seifert
