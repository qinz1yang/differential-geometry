import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphBijective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphInjective

/-!
# The fold data of the spherical compact triangles

Lane CF-S3, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §7, the interface `CompactShape.FoldData` of
`SF/CompactFoldSpec.lean`). For a spherical `CompactShape` (`(2,2,n)`, `(2,3,3)`, `(2,3,4)`,
`(2,3,5)` in any order) the fold is the core-replaced map `F` of `exists_sphFoldCore_bijOn` for
`sphPreFold`, with the good set and cover of `CompactFoldSphGood`, `CompactFoldSphCover` and the
injectivity `injOn_sphPreFold` (`exists_foldData_spherical`); `nonempty_foldData_of_sphCore`
assembles the fields from the conclusions of the core replacement:
* `U` is the open set of the core replacement (the core disc, a neighbourhood of the core circle
  and the part of the good set outside the core, minus `0`);
* the wall neighbourhoods are `sphWallNbhd G' sphPreFoldParams i` of `CompactFoldSphWalls` for
  the open set `G'` of points of the good set outside the closed core disc, where `F = sphPreFold`
  and the reflection identities `sphPreFold_refl` hold; the walls lie outside the core with its
  margin (`sphCore_add_le_of_wall`), hence in `G'`;
* the apex radii come from continuity: near each vertex the points lie outside the closed core
  disc and in the germ piece of that vertex (`exists_sphApexRadius`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

omit hs in
theorem sphMoebInv_near {a : ℂ} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, 1 + conj a * z ≠ 0 → ‖sphMoeb a z‖ < δ → ‖z - a‖ < ε := by
  have hc : ContinuousAt (sphMoebInv a) 0 :=
    (continuousAt_id.add continuousAt_const).div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (by simp)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hc ε hε
  refine ⟨δ, hδ, fun z hz hq => ?_⟩
  have h := hδε (x := sphMoeb a z) (by rwa [dist_zero_right])
  rw [sphMoebInv_sphMoeb hz, dist_eq_norm] at h
  have e : sphMoebInv a 0 = a := by simp [sphMoebInv]
  rwa [e] at h

theorem chartOne_of_apexDisc {z : ℂ} {ρ : ℝ} (hz : z ∈ σ.apexDisc σ.vertexOne ρ) :
    1 + conj σ.vertexOne * z ≠ 0 ∧ ‖σ.rotOne z‖ < ρ := by
  obtain ⟨h1, h2⟩ := hz
  rw [eps_sph hs] at h1
  refine ⟨by convert h1 using 1; push_cast; ring, ?_⟩
  rwa [norm_rotOne_sph hs, ← disc_sph hs]

theorem chartTwo_of_apexDisc {z : ℂ} {ρ : ℝ} (hz : z ∈ σ.apexDisc σ.vertexTwo ρ) :
    1 + conj σ.vertexTwo * z ≠ 0 ∧ ‖σ.rotTwo z‖ < ρ := by
  obtain ⟨h1, h2⟩ := hz
  rw [eps_sph hs] at h1
  refine ⟨by convert h1 using 1; push_cast; ring, ?_⟩
  rwa [norm_rotTwo_sph hs, ← disc_sph hs]

theorem exists_sphApexRadius :
    ∃ ρ > 0, ρ ≤ σ.sphGermRadius ∧ ρ ≤ σ.sphOuterGermRadius ∧
      (∀ z, 1 + conj σ.vertexOne * z ≠ 0 → ‖σ.rotOne z‖ < ρ →
        z ≠ 0 ∧ σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖) ∧
      (∀ z, 1 + conj σ.vertexTwo * z ≠ 0 → ‖σ.rotTwo z‖ < ρ →
        z ∈ σ.sphPieceApexTwo ∧ z ≠ 0 ∧ σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖) ∧
      (∀ z, 0 < ‖z‖ → ‖z‖ < ρ →
        z ∈ σ.sphPieceOuter ∧ σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖) := by
  set c := σ.sphCoreCenter
  set r := σ.sphCoreRadius
  have hm := sphCoreMargin_pos hs
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, hgc2, -, -, hc1τ, hc2τ, hg3τ, -, -⟩ := sphLayout_ineqs hs
  have hfar : ∀ i, ∀ v ∈ σ.triangle, σ.wallSide i v = 0 → r < ‖σ.rotTwo v - c‖ := by
    intro i v hv hw
    have := sphCore_add_le_of_wall hs hv hw
    linarith
  have hfo := isOpen_rotTwo_far_sph hs c r
  have O1 : IsOpen ({z : ℂ | z ≠ 0} ∩ {z | r < ‖σ.rotTwo z - c‖}) := isOpen_ne.inter hfo
  have m1 : σ.vertexOne ∈ {z : ℂ | z ≠ 0} ∩ {z | r < ‖σ.rotTwo z - c‖} := by
    refine ⟨?_, hfar 1 _ (vertexOne_mem_triangle_sph hs) wallSide_one_vertexOne_sph⟩
    intro h0
    have := wallSide_zero_vertexOne_pos_sph hs
    rw [h0, wallSide_zero_zero_sph] at this
    exact lt_irrefl 0 this
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 O1 _ m1
  obtain ⟨δ₁, hδ₁, hn₁⟩ := sphMoebInv_near (a := σ.vertexOne) hε₁
  have hv2A := vertexTwo_mem_sphPieceApexTwo hs
  set O2 : Set ℂ := σ.sphPieceApexTwo ∩ ({z : ℂ | z ≠ 0} ∩ {z | r < ‖σ.rotTwo z - c‖})
  have O2o : IsOpen O2 := (isOpen_sphPieceApexTwo hs).inter O1
  have m2 : σ.vertexTwo ∈ O2 := by
    refine ⟨hv2A, ?_, hfar 0 _ (vertexTwo_mem_triangle_sph hs) wallSide_zero_vertexTwo_sph⟩
    intro h0
    have := wallSide_one_vertexTwo_pos_sph hs
    rw [h0, wallSide_one_zero_sph] at this
    exact lt_irrefl 0 this
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.1 O2o _ m2
  obtain ⟨δ₂, hδ₂, hn₂⟩ := sphMoebInv_near (a := σ.vertexTwo) hε₂
  set O3 : Set ℂ := {z | 1 + conj σ.vertexOne * z ≠ 0 ∧ σ.sphGermRadius < ‖σ.rotOne z‖ ∧
    1 + σ.vertexTwo * z ≠ 0 ∧ σ.sphGermRadius < ‖σ.rotTwo z‖} ∩ {z | r < ‖σ.rotTwo z - c‖}
  have O3o : IsOpen O3 := by
    refine IsOpen.inter (isOpen_iff_mem_nhds.2 fun z hz => ?_) hfo
    obtain ⟨a1, a2, a3, a4⟩ := hz
    filter_upwards [ev_chartOne_sph a1, EuclidShape.ev_lt (continuousAt_normRotOne_sph hs a1) a2,
      ev_chartTwo_sph a3, EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs a3) a4] with
      u c1 c2 c3 c4
    exact ⟨c1, c2, c3, c4⟩
  have m3 : (0 : ℂ) ∈ O3 := by
    have g0 : σ.sphGermRadius < σ.sphTau 0 := by linarith
    have g1 : σ.sphGermRadius < σ.sphTau 1 := by linarith
    have t2 := sphTau_pos hs 2
    have h0T := zero_mem_triangle_sph hs
    obtain ⟨p1, p2⟩ := sphDist_gt_of_outer hs h0T (by rw [norm_zero]; exact t2)
    refine ⟨⟨by simp, by linarith, by simp, by linarith⟩,
      hfar 0 _ h0T (wallSide_zero_zero_sph)⟩
  obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.isOpen_iff.1 O3o _ m3
  refine ⟨min (min δ₁ δ₂) (min ε₃ (min σ.sphGermRadius σ.sphOuterGermRadius)), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact lt_min (lt_min hδ₁ hδ₂) (lt_min hε₃ (lt_min hg hg3))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  · intro z hz hq
    have hq' : ‖sphMoeb σ.vertexOne z‖ < δ₁ := by
      rw [← norm_rotOne_sph hs]
      exact hq.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hmem := hb₁ (mem_ball_iff_norm.2 (hn₁ z hz hq'))
    exact ⟨hmem.1, hmem.2⟩
  · intro z hz hq
    have hq' : ‖sphMoeb σ.vertexTwo z‖ < δ₂ := by
      rw [← norm_rotTwo_sph hs]
      exact hq.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hmem := hb₂ (mem_ball_iff_norm.2 (hn₂ z hz hq'))
    exact ⟨hmem.1, hmem.2.1, hmem.2.2⟩
  · intro z hz0 hz
    have hz3 : ‖z‖ < ε₃ := hz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hzg : ‖z‖ < σ.sphOuterGermRadius :=
      hz.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hmem := hb₃ (mem_ball_zero_iff.2 hz3)
    obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := hmem
    exact ⟨⟨hz0, hzg, a1, a2, a3, a4⟩, a5⟩

theorem nonempty_foldData_of_sphCore {F : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (h0U : (0 : ℂ) ∉ U) (hTU : σ.triangle \ {0} ⊆ U)
    (hUmem : ∀ z, z ≠ 0 → z ∈ σ.sphGoodSet →
      σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖ → z ∈ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det)
    (hagree : ∀ z, σ.sphCoreRadius ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → F z = σ.sphPreFold z)
    (hbij : BijOn F (σ.triangle \ {0}) basePlusSeven) : Nonempty σ.FoldData := by
  set c := σ.sphCoreCenter
  set r := σ.sphCoreRadius
  have hm := sphCoreMargin_pos hs
  set G' : Set ℂ := σ.sphGoodSet ∩ {z | r < ‖σ.rotTwo z - c‖} with hG'
  have hG'o : IsOpen G' := (isOpen_sphGoodSet hs).inter (isOpen_rotTwo_far_sph hs c r)
  set V : Fin 3 → Set ℂ := fun i => σ.sphWallNbhd G' σ.sphPreFoldParams i with hV
  have hgood : ∀ i, ∀ z ∈ V i, z ∈ U ∧ F z = σ.sphPreFold z := by
    intro i z hz
    have hz' := sphWallNbhd_subset G' σ.sphPreFoldParams i hz
    exact ⟨hUmem z (ne_zero_of_mem_sphPreFoldNbhd hs hz) hz'.1 hz'.2, hagree z hz'.2.le⟩
  obtain ⟨ρ, hρ, hρg, hρg3, hA1, hA2, hA3⟩ := exists_sphApexRadius hs
  refine ⟨{
    U := U
    f := F
    isOpen_U := hUo
    U_subset_plane := by rw [plane_sph hs]; exact subset_univ U
    zero_not_mem_U := h0U
    triangle_diff_subset_U := hTU
    contDiffOn_f := hF
    det_fderiv_pos := hdet
    V := V
    isOpen_V := fun i => isOpen_sphWallNbhd hs hG'o σ.sphPreFoldParams i
    V_subset_U := fun i z hz => (hgood i z hz).1
    V_subset_reflChart := fun i => sphWallNbhd_subset_reflChart G' σ.sphPreFoldParams i
    foldWall_diff_subset_V := fun i z hz => by
      obtain ⟨⟨hT, hw⟩, h0⟩ := hz
      have h0' : z ≠ 0 := h0
      have hfar := sphCore_add_le_of_wall hs hT hw
      exact wall_mem_sphPreFoldNbhd hs i hT h0' hw
        ⟨wall_mem_sphGoodSet hs i hT h0' hw, by change r < _; linarith⟩
    refl_mapsTo_V := fun i => refl_mapsTo_sphWallNbhd hs G' σ.sphPreFoldParams i
    f_refl := fun i z hz => by
      rw [(hgood i _ (refl_mapsTo_sphWallNbhd hs G' σ.sphPreFoldParams i hz)).2,
        (hgood i z hz).2]
      exact sphPreFold_refl hs i hz
    bijOn_f := hbij
    apexRadius := fun _ => ρ
    apexRadius_pos := fun _ => hρ
    f_apexOne := fun z hz => by
      obtain ⟨hv1, hq⟩ := chartOne_of_apexDisc hs hz
      obtain ⟨hz0, hfar⟩ := hA1 z hv1 hq
      have hp : z ∈ σ.sphPieceApexOne := ⟨hv1, hq.trans_le hρg⟩
      have hg : z ∈ σ.sphGoodSet :=
        Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hp)))))))
      refine ⟨hUmem z hz0 hg hfar, ?_⟩
      rw [hagree z hfar.le, sphPreFold_eq_apexOne hp, sphApexOne]
    f_apexTwo := fun z hz => by
      obtain ⟨hv2, hq⟩ := chartTwo_of_apexDisc hs hz
      obtain ⟨hp, hz0, hfar⟩ := hA2 z hv2 hq
      have hg : z ∈ σ.sphGoodSet :=
        Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))
      refine ⟨hUmem z hz0 hg hfar, ?_⟩
      rw [hagree z hfar.le, sphPreFold_eq_apexTwo hp, sphApexTwo]
    f_outer := fun z hz0 hz => by
      obtain ⟨hp, hfar⟩ := hA3 z hz0 hz
      have hg : z ∈ σ.sphGoodSet :=
        Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
      exact ⟨hUmem z (norm_pos_iff.1 hz0) hg hfar,
        (hagree z hfar.le).trans (sphPreFold_eq_outer hp)⟩ }⟩

end Spherical

theorem exists_foldData_spherical (σ : CompactShape) (hs : σ.curv = .spherical) :
    Nonempty σ.FoldData := by
  obtain ⟨F, U, hUo, h0U, hTU, hUmem, hF, hdet, hagree, -, -, hbij⟩ :=
    exists_sphFoldCore_bijOn hs (isOpen_sphGoodSet hs)
      (fun z hz => contDiffAt_sphPreFold_of_good hs hz)
      (fun z hz h1 h2 => (sphGood_sphPreFold hs hz h1 h2).2)
      (fun z hz h0 hc => mem_sphGoodSet hs hz h0 hc) (fun ζ hζ => sphCore_hin hs hζ)
      (injOn_sphPreFold hs)
  exact nonempty_foldData_of_sphCore hs hUo h0U hTU hUmem hF hdet hagree hbij

end CompactShape

end GC.Seifert
