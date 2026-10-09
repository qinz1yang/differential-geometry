import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimQuadrantProducer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPieces
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMapApplications

/-!
# FC42 packet H3a, part 1: the common defining function near and off the rims

`ρ = circ.roundedFunction` (lane ASM-TOR: `rounding ∘ proj` on the open `circ.domain`) is the common
defining function of the rounded circle region `{x ∈ domain | ρ x ≤ 0}`; the ball–handle side of the
rounding is the CLOSED COMPLEMENT `roundedComplement = {x ∉ domain ∨ 0 ≤ ρ x}` of the open rounded
region (review 42 §3.1: the sign is `< 0` for the removed set). This file proves, for any
`DecompositionCertificate`:

* in a rim chart `ρ (rimChart h b p) = -(λ ψ_std p.2)` (`roundedFunction_rimChart`);
* off the closed unit boxes of all rim charts (`rimCore`, closed) `ρ ≤ 0` is the cornered circle
  region (`rounding_le_zero_iff_of_not_mem_rimCore`; rim whole-fibre saturation = the tree's
  `roundingSupport_handleCorner`);
* `ρ < 0` only in the interior of the circle region (`mem_interior_region_of_roundedFunction_neg`),
  hence vertex and handle points satisfy `ρ ≥ 0` (`nonneg_roundedFunction_of_mem_vertex_image`,
  `nonneg_roundedFunction_of_mem_handle`; density + `circ_vertex_disjoint`/`circ_handle_disjoint`);
* regularity in the usable form: near a zero of `ρ` there are points with `ρ > 0`
  (`exists_pos_roundedFunction_of_mem_nhds`; the submersion neighbourhood theorem of the tree, X99,
  for `rounding` and the open map `proj`). The defining function is used only on the open domain
  (review 40 §4.6: no global use of a function that is constant off `domain`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsR_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothR_ASMCYC3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The closed unit square. -/
def rimClosedBox : Set (ℝ × ℝ) := {v | |v.1| ≤ 1 ∧ |v.2| ≤ 1}

theorem rimBox_one_subset_rimClosedBox : rimBox 1 ⊆ rimClosedBox :=
  fun _ hv => ⟨hv.1.le, hv.2.le⟩

theorem rimClosedBox_subset_rimBox_two : rimClosedBox ⊆ rimBox 2 :=
  fun _ hv => ⟨hv.1.trans_lt (by norm_num), hv.2.trans_lt (by norm_num)⟩

theorem isCompact_rimClosedBox : IsCompact rimClosedBox := by
  have he : rimClosedBox = Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    ext v
    simp only [rimClosedBox, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq, abs_le]
  rw [he]
  exact isCompact_Icc.prod isCompact_Icc

namespace CircleRegion

variable {W : CompactCarrier.{u}}

theorem exists_pos_rounding_of_mem_nhds
    (R : CircleRegion W) {b : R.Base} (hb : R.rounding b = 0) {N : Set R.Base}
    (hN : N ∈ 𝓝 b) : ∃ b' ∈ N, 0 < R.rounding b' := by
  have hne := R.rounding_regular b hb
  have hsurj : Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) R.rounding b) := by
    let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) R.rounding b
    have hL : L ≠ 0 := hne
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hL (ContinuousLinearMap.ext hall)
    intro r
    let r' : ℝ := r
    refine ⟨(r' / L v) • v, ?_⟩
    change L ((r' / L v) • v) = r'
    rw [L.map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hmap := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at
    (R.rounding_smooth.contMDiffAt.of_le (by norm_num)) hsurj
  have himg : R.rounding '' N ∈ 𝓝 (0 : ℝ) := by
    rw [← hb, ← hmap]
    exact Filter.image_mem_map hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  obtain ⟨b', hb'N, hb'⟩ := hball (show ε / 2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith)
  exact ⟨b', hb'N, by rw [hb']; linarith⟩

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The closed unit-box images of all rim charts. -/
def rimCore : Set W.Carrier :=
  ⋃ h, ⋃ b, D.rimChart h b '' {p | p.2 ∈ rimClosedBox}

theorem isClosed_rimCore : IsClosed D.rimCore := by
  refine isClosed_iUnion_of_finite fun h => isClosed_iUnion_of_finite fun b => ?_
  have hK : IsCompact {p : Circle × (ℝ × ℝ) | p.2 ∈ rimClosedBox} := by
    convert (isCompact_univ (X := Circle)).prod isCompact_rimClosedBox using 1
    ext p
    simp
  refine (hK.image_of_continuousOn ((D.rimChart h b).contMDiffOn.continuousOn.mono ?_)).isClosed
  intro p hp
  exact (D.rim_source _ _).mpr (rimClosedBox_subset_rimBox_two hp)

theorem rimCore_subset_target {x : W.Carrier} (hx : x ∈ D.rimCore) :
    ∃ h b, x ∈ (D.rimChart h b).target := by
  obtain ⟨h, b, p, hp, rfl⟩ := mem_iUnion₂.mp hx
  exact ⟨h, b, (D.rimChart h b).map_source
    ((D.rim_source _ _).mpr (rimClosedBox_subset_rimBox_two hp))⟩

/-- Off the closed rim boxes, the projection avoids the unit boxes of the corner charts. -/
theorem proj_not_mem_box_of_not_mem_rimCore (y : D.circ.domain) (hy : y.1 ∉ D.rimCore) :
    D.circ.proj y ∉ ⋃ c, D.circ.cornerChart c '' rimBox 1 := by
  intro hmem
  obtain ⟨c, v, hv, hvy⟩ := mem_iUnion.mp hmem
  obtain ⟨h, b, hc, hsupp⟩ := D.exists_roundingSupport_eq_rimChart_target c
  have hvs : v ∈ (D.circ.cornerChart c).source := by
    rw [D.circ.cornerChart_source]
    exact rimBox_mono (by norm_num) hv
  have hyS : y.1 ∈ D.circ.roundingSupport c :=
    ⟨y, by rw [Set.mem_preimage, ← hvy]; exact (D.circ.cornerChart c).map_source hvs, rfl⟩
  rw [hsupp] at hyS
  obtain ⟨p, hp, hpy⟩ : ∃ p, p ∈ (D.rimChart h b).source ∧ D.rimChart h b p = y.1 :=
    ⟨(D.rimChart h b).symm y.1, (D.rimChart h b).map_target hyS, (D.rimChart h b).right_inv hyS⟩
  obtain ⟨hx, hproj⟩ := D.rim_proj h b p hp
  have hyy : (⟨D.rimChart h b p, hx⟩ : D.circ.domain) = y := Subtype.ext hpy
  rw [hyy, hc, ← hvy] at hproj
  have hp2 : p.2 ∈ (D.circ.cornerChart c).source := by
    rw [D.circ.cornerChart_source]
    exact (D.rim_source h b).mp hp
  have hpv : p.2 = v := ((D.circ.cornerChart c).injOn hp2 hvs hproj.symm)
  apply hy
  refine mem_iUnion₂.mpr ⟨h, b, p, ?_, hpy⟩
  rw [Set.mem_ofPred_eq, hpv]
  exact rimBox_one_subset_rimClosedBox hv

variable {D} in
/-- Off the closed rim boxes, `rounding ∘ proj ≤ 0` is the cornered circle region. -/
theorem rounding_le_zero_iff_of_not_mem_rimCore {y : D.circ.domain} (hy : y.1 ∉ D.rimCore) :
    D.circ.rounding (D.circ.proj y) ≤ 0 ↔ y.1 ∈ D.circ.region := by
  rw [CircleRegion.rounding_le_zero_iff (D.proj_not_mem_box_of_not_mem_rimCore y hy)]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← Subtype.ext hzy]

/-- The defining function in a rim chart: `ρ = -(λ ψ_std)`. -/
theorem roundedFunction_rimChart (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.rimChart h b).source) :
    D.circ.roundedFunction (D.rimChart h b p) =
      -(D.circ.cornerScale (D.handleCorner h b) * standardRimRounding p.2) := by
  obtain ⟨hx, hproj⟩ := D.rim_proj h b p hp
  have h1 := D.circ.roundedFunction_apply ⟨_, hx⟩
  rw [hproj, D.circ.rounding_chart _ _ ((D.rim_source h b).mp hp)] at h1
  exact h1

theorem mem_domain_of_mem_rimChart_target {h : Fin D.handleCount} {b : Bool} {x : W.Carrier}
    (hx : x ∈ (D.rimChart h b).target) : x ∈ D.circ.domain := by
  obtain ⟨hd, -⟩ := D.rim_proj h b _ ((D.rimChart h b).map_target hx)
  rwa [(D.rimChart h b).right_inv hx] at hd

/-- **Negative `ρ` means the interior of the circle region.** -/
theorem mem_interior_region_of_roundedFunction_neg {y : W.Carrier} (hyd : y ∈ D.circ.domain)
    (hρ : D.circ.roundedFunction y < 0) : y ∈ interior D.circ.region := by
  by_cases hc : y ∈ D.rimCore
  · obtain ⟨h, b, hT⟩ := D.rimCore_subset_target hc
    obtain ⟨p, hp, rfl⟩ : ∃ p, p ∈ (D.rimChart h b).source ∧ D.rimChart h b p = y :=
      ⟨(D.rimChart h b).symm y, (D.rimChart h b).map_target hT, (D.rimChart h b).right_inv hT⟩
    rw [D.roundedFunction_rimChart h b hp] at hρ
    have hψ : 0 < standardRimRounding p.2 := by
      have := D.circ.cornerScale_pos (D.handleCorner h b)
      by_contra hle
      have : 0 ≤ D.circ.cornerScale (D.handleCorner h b) * -standardRimRounding p.2 :=
        mul_nonneg this.le (by linarith)
      linarith
    have hx : 0 < p.2.1 := by
      by_contra hx
      exact (not_le.mpr hψ) (standardRimRounding_nonpos_of _ (Or.inr (not_lt.mp hx)))
    have hy : 0 < p.2.2 := by
      by_contra hy
      exact (not_le.mpr hψ) (standardRimRounding_nonpos_of _ (Or.inl (not_lt.mp hy)))
    exact D.rimQuadrant_subset_interior_region h b ⟨p, ⟨hp, hx, hy⟩, rfl⟩
  · -- off the closed boxes: an open neighbourhood inside the region
    let O : Set W.Carrier := {z | ∃ hz : z ∈ D.circ.domain, D.circ.rounding (D.circ.proj ⟨z, hz⟩) < 0}
    have hO : IsOpen O := by
      have hcont : Continuous fun z : D.circ.domain => D.circ.rounding (D.circ.proj z) :=
        D.circ.rounding_smooth.continuous.comp D.circ.proj.continuous
      have h1 : IsOpen ((fun z : D.circ.domain => D.circ.rounding (D.circ.proj z)) ⁻¹' Iio 0) :=
        isOpen_Iio.preimage hcont
      have h2 := D.circ.domain.isOpen.isOpenMap_subtype_val _ h1
      convert h2 using 1
      ext z
      constructor
      · rintro ⟨hz, hzr⟩
        exact ⟨⟨z, hz⟩, hzr, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw⟩
    have hyO : y ∈ O ∩ D.rimCoreᶜ := by
      refine ⟨⟨hyd, ?_⟩, hc⟩
      have := D.circ.roundedFunction_apply ⟨y, hyd⟩
      rw [← this]
      exact hρ
    refine interior_maximal ?_ (hO.inter D.isClosed_rimCore.isOpen_compl) hyO
    rintro z ⟨⟨hz, hzr⟩, hzc⟩
    exact (rounding_le_zero_iff_of_not_mem_rimCore (y := ⟨z, hz⟩) hzc).mp hzr.le

theorem not_mem_interior_region_of_mem_vertex_image (k : Fin D.vertexCount) {y : W.Carrier}
    (hy : y ∈ (D.vertex k).image) : y ∉ interior D.circ.region := by
  intro hyI
  rw [Vertex.image_eq_range_piece] at hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨w, hwO, hwV⟩ := exists_mem_inter_interior_range (I := 𝓡∂ 3) finrank_euclideanSpace_fin
    (D.vertex k).piece.smooth (D.vertex k).piece.mfderiv_bijective isOpen_interior hyI
  rw [← Vertex.image_eq_range_piece] at hwV
  exact Set.disjoint_left.mp (D.circ_vertex_disjoint k) hwO hwV

theorem not_mem_interior_region_of_mem_handle (h : Fin D.handleCount) {y : W.Carrier}
    (hy : y ∈ range (D.handle h).map) : y ∉ interior D.circ.region := by
  intro hyI
  obtain ⟨x, rfl⟩ := hy
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  obtain ⟨w, hwO, hwH⟩ := exists_mem_inter_interior_range (I := (𝓡∂ 2).prod (𝓡∂ 1)) hdim
    (D.handle h).smooth (D.handle h).mfderiv_bijective isOpen_interior hyI
  exact Set.disjoint_left.mp (D.circ_handle_disjoint h) hwO hwH

/-- Vertex points are on the closed side `ρ ≥ 0`. -/
theorem nonneg_roundedFunction_of_mem_vertex_image (k : Fin D.vertexCount) {y : W.Carrier}
    (hy : y ∈ (D.vertex k).image) (hyd : y ∈ D.circ.domain) : 0 ≤ D.circ.roundedFunction y :=
  not_lt.mp fun hρ => D.not_mem_interior_region_of_mem_vertex_image k hy
    (D.mem_interior_region_of_roundedFunction_neg hyd hρ)

/-- Handle points are on the closed side `ρ ≥ 0`. -/
theorem nonneg_roundedFunction_of_mem_handle (h : Fin D.handleCount) {y : W.Carrier}
    (hy : y ∈ range (D.handle h).map) (hyd : y ∈ D.circ.domain) : 0 ≤ D.circ.roundedFunction y :=
  not_lt.mp fun hρ => D.not_mem_interior_region_of_mem_handle h hy
    (D.mem_interior_region_of_roundedFunction_neg hyd hρ)

/-- The closed complement of the open rounded circle region. -/
def roundedComplement : Set W.Carrier :=
  {x | x ∉ D.circ.domain ∨ 0 ≤ D.circ.roundedFunction x}

theorem exists_pos_roundedFunction_of_mem_nhds {y : W.Carrier} (hyd : y ∈ D.circ.domain)
    (hρ : D.circ.roundedFunction y = 0) {N : Set W.Carrier} (hN : N ∈ 𝓝 y) :
    ∃ z ∈ N, z ∈ D.circ.domain ∧ 0 < D.circ.roundedFunction z := by
  have hN' : (Subtype.val ⁻¹' N : Set D.circ.domain) ∈ 𝓝 (⟨y, hyd⟩ : D.circ.domain) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  have himg := (CircleRegion.isOpenMap_proj_of_submersion D.circ).image_mem_nhds hN'
  have h0 : D.circ.rounding (D.circ.proj ⟨y, hyd⟩) = 0 := by
    rw [← D.circ.roundedFunction_apply ⟨y, hyd⟩]
    exact hρ
  obtain ⟨b', ⟨z, hzN, rfl⟩, hpos⟩ := D.circ.exists_pos_rounding_of_mem_nhds h0 himg
  refine ⟨z.1, hzN, z.2, ?_⟩
  rw [D.circ.roundedFunction_apply z]
  exact hpos

/-- An end disk of a certificate handle lies in the image of its end vertex. -/
theorem endDisk_subset_vertex_image
    (h : Fin D.handleCount) (b : Bool) :
    (D.handle h).endDisk b ⊆ (D.vertex (D.handleEnd h b)).image := by
  intro x hx
  have h1 := D.face_subset_boundaryImage (D.handleFace h b) (D.handleEnd_face h b hx)
  rw [D.handleFace_owner] at h1
  obtain ⟨q, -, hq⟩ := h1
  rw [Vertex.image_eq_range_piece]
  exact ⟨q, hq⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
