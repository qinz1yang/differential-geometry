import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionToriApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSidesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleThirdPieceApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpaceApplications

/-!
# FC42 packet T4a §1: the new zero level against the certificate pieces; seam deduplication

For a V4 certificate `D`, `ρ = circ.roundedFunction` and the new zero level
`Z_R = circ.roundedLevel = {x ∈ domain | ρ x = 0}` (packet T3):

* `exists_neg_roundedFunction_of_mem_roundedLevel`: next to every point of `Z_R` there are points
  with `ρ < 0` (the collars of packet T3); with the tree's `exists_pos_roundedFunction_of_mem_nhds`
  `Z_R` meets neither the interior of a vertex image, nor the interior of an edge circle image, nor
  (off the rim boxes) the interior of the circle region;
* `mem_roundedLevel_of_mem_vertex_of_mem_region`, `mem_roundedLevel_of_mem_edgeCircle_of_mem_region`:
  a point of a vertex that is not a handle end, or of an edge circle piece, lying in the circle
  region, is on `Z_R`;
* **deduplication** (review 40 §3.6; lead condition (c)):
  `seamTorus_subset_roundedLevel_of_none` and `exists_levelTorus_eq_seamTorus_of_none`: a seam torus
  with one `some` and one `none` side IS a whole boundary torus of the rounded region (so it is listed
  once, as a level torus); `disjoint_seamTorus_roundedLevel_of_none_none`: a `none / none` seam torus
  lies in the interior of the circle region and avoids `Z_R` (dropped);
  `disjoint_seamTorus_roundedLevel`: a vertex–vertex seam torus avoids `Z_R`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The vertex–vertex torus seams (both sides are vertices). -/
def IsVertexSeam (c : Fin D.torusSeamCount) : Prop :=
  (D.torusSide c true).isSome ∧ (D.torusSide c false).isSome

/-- The zero torus of a certificate torus seam. -/
def seamTorus (c : Fin D.torusSeamCount) : Set W.Carrier :=
  range fun t => (D.torusSeam c).collar (t, 0)

theorem seamTorus_subset_target (c : Fin D.torusSeamCount) :
    D.seamTorus c ⊆ (D.torusSeam c).collar.target := by
  rintro _ ⟨t, rfl⟩
  apply (D.torusSeam c).collar.map_source
  rw [(D.torusSeam c).source_eq]
  exact ⟨by norm_num, by norm_num⟩

theorem isCompact_seamTorus (c : Fin D.torusSeamCount) : IsCompact (D.seamTorus c) := by
  refine isCompact_range ((D.torusSeam c).collar.contMDiffOn.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const) fun t => ?_)
  rw [(D.torusSeam c).source_eq]
  exact ⟨by norm_num, by norm_num⟩

theorem isConnected_seamTorus (c : Fin D.torusSeamCount) : IsConnected (D.seamTorus c) := by
  refine isConnected_range ((D.torusSeam c).collar.contMDiffOn.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const) fun t => ?_)
  rw [(D.torusSeam c).source_eq]
  exact ⟨by norm_num, by norm_num⟩

/-! ## Points with negative `ρ` near the zero level -/

theorem exists_neg_roundedFunction_of_mem_roundedLevel {x : W.Carrier}
    (hx : x ∈ D.circ.roundedLevel) {N : Set W.Carrier} (hN : N ∈ 𝓝 x) :
    ∃ z ∈ N, z ∈ D.circ.domain ∧ D.circ.roundedFunction z < 0 := by
  obtain ⟨δ, S, hδ, hS, hrange, -, hval⟩ :=
    D.circ.exists_levelTorus_seams univ isOpen_univ (subset_univ _)
  rw [← D.circ.iUnion_levelTorus] at hx
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  rw [← hrange c] at hc
  obtain ⟨t, rfl⟩ := hc
  have hsrc : ∀ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → ((t, s) : Torus × ℝ) ∈ (S c).collar.source := by
    intro s hs
    rw [(S c).source_eq]
    exact hs
  have hcont : ContinuousAt (fun s : ℝ => (S c).collar (t, s)) 0 :=
    ((S c).collar.contMDiffOn.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      hsrc).continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds hN)
  set s : ℝ := -min (ε / 2) (1 / 2) with hsdef
  have hs0 : s < 0 := by
    have : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
    linarith
  have hs1 : -1 < s := by
    have : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hs0]
    have : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  have hs : s ∈ Ioo (-1 : ℝ) 1 := ⟨hs1, by linarith⟩
  have hsT : (S c).collar (t, s) ∈ (S c).collar.target := (S c).collar.map_source (hsrc s hs)
  refine ⟨_, hball hsball, (hS c hsT).2, ?_⟩
  rw [hval c (t, s) ⟨hs.1, hs.2⟩]
  exact mul_neg_of_pos_of_neg (hδ c) hs0

/-- `Z_R` avoids the ambient interior of every vertex image. -/
theorem not_mem_interior_vertex_of_mem_roundedLevel (k : Fin D.vertexCount) {x : W.Carrier}
    (hx : x ∈ D.circ.roundedLevel) : x ∉ interior (D.vertex k).image := by
  intro hxi
  obtain ⟨z, hzN, hzd, hzneg⟩ := D.exists_neg_roundedFunction_of_mem_roundedLevel hx
    (isOpen_interior.mem_nhds hxi)
  exact Set.disjoint_left.mp (D.circ_vertex_disjoint k)
    (D.mem_interior_region_of_roundedFunction_neg hzd hzneg) hzN

/-- `Z_R` avoids the ambient interior of every edge circle image. -/
theorem not_mem_interior_edgeCircle_of_mem_roundedLevel (e : Fin D.edgeCircleCount) {x : W.Carrier}
    (hx : x ∈ D.circ.roundedLevel) : x ∉ interior (range (D.edgeCircle e).piece.map) := by
  intro hxi
  obtain ⟨z, hzN, hzd, hzneg⟩ := D.exists_neg_roundedFunction_of_mem_roundedLevel hx
    (isOpen_interior.mem_nhds hxi)
  exact Set.disjoint_left.mp (D.circ_edgeCircle_disjoint e)
    (D.mem_interior_region_of_roundedFunction_neg hzd hzneg) hzN

/-- Off the closed rim boxes, `Z_R` avoids the interior of the circle region. -/
theorem not_mem_interior_region_of_mem_roundedLevel {x : W.Carrier} (hx : x ∈ D.circ.roundedLevel)
    (hxc : x ∉ D.rimCore) : x ∉ interior D.circ.region := by
  intro hxi
  have hxd : x ∈ D.circ.domain := D.circ.roundedLevel_subset_domain hx
  have h0 : D.circ.roundedFunction x = 0 := by
    rw [D.circ.roundedLevel_eq] at hx
    exact hx.2
  obtain ⟨z, ⟨hzR, hzc⟩, hzd, hzpos⟩ := D.exists_pos_roundedFunction_of_mem_nhds hxd h0
    (inter_mem (mem_interior_iff_mem_nhds.mp hxi) (D.isClosed_rimCore.isOpen_compl.mem_nhds hxc))
  have hle := (rounding_le_zero_iff_of_not_mem_rimCore (y := ⟨z, hzd⟩) hzc).mpr hzR
  rw [← D.circ.roundedFunction_apply ⟨z, hzd⟩] at hle
  exact absurd hle (not_le.mpr hzpos)

/-! ## Vertex and edge-circle points in the circle region are on `Z_R` -/

theorem not_mem_rimCore_of_mem_vertex (k : Fin D.vertexCount) (hk : ∀ h b, D.handleEnd h b ≠ k)
    {x : W.Carrier} (hx : x ∈ (D.vertex k).image) : x ∉ D.rimCore := fun hc => by
  obtain ⟨h, b, hT⟩ := D.rimCore_subset_target hc
  exact Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target h b k (hk h b).symm) hx hT

theorem not_mem_rimCore_of_mem_edgeCircle (e : Fin D.edgeCircleCount) {x : W.Carrier}
    (hx : x ∈ range (D.edgeCircle e).piece.map) : x ∉ D.rimCore := fun hc => by
  obtain ⟨h, b, hT⟩ := D.rimCore_subset_target hc
  exact Set.disjoint_left.mp (D.disjoint_edgeCircle_rimChart_target h b e) hx hT

theorem nonneg_roundedFunction_of_mem_edgeCircle (e : Fin D.edgeCircleCount) {y : W.Carrier}
    (hy : y ∈ range (D.edgeCircle e).piece.map) (hyd : y ∈ D.circ.domain) :
    0 ≤ D.circ.roundedFunction y := by
  refine not_lt.mp fun hρ => ?_
  have hyI := D.mem_interior_region_of_roundedFunction_neg hyd hρ
  obtain ⟨q, rfl⟩ := hy
  obtain ⟨w, hwO, hwE⟩ := exists_mem_inter_interior_range (I := 𝓡∂ 3) finrank_euclideanSpace_fin
    (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective isOpen_interior hyI
  exact Set.disjoint_left.mp (D.circ_edgeCircle_disjoint e) hwO hwE

theorem mem_roundedLevel_of_nonneg_of_mem_region {x : W.Carrier} (hxc : x ∉ D.rimCore)
    (hxR : x ∈ D.circ.region) (hge : x ∈ D.circ.domain → 0 ≤ D.circ.roundedFunction x) :
    x ∈ D.circ.roundedLevel := by
  have hxd : x ∈ D.circ.domain := D.circ.region_subset_domain hxR
  have hle := (rounding_le_zero_iff_of_not_mem_rimCore (y := ⟨x, hxd⟩) hxc).mpr hxR
  rw [← D.circ.roundedFunction_apply ⟨x, hxd⟩] at hle
  rw [D.circ.roundedLevel_eq]
  exact ⟨hxd, le_antisymm hle (hge hxd)⟩

/-- **A vertex point in the circle region is on the new zero level** (vertex not a handle end). -/
theorem mem_roundedLevel_of_mem_vertex_of_mem_region (k : Fin D.vertexCount)
    (hk : ∀ h b, D.handleEnd h b ≠ k) {x : W.Carrier} (hxk : x ∈ (D.vertex k).image)
    (hxR : x ∈ D.circ.region) : x ∈ D.circ.roundedLevel :=
  D.mem_roundedLevel_of_nonneg_of_mem_region (D.not_mem_rimCore_of_mem_vertex k hk hxk) hxR
    fun hxd => D.nonneg_roundedFunction_of_mem_vertex_image k hxk hxd

/-- **An edge-circle point in the circle region is on the new zero level.** -/
theorem mem_roundedLevel_of_mem_edgeCircle_of_mem_region (e : Fin D.edgeCircleCount)
    {x : W.Carrier} (hxe : x ∈ range (D.edgeCircle e).piece.map) (hxR : x ∈ D.circ.region) :
    x ∈ D.circ.roundedLevel :=
  D.mem_roundedLevel_of_nonneg_of_mem_region (D.not_mem_rimCore_of_mem_edgeCircle e hxe) hxR
    fun hxd => D.nonneg_roundedFunction_of_mem_edgeCircle e hxe hxd

/-! ## Seam tori and the zero level: deduplication -/

theorem collar_not_mem_rimCore (c : Fin D.torusSeamCount) {x : W.Carrier}
    (hx : x ∈ (D.torusSeam c).collar.target) : x ∉ D.rimCore := fun hc => by
  obtain ⟨h, b, hT⟩ := D.rimCore_subset_target hc
  exact Set.disjoint_left.mp (D.rim_torusSeam_disjoint h b c) hT hx

/-- The open part `{s < 0}` (side `true`) or `{s > 0}` (side `false`) of a seam collar. -/
def openHalfCollar (c : Fin D.torusSeamCount) (b : Bool) : Set W.Carrier :=
  (D.torusSeam c).collar '' {p | p ∈ signedCollarSource ∧ (if b then p.2 < 0 else 0 < p.2)}

theorem isOpen_openHalfCollar (c : Fin D.torusSeamCount) (b : Bool) :
    IsOpen (D.openHalfCollar c b) := by
  refine (D.torusSeam c).collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ ?_
  · have h1 : IsOpen (signedCollarSource : Set (Torus × ℝ)) := signedCollarSource_isOpen
    cases b
    · exact h1.inter (isOpen_lt continuous_const continuous_snd)
    · exact h1.inter (isOpen_lt continuous_snd continuous_const)
  · intro p hp
    change p ∈ (D.torusSeam c).collar.source
    rw [(D.torusSeam c).source_eq]
    exact hp.1

theorem openHalfCollar_subset (c : Fin D.torusSeamCount) (b : Bool) :
    D.openHalfCollar c b ⊆
      ((D.torusSide c b).elim D.circ.region fun k => (D.vertex k).image) := by
  rintro _ ⟨p, ⟨hp, hs⟩, rfl⟩
  have hp' : p = (p.1, p.2) := rfl
  rw [hp']
  cases b
  · exact D.torusSide_pos c p.1 p.2 (le_of_lt hs) hp.2
  · exact D.torusSide_neg c p.1 p.2 hp.1 (le_of_lt hs)

theorem openHalfCollar_subset_interior (c : Fin D.torusSeamCount) (b : Bool) :
    D.openHalfCollar c b ⊆
      interior ((D.torusSide c b).elim D.circ.region fun k => (D.vertex k).image) :=
  interior_maximal (D.openHalfCollar_subset c b) (D.isOpen_openHalfCollar c b)

theorem disjoint_openHalfCollar_roundedLevel (c : Fin D.torusSeamCount) (b : Bool) :
    Disjoint (D.openHalfCollar c b) D.circ.roundedLevel := by
  rw [Set.disjoint_left]
  intro x hx hxZ
  have hxT : x ∈ (D.torusSeam c).collar.target := by
    obtain ⟨p, hp, rfl⟩ := hx
    apply (D.torusSeam c).collar.map_source
    rw [(D.torusSeam c).source_eq]
    exact hp.1
  have hxi := D.openHalfCollar_subset_interior c b hx
  rcases hside : D.torusSide c b with _ | k
  · rw [hside] at hxi
    exact D.not_mem_interior_region_of_mem_roundedLevel hxZ (D.collar_not_mem_rimCore c hxT) hxi
  · rw [hside] at hxi
    exact D.not_mem_interior_vertex_of_mem_roundedLevel k hxZ hxi

/-- Within a seam collar, the zero level is contained in the seam torus. -/
theorem roundedLevel_inter_target_subset (c : Fin D.torusSeamCount) :
    D.circ.roundedLevel ∩ (D.torusSeam c).collar.target ⊆ D.seamTorus c := by
  rintro x ⟨hxZ, hxT⟩
  have hp : (D.torusSeam c).collar.symm x ∈ signedCollarSource := by
    rw [← (D.torusSeam c).source_eq]
    exact (D.torusSeam c).collar.map_target hxT
  have hxp : (D.torusSeam c).collar ((D.torusSeam c).collar.symm x) = x :=
    (D.torusSeam c).collar.right_inv hxT
  set p := (D.torusSeam c).collar.symm x with hpdef
  rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
  · exact absurd hxZ (Set.disjoint_left.mp (D.disjoint_openHalfCollar_roundedLevel c true)
      ⟨p, ⟨hp, hneg⟩, hxp⟩)
  · refine ⟨p.1, ?_⟩
    rw [← hxp]
    change (D.torusSeam c).collar (p.1, 0) = (D.torusSeam c).collar p
    rw [← hzero]
  · exact absurd hxZ (Set.disjoint_left.mp (D.disjoint_openHalfCollar_roundedLevel c false)
      ⟨p, ⟨hp, hpos⟩, hxp⟩)

theorem seamTorus_subset_side (c : Fin D.torusSeamCount) (b : Bool) :
    D.seamTorus c ⊆ ((D.torusSide c b).elim D.circ.region fun k => (D.vertex k).image) := by
  rintro _ ⟨t, rfl⟩
  cases b
  · exact D.torusSide_pos c t 0 le_rfl (by norm_num)
  · exact D.torusSide_neg c t 0 (by norm_num) le_rfl

/-- **Deduplication, `some / none`.** A seam torus with a vertex on one side and the circle region
on the other lies on the new zero level. -/
theorem seamTorus_subset_roundedLevel_of_none (hbad : D.badVertexCount = 0)
    (c : Fin D.torusSeamCount) (b : Bool) {k : Fin D.vertexCount}
    (hk : D.torusSide c b = some k) (hnone : D.torusSide c (!b) = none) :
    D.seamTorus c ⊆ D.circ.roundedLevel := by
  intro x hx
  have hxk : x ∈ (D.vertex k).image := by
    have h := D.seamTorus_subset_side c b hx
    rwa [hk] at h
  have hxR : x ∈ D.circ.region := by
    have h := D.seamTorus_subset_side c (!b) hx
    rwa [hnone] at h
  have hkb : ¬ (D.vertex k).IsBall := by
    intro hball
    obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b k hk
    exact D.faceKind_ne_torusSeam_of_isBall hball hfo c b hfk
  have hend : ∀ h b', D.handleEnd h b' ≠ k := fun h b' heq => hkb (heq ▸ D.isBall_handleEnd
    (fun f hf hS => D.partitionedSphereFace_ball_of_badVertexCount_eq_zero hbad f hf hS) h b')
  exact D.mem_roundedLevel_of_mem_vertex_of_mem_region k hend hxk hxR

/-- A connected subset of the new zero level lies in one boundary torus of the rounded region. -/
theorem exists_levelTorus_of_isPreconnected {s : Set W.Carrier} (hs : IsPreconnected s)
    (hsZ : s ⊆ D.circ.roundedLevel) (hne : s.Nonempty) :
    ∃ l, s ⊆ D.circ.levelTorus l := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hxZ := hsZ hx
  rw [← D.circ.iUnion_levelTorus] at hxZ
  obtain ⟨l, hl⟩ := mem_iUnion.mp hxZ
  refine ⟨l, ?_⟩
  let t' : Set W.Carrier := ⋃ l' ∈ ({l}ᶜ : Set (ConnectedComponents D.circ.BaseLevel)),
    D.circ.levelTorus l'
  have hclosed : ∀ l', IsClosed (D.circ.levelTorus l') := fun l' =>
    (D.circ.isCompact_levelTorus l').isClosed
  have ht' : IsClosed t' := (Set.toFinite _).isClosed_biUnion fun l' _ => hclosed l'
  have hsub : s ⊆ D.circ.levelTorus l ∪ t' := by
    intro y hy
    have hyZ := hsZ hy
    rw [← D.circ.iUnion_levelTorus] at hyZ
    obtain ⟨l', hl'⟩ := mem_iUnion.mp hyZ
    by_cases hll : l' = l
    · exact Or.inl (hll ▸ hl')
    · exact Or.inr (mem_biUnion (show l' ∈ ({l}ᶜ : Set _) from hll) hl')
  intro y hy
  by_contra hnot
  obtain ⟨z, -, hzl, hzt⟩ := isPreconnected_closed_iff.mp hs _ _ (hclosed l) ht' hsub
    ⟨x, hx, hl⟩ ⟨y, hy, (hsub hy).resolve_left hnot⟩
  obtain ⟨l', hl', hzl'⟩ := mem_iUnion₂.mp hzt
  exact (D.circ.pairwise_disjoint_levelTorus (show l ≠ l' from fun h => hl' (h ▸ rfl))).le_bot
    ⟨hzl, hzl'⟩

/-- **Deduplication, `some / none`.** Such a seam torus IS a whole boundary torus of the rounded
region; it is listed once, as a level torus. -/
theorem exists_levelTorus_eq_seamTorus_of_none (hbad : D.badVertexCount = 0)
    (c : Fin D.torusSeamCount) (b : Bool) {k : Fin D.vertexCount}
    (hk : D.torusSide c b = some k) (hnone : D.torusSide c (!b) = none) :
    ∃ l, D.circ.levelTorus l = D.seamTorus c := by
  have hsub := D.seamTorus_subset_roundedLevel_of_none hbad c b hk hnone
  obtain ⟨l, hl⟩ := D.exists_levelTorus_of_isPreconnected (D.isConnected_seamTorus c).isPreconnected
    hsub (D.isConnected_seamTorus c).nonempty
  refine ⟨l, Subset.antisymm ?_ hl⟩
  -- `T_l ∩ seamTorus` is open and closed in the connected `T_l`
  have hT := D.circ.isConnected_levelTorus l
  have hopen : D.circ.levelTorus l ∩ D.seamTorus c =
      D.circ.levelTorus l ∩ (D.torusSeam c).collar.target := by
    apply Subset.antisymm
    · exact fun y hy => ⟨hy.1, D.seamTorus_subset_target c hy.2⟩
    · exact fun y hy => ⟨hy.1, D.roundedLevel_inter_target_subset c
        ⟨D.circ.levelTorus_subset_roundedLevel l hy.1, hy.2⟩⟩
  intro y hy
  by_contra hny
  obtain ⟨x0, hx0⟩ := (D.isConnected_seamTorus c).nonempty
  obtain ⟨z, hzT, hzu, hzv⟩ := hT.isPreconnected (D.torusSeam c).collar.target (D.seamTorus c)ᶜ
    (D.torusSeam c).collar.open_target (D.isCompact_seamTorus c).isClosed.isOpen_compl
    (fun w _ => by
      by_cases hws : w ∈ D.seamTorus c
      · exact Or.inl (D.seamTorus_subset_target c hws)
      · exact Or.inr hws)
    ⟨x0, hl hx0, D.seamTorus_subset_target c hx0⟩ ⟨y, hy, hny⟩
  have hz : z ∈ D.circ.levelTorus l ∩ (D.torusSeam c).collar.target := ⟨hzT, hzu⟩
  rw [← hopen] at hz
  exact hzv hz.2

/-- **Deduplication, `none / none`.** Such a seam torus lies in the interior of the circle region. -/
theorem seamTorus_subset_interior_region_of_none_none (c : Fin D.torusSeamCount)
    (h1 : D.torusSide c true = none) (h2 : D.torusSide c false = none) :
    D.seamTorus c ⊆ interior D.circ.region :=
  (D.seamTorus_subset_target c).trans (interior_maximal (D.collar_target_subset_region h1 h2)
    (D.torusSeam c).collar.open_target)

/-- **Deduplication, `none / none`.** Such a seam torus avoids the new zero level: it is not a
boundary torus of the rounded region and is dropped from the final seams. -/
theorem disjoint_seamTorus_roundedLevel_of_none_none (c : Fin D.torusSeamCount)
    (h1 : D.torusSide c true = none) (h2 : D.torusSide c false = none) :
    Disjoint (D.seamTorus c) D.circ.roundedLevel := by
  rw [Set.disjoint_left]
  intro x hx hxZ
  exact D.not_mem_interior_region_of_mem_roundedLevel hxZ
    (D.collar_not_mem_rimCore c (D.seamTorus_subset_target c hx))
    (D.seamTorus_subset_interior_region_of_none_none c h1 h2 hx)

/-- **A vertex–vertex seam torus avoids the new zero level.** -/
theorem disjoint_seamTorus_roundedLevel (c : Fin D.torusSeamCount) (hc : D.IsVertexSeam c) :
    Disjoint (D.seamTorus c) D.circ.roundedLevel := by
  rw [Set.disjoint_left]
  intro x hx hxZ
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc.1
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hc.2
  obtain ⟨z, hzN, hzd, hzneg⟩ := D.exists_neg_roundedFunction_of_mem_roundedLevel hxZ
    ((D.torusSeam c).collar.open_target.mem_nhds (D.seamTorus_subset_target c hx))
  have hp : (D.torusSeam c).collar.symm z ∈ signedCollarSource := by
    rw [← (D.torusSeam c).source_eq]
    exact (D.torusSeam c).collar.map_target hzN
  have hzp : (D.torusSeam c).collar ((D.torusSeam c).collar.symm z) = z :=
    (D.torusSeam c).collar.right_inv hzN
  have hzV : ∃ k'', z ∈ (D.vertex k'').image := by
    rcases le_total ((D.torusSeam c).collar.symm z).2 0 with hs | hs
    · have h := D.torusSide_neg c ((D.torusSeam c).collar.symm z).1
        ((D.torusSeam c).collar.symm z).2 hp.1 hs
      rw [hk, Prod.mk.eta, hzp] at h
      exact ⟨k, h⟩
    · have h := D.torusSide_pos c ((D.torusSeam c).collar.symm z).1
        ((D.torusSeam c).collar.symm z).2 hs hp.2
      rw [hk', Prod.mk.eta, hzp] at h
      exact ⟨k', h⟩
  obtain ⟨k'', hz⟩ := hzV
  exact absurd (D.nonneg_roundedFunction_of_mem_vertex_image k'' hz hzd) (not_le.mpr hzneg)

end DecompositionCertificate

end GC.GraphManifold.Assembly
