import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyCover

/-!
# FC42 packet T4a §4: the boundaries of the final pieces; seam sides and port lifts

* `mem_boundaryImage_cases_of_not_isBall` (and the frozen `boundaryImage_subset_of_not_isBall`): the
  model boundary of a non-ball vertex consists of its external port tori, its vertex–vertex seam
  tori and points of the new zero level `Z_R` (`μ = 0`);
* `edgeCircle_boundary_subset_roundedLevel`, `roundedUnion_boundary_subset_roundedLevel`,
  `CircleRegion.roundedRegionPiece_boundary_subset_roundedLevel`: the boundaries of the edge circles,
  of the cycle unions and of the rounded pieces lie on `Z_R`;
* `not_isBall_externalOwner`: the owner of an external port is a non-ball vertex;
* `range_vertex_inter_collar_target`: a vertex on side `b` of a vertex–vertex seam meets the seam
  collar exactly in the closed side-`b` half collar (the input of B2-side);
* `TorusSeam.shrink` and `TorusSeam.range_inter_shrink_target`: the shrunk seam, which keeps the
  side property; `TorusSeam.shrink_target_subset_image` with `TorusSeam.isCompact_image_Icc`: the
  shrunk target lies in a compact part of the old one;
* `exists_halfCollar_of_target_subset_range`: an external half collar whose target lies in an
  injective piece lifts to a half collar of the piece (B2 for ports).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## Shrunk torus seams -/

namespace TorusSeam

variable {W : CompactCarrier.{u}} (S : TorusSeam W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)

/-- The seam with the collar parameter scaled by `ε`. -/
def shrink : TorusSeam W where
  collar := shrinkSignedCollar hε S.collar
  source_eq := shrinkSignedCollar_source hε hε1 S.source_eq
  target_interior := (shrinkSignedCollar_target_subset hε _).trans S.target_interior

theorem shrink_collar_apply (p : Torus × ℝ) :
    (S.shrink hε hε1).collar p = S.collar (p.1, ε * p.2) := rfl

theorem shrink_target_subset : (S.shrink hε hε1).collar.target ⊆ S.collar.target :=
  shrinkSignedCollar_target_subset hε _

theorem shrink_collar_zero (t : Torus) : (S.shrink hε hε1).collar (t, 0) = S.collar (t, 0) := by
  rw [shrink_collar_apply, mul_zero]

theorem range_shrink_collar_zero :
    (range fun t => (S.shrink hε hε1).collar (t, 0)) = range fun t => S.collar (t, 0) := by
  simp only [shrink_collar_zero]

/-- The shrunk target lies in the image of the closed band `|s| ≤ ε`. -/
theorem shrink_target_subset_image :
    (S.shrink hε hε1).collar.target ⊆ S.collar '' (univ ×ˢ Icc (-ε) ε) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ signedCollarSource, (S.shrink hε hε1).collar p = y :=
    ⟨_, (S.shrink hε hε1).source_eq ▸ (S.shrink hε hε1).collar.map_target hy,
      (S.shrink hε hε1).collar.right_inv hy⟩
  obtain ⟨h1, h2⟩ := hp
  refine ⟨(p.1, ε * p.2), ⟨mem_univ _, ?_, ?_⟩, rfl⟩
  · change -ε ≤ ε * p.2
    nlinarith
  · change ε * p.2 ≤ ε
    nlinarith

theorem image_Icc_subset_source {ε : ℝ} (hε1 : ε < 1) :
    univ ×ˢ Icc (-ε) ε ⊆ S.collar.source := by
  rintro p ⟨-, h1, h2⟩
  rw [S.source_eq]
  exact ⟨by linarith, by linarith⟩

theorem isCompact_image_Icc {ε : ℝ} (hε1 : ε < 1) :
    IsCompact (S.collar '' (univ ×ˢ Icc (-ε) ε)) :=
  (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (S.collar.contMDiffOn.continuousOn.mono (S.image_Icc_subset_source hε1))

theorem image_Icc_subset_target {ε : ℝ} (hε1 : ε < 1) :
    S.collar '' (univ ×ˢ Icc (-ε) ε) ⊆ S.collar.target := by
  rintro _ ⟨p, hp, rfl⟩
  exact S.collar.map_source (S.image_Icc_subset_source hε1 hp)

/-- **The side property survives the shrink.** -/
theorem range_inter_shrink_target {X : Set W.Carrier} (b : Bool)
    (hX : X ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2}) :
    X ∩ (S.shrink hε hε1).collar.target =
      (S.shrink hε hε1).collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2} := by
  have hside : ∀ s : ℝ, (if b then ε * s ≤ 0 else 0 ≤ ε * s) ↔ (if b then s ≤ 0 else 0 ≤ s) :=
    fun s => by
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        refine ⟨fun h => ?_, fun h => mul_nonneg hε.le h⟩
        by_contra h'
        have := mul_neg_of_pos_of_neg hε (not_le.mp h')
        linarith
      · simp only [ite_true]
        refine ⟨fun h => ?_, fun h => mul_nonpos_of_nonneg_of_nonpos hε.le h⟩
        by_contra h'
        have := mul_pos hε (not_le.mp h')
        linarith
  have hsrc : ∀ p : Torus × ℝ, p ∈ signedCollarSource → (p.1, ε * p.2) ∈ signedCollarSource :=
    fun p hp => by
      obtain ⟨h1, h2⟩ := hp
      exact ⟨by nlinarith, by nlinarith⟩
  apply Subset.antisymm
  · rintro y ⟨hyX, hyT⟩
    have hp := (S.shrink hε hε1).collar.map_target hyT
    rw [(S.shrink hε hε1).source_eq] at hp
    set p := (S.shrink hε hε1).collar.symm y
    have hyp : S.collar (p.1, ε * p.2) = y := (S.shrink hε hε1).collar.right_inv hyT
    have hmem : y ∈ X ∩ S.collar.target := ⟨hyX, S.shrink_target_subset hε hε1 hyT⟩
    rw [hX] at hmem
    obtain ⟨p', ⟨hp', hs'⟩, hp'y⟩ := hmem
    have heq : p' = (p.1, ε * p.2) := S.collar.injOn (S.source_eq ▸ hp')
      (S.source_eq ▸ hsrc p hp) (hp'y.trans hyp.symm)
    refine ⟨p, ⟨hp, (hside p.2).mp ?_⟩, hyp⟩
    rw [heq] at hs'
    exact hs'
  · rintro _ ⟨p, ⟨hp, hs⟩, rfl⟩
    refine ⟨?_, (S.shrink hε hε1).collar.map_source ((S.shrink hε hε1).source_eq ▸ hp)⟩
    have hmem : S.collar (p.1, ε * p.2) ∈ X ∩ S.collar.target := by
      rw [hX]
      exact ⟨(p.1, ε * p.2), ⟨hsrc p hp, (hside p.2).mpr hs⟩, rfl⟩
    exact hmem.1

end TorusSeam

/-! ## B2 for ports: half collars in an injective piece -/

/-- **An external half collar inside an injective piece lifts to the piece.** -/
theorem exists_halfCollar_of_target_subset_range {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (c : PartialDiffeomorph halfCollarModel W.model (Torus × EuclideanHalfSpace 1) W.Carrier ∞)
    (hc : c.source = halfCollarSource) (hsub : c.target ⊆ range P.map) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞,
      L.source = halfCollarSource ∧ L.target = P.map ⁻¹' c.target ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ p ∈ halfCollarSource, P.map (L p) = c p := by
  classical
  have hcs : ∀ p ∈ halfCollarSource, p ∈ c.source := fun p hp => hc.symm ▸ hp
  let L0 : Torus × EuclideanHalfSpace 1 → P.Piece := fun p => Function.invFun P.map (c p)
  have hL0 : ∀ p ∈ halfCollarSource, P.map (L0 p) = c p :=
    fun p hp => Function.invFun_eq (hsub (c.map_source (hcs p hp)))
  let A : Set P.Piece := P.map ⁻¹' c.target
  have hAopen : IsOpen A := c.open_target.preimage P.continuous_map
  let Ψ : P.Piece → Torus × EuclideanHalfSpace 1 := fun q => c.invFun (P.map q)
  have hΨsm : ContMDiffOn (𝓡∂ 3) halfCollarModel ∞ Ψ A :=
    c.contMDiffOn_invFun.comp P.smooth.contMDiffOn (fun q hq => hq)
  have hΨsrc : ∀ q ∈ A, Ψ q ∈ halfCollarSource := fun q hq => hc ▸ c.map_target hq
  have hbijΨ : ∀ q ∈ A, Bijective (mfderiv (𝓡∂ 3) halfCollarModel Ψ q) := by
    intro q hq
    have hCd : IsLocalDiffeomorphAt W.model halfCollarModel ∞ c.invFun (P.map q) :=
      c.symm.isLocalDiffeomorphAt W.model halfCollarModel ∞ hq
    have hmΨ : mfderiv (𝓡∂ 3) halfCollarModel Ψ q =
        (mfderiv W.model halfCollarModel c.invFun (P.map q)).comp
          (mfderiv (𝓡∂ 3) W.model P.map q) :=
      mfderiv_comp q (hCd.mdifferentiableAt (by simp)) (P.mdifferentiable_map q)
    have hb1 : Bijective (mfderiv W.model halfCollarModel c.invFun (P.map q)) :=
      (hCd.mfderivToContinuousLinearEquiv (by simp)).bijective
    rw [hmΨ, ContinuousLinearMap.coe_comp]
    exact hb1.comp (P.mfderiv_bijective q)
  have hLA : ∀ p ∈ halfCollarSource, L0 p ∈ A := fun p hp => by
    change P.map (L0 p) ∈ c.target
    rw [hL0 p hp]
    exact c.map_source (hcs p hp)
  have hΨL : ∀ p ∈ halfCollarSource, Ψ (L0 p) = p := fun p hp => by
    change c.invFun (P.map (L0 p)) = p
    rw [hL0 p hp]
    exact c.left_inv (hcs p hp)
  have hLΨ : ∀ q ∈ A, L0 (Ψ q) = q := fun q hq => by
    apply P.injective
    rw [hL0 _ (hΨsrc q hq)]
    exact c.right_inv hq
  have hL0c : ContinuousOn L0 halfCollarSource := by
    rw [P.isClosedEmbedding_map.isEmbedding.continuousOn_iff]
    exact (c.contMDiffOn_toFun.continuousOn.mono fun p hp => hcs p hp).congr fun p hp => hL0 p hp
  have hL0sm : ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ L0 halfCollarSource :=
    contMDiffOn_of_leftInverse_of_bijective_mfderiv hAopen GC.Seifert.isOpen_halfCollarSource'
      hΨsm hΨsrc hLA hΨL hLΨ hL0c hbijΨ
  let L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞ :=
    { toFun := L0
      invFun := Ψ
      source := halfCollarSource
      target := A
      map_source' := hLA
      map_target' := hΨsrc
      left_inv' := hΨL
      right_inv' := hLΨ
      open_source := GC.Seifert.isOpen_halfCollarSource'
      open_target := hAopen
      contMDiffOn_toFun := hL0sm
      contMDiffOn_invFun := hΨsm }
  refine ⟨L, rfl, rfl, fun t => ?_, hL0⟩
  have hmem : (t, halfZero) ∈ L.source := by
    change (0 : ℝ) < 1
    norm_num
  exact ((L.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hmem).isBoundaryPoint_iff (by simp)).mp
    (halfCollar_isBoundaryPoint_halfZero t)

/-! ## The boundaries of the final pieces -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The boundary of a rounded piece lies on the new zero level. -/
theorem roundedRegionPiece_boundary_subset_roundedLevel (j : ConnectedComponents R.roundedBase) :
    (R.roundedRegionPiece j).map '' (𝓡∂ 3).boundary (R.roundedRegionPiece j).Piece ⊆
      R.roundedLevel := by
  rintro _ ⟨q, hq, rfl⟩
  rw [R.roundedLevel_eq]
  have hr := R.range_roundedRegionPiece_subset_rounded j (mem_range_self q)
  rw [R.rounded_eq_sublevel] at hr
  exact ⟨hr.1, roundedRegionPiece_isBoundaryPoint_iff.mp hq⟩

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The owner of an external port is not a ball.** -/
theorem not_isBall_externalOwner (i : Fin n) : ¬ (D.vertex (D.externalOwner i)).IsBall := by
  intro hk
  obtain ⟨f, hf⟩ := D.external_face i
  exact D.faceKind_ne_external_of_isBall hk (D.face_external f i hf).2.symm i hf

/-- A partitioned face whose owner is not a handle end lies in the circle region. -/
theorem face_subset_region_of_partitioned {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) (hk : ∀ h b, D.handleEnd h b ≠ D.faceOwner f) :
    D.face f ⊆ D.circ.region := by
  intro x hx
  have hx' := hx
  rw [← D.face_partition f hf] at hx'
  rcases hx' with (hd | ha) | hl
  · simp only [mem_iUnion] at hd
    obtain ⟨h, b, hfb, -⟩ := hd
    exact absurd ((D.handleFace_owner h b).symm.trans (congrArg D.faceOwner hfb)) (hk h b)
  · have hmem : x ∈ D.face f ∩ D.circ.region := by
      rw [D.face_region_inter f hf]
      exact Or.inl ha
    exact hmem.2
  · have hmem : x ∈ D.face f ∩ D.circ.region := by
      rw [D.face_region_inter f hf]
      exact Or.inr hl
    exact hmem.2

theorem boundaryImage_subset_image (k : Fin D.vertexCount) :
    (D.vertex k).boundaryImage ⊆ (D.vertex k).image := by
  rw [Vertex.image_eq_range_piece]
  exact image_subset_range _ _

/-- **The boundary of a non-ball vertex** (`μ = 0`): external port tori owned by it, vertex–vertex
seam tori with it on one side, and points of the new zero level. -/
theorem mem_boundaryImage_cases_of_not_isBall (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall)
    {x : W.Carrier} (hx : x ∈ (D.vertex k).boundaryImage) :
    (∃ i t, D.externalOwner i = k ∧ x = E.torusMap i t) ∨
      (∃ c b, D.IsVertexSeam c ∧ D.torusSide c b = some k ∧ x ∈ D.seamTorus c) ∨
      x ∈ D.circ.roundedLevel := by
  have hxk := D.boundaryImage_subset_image k hx
  rw [← D.face_exhausted k] at hx
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
  rcases hkind : D.faceKind f with i | ⟨c, b⟩ | ⟨c, b⟩ | _
  · obtain ⟨hface, howner⟩ := D.face_external f i hkind
    rw [hface] at hxf
    obtain ⟨t, rfl⟩ := hxf
    exact Or.inl ⟨i, t, howner.trans hf, rfl⟩
  · obtain ⟨hface, hside⟩ := D.face_torusSeam f c b hkind
    rw [hf] at hside
    have hxS : x ∈ D.seamTorus c := by
      rw [seamTorus, ← hface]
      exact hxf
    rcases hother : D.torusSide c (!b) with _ | k'
    · exact Or.inr (Or.inr (D.seamTorus_subset_roundedLevel_of_none hbad c b hside hother hxS))
    · have h1 : (D.torusSide c b).isSome := by rw [hside]; rfl
      have h2 : (D.torusSide c (!b)).isSome := by rw [hother]; rfl
      have hc : D.IsVertexSeam c := by
        cases b
        · exact ⟨h2, h1⟩
        · exact ⟨h1, h2⟩
      exact Or.inr (Or.inl ⟨c, b, hc, hside, hxS⟩)
  · exact absurd c.2 (by omega)
  · have hk' : ∀ h b, D.handleEnd h b ≠ D.faceOwner f := by
      rw [hf]
      exact D.handleEnd_ne_of_not_isBall hbad hk
    have hxR := D.face_subset_region_of_partitioned hkind hk' hxf
    exact Or.inr (Or.inr (D.mem_roundedLevel_of_mem_vertex_of_mem_region k
      (D.handleEnd_ne_of_not_isBall hbad hk) hxk hxR))

/-- **T4a §4 (frozen form).** -/
theorem boundaryImage_subset_of_not_isBall (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall) :
    (D.vertex k).boundaryImage ⊆ E.image ∪
      (⋃ (c : Fin D.torusSeamCount) (_ : D.IsVertexSeam c), D.seamTorus c) ∪
      D.circ.roundedLevel := by
  intro x hx
  rcases D.mem_boundaryImage_cases_of_not_isBall hsph hbad k hk hx with
    ⟨i, t, -, rfl⟩ | ⟨c, -, hc, -, hxc⟩ | hZ
  · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨i, mem_range_self t⟩))
  · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨c, hc, hxc⟩))
  · exact Or.inr hZ

/-- **The boundary of an edge circle lies on the new zero level.** -/
theorem edgeCircle_boundary_subset_roundedLevel (e : Fin D.edgeCircleCount) :
    (D.edgeCircle e).piece.map '' (𝓡∂ 3).boundary (D.edgeCircle e).piece.Piece ⊆
      D.circ.roundedLevel := by
  rintro _ ⟨q, hq, rfl⟩
  exact D.mem_roundedLevel_of_mem_edgeCircle_of_mem_region e (mem_range_self q)
    (D.edgeCircle_vertical e ⟨q, hq, rfl⟩)

/-- **The boundary of a cycle union lies on the new zero level.** -/
theorem roundedUnion_boundary_subset_roundedLevel (P : D.CyclePartition) (j : Fin P.cnt) :
    (P.roundedUnion j).map '' (𝓡∂ 3).boundary (P.roundedUnion j).Piece ⊆ D.circ.roundedLevel := by
  rw [P.image_boundary_roundedUnion, D.circ.roundedLevel_eq]
  exact inter_subset_right

/-- **B2-side input for a vertex–vertex seam.** The vertex on side `b` meets the seam collar exactly
in the closed side-`b` half collar. -/
theorem range_vertex_inter_collar_target {c : Fin D.torusSeamCount} (hc : D.IsVertexSeam c)
    (b : Bool) {k : Fin D.vertexCount} (hk : D.torusSide c b = some k) :
    range (D.vertex k).piece.map ∩ (D.torusSeam c).collar.target =
      (D.torusSeam c).collar ''
        {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2} := by
  obtain ⟨k', hk'⟩ : ∃ k', D.torusSide c (!b) = some k' := by
    cases b
    · exact Option.isSome_iff_exists.mp hc.1
    · exact Option.isSome_iff_exists.mp hc.2
  have hS := (D.torusSeam c).source_eq
  -- every collar point on the closed side `b'` lies in the vertex on that side
  have hclosed : ∀ (b' : Bool) {k₀ : Fin D.vertexCount}, D.torusSide c b' = some k₀ →
      ∀ p ∈ signedCollarSource, (if b' then p.2 ≤ 0 else 0 ≤ p.2) →
        (D.torusSeam c).collar p ∈ (D.vertex k₀).image := by
    intro b' k₀ hk₀ p hp hs
    obtain ⟨h1, h2⟩ := hp
    cases b'
    · have h := D.torusSide_pos c p.1 p.2 hs h2
      rw [hk₀] at h
      exact h
    · have h := D.torusSide_neg c p.1 p.2 h1 hs
      rw [hk₀] at h
      exact h
  apply Subset.antisymm
  · rintro x ⟨hxk, hxT⟩
    have hp := (D.torusSeam c).collar.map_target hxT
    have hxp : (D.torusSeam c).collar ((D.torusSeam c).collar.symm x) = x :=
      (D.torusSeam c).collar.right_inv hxT
    by_cases hs : (if b then ((D.torusSeam c).collar.symm x).2 ≤ 0
        else 0 ≤ ((D.torusSeam c).collar.symm x).2)
    · exact ⟨_, ⟨hS ▸ hp, hs⟩, hxp⟩
    exfalso
    have hs' : (if !b then ((D.torusSeam c).collar.symm x).2 < 0
        else 0 < ((D.torusSeam c).collar.symm x).2) := by
      cases b
      · exact not_le.mp hs
      · exact not_le.mp hs
    have hxO : x ∈ D.openHalfCollar c (!b) := ⟨_, ⟨hS ▸ hp, hs'⟩, hxp⟩
    have hxI := D.openHalfCollar_subset_interior c (!b) hxO
    rw [hk'] at hxI
    change x ∈ interior (D.vertex k').image at hxI
    rw [← Vertex.image_eq_range_piece] at hxk
    by_cases hkk : k' = k
    · subst hkk
      -- both sides are the same vertex: the seam torus is interior, but it is a face
      have hTI : (D.torusSeam c).collar.target ⊆ interior (D.vertex k').image := by
        refine interior_maximal (fun y hy => ?_) (D.torusSeam c).collar.open_target
        have hq := (D.torusSeam c).collar.map_target hy
        have hyq := (D.torusSeam c).collar.right_inv hy
        rw [← hyq]
        by_cases hsy : 0 ≤ ((D.torusSeam c).collar.symm y).2
        · cases b
          · exact hclosed false hk _ (hS ▸ hq) hsy
          · exact hclosed false hk' _ (hS ▸ hq) hsy
        · have hsy' : ((D.torusSeam c).collar.symm y).2 ≤ 0 := le_of_lt (not_le.mp hsy)
          cases b
          · exact hclosed true hk' _ (hS ▸ hq) hsy'
          · exact hclosed true hk _ (hS ▸ hq) hsy'
      obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b k' hk
      have hz : (D.torusSeam c).collar (((D.torusSeam c).collar.symm x).1, 0) ∈ D.face f := by
        rw [(D.face_torusSeam f c b hfk).1]
        exact mem_range_self _
      have hzB := D.face_subset_boundaryImage f hz
      rw [hfo] at hzB
      obtain ⟨q, hq, hqz⟩ := hzB
      have hzT : (D.torusSeam c).collar (((D.torusSeam c).collar.symm x).1, 0) ∈
          (D.torusSeam c).collar.target := by
        apply (D.torusSeam c).collar.map_source
        rw [hS]
        exact ⟨by norm_num, by norm_num⟩
      have hzW := (D.torusSeam c).target_interior hzT
      have hzI := hTI hzT
      rw [Vertex.image_eq_range_piece, ← hqz] at hzI
      rw [← hqz] at hzW
      exact (D.vertex k').piece.map_not_mem_interior_range hq hzW hzI
    · exact D.not_mem_interior_of_mem_two hkk hxk hxI
  · rintro _ ⟨p, ⟨hp, hs⟩, rfl⟩
    refine ⟨?_, (D.torusSeam c).collar.map_source (hS ▸ hp)⟩
    rw [← Vertex.image_eq_range_piece]
    exact hclosed b hk p hp hs

end DecompositionCertificate

end GC.GraphManifold.Assembly
