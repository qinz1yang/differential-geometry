import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRP3Pieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRimShrinkApplications

/-!
# FC42 normalization, packet N2a: the split of a bad punctured `ℝP³` vertex

Lane ASM-NRM4 (frozen statement `stub_N2a_split`, `build-logs/scratch/ASM-NRM/Targets.lean` v2;
design of lane ASM-NRM3, approved by main). A bad vertex `k = .zero P (.puncturedRP3 c f hf hr)`
of a certificate without sphere seams is split along the sphere of chart radius `1 + η`
(`η = 1 / (4 max B 1)`, `B` a bound of the derivative of the smooth transition):

* `V₁` = the shell `S² × [0, 1]` between chart radii `1` and `1 + η` (`shellVertex`, a slim
  `sphereInterval` vertex owning the old faces of `k`);
* `V₂` = the pushed punctured `ℝP³` (`pushedVertex`: the same model, `P.map` replaced by
  `Ψ ∘ chartPush c η ∘ f`), whose model boundary is the seam sphere;
* the seam `pushSeam` with collar `(z, s) ↦ Ψ (c ((1 + η + η s / 4) z))`.

N1 (`exists_shrinkRims_avoiding_interior`) first shrinks the rim charts off the compact zone of
heights `[1 + η/2, 1 + 3η/2]` (`pushZone`); then ONE call of the generic split
`exists_vsplit_output` gives the output.

* `DecompositionCertificate.exists_splitPuncturedRP3` (**N2a**). Deviation from the frozen text: the
  instance argument `[ConnectedSpace W.Carrier]` is not used and is dropped (strengthening); the
  verbatim form is kept as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} {P : PieceEmbedding W}
  (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
  {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
  (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)

/-- **The shell vertex** `V₁` of the split: the slim `S² × [0, 1]` vertex between chart radii `1`
and `1 + η`. -/
def shellVertex : Vertex W :=
  .slim (P.shellPiece hf c.closedBall_subset_source hr hη hη4)
    (.sphereInterval (P.shellPieceDiffeo hf c.closedBall_subset_source hr hη hη4))

/-- **The pushed vertex** `V₂` of the split: the punctured `ℝP³` model of `k`, mapped by
`Ψ ∘ chartPush c η ∘ f`. -/
def pushedVertex {B : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hηB : η * B ≤ 1 / 4) :
    Vertex W :=
  .zero (P.pushedPiece hf c.closedBall_subset_source hr hB hη hηB hη4) (.puncturedRP3 c f hf hr)

/-- The seam of the split. -/
def projectiveSeam : SphereSeam W :=
  pushSeam hf c.closedBall_subset_source hr hη hη4

/-- The compact zone of heights `[1 + η/2, 1 + 3η/2]`. -/
def pushZone (P : PieceEmbedding W) (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
    (η : ℝ) : Set W.Carrier :=
  range P.map ∩ P.pushHeight f c.chart ⁻¹' Icc (1 + η / 2) (1 + 3 * η / 2)

theorem image_shellVertex : (shellVertex c hf hr hη hη4).image = range (P.shellMap f c.chart η) :=
  rfl

theorem image_pushedVertex {B : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hηB : η * B ≤ 1 / 4) :
    (pushedVertex c hf hr hη hη4 hB hηB).image = range (P.pushedMap f c.chart η) :=
  rfl

include hf in
theorem isCompact_pushZone : IsCompact (pushZone c P f η) :=
  ((continuousOn_pushHeight hf c.closedBall_subset_source).preimage_isClosed_of_isClosed
    P.isClosed_range isClosed_Icc).isCompact

include hf hr hη in
theorem pushZone_subset : pushZone c P f η ⊆ interior (range P.map) ∩ W.interior := by
  rintro x ⟨hx, hh⟩
  exact mem_interior_of_one_lt_pushHeight hf c.closedBall_subset_source hr hx
    (by linarith [hh.1])

include hη hη4 in
theorem projectiveSeam_target_subset :
    (projectiveSeam c hf hr hη hη4).collar.target ⊆ pushZone c P f η := by
  rw [projectiveSeam, pushSeam_target]
  rintro _ ⟨p, hp, rfl⟩
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  refine ⟨transfer_mem_range _, ?_⟩
  change P.pushHeight f c.chart (P.collarMap f c.chart η p) ∈ Icc (1 + η / 2) (1 + 3 * η / 2)
  rw [pushHeight_collarMap hf c.closedBall_subset_source hr hη hη4 hs]
  constructor <;> nlinarith [hs.1, hs.2]

theorem projectiveSeam_collar_apply (p : ClosureSphere.{u} × ℝ) :
    (projectiveSeam c hf hr hη hη4).collar p = P.collarMap f c.chart η p :=
  pushSeam_collar_apply hf c.closedBall_subset_source hr hη hη4 p

theorem zeroSphere_projectiveSeam :
    (projectiveSeam c hf hr hη hη4).zeroSphere =
      range fun z => P.shellMap f c.chart η (z, iccOne) := by
  unfold SphereSeam.zeroSphere
  congr 1
  funext z
  rw [projectiveSeam_collar_apply, collarMap_zero]

theorem sphereLevel_shellPiece (t : Icc (0 : ℝ) 1) :
    (P.shellPiece hf c.closedBall_subset_source hr hη hη4).sphereLevel
        (P.shellPieceDiffeo hf c.closedBall_subset_source hr hη hη4) t =
      range fun z => P.shellMap f c.chart η (z, t) :=
  rfl

end PieceEmbedding

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

section Projective

variable {D : DecompositionCertificate W E} {k : Fin D.vertexCount} {P : PieceEmbedding W}
  {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
  {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
  {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}

theorem image_eq_of_puncturedRP3 (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) :
    (D.vertex k).image = range P.map := by
  rw [hv]
  rfl

theorem boundaryImage_eq_of_puncturedRP3 (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) :
    (D.vertex k).boundaryImage = P.map '' (𝓡∂ 3).boundary P.Piece := by
  rw [hv]
  rfl

/-- The model boundary of a punctured `ℝP³` vertex is the bottom sphere of any thin shell. -/
theorem boundaryImage_eq_sphereLevel_of_puncturedRP3
    (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    (D.vertex k).boundaryImage =
      (P.shellPiece hf c.closedBall_subset_source hr hη hη4).sphereLevel
        (P.shellPieceDiffeo hf c.closedBall_subset_source hr hη hη4) iccZero := by
  rw [boundaryImage_eq_of_puncturedRP3 hv,
    P.image_boundary_eq_shellMap_zero hf c.closedBall_subset_source hr hη hη4]
  rfl

/-- **The faces of a punctured `ℝP³` vertex**: each is its whole boundary sphere. -/
theorem face_eq_sphereLevel_of_puncturedRP3
    (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (f' : Fin D.faceCount) (hf' : D.faceOwner f' = k) :
    D.face f' = (P.shellPiece hf c.closedBall_subset_source hr hη hη4).sphereLevel
        (P.shellPieceDiffeo hf c.closedBall_subset_source hr hη hη4) iccZero := by
  have hB := boundaryImage_eq_sphereLevel_of_puncturedRP3 hv hη hη4
  have hpre : IsPreconnected (D.vertex k).boundaryImage := by
    rw [hB]
    exact PieceEmbedding.isPreconnected_sphereLevel _ _ _
  rw [D.face_eq_boundaryImage_of_isPreconnected hpre f' hf', hB]

/-- A punctured `ℝP³` vertex is no torus side. -/
theorem torusSide_ne_of_puncturedRP3 (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr))
    (c' : Fin D.torusSeamCount) (b : Bool) : D.torusSide c' b ≠ some k := by
  intro hs
  obtain ⟨f', hfo, hfk⟩ := D.torusSeam_face c' b k hs
  have hface := (D.face_torusSeam f' c' b hfk).1
  have hsrc0 : ∀ t : Torus, (t, (0 : ℝ)) ∈ (D.torusSeam c').collar.source := fun t => by
    rw [(D.torusSeam c').source_eq]
    exact ⟨by norm_num, by norm_num⟩
  have hcont : Continuous fun t : Torus => (D.torusSeam c').collar (t, 0) :=
    (D.torusSeam c').collar.contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) hsrc0
  have hinj : Injective fun t : Torus => (D.torusSeam c').collar (t, 0) := fun t t' h =>
    congrArg Prod.fst ((D.torusSeam c').collar.injOn (hsrc0 t) (hsrc0 t') h)
  exact PieceEmbedding.false_of_sphereLevel_eq_range_torus _ _ hcont hinj
    ((face_eq_sphereLevel_of_puncturedRP3 hv (η := 1 / 4) (by norm_num) le_rfl f' hfo).symm.trans
      hface)

/-- A punctured `ℝP³` vertex owns no external port. -/
theorem externalOwner_ne_of_puncturedRP3 (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr))
    (i : Fin n) : D.externalOwner i ≠ k := by
  intro hi
  obtain ⟨f', hfk⟩ := D.external_face i
  obtain ⟨hface, hown⟩ := D.face_external f' i hfk
  exact PieceEmbedding.false_of_sphereLevel_eq_range_torus _ _
    (E.torusMap_isEmbedding i).continuous (E.torusMap_isEmbedding i).injective
    ((face_eq_sphereLevel_of_puncturedRP3 hv (η := 1 / 4) (by norm_num) le_rfl f'
      (hown.symm.trans hi)).symm.trans hface)

section Split

variable (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) {η : ℝ} (hη : 0 < η)
  (hη4 : η ≤ 1 / 4) {B : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hηB : η * B ≤ 1 / 4)

include hv hB hηB in
/-- The two vertices of the split cover the old vertex. -/
theorem shellVertex_union_pushedVertex :
    (PieceEmbedding.shellVertex c hf hr hη hη4).image ∪
        (PieceEmbedding.pushedVertex c hf hr hη hη4 hB hηB).image = (D.vertex k).image := by
  rw [PieceEmbedding.image_shellVertex, PieceEmbedding.image_pushedVertex,
    image_eq_of_puncturedRP3 hv]
  ext x
  rw [mem_union, PieceEmbedding.mem_range_shellMap_iff hf c.closedBall_subset_source hr hη hη4,
    PieceEmbedding.mem_range_pushedMap_iff hf c.closedBall_subset_source hr hB hη hηB hη4]
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · intro hx
    rcases le_total (P.pushHeight f c.chart x) (1 + η) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

include hB hηB in
/-- The interiors of the two vertices of the split are disjoint. -/
theorem disjoint_interior_shellVertex_pushedVertex :
    Disjoint (interior (PieceEmbedding.shellVertex c hf hr hη hη4).image)
      (interior (PieceEmbedding.pushedVertex c hf hr hη hη4 hB hηB).image) := by
  have hc := c.closedBall_subset_source
  rw [PieceEmbedding.image_shellVertex, PieceEmbedding.image_pushedVertex, Set.disjoint_left]
  intro x hx1 hx2
  obtain ⟨p, rfl⟩ := interior_subset hx1
  have hge := ((PieceEmbedding.mem_range_pushedMap_iff hf hc hr hB hη hηB hη4).mp
    (interior_subset hx2)).2
  rw [PieceEmbedding.pushHeight_shellMap hf hc hr hη hη4] at hge
  have hp2 : (p.2 : ℝ) = 1 := by nlinarith [p.2.2.2]
  have hp : p = (p.1, iccOne) := Prod.ext rfl (Subtype.ext hp2)
  rw [hp, ← PieceEmbedding.collarMap_zero] at hx1
  let g : ℝ → W.Carrier := fun s => P.collarMap f c.chart η (p.1, s)
  have hsrc : ((p.1, (0 : ℝ)) : ClosureSphere.{u} × ℝ) ∈ sphereSignedCollarSource :=
    ⟨mem_univ _, by norm_num, by norm_num⟩
  have hloc := PieceEmbedding.isLocalDiffeomorphOn_collarMap hf hc hr hη hη4 ⟨_, hsrc⟩
  have hloc' : ContinuousAt (P.collarMap f c.chart η) (p.1, (0 : ℝ)) :=
    hloc.contMDiffAt.continuousAt
  have hin : ContinuousAt (fun s : ℝ => ((p.1, s) : ClosureSphere.{u} × ℝ)) 0 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hg : ContinuousAt g 0 := ContinuousAt.comp (g := P.collarMap f c.chart η) hloc' hin
  have hN : g ⁻¹' interior (range (P.shellMap f c.chart η)) ∈ 𝓝 (0 : ℝ) :=
    hg.preimage_mem_nhds (isOpen_interior.mem_nhds hx1)
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  set s := min (b / 2) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by norm_num)
  have hsb : s < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hgs := interior_subset (hab ⟨by linarith, hsb⟩)
  obtain ⟨-, hle⟩ := (PieceEmbedding.mem_range_shellMap_iff hf hc hr hη hη4).mp hgs
  have hh := PieceEmbedding.pushHeight_collarMap hf hc hr hη hη4
    (p := (p.1, s)) ⟨by linarith, hs1⟩
  change P.pushHeight f c.chart (P.collarMap f c.chart η (p.1, s)) ≤ 1 + η at hle
  rw [hh] at hle
  have : 0 < η / 4 * s := by positivity
  linarith

include hη4 in
theorem projectiveSeam_mem_shellVertex (z : ClosureSphere.{u}) (s : ℝ) (hs0 : s ≤ 0)
    (hs1 : -1 < s) :
    (PieceEmbedding.projectiveSeam c hf hr hη hη4).collar (z, s) ∈
      (PieceEmbedding.shellVertex c hf hr hη hη4).image := by
  rw [PieceEmbedding.projectiveSeam_collar_apply, PieceEmbedding.collarMap_eq_shellMap hs1 hs0]
  exact ⟨_, rfl⟩

include hB hηB in
theorem projectiveSeam_mem_pushedVertex (z : ClosureSphere.{u}) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (PieceEmbedding.projectiveSeam c hf hr hη hη4).collar (z, s) ∈
      (PieceEmbedding.pushedVertex c hf hr hη hη4 hB hηB).image := by
  have hc := c.closedBall_subset_source
  rw [PieceEmbedding.projectiveSeam_collar_apply, PieceEmbedding.image_pushedVertex,
    PieceEmbedding.mem_range_pushedMap_iff hf hc hr hB hη hηB hη4,
    PieceEmbedding.pushHeight_collarMap hf hc hr hη hη4 (p := (z, s)) ⟨by linarith, hs1⟩]
  refine ⟨PieceEmbedding.transfer_mem_range _, ?_⟩
  have : 0 ≤ η / 4 * s := by positivity
  change 1 + η ≤ 1 + η + η / 4 * s
  linarith

include hv in
theorem projectiveSeam_target_subset_interior :
    (PieceEmbedding.projectiveSeam c hf hr hη hη4).collar.target ⊆
      interior (D.vertex k).image := by
  rw [image_eq_of_puncturedRP3 hv]
  exact fun x hx => (PieceEmbedding.pushZone_subset c hf hr hη
    (PieceEmbedding.projectiveSeam_target_subset c hf hr hη hη4 hx)).1

include hv in
theorem boundaryImage_shellVertex :
    (PieceEmbedding.shellVertex c hf hr hη hη4).boundaryImage =
      (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = k)
        (_ : (fun _ => true : Fin D.faceCount → Bool) f' = true), D.face f') ∪
        (PieceEmbedding.projectiveSeam c hf hr hη hη4).zeroSphere := by
  have h1 : (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = k)
      (_ : (fun _ => true : Fin D.faceCount → Bool) f' = true), D.face f') =
      (D.vertex k).boundaryImage := by
    rw [← D.face_exhausted k]
    simp only [iUnion_true]
  rw [h1, boundaryImage_eq_sphereLevel_of_puncturedRP3 hv hη hη4,
    PieceEmbedding.zeroSphere_projectiveSeam]
  exact PieceEmbedding.image_boundary_sphereInterval _ _

include hB hηB in
theorem boundaryImage_pushedVertex :
    (PieceEmbedding.pushedVertex c hf hr hη hη4 hB hηB).boundaryImage =
      (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = k)
        (_ : (fun _ => true : Fin D.faceCount → Bool) f' = false), D.face f') ∪
        (PieceEmbedding.projectiveSeam c hf hr hη hη4).zeroSphere := by
  have h1 : (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = k)
      (_ : (fun _ => true : Fin D.faceCount → Bool) f' = false), D.face f') = ∅ := by
    simp
  rw [h1, empty_union, PieceEmbedding.zeroSphere_projectiveSeam]
  exact PieceEmbedding.image_boundary_pushedMap hf c.closedBall_subset_source hr

include hv in
/-- No face meets the seam sphere. -/
theorem disjoint_face_projectiveSeam (f' : Fin D.faceCount) :
    Disjoint (D.face f') (PieceEmbedding.projectiveSeam c hf hr hη hη4).zeroSphere := by
  by_cases hf' : D.faceOwner f' = k
  · rw [face_eq_sphereLevel_of_puncturedRP3 hv hη hη4 f' hf',
      PieceEmbedding.zeroSphere_projectiveSeam,
      ← PieceEmbedding.sphereLevel_shellPiece c hf hr hη hη4]
    refine PieceEmbedding.disjoint_sphereLevel _ _ fun h => ?_
    have := congrArg Subtype.val h
    norm_num [iccZero, iccOne] at this
  · have hsub : D.face f' ⊆ (D.vertex (D.faceOwner f')).image := by
      refine (D.face_subset_boundaryImage f').trans ?_
      rw [Vertex.image_eq_range_piece]
      exact image_subset_range _ _
    have hS : (PieceEmbedding.projectiveSeam c hf hr hη hη4).zeroSphere ⊆
        interior (D.vertex k).image :=
      (SphereSeam.zeroSphere_subset_target _).trans
        (projectiveSeam_target_subset_interior hv hη hη4)
    exact ((D.disjoint_interior_image_vertex hf').mono hS hsub).symm

include hv in
/-- **The vertex side of a rim chart at the split vertex stays in the shell**, when the rim chart
target avoids the zone of heights `[1 + η/2, 1 + 3η/2]`. -/
theorem rimChart_mem_shellVertex {h : Fin D.handleCount} {b : Bool} (hk : D.handleEnd h b = k)
    (hrim : Disjoint (D.rimChart h b).target (PieceEmbedding.pushZone c P f η))
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart h b).source) (hp2 : p.2.2 ≤ 0) :
    D.rimChart h b p ∈ (PieceEmbedding.shellVertex c hf hr hη hη4).image := by
  have hc := c.closedBall_subset_source
  rw [PieceEmbedding.image_shellVertex]
  set χ := D.rimChart h b with hχ
  let A : Set (Circle × (ℝ × ℝ)) := {p | p ∈ χ.source ∧ p.2.2 ≤ 0}
  have hA : A = univ ×ˢ (Ioo (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 0) := by
    ext q
    have hs : q ∈ χ.source ↔ q.2 ∈ rimBox 2 := D.rim_source h b
    constructor
    · rintro ⟨hq, h3⟩
      obtain ⟨h1, h2⟩ := hs.mp hq
      exact ⟨mem_univ _, abs_lt.mp h1, ⟨(abs_lt.mp h2).1, h3⟩⟩
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨hs.mpr ⟨abs_lt.mpr h1, abs_lt.mpr ⟨h2, by linarith⟩⟩, h3⟩
  have hApre : IsPreconnected A := by
    rw [hA]
    exact isPreconnected_univ.prod (isPreconnected_Ioo.prod isPreconnected_Ioc)
  have hCpre : IsPreconnected (χ '' A) :=
    hApre.image _ (χ.contMDiffOn.continuousOn.mono fun q hq => hq.1)
  have hCsub : χ '' A ⊆ range P.map := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← image_eq_of_puncturedRP3 hv, ← hk]
    exact (D.rim_vertex h b hq.1).mpr hq.2
  have hH : IsPreconnected (P.pushHeight f c.chart '' (χ '' A)) :=
    hCpre.image _ ((PieceEmbedding.continuousOn_pushHeight hf hc).mono hCsub)
  have hp₀ : ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ A :=
    ⟨(D.rim_source h b).mpr ⟨by norm_num, by norm_num⟩, le_rfl⟩
  have hx₀ : χ ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ D.face (D.handleFace h b) := by
    apply D.handleEnd_face h b
    have hmem : χ ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ χ '' {q | q.2 = (0, 0)} := ⟨_, rfl, rfl⟩
    rw [hχ, D.rim_label h b] at hmem
    obtain ⟨y, -, hy⟩ := hmem
    exact ⟨y, hy⟩
  rw [face_eq_sphereLevel_of_puncturedRP3 hv hη hη4 _ ((D.handleFace_owner h b).trans hk),
    PieceEmbedding.sphereLevel_shellPiece] at hx₀
  obtain ⟨z₀, hz₀⟩ := hx₀
  have hh₀ : P.pushHeight f c.chart (χ ((1 : Circle), ((0 : ℝ), (0 : ℝ)))) = 1 := by
    rw [← hz₀, PieceEmbedding.pushHeight_shellMap hf hc hr hη hη4]
    change 1 + η * 0 = 1
    ring
  have hxp : χ p ∈ χ '' A := ⟨p, ⟨hp, hp2⟩, rfl⟩
  have hxr := hCsub hxp
  refine (PieceEmbedding.mem_range_shellMap_iff hf hc hr hη hη4).mpr ⟨hxr, not_lt.mp fun hlt => ?_⟩
  have hin₀ : (1 : ℝ) ∈ P.pushHeight f c.chart '' (χ '' A) := ⟨_, ⟨_, hp₀, rfl⟩, hh₀⟩
  have hinp : P.pushHeight f c.chart (χ p) ∈ P.pushHeight f c.chart '' (χ '' A) := ⟨_, hxp, rfl⟩
  obtain ⟨x, hx, hx2⟩ := hH.Icc_subset hin₀ hinp ⟨by linarith, hlt.le⟩
  obtain ⟨q, hq, rfl⟩ := hx
  refine Set.disjoint_left.mp hrim (χ.map_source hq.1) ⟨hCsub ⟨q, hq, rfl⟩, ?_⟩
  change P.pushHeight f c.chart (χ q) ∈ Icc (1 + η / 2) (1 + 3 * η / 2)
  rw [hx2]
  constructor <;> linarith

end Split

end Projective

/-- **N2a. The split of a bad punctured `ℝP³` vertex** along the parallel sphere of chart radius
`1 + η` (after N1): a certificate on the same `W, E` with one sphere seam whose non-side bad
vertices are at most the bad vertices of `D` other than `k`, without closed zero vertices,
inheriting the rim-product clause. -/
theorem exists_splitPuncturedRP3 (D : DecompositionCertificate W E)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet)
    {P : PieceEmbedding W}
    {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤
        D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) := by
  obtain ⟨B, hB0, hB⟩ := exists_deriv_smoothTransition_bound
  set η : ℝ := 1 / (4 * max B 1) with hηdef
  have hM : 1 ≤ max B 1 := le_max_right _ _
  have hη : 0 < η := by positivity
  have hη4 : η ≤ 1 / 4 := by
    rw [hηdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hηB : η * B ≤ 1 / 4 := by
    rw [hηdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [le_max_left B 1]
  have hK : PieceEmbedding.pushZone c P f η ⊆ interior (D.vertex k).image ∩ W.interior := by
    rw [image_eq_of_puncturedRP3 hv]
    exact PieceEmbedding.pushZone_subset c hf hr hη
  obtain ⟨ε, hε, hε1, hdisj, -, -, hrp⟩ :=
    D.exists_shrinkRims_avoiding_interior (PieceEmbedding.isCompact_pushZone c hf) hK
  have hσ' : (D.shrinkRims ε hε hε1).sphereSeamCount = 0 := hσ
  have hv' : (D.shrinkRims ε hε hε1).vertex k = .zero P (.puncturedRP3 c f hf hr) := hv
  have hk' : k ∈ (D.shrinkRims ε hε hε1).badVertexSet := by
    rw [D.badVertexSet_shrinkRims ε hε hε1]
    exact hk
  have hnz' : ∀ j C, (D.shrinkRims ε hε hε1).vertex j ≠ .closedZero C := hnz
  let S := PieceEmbedding.projectiveSeam c hf hr hη hη4
  let μ : S.zeroSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (Homeomorph.setCongr ((PieceEmbedding.zeroSphere_projectiveSeam c hf hr hη hη4).trans
      (PieceEmbedding.sphereLevel_shellPiece c hf hr hη hη4 iccOne).symm)).trans
      (PieceEmbedding.sphereLevelHomeomorph _ _ iccOne)
  obtain ⟨D'', c'', h1, hcount, hnz'', hrp''⟩ :=
    exists_vsplit_output (D := D.shrinkRims ε hε hε1) hσ' k
    (PieceEmbedding.shellVertex c hf hr hη hη4) (PieceEmbedding.pushedVertex c hf hr hη hη4 hB hηB)
    S (fun _ => true) μ (shellVertex_union_pushedVertex hv' hη hη4 hB hηB)
    (disjoint_interior_shellVertex_pushedVertex hη hη4 hB hηB)
    (projectiveSeam_mem_shellVertex hη hη4) (projectiveSeam_mem_pushedVertex hη hη4 hB hηB)
    (projectiveSeam_target_subset_interior hv' hη hη4) (torusSide_ne_of_puncturedRP3 hv')
    (externalOwner_ne_of_puncturedRP3 hv') (boundaryImage_shellVertex hv' hη hη4)
    (boundaryImage_pushedVertex hη hη4 hB hηB) (disjoint_face_projectiveSeam hv' hη hη4)
    (fun h b _ hk hp hp2 => rimChart_mem_shellVertex hv' hη hη4 hk
      ((hdisj h b).mono_right subset_rfl) hp hp2)
    (fun h b => (hdisj h b).mono_right (PieceEmbedding.projectiveSeam_target_subset c hf hr hη hη4))
    hk' hnz' (fun C h => by cases h) (fun C h => by cases h)
  exact ⟨D'', c'', h1, hcount.trans_eq (D.badVertexCount_shrinkRims ε hε hε1), hnz'',
    fun hD => hrp'' (hrp hD)⟩

/-- The frozen form of N2a (`stub_N2a_split`), with its unused connectedness instance. -/
example [ConnectedSpace W.Carrier] (D : DecompositionCertificate W E)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet)
    {P : PieceEmbedding W}
    {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤ D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) :=
  D.exists_splitPuncturedRP3 hnz hσ hk hv

/-- **Consumer: the split step without sphere seams.** With no sphere seam, no closed zero vertex
and positive measure, a split certificate with one sphere seam and fewer non-side bad vertices
exists (N2a at a bad punctured `ℝP³` vertex, N3a at a bad `S² × I` vertex). -/
theorem exists_split_of_sphereMeasure_pos (D : DecompositionCertificate W E)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    (hμ : 0 < D.sphereMeasure) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤
        D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) := by
  rcases D.exists_puncturedRP3_or_splitSphereInterval hnz hσ hμ with
    ⟨k, hk, P, c, f, hf, hr, hv⟩ | h
  · exact D.exists_splitPuncturedRP3 hnz hσ hk hv
  · exact h

end DecompositionCertificate

end GC.GraphManifold.Assembly
