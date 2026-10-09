import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyLevel
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary

/-!
# FC42 packet T4a §0: with `μ = 0`, the non-ball vertices are torus-faced

A vertex of a V4 certificate is a ball, a solid torus, a twisted `I`-bundle, a punctured `ℝP³`, a
closed zero piece, a slim `S² × I`, `T² × I` or closed piece over the circle, or a cusp core. With
no sphere seam and no bad vertex (`μ(D) = 0`), a face of a NON-ball vertex is never a two-sphere
(`false_of_face_homeomorph_sphereTwo`: external and torus-seam faces are tori, a partitioned
two-sphere face makes the owner bad, and a torus model is not a sphere). The punctured `ℝP³` and the
`S² × I` models have a two-sphere boundary component (`exists_sphereTwo_boundary_of_puncturedRP3`,
`exists_sphereTwo_boundary_of_sphereInterval`), which would be a face
(`false_of_sphereTwo_boundary_component`). With the closed zero and closed slim branches excluded
(they are the other branches of the dry FC42), the non-ball vertices are the four torus-faced models
(`torusFaced_of_not_isBall`), the input of `Vertex.rawPiece_of_torusFaced`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The boundary of a punctured `ℝP³` piece is a two-sphere.** -/
theorem PieceEmbedding.exists_sphereTwo_boundary_of_puncturedRP3 {W : CompactCarrier.{u}}
    (P : PieceEmbedding W)
    (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
    (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
    (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hrange : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}) :
    ∃ g : SphereTwo → W.Carrier, Continuous g ∧ Injective g ∧
      range g = P.map '' (𝓡∂ 3).boundary P.Piece := by
  have hsrc : ∀ z : SphereTwo, z.1 ∈ c.chart.source := fun z =>
    c.closedBall_subset_source (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by norm_num)) z.2)
  have hbd : f '' (𝓡∂ 3).boundary P.Piece =
      c.chart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rw [DifferentialGeometry.Geometry.Boundary.image_boundary_eq_frontier_of_fullRank_closedEmbedding
      f hf.contMDiff (hf.contMDiff.continuous.isClosedEmbedding hf.isEmbedding.injective)
      (fun x => (hf.isImmersion.isImmersionAt x).mfderiv_injective (by simp)) (by simp), hrange]
    change frontier (c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ = _
    rw [frontier_compl]
    exact DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph c.chart
      ((Metric.closedBall_subset_closedBall (by norm_num)).trans c.closedBall_subset_source)
  have hsub : range (fun z : SphereTwo => c.chart z.1) ⊆ range f := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨q, -, hq⟩ : c.chart z.1 ∈ f '' (𝓡∂ 3).boundary P.Piece :=
      hbd ▸ mem_image_of_mem _ z.2
    exact ⟨q, hq⟩
  have hcc : Continuous fun z : SphereTwo => c.chart z.1 :=
    c.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc
  let l : SphereTwo → P.Piece := fun z =>
    hf.isEmbedding.toHomeomorph.symm ⟨c.chart z.1, hsub (mem_range_self z)⟩
  have hl : ∀ z, f (l z) = c.chart z.1 := fun z =>
    congrArg Subtype.val (hf.isEmbedding.toHomeomorph.apply_symm_apply _)
  have hlc : Continuous l :=
    hf.isEmbedding.toHomeomorph.symm.continuous.comp (hcc.subtype_mk _)
  refine ⟨fun z => P.map (l z), P.continuous_map.comp hlc, fun z z' h => ?_, ?_⟩
  · have h1 := congrArg f (P.injective h)
    rw [hl, hl] at h1
    exact Subtype.ext (c.chart.injOn (hsrc z) (hsrc z') h1)
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨q, hq, hqz⟩ : c.chart z.1 ∈ f '' (𝓡∂ 3).boundary P.Piece :=
        hbd ▸ mem_image_of_mem _ z.2
      have hql : q = l z := hf.isEmbedding.injective (hqz.trans (hl z).symm)
      exact ⟨q, hq, by rw [hql]⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, hy, hyq⟩ : f q ∈ c.chart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        hbd ▸ mem_image_of_mem _ hq
      have hlq : l ⟨y, hy⟩ = q := hf.isEmbedding.injective ((hl _).trans hyq)
      exact ⟨⟨y, hy⟩, congrArg P.map hlq⟩

/-- **The boundary of an `S² × I` piece is two disjoint two-spheres.** -/
theorem PieceEmbedding.exists_sphereTwo_boundary_of_sphereInterval {W : CompactCarrier.{u}}
    (P : PieceEmbedding W)
    (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece) :
    ∃ g₀ g₁ : SphereTwo → W.Carrier, Continuous g₀ ∧ Continuous g₁ ∧ Injective g₀ ∧
      P.map '' (𝓡∂ 3).boundary P.Piece = range g₀ ∪ range g₁ ∧
      Disjoint (range g₀) (range g₁) := by
  have hbd : ∀ q : P.Piece, q ∈ (𝓡∂ 3).boundary P.Piece ↔
      (e.symm q).2 = ⊥ ∨ (e.symm q).2 = ⊤ := by
    intro q
    rw [← Diffeomorph.preimage_boundary (by simp) e.symm, mem_preimage, boundary_product]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  let g : Icc (0 : ℝ) 1 → SphereTwo → W.Carrier := fun b z => P.map (e (ULift.up z, b))
  have hg : ∀ b, Continuous (g b) := fun b =>
    P.continuous_map.comp (e.continuous.comp (continuous_uliftUp.prodMk continuous_const))
  have hinj : ∀ b, Injective (g b) := fun b z z' h => by
    have h1 := e.injective (P.injective h)
    exact ULift.up_injective (congrArg Prod.fst h1)
  have heq : ∀ q : P.Piece, e (ULift.up (e.symm q).1.down, (e.symm q).2) = q := fun q =>
    e.apply_symm_apply q
  refine ⟨g ⊥, g ⊤, hg ⊥, hg ⊤, hinj ⊥, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases (hbd q).mp hq with h | h
      · refine Or.inl ⟨(e.symm q).1.down, ?_⟩
        change P.map (e (ULift.up (e.symm q).1.down, ⊥)) = P.map q
        rw [← h, heq]
      · refine Or.inr ⟨(e.symm q).1.down, ?_⟩
        change P.map (e (ULift.up (e.symm q).1.down, ⊤)) = P.map q
        rw [← h, heq]
    · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · exact ⟨e (ULift.up z, ⊥), (hbd _).mpr (Or.inl (by rw [e.symm_apply_apply])), rfl⟩
      · exact ⟨e (ULift.up z, ⊤), (hbd _).mpr (Or.inr (by rw [e.symm_apply_apply])), rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨z', h⟩
    have h1 := congrArg (fun p => (p.2 : ℝ)) (e.injective (P.injective h))
    simp only [Set.Icc.coe_top, Set.Icc.coe_bot] at h1
    exact one_ne_zero h1

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **With `μ = 0`, a face of a non-ball vertex is not a two-sphere.** -/
theorem false_of_face_homeomorph_sphereTwo (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) {f : Fin D.faceCount}
    (hf : ¬ (D.vertex (D.faceOwner f)).IsBall) (φ : D.face f ≃ₜ SphereTwo) : False := by
  rcases hkind : D.faceKind f with i | ⟨c, b⟩ | ⟨c, b⟩ | _
  · have hface := (D.face_external f i hkind).1
    have hT := E.torusMap_isEmbedding i
    exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ
      ((Homeomorph.setCongr hface).trans (homeomorphRangeOfTorus hT.continuous hT.injective))
  · have hface := (D.face_torusSeam f c b hkind).1
    have hsrc : ∀ t : Circle × Circle, (t, (0 : ℝ)) ∈ (D.torusSeam c).collar.source := by
      intro t
      rw [(D.torusSeam c).source_eq]
      exact ⟨by norm_num, by norm_num⟩
    have hcont : Continuous fun t : Circle × Circle => (D.torusSeam c).collar (t, 0) :=
      (D.torusSeam c).collar.contMDiffOn.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) hsrc
    have hinj : Injective fun t : Circle × Circle => (D.torusSeam c).collar (t, 0) := by
      intro t t' h
      exact congrArg Prod.fst ((D.torusSeam c).collar.injOn (hsrc t) (hsrc t') h)
    exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ
      ((Homeomorph.setCongr hface).trans (homeomorphRangeOfTorus hcont hinj))
  · exact absurd c.2 (by omega)
  · rcases hm : D.faceModel f with e | ψ
    · exact hf (D.partitionedSphereFace_ball_of_badVertexCount_eq_zero hbad f hkind ⟨e, hm⟩)
    · exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ ψ

/-- **With `μ = 0`, a non-ball vertex has no two-sphere boundary component.** A two-sphere in the
model-boundary image that is separated from the rest of it by a closed set would be a whole face. -/
theorem false_of_sphereTwo_boundary_component (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall)
    {g : SphereTwo → W.Carrier} (hg : Continuous g) (hinj : Injective g)
    (hgB : range g ⊆ (D.vertex k).boundaryImage) {T : Set W.Carrier} (hT : IsClosed T)
    (hcov : (D.vertex k).boundaryImage ⊆ range g ∪ T) (hdisj : Disjoint (range g) T) : False := by
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3)))
    (r := 1)).mpr zero_le_one
  have hzB : g ⟨z, hz⟩ ∈ (D.vertex k).boundaryImage := hgB (mem_range_self _)
  rw [← D.face_exhausted k] at hzB
  obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hzB
  have hgf : range g ⊆ D.face f := by
    subst hf
    exact D.subset_face_of_isPreconnected f (isPreconnected_range hg) hgB (mem_range_self _) hzf
  have hfg : D.face f ⊆ range g := by
    have hpre := (D.isConnected_face f).isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
    have hFB : D.face f ⊆ (D.vertex k).boundaryImage := hf ▸ D.face_subset_boundaryImage f
    rcases hpre _ _ (isCompact_range hg).isClosed hT (hFB.trans hcov)
        (by rw [hdisj.inter_eq, inter_empty]) with h | h
    · exact h
    · exact absurd (h hzf) (Set.disjoint_left.mp hdisj (mem_range_self _))
  have hk' : ¬ (D.vertex (D.faceOwner f)).IsBall := by
    rw [hf]
    exact hk
  exact D.false_of_face_homeomorph_sphereTwo hsph hbad hk'
    ((Homeomorph.setCongr (hfg.antisymm hgf)).trans
      ((hg.isClosedEmbedding hinj).isEmbedding.toHomeomorph).symm)

/-- **T4a §0: with `μ = 0`, the non-ball vertices are torus-faced** (closed zero pieces and closed
slim pieces over the circle excluded). -/
theorem torusFaced_of_not_isBall (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall) :
    (∃ P e, D.vertex k = .zero P (.solidTorus e)) ∨
      (∃ P e, D.vertex k = .zero P (.twistedIBundle e)) ∨
      (∃ P e, D.vertex k = .slim P (.torusInterval e)) ∨ (∃ P e, D.vertex k = .cuspCore P e) := by
  rcases hv : D.vertex k with ⟨P, m⟩ | C | ⟨P, m⟩ | ⟨P, e⟩
  · rcases m with e | e | e | ⟨c, f, hf, hrange⟩
    · exact (hk ⟨P, e, hv⟩).elim
    · exact Or.inl ⟨P, e, rfl⟩
    · exact Or.inr (Or.inl ⟨P, e, rfl⟩)
    · exfalso
      obtain ⟨g, hg, hinj, hrg⟩ := P.exists_sphereTwo_boundary_of_puncturedRP3 c f hf hrange
      have hB : (D.vertex k).boundaryImage = range g := by
        rw [hv]
        exact hrg.symm
      exact D.false_of_sphereTwo_boundary_component hsph hbad k hk hg hinj hB.ge isClosed_empty
        (by rw [hB, union_empty]) (disjoint_empty _)
  · exact (hnz k C hv).elim
  · rcases m with e | e | ⟨p, hp, hsub, fib, hcl⟩
    · exfalso
      obtain ⟨g₀, g₁, hg₀, hg₁, hinj, hrg, hdisj⟩ := P.exists_sphereTwo_boundary_of_sphereInterval e
      have hB : (D.vertex k).boundaryImage = range g₀ ∪ range g₁ := by
        rw [hv]
        exact hrg
      exact D.false_of_sphereTwo_boundary_component hsph hbad k hk hg₀ hinj
        (hB ▸ subset_union_left) (isCompact_range hg₁).isClosed hB.le hdisj
    · exact Or.inr (Or.inr (Or.inl ⟨P, e, rfl⟩))
    · exact (hslim ⟨k, P, p, hp, hsub, fib, hcl, hv⟩).elim
  · exact Or.inr (Or.inr (Or.inr ⟨P, e, rfl⟩))

end DecompositionCertificate

end GC.GraphManifold.Assembly
