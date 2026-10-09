import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSphereFacesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleBallVertex

/-!
# FC42 packet H2-a: ball vertices own exactly one face, a partitioned two-sphere

For a `DecompositionCertificate W E` (V4) and a ball vertex (`Vertex.IsBall`,
`AssemblyCycleBallVertex.lean`, whose model boundary image is a two-sphere,
`Vertex.IsBall.nonempty_boundaryImage_homeomorph_sphereTwo`): two certificate faces
coincide or are disjoint (`face_eq_or_disjoint`: V4 `face_disjoint`, the opposite seam sides having
the same image). As the boundary of a ball is connected, EVERY face of a ball vertex is its whole
model boundary (`face_eq_boundaryImage_of_isBall`). A two-sphere is not a torus
(`false_of_homeomorph_sphereTwo_of_homeomorph_torus`), so without sphere seams a ball
vertex owns exactly one partitioned face (`existsUnique_partitioned_face_of_isBall`), with the sphere
model; FC40 then gives DEGREE TWO: exactly two handle ends lie on a ball vertex
(`card_handleEnd_eq_two_of_isBall`). With `hball` (every partitioned sphere face is owned by a ball,
i.e. no bad vertex) every handle end is a ball vertex (`isBall_handleEnd`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

theorem boundaryImage_nonempty_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall) :
    (D.vertex k).boundaryImage.Nonempty :=
  hk.boundaryImage_nonempty

/-- A face is nonempty (a two-sphere or a torus). -/
theorem face_nonempty (f : Fin D.faceCount) : (D.face f).Nonempty := by
  rcases D.faceModel f with φ | ψ
  · obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3)))
      (r := 1)).mpr zero_le_one
    exact ⟨(φ.symm ⟨x, hx⟩).1, (φ.symm ⟨x, hx⟩).2⟩
  · exact ⟨(ψ.symm (1, 1)).1, (ψ.symm (1, 1)).2⟩

/-- **Faces coincide or are disjoint** (V4: the opposite sides of one seam have the same image). -/
theorem face_eq_or_disjoint (f f' : Fin D.faceCount) :
    D.face f = D.face f' ∨ Disjoint (D.face f) (D.face f') := by
  by_cases hff : f = f'
  · exact Or.inl (hff ▸ rfl)
  by_cases hs : ∃ c b, D.faceKind f = .sphereSeam c b ∧ D.faceKind f' = .sphereSeam c (!b)
  · obtain ⟨c, b, h1, h2⟩ := hs
    exact Or.inl ((D.face_sphereSeam f c b h1).1.trans (D.face_sphereSeam f' c (!b) h2).1.symm)
  by_cases ht : ∃ c b, D.faceKind f = .torusSeam c b ∧ D.faceKind f' = .torusSeam c (!b)
  · obtain ⟨c, b, h1, h2⟩ := ht
    exact Or.inl ((D.face_torusSeam f c b h1).1.trans (D.face_torusSeam f' c (!b) h2).1.symm)
  push Not at hs ht
  exact Or.inr (D.face_disjoint f f' hff (fun c b h => hs c b h.1 h.2)
    (fun c b h => ht c b h.1 h.2))

/-- **Every face of a ball vertex is its whole model boundary image.** -/
theorem face_eq_boundaryImage_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    {f : Fin D.faceCount} (hf : D.faceOwner f = k) : D.face f = (D.vertex k).boundaryImage := by
  have hsub : D.face f ⊆ (D.vertex k).boundaryImage := hf ▸ D.face_subset_boundaryImage f
  refine Subset.antisymm hsub ?_
  let C : Set W.Carrier := ⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = k)
    (_ : Disjoint (D.face f) (D.face f')), D.face f'
  have hC : IsClosed C :=
    isClosed_iUnion_of_finite fun f' => isClosed_iUnion_of_finite fun _ =>
      isClosed_iUnion_of_finite fun _ => D.isClosed_face f'
  have hcov : (D.vertex k).boundaryImage ⊆ D.face f ∪ C := by
    intro x hx
    rw [← D.face_exhausted k] at hx
    obtain ⟨f', hx⟩ := mem_iUnion.mp hx
    obtain ⟨hf', hx⟩ := mem_iUnion.mp hx
    rcases D.face_eq_or_disjoint f f' with heq | hdis
    · exact Or.inl (heq ▸ hx)
    · exact Or.inr (mem_iUnion₂.mpr ⟨f', hf', mem_iUnion.mpr ⟨hdis, hx⟩⟩)
  have hdisj : Disjoint (D.face f) C := by
    refine disjoint_iUnion_right.mpr fun f' => disjoint_iUnion_right.mpr fun _ =>
      disjoint_iUnion_right.mpr fun hdis => hdis
  intro x hx
  rcases hcov hx with h | h
  · exact h
  · exfalso
    have hpre := hk.isConnected_boundaryImage.isPreconnected
    rw [isPreconnected_closed_iff] at hpre
    obtain ⟨y, hy⟩ := D.face_nonempty f
    obtain ⟨z, -, hz1, hz2⟩ := hpre (D.face f) C (D.isClosed_face f) hC hcov ⟨y, hsub hy, hy⟩
      ⟨x, hx, h⟩
    exact Set.disjoint_left.mp hdisj hz1 hz2

/-- The faces of a ball vertex are two-spheres: the torus model is impossible. -/
theorem false_of_isBall_of_face_homeomorph_torus {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    {f : Fin D.faceCount} (hf : D.faceOwner f = k) (ψ : D.face f ≃ₜ Circle × Circle) : False := by
  exact hk.false_of_homeomorph_torus (D.face_eq_boundaryImage_of_isBall hk hf) ψ

/-- The face of a ball vertex is not an external port. -/
theorem faceKind_ne_external_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    {f : Fin D.faceCount} (hf : D.faceOwner f = k) (i : Fin n) : D.faceKind f ≠ .external i := by
  intro hi
  have hface := (D.face_external f i hi).1
  have hT := E.torusMap_isEmbedding i
  exact D.false_of_isBall_of_face_homeomorph_torus hk hf
    ((Homeomorph.setCongr hface).trans (homeomorphRangeOfTorus hT.continuous hT.injective))

/-- The face of a ball vertex is not a torus seam side. -/
theorem faceKind_ne_torusSeam_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    {f : Fin D.faceCount} (hf : D.faceOwner f = k) (c : Fin D.torusSeamCount) (b : Bool) :
    D.faceKind f ≠ .torusSeam c b := by
  intro hc
  have hface := (D.face_torusSeam f c b hc).1
  have hsrc : ∀ t : Circle × Circle, (t, (0 : ℝ)) ∈ (D.torusSeam c).collar.source := by
    intro t
    rw [(D.torusSeam c).source_eq]
    exact ⟨by norm_num, by norm_num⟩
  have hcont : Continuous fun t : Circle × Circle => (D.torusSeam c).collar (t, 0) :=
    (D.torusSeam c).collar.contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) hsrc
  have hinj : Injective fun t : Circle × Circle => (D.torusSeam c).collar (t, 0) := by
    intro t t' h
    have := (D.torusSeam c).collar.injOn (hsrc t) (hsrc t') h
    exact congrArg Prod.fst this
  exact D.false_of_isBall_of_face_homeomorph_torus hk hf
    ((Homeomorph.setCongr hface).trans (homeomorphRangeOfTorus hcont hinj))

/-- **A ball vertex owns exactly one partitioned face** (no sphere seams). -/
theorem existsUnique_partitioned_face_of_isBall (hsph : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall) :
    ∃! f, D.faceOwner f = k ∧ D.faceKind f = .partitioned := by
  obtain ⟨x, hx⟩ := D.boundaryImage_nonempty_of_isBall hk
  rw [← D.face_exhausted k] at hx
  obtain ⟨f, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hf, -⟩ := mem_iUnion.mp hx
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · rcases hkind : D.faceKind f with i | ⟨c, b⟩ | ⟨c, b⟩ | _
    · exact absurd hkind (D.faceKind_ne_external_of_isBall hk hf i)
    · exact absurd hkind (D.faceKind_ne_torusSeam_of_isBall hk hf c b)
    · exact (Fin.cast hsph c).elim0
    · rfl
  · rintro f' ⟨hf', hpart⟩
    by_contra hne
    have hdis := D.face_disjoint f' f hne (fun c b h => by simp [hpart] at h)
      (fun c b h => by simp [hpart] at h)
    rw [D.face_eq_boundaryImage_of_isBall hk hf', D.face_eq_boundaryImage_of_isBall hk hf,
      disjoint_self, bot_eq_empty] at hdis
    exact (D.boundaryImage_nonempty_of_isBall hk).ne_empty hdis

/-- The partitioned face of a ball vertex has the sphere model, hence two handle ends (FC40). -/
theorem card_faceEnd_eq_two_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    {f : Fin D.faceCount} (hf : D.faceOwner f = k) (hpart : D.faceKind f = .partitioned) :
    Fintype.card (D.FaceEnd f) = 2 := by
  rcases D.faceModel f with φ | ψ
  · exact (D.card_faceStratum_eq_one_and_card_faceEnd_eq_two hpart φ).2
  · exact (D.false_of_isBall_of_face_homeomorph_torus hk hf ψ).elim

/-- **Degree two.** Without sphere seams, exactly two handle ends lie on a ball vertex. -/
theorem card_handleEnd_eq_two_of_isBall (hsph : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall) :
    (Finset.univ.filter fun hb : Fin D.handleCount × Bool => D.handleEnd hb.1 hb.2 = k).card =
      2 := by
  obtain ⟨f, ⟨hf, hpart⟩, huniq⟩ := D.existsUnique_partitioned_face_of_isBall hsph hk
  have hset : (Finset.univ.filter fun hb : Fin D.handleCount × Bool => D.handleEnd hb.1 hb.2 = k) =
      Finset.univ.filter fun hb : Fin D.handleCount × Bool => D.handleFace hb.1 hb.2 = f := by
    ext ⟨h, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro he
      exact huniq _ ⟨(D.handleFace_owner h b).trans he, D.handleFace_kind h b⟩
    · intro hhf
      rw [← D.handleFace_owner h b, hhf, hf]
  rw [hset, ← Fintype.card_subtype]
  exact D.card_faceEnd_eq_two_of_isBall hk hf hpart

/-- With `hball` (every partitioned sphere face is owned by a ball: no bad vertex), every handle
end is a ball vertex. -/
theorem isBall_handleEnd
    (hball : ∀ f, D.faceKind f = .partitioned →
      (∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) →
      (D.vertex (D.faceOwner f)).IsBall)
    (h : Fin D.handleCount) (b : Bool) : (D.vertex (D.handleEnd h b)).IsBall := by
  rw [← D.handleFace_owner h b]
  rcases hm : D.faceModel (D.handleFace h b) with φ | ψ
  · exact hball _ (D.handleFace_kind h b) ⟨φ, hm⟩
  · exact (D.handleFace_ne_of_torus (D.handleFace_kind h b) ψ h b rfl).elim

end DecompositionCertificate

end GC.GraphManifold.Assembly
