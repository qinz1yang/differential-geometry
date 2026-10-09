import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitSphereApplications

/-!
# FC42 normalization, packet N2a (builder): the generic vertex split

Lane ASM-NRM3 (N2a design point 4, approved by main 2026-10-04). A vertex `k` of a certificate
without sphere seams is replaced by two vertices `V₁` (index `castSucc k`) and `V₂` (new last index)
glued along one registered sphere seam `S` (side `true` = `V₁`); the old faces of `k` go to `V₁` / `V₂`
by `side`; handles, edge circles, circle region, torus seams, ports, arcs, loops and rim charts are
those of `D`. Inputs (all hypotheses explicit): the two images cover `k`'s image with disjoint
interiors, the collar sides, the seam inside the ambient interior of `k`'s image, `k` no torus side
and no port owner, the two model-boundary images, faces disjoint from the seam sphere, the rim
vertex side inside the half of its face, rim targets off the seam collar.

* `DecompositionCertificate.vsplit` (every field proved; data `vsplitVertex`, `vsplitFace`,
  `vsplitFaceModel`, `vsplitOwnerOld`, `vsplitFaceOwner`, reusing `splitSide`, `splitNewFace`,
  `splitFaceKind`, `splitBase` of `AssemblyNormSplitSphere.lean`);
* `RimProduct.vsplit`, `vsplit_ne_closedZero`, `card_filter_badVertexSet_vsplit`;
* consumer `exists_vsplit_output`: the output format of N2a / N3a.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

section VSplitData

variable (k : Fin D.vertexCount) (V₁ V₂ : Vertex W) (S : SphereSeam W)
  (side : Fin D.faceCount → Bool)
  (μ : S.zeroSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The vertices of a generic split. -/
def vsplitVertex (j : Fin (D.vertexCount + 1)) : Vertex W :=
  if h : (j : ℕ) < D.vertexCount then
    if (⟨j, h⟩ : Fin D.vertexCount) = k then V₁ else D.vertex ⟨j, h⟩
  else V₂

/-- The faces of a generic split: the old faces, then the seam sphere twice. -/
def vsplitFace (f : Fin (D.faceCount + 2)) : Set W.Carrier :=
  if h : (f : ℕ) < D.faceCount then D.face ⟨f, h⟩ else S.zeroSphere

/-- The face models of a generic split. -/
def vsplitFaceModel (f : Fin (D.faceCount + 2)) :
    (D.vsplitFace S f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕
      (D.vsplitFace S f ≃ₜ Circle × Circle) :=
  if h : (f : ℕ) < D.faceCount then
    have hf : D.vsplitFace S f = D.face ⟨f, h⟩ := dite_eq_left h
    (D.faceModel ⟨f, h⟩).map (fun φ => (Homeomorph.setCongr hf).trans φ)
      (fun ψ => (Homeomorph.setCongr hf).trans ψ)
  else
    have hf : D.vsplitFace S f = S.zeroSphere := dite_eq_right h
    .inl ((Homeomorph.setCongr hf).trans μ)

/-- The owner of an old face in a generic split. -/
def vsplitOwnerOld (f : Fin D.faceCount) : Fin (D.vertexCount + 1) :=
  if D.faceOwner f = k then cond (side f) (Fin.castSucc k) (Fin.last _)
  else Fin.castSucc (D.faceOwner f)

/-- The face owners of a generic split. -/
def vsplitFaceOwner (f : Fin (D.faceCount + 2)) : Fin (D.vertexCount + 1) :=
  if h : (f : ℕ) < D.faceCount then D.vsplitOwnerOld k side ⟨f, h⟩
  else D.splitSide k (decide ((f : ℕ) = D.faceCount))

theorem vsplitVertex_castSucc {j : Fin D.vertexCount} (hj : j ≠ k) :
    D.vsplitVertex k V₁ V₂ (Fin.castSucc j) = D.vertex j := by
  unfold vsplitVertex
  rw [dite_eq_left (show ((Fin.castSucc j : Fin _) : ℕ) < D.vertexCount from j.isLt)]
  exact ite_eq_right hj

theorem vsplitVertex_castSucc_self : D.vsplitVertex k V₁ V₂ (Fin.castSucc k) = V₁ := by
  unfold vsplitVertex
  rw [dite_eq_left (show ((Fin.castSucc k : Fin _) : ℕ) < D.vertexCount from k.isLt)]
  exact ite_eq_left rfl

theorem vsplitVertex_last : D.vsplitVertex k V₁ V₂ (Fin.last _) = V₂ := by
  unfold vsplitVertex
  exact dite_eq_right (by simp)

theorem vsplitFace_castAdd (f : Fin D.faceCount) : D.vsplitFace S (Fin.castAdd 2 f) = D.face f := by
  unfold vsplitFace
  exact dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)

theorem vsplitFace_splitNewFace (b : Bool) : D.vsplitFace S (D.splitNewFace b) = S.zeroSphere := by
  unfold vsplitFace
  exact dite_eq_right (by cases b <;> simp [splitNewFace])

theorem vsplitFaceOwner_castAdd (f : Fin D.faceCount) :
    D.vsplitFaceOwner k side (Fin.castAdd 2 f) = D.vsplitOwnerOld k side f := by
  unfold vsplitFaceOwner
  exact dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)

theorem vsplitFaceOwner_splitNewFace (b : Bool) :
    D.vsplitFaceOwner k side (D.splitNewFace b) = D.splitSide k b := by
  unfold vsplitFaceOwner
  rw [dite_eq_right (by cases b <;> simp [splitNewFace])]
  cases b <;> simp [splitNewFace]

theorem vsplitOwnerOld_cases (f : Fin D.faceCount) :
    (D.faceOwner f ≠ k ∧ D.vsplitOwnerOld k side f = Fin.castSucc (D.faceOwner f)) ∨
      (D.faceOwner f = k ∧ side f = true ∧ D.vsplitOwnerOld k side f = Fin.castSucc k) ∨
      (D.faceOwner f = k ∧ side f = false ∧ D.vsplitOwnerOld k side f = Fin.last _) := by
  by_cases hf : D.faceOwner f = k
  · cases hs : side f
    · exact Or.inr (Or.inr ⟨hf, rfl, by simp [vsplitOwnerOld, hf, hs]⟩)
    · exact Or.inr (Or.inl ⟨hf, rfl, by simp [vsplitOwnerOld, hf, hs]⟩)
  · exact Or.inl ⟨hf, by simp [vsplitOwnerOld, hf]⟩

theorem exists_faceModel_of_vsplitFaceModel (f : Fin D.faceCount)
    {φ : D.vsplitFace S (Fin.castAdd 2 f) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (h : D.vsplitFaceModel S μ (Fin.castAdd 2 f) = .inl φ) :
    ∃ φ' : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl φ' := by
  unfold vsplitFaceModel at h
  rw [dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)] at h
  rcases hm : D.faceModel f with φ' | ψ'
  · exact ⟨φ', rfl⟩
  · exfalso
    change Sum.map _ _ (D.faceModel f) = _ at h
    rw [hm] at h
    cases h

end VSplitData

section VSplitGeometry

variable {D} {k : Fin D.vertexCount} {V₁ V₂ : Vertex W} {S : SphereSeam W}
  {side : Fin D.faceCount → Bool}

theorem image_vsplitVertex_subset (hcov : V₁.image ∪ V₂.image = (D.vertex k).image)
    (j : Fin (D.vertexCount + 1)) :
    (D.vsplitVertex k V₁ V₂ j).image ⊆ (D.vertex (D.splitBase k j)).image := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [splitBase_castSucc]
    by_cases hj : j' = k
    · rw [hj, vsplitVertex_castSucc_self, ← hcov]
      exact subset_union_left
    · rw [D.vsplitVertex_castSucc k V₁ V₂ hj]
  · rw [splitBase_last, vsplitVertex_last, ← hcov]
    exact subset_union_right

theorem iUnion_image_vsplitVertex (hcov : V₁.image ∪ V₂.image = (D.vertex k).image) :
    ⋃ j, (D.vsplitVertex k V₁ V₂ j).image = ⋃ j, (D.vertex j).image := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => (image_vsplitVertex_subset hcov j).trans
      (subset_iUnion (fun i => (D.vertex i).image) _)
  · refine iUnion_subset fun j => ?_
    by_cases hj : j = k
    · rw [hj, ← hcov]
      rintro x (hx | hx)
      · refine mem_iUnion.mpr ⟨Fin.castSucc k, ?_⟩
        rw [vsplitVertex_castSucc_self]
        exact hx
      · refine mem_iUnion.mpr ⟨Fin.last _, ?_⟩
        rw [vsplitVertex_last]
        exact hx
    · rw [← D.vsplitVertex_castSucc k V₁ V₂ hj]
      exact subset_iUnion (fun i => (D.vsplitVertex k V₁ V₂ i).image) _

theorem vsplitVertex_disjoint (hcov : V₁.image ∪ V₂.image = (D.vertex k).image)
    (hint : Disjoint (interior V₁.image) (interior V₂.image)) :
    Pairwise fun i j => Disjoint (interior (D.vsplitVertex k V₁ V₂ i).image)
      (interior (D.vsplitVertex k V₁ V₂ j).image) := by
  intro i j hij
  by_cases hb : D.splitBase k i = D.splitBase k j
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [splitBase_castSucc, splitBase_castSucc] at hb
      exact (hij (congrArg _ hb)).elim
    · rw [splitBase_castSucc, splitBase_last] at hb
      rw [hb, vsplitVertex_castSucc_self, vsplitVertex_last]
      exact hint
    · rw [splitBase_last, splitBase_castSucc] at hb
      rw [← hb, vsplitVertex_castSucc_self, vsplitVertex_last]
      exact hint.symm
    · exact (hij rfl).elim
  · exact (D.vertex_disjoint hb).mono (interior_mono (image_vsplitVertex_subset hcov i))
      (interior_mono (image_vsplitVertex_subset hcov j))

theorem mem_vsplitTorusSide (htor : ∀ c b, D.torusSide c b ≠ some k)
    (c : Fin D.torusSeamCount) (β : Bool) {x : W.Carrier}
    (hx : x ∈ (D.torusSide c β).elim D.circ.region fun j => (D.vertex j).image) :
    x ∈ ((D.torusSide c β).map Fin.castSucc).elim D.circ.region
      fun j => (D.vsplitVertex k V₁ V₂ j).image := by
  cases hs : D.torusSide c β with
  | none =>
    rw [hs] at hx
    exact hx
  | some a =>
    rw [hs] at hx
    have ha : a ≠ k := fun h => htor c β (hs.trans (congrArg some h))
    change x ∈ (D.vsplitVertex k V₁ V₂ (Fin.castSucc a)).image
    rw [D.vsplitVertex_castSucc k V₁ V₂ ha]
    exact hx

theorem vsplitFace_exhausted
    (hB₁ : V₁.boundaryImage =
      (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = true), D.face f) ∪
        S.zeroSphere)
    (hB₂ : V₂.boundaryImage =
      (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = false), D.face f) ∪
        S.zeroSphere)
    (j : Fin (D.vertexCount + 1)) :
    (⋃ (f : Fin (D.faceCount + 2)) (_ : D.vsplitFaceOwner k side f = j), D.vsplitFace S f) =
      (D.vsplitVertex k V₁ V₂ j).boundaryImage := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨f, hfj, hx⟩
    rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b, rfl⟩
    · rw [vsplitFace_castAdd] at hx
      rw [vsplitFaceOwner_castAdd] at hfj
      rcases D.vsplitOwnerOld_cases k side f' with ⟨hne, ho⟩ | ⟨hk, hs, ho⟩ | ⟨hk, hs, ho⟩
      · rw [← hfj, ho, D.vsplitVertex_castSucc k V₁ V₂ hne]
        exact D.face_subset_boundaryImage f' hx
      · rw [← hfj, ho, vsplitVertex_castSucc_self, hB₁]
        exact Or.inl (mem_iUnion₂.mpr ⟨f', hk, mem_iUnion.mpr ⟨hs, hx⟩⟩)
      · rw [← hfj, ho, vsplitVertex_last, hB₂]
        exact Or.inl (mem_iUnion₂.mpr ⟨f', hk, mem_iUnion.mpr ⟨hs, hx⟩⟩)
    · rw [vsplitFace_splitNewFace] at hx
      rw [vsplitFaceOwner_splitNewFace] at hfj
      rw [← hfj]
      cases b
      · change x ∈ (D.vsplitVertex k V₁ V₂ (Fin.last _)).boundaryImage
        rw [vsplitVertex_last, hB₂]
        exact Or.inr hx
      · change x ∈ (D.vsplitVertex k V₁ V₂ (Fin.castSucc k)).boundaryImage
        rw [vsplitVertex_castSucc_self, hB₁]
        exact Or.inr hx
  · intro hx
    rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
    · by_cases ha : a = k
      · rw [ha, vsplitVertex_castSucc_self, hB₁] at hx
        rcases hx with hx | hx
        · obtain ⟨f, hfo, hx⟩ := mem_iUnion₂.mp hx
          obtain ⟨hs, hx⟩ := mem_iUnion.mp hx
          refine ⟨Fin.castAdd 2 f, ?_, by rw [vsplitFace_castAdd]; exact hx⟩
          rw [vsplitFaceOwner_castAdd, ha]
          simp [vsplitOwnerOld, hfo, hs]
        · refine ⟨D.splitNewFace true, ?_, by rw [vsplitFace_splitNewFace]; exact hx⟩
          rw [vsplitFaceOwner_splitNewFace, ha]
          rfl
      · rw [D.vsplitVertex_castSucc k V₁ V₂ ha, ← D.face_exhausted] at hx
        obtain ⟨f, hx⟩ := mem_iUnion.mp hx
        obtain ⟨hfo, hx⟩ := mem_iUnion.mp hx
        refine ⟨Fin.castAdd 2 f, ?_, by rw [vsplitFace_castAdd]; exact hx⟩
        have hne : D.faceOwner f ≠ k := fun h => ha (hfo.symm.trans h)
        rcases D.vsplitOwnerOld_cases k side f with ⟨-, ho⟩ | ⟨hk', -⟩ | ⟨hk', -⟩
        · rw [vsplitFaceOwner_castAdd, ho, hfo]
        · exact (hne hk').elim
        · exact (hne hk').elim
    · rw [vsplitVertex_last, hB₂] at hx
      rcases hx with hx | hx
      · obtain ⟨f, hfo, hx⟩ := mem_iUnion₂.mp hx
        obtain ⟨hs, hx⟩ := mem_iUnion.mp hx
        refine ⟨Fin.castAdd 2 f, ?_, by rw [vsplitFace_castAdd]; exact hx⟩
        rw [vsplitFaceOwner_castAdd]
        simp [vsplitOwnerOld, hfo, hs]
      · exact ⟨D.splitNewFace false, by rw [vsplitFaceOwner_splitNewFace]; rfl,
          by rw [vsplitFace_splitNewFace]; exact hx⟩

theorem vsplitFace_disjoint (hσ : D.sphereSeamCount = 0)
    (hfS : ∀ f, Disjoint (D.face f) S.zeroSphere) (f f' : Fin (D.faceCount + 2)) (hne : f ≠ f')
    (hS : ∀ c b, ¬ (D.splitFaceKind hσ f = .sphereSeam c b ∧
      D.splitFaceKind hσ f' = .sphereSeam c (!b)))
    (hT : ∀ c b, ¬ (D.splitFaceKind hσ f = .torusSeam c b ∧
      D.splitFaceKind hσ f' = .torusSeam c (!b))) :
    Disjoint (D.vsplitFace S f) (D.vsplitFace S f') := by
  rcases D.splitFace_cases f with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases D.splitFace_cases f' with ⟨a', rfl⟩ | ⟨b', rfl⟩
  · rw [vsplitFace_castAdd, vsplitFace_castAdd]
    refine D.face_disjoint a a' (fun h => hne (congrArg _ h)) (fun c _ _ => (Fin.cast hσ c).elim0)
      fun c β ⟨h1, h2⟩ => hT c β ⟨?_, ?_⟩
    · rw [splitFaceKind_castAdd, h1]
      rfl
    · rw [splitFaceKind_castAdd, h2]
      rfl
  · rw [vsplitFace_castAdd, vsplitFace_splitNewFace]
    exact hfS a
  · rw [vsplitFace_castAdd, vsplitFace_splitNewFace]
    exact (hfS a').symm
  · have hbb : b' = !b := by
      cases b <;> cases b' <;> first | rfl | exact (hne rfl).elim
    exact (hS 0 b ⟨D.splitFaceKind_splitNewFace hσ b,
      by rw [hbb, D.splitFaceKind_splitNewFace hσ]⟩).elim

theorem vsplitRim_vertex (hcov : V₁.image ∪ V₂.image = (D.vertex k).image)
    (hrimV : ∀ h b {p}, D.handleEnd h b = k → p ∈ (D.rimChart h b).source → p.2.2 ≤ 0 →
      D.rimChart h b p ∈ (cond (side (D.handleFace h b)) V₁ V₂).image)
    (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart h b).source) :
    D.rimChart h b p ∈
        (D.vsplitVertex k V₁ V₂ (D.vsplitFaceOwner k side (Fin.castAdd 2 (D.handleFace h b)))).image ↔
      p.2.2 ≤ 0 := by
  have hown := D.handleFace_owner h b
  rw [vsplitFaceOwner_castAdd]
  rcases D.vsplitOwnerOld_cases k side (D.handleFace h b) with ⟨hne, ho⟩ | ⟨hk, hs, ho⟩ |
    ⟨hk, hs, ho⟩
  · rw [ho, D.vsplitVertex_castSucc k V₁ V₂ hne, hown]
    exact D.rim_vertex h b hp
  · rw [ho, vsplitVertex_castSucc_self]
    have hk' : D.handleEnd h b = k := hown ▸ hk
    refine ⟨fun hx => (D.rim_vertex h b hp).mp ?_, fun hp2 => ?_⟩
    · rw [hk', ← hcov]
      exact Or.inl hx
    · have := hrimV h b hk' hp hp2
      rw [hs] at this
      exact this
  · rw [ho, vsplitVertex_last]
    have hk' : D.handleEnd h b = k := hown ▸ hk
    refine ⟨fun hx => (D.rim_vertex h b hp).mp ?_, fun hp2 => ?_⟩
    · rw [hk', ← hcov]
      exact Or.inr hx
    · have := hrimV h b hk' hp hp2
      rw [hs] at this
      exact this

theorem vsplitFace_external (hσ : D.sphereSeamCount = 0) (hext : ∀ i, D.externalOwner i ≠ k)
    (f : Fin (D.faceCount + 2)) (i : Fin n) (hk : D.splitFaceKind hσ f = .external i) :
    D.vsplitFace S f = range (E.torusMap i) ∧
      Fin.castSucc (D.externalOwner i) = D.vsplitFaceOwner k side f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b, rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    obtain ⟨h1, h2⟩ := D.face_external f' i (FaceKind.eq_of_liftNoSphere_eq_external hk)
    have hne : D.faceOwner f' ≠ k := fun h => hext i (h2.trans h)
    rcases D.vsplitOwnerOld_cases k side f' with ⟨-, ho⟩ | ⟨hk', -⟩ | ⟨hk', -⟩
    · rw [vsplitFace_castAdd, vsplitFaceOwner_castAdd, ho, h2]
      exact ⟨h1, rfl⟩
    · exact (hne hk').elim
    · exact (hne hk').elim
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem vsplitFace_torusSeam (hσ : D.sphereSeamCount = 0) (htor : ∀ c b, D.torusSide c b ≠ some k)
    (f : Fin (D.faceCount + 2)) (c : Fin D.torusSeamCount) (b : Bool)
    (hk : D.splitFaceKind hσ f = .torusSeam c b) :
    D.vsplitFace S f = range (fun t => (D.torusSeam c).collar (t, 0)) ∧
      (D.torusSide c b).map Fin.castSucc = some (D.vsplitFaceOwner k side f) := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    obtain ⟨h1, h2⟩ := D.face_torusSeam f' c b (FaceKind.eq_of_liftNoSphere_eq_torusSeam hk)
    have hne : D.faceOwner f' ≠ k := fun h => htor c b (h2.trans (congrArg some h))
    rcases D.vsplitOwnerOld_cases k side f' with ⟨-, ho⟩ | ⟨hk', -⟩ | ⟨hk', -⟩
    · rw [vsplitFace_castAdd, vsplitFaceOwner_castAdd, ho, h2]
      exact ⟨h1, rfl⟩
    · exact (hne hk').elim
    · exact (hne hk').elim
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem vsplitTorusSeam_face (hσ : D.sphereSeamCount = 0) (htor : ∀ c b, D.torusSide c b ≠ some k)
    (c : Fin D.torusSeamCount) (b : Bool) (j : Fin (D.vertexCount + 1))
    (hs : (D.torusSide c b).map Fin.castSucc = some j) :
    ∃ f, D.vsplitFaceOwner k side f = j ∧ D.splitFaceKind hσ f = .torusSeam c b := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b a ha
  have hne : D.faceOwner f ≠ k := fun h =>
    htor c b (ha.trans (congrArg some (hfo.symm.trans h)))
  refine ⟨Fin.castAdd 2 f, ?_, ?_⟩
  · rcases D.vsplitOwnerOld_cases k side f with ⟨-, ho⟩ | ⟨hk', -⟩ | ⟨hk', -⟩
    · rw [vsplitFaceOwner_castAdd, ho, hfo]
    · exact (hne hk').elim
    · exact (hne hk').elim
  · rw [splitFaceKind_castAdd, hfk]
    rfl

theorem vsplitFace_sphereSeam (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (c : Fin 1) (b : Bool) (hk : D.splitFaceKind hσ f = .sphereSeam c b) :
    D.vsplitFace S f = range (fun z => S.collar (z, 0)) ∧
      D.splitSide k b = D.vsplitFaceOwner k side f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    exact (FaceKind.liftNoSphere_ne_sphereSeam _ c b hk).elim
  · rw [splitFaceKind_splitNewFace] at hk
    simp only [FaceKind.sphereSeam.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    rw [vsplitFace_splitNewFace, vsplitFaceOwner_splitNewFace]
    exact ⟨rfl, rfl⟩

theorem vsplitFace_partition (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (hk : D.splitFaceKind hσ f = .partitioned) :
    (⋃ (h : Fin D.handleCount) (b : Bool) (_ : Fin.castAdd 2 (D.handleFace h b) = f),
        (D.handle h).endDisk b) ∪
      (⋃ (j : Fin D.arcFaceCount) (_ : Fin.castAdd 2 (D.arcOwner j) = f), D.arcFace j) ∪
      (⋃ (j : Fin D.loopFaceCount) (_ : Fin.castAdd 2 (D.loopOwner j) = f), D.loopFace j) =
      D.vsplitFace S f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    simp only [Fin.castAdd_inj, vsplitFace_castAdd]
    exact D.face_partition f' (FaceKind.eq_of_liftNoSphere_eq_partitioned hk)
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem vsplitFace_region_inter (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (hk : D.splitFaceKind hσ f = .partitioned) :
    D.vsplitFace S f ∩ D.circ.region =
      (⋃ (j : Fin D.arcFaceCount) (_ : Fin.castAdd 2 (D.arcOwner j) = f), D.arcFace j) ∪
        (⋃ (j : Fin D.loopFaceCount) (_ : Fin.castAdd 2 (D.loopOwner j) = f), D.loopFace j) := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    simp only [Fin.castAdd_inj, vsplitFace_castAdd]
    exact D.face_region_inter f' (FaceKind.eq_of_liftNoSphere_eq_partitioned hk)
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

end VSplitGeometry

/-- **The generic vertex split.** Vertex `k` of a certificate without sphere seams is replaced by
`V₁` (index `castSucc k`) and `V₂` (new last index), glued along the one registered sphere seam `S`
(side `true` = `V₁`); the old faces of `k` go to `V₁` / `V₂` by `side`; every other datum is `D`'s. -/
def vsplit (hσ : D.sphereSeamCount = 0) (k : Fin D.vertexCount) (V₁ V₂ : Vertex W)
    (S : SphereSeam W) (side : Fin D.faceCount → Bool)
    (μ : S.zeroSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hcov : V₁.image ∪ V₂.image = (D.vertex k).image)
    (hint : Disjoint (interior V₁.image) (interior V₂.image))
    (hS₁ : ∀ z s, s ≤ 0 → -1 < s → S.collar (z, s) ∈ V₁.image)
    (hS₂ : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, s) ∈ V₂.image)
    (hSk : S.collar.target ⊆ interior (D.vertex k).image)
    (htor : ∀ c b, D.torusSide c b ≠ some k) (hext : ∀ i, D.externalOwner i ≠ k)
    (hB₁ : V₁.boundaryImage =
      (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = true), D.face f) ∪
        S.zeroSphere)
    (hB₂ : V₂.boundaryImage =
      (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = false), D.face f) ∪
        S.zeroSphere)
    (hfS : ∀ f, Disjoint (D.face f) S.zeroSphere)
    (hrimV : ∀ h b {p}, D.handleEnd h b = k → p ∈ (D.rimChart h b).source → p.2.2 ≤ 0 →
      D.rimChart h b p ∈ (cond (side (D.handleFace h b)) V₁ V₂).image)
    (hrimS : ∀ h b, Disjoint (D.rimChart h b).target S.collar.target) :
    DecompositionCertificate W E where
  external_exhausted := D.external_exhausted
  vertexCount := D.vertexCount + 1
  vertex := D.vsplitVertex k V₁ V₂
  handleCount := D.handleCount
  handle := D.handle
  edgeCircleCount := D.edgeCircleCount
  edgeCircle := D.edgeCircle
  circ := D.circ
  cover := by
    rw [iUnion_image_vsplitVertex hcov]
    exact D.cover
  vertex_disjoint := vsplitVertex_disjoint hcov hint
  handle_disjoint := D.handle_disjoint
  edgeCircle_disjoint := D.edgeCircle_disjoint
  vertex_handle_disjoint j h := (D.vertex_handle_disjoint (D.splitBase k j) h).mono_left
    (interior_mono (image_vsplitVertex_subset hcov j))
  edgeCircle_vertex_disjoint c j := (D.edgeCircle_vertex_disjoint c (D.splitBase k j)).mono_right
    (interior_mono (image_vsplitVertex_subset hcov j))
  edgeCircle_handle_disjoint := D.edgeCircle_handle_disjoint
  circ_vertex_disjoint j := (D.circ_vertex_disjoint (D.splitBase k j)).mono_right
    (interior_mono (image_vsplitVertex_subset hcov j))
  circ_handle_disjoint := D.circ_handle_disjoint
  circ_edgeCircle_disjoint := D.circ_edgeCircle_disjoint
  vertical_fibre := D.vertical_fibre
  edgeCircle_vertical := D.edgeCircle_vertical
  torusSeamCount := D.torusSeamCount
  torusSeam := D.torusSeam
  torusSide c b := (D.torusSide c b).map Fin.castSucc
  torusSide_neg c t s h1 h2 := mem_vsplitTorusSide htor c true (D.torusSide_neg c t s h1 h2)
  torusSide_pos c t s h1 h2 := mem_vsplitTorusSide htor c false (D.torusSide_pos c t s h1 h2)
  torusSeam_disjoint := D.torusSeam_disjoint
  sphereSeamCount := 1
  sphereSeam _ := S
  sphereSide _ b := D.splitSide k b
  sphereSide_neg _ z s h1 h2 := by
    change _ ∈ (D.vsplitVertex k V₁ V₂ (Fin.castSucc k)).image
    rw [vsplitVertex_castSucc_self]
    exact hS₁ z s h1 h2
  sphereSide_pos _ z s h1 h2 := by
    change _ ∈ (D.vsplitVertex k V₁ V₂ (Fin.last _)).image
    rw [vsplitVertex_last]
    exact hS₂ z s h1 h2
  sphereSeam_disjoint c d hcd := (hcd (Subsingleton.elim c d)).elim
  sphere_torus_seam_disjoint _ d := (D.disjoint_interior_image_torusSeam htor d).mono_left hSk
  externalOwner i := Fin.castSucc (D.externalOwner i)
  external_owned i := by
    rw [D.vsplitVertex_castSucc k V₁ V₂ (hext i)]
    exact D.external_owned i
  faceCount := D.faceCount + 2
  face := D.vsplitFace S
  faceOwner := D.vsplitFaceOwner k side
  faceModel := D.vsplitFaceModel S μ
  face_exhausted := vsplitFace_exhausted hB₁ hB₂
  faceKind := D.splitFaceKind hσ
  face_disjoint := vsplitFace_disjoint hσ hfS
  face_external := vsplitFace_external hσ hext
  external_face i := by
    obtain ⟨f, hf⟩ := D.external_face i
    refine ⟨Fin.castAdd 2 f, ?_⟩
    rw [splitFaceKind_castAdd, hf]
    rfl
  face_torusSeam := vsplitFace_torusSeam hσ htor
  torusSeam_face := vsplitTorusSeam_face hσ htor
  face_sphereSeam := vsplitFace_sphereSeam hσ
  sphereSeam_face c b := ⟨D.splitNewFace b, by rw [vsplitFaceOwner_splitNewFace], by
    rw [splitFaceKind_splitNewFace, Subsingleton.elim c 0]⟩
  handleEnd h b := D.vsplitFaceOwner k side (Fin.castAdd 2 (D.handleFace h b))
  handleFace h b := Fin.castAdd 2 (D.handleFace h b)
  handleFace_owner _ _ := rfl
  handleFace_kind h b := by
    rw [splitFaceKind_castAdd, D.handleFace_kind]
    rfl
  handleEnd_face h b := by
    rw [vsplitFace_castAdd]
    exact D.handleEnd_face h b
  endDisk_disjoint := D.endDisk_disjoint
  arcFaceCount := D.arcFaceCount
  arcFace := D.arcFace
  arcOwner j := Fin.castAdd 2 (D.arcOwner j)
  arcOwner_kind j := by
    rw [splitFaceKind_castAdd, D.arcOwner_kind]
    rfl
  arcBase := D.arcBase
  arcBase_embedding := D.arcBase_embedding
  arcFace_eq := D.arcFace_eq
  arcDefining := D.arcDefining
  arcBase_defining := D.arcBase_defining
  arcAnnulus := D.arcAnnulus
  arcAnnulus_continuous := D.arcAnnulus_continuous
  arcAnnulus_injective := D.arcAnnulus_injective
  arcAnnulus_range := D.arcAnnulus_range
  arcAnnulus_proj := D.arcAnnulus_proj
  loopFaceCount := D.loopFaceCount
  loopFace := D.loopFace
  loopOwner j := Fin.castAdd 2 (D.loopOwner j)
  loopOwner_kind j := by
    rw [splitFaceKind_castAdd, D.loopOwner_kind]
    rfl
  loopBase := D.loopBase
  loopBase_embedding := D.loopBase_embedding
  loopFace_eq := D.loopFace_eq
  loopDefining := D.loopDefining
  loopBase_defining := D.loopBase_defining
  loopFace_closed := D.loopFace_closed
  loopFace_nonempty := D.loopFace_nonempty
  arcFace_disjoint := D.arcFace_disjoint
  loopFace_disjoint := D.loopFace_disjoint
  arc_loop_disjoint := D.arc_loop_disjoint
  face_partition := vsplitFace_partition hσ
  face_region_inter := vsplitFace_region_inter hσ
  handleArc := D.handleArc
  handleArc_owner h b := congrArg (Fin.castAdd 2) (D.handleArc_owner h b)
  handleArc_meets := D.handleArc_meets
  endDisk_loop_disjoint := D.endDisk_loop_disjoint
  endDisk_rim := D.endDisk_rim
  arcEnd := D.arcEnd
  arcEnd_arc := D.arcEnd_arc
  arcEnd_injective := D.arcEnd_injective
  arcEnd_surjective := D.arcEnd_surjective
  arcAnnulus_end := D.arcAnnulus_end
  handleCorner := D.handleCorner
  handleCorner_bijective := D.handleCorner_bijective
  arcBase_end := D.arcBase_end
  rimChart := D.rimChart
  rim_source := D.rim_source
  rim_proj := D.rim_proj
  rim_vertex h b := vsplitRim_vertex hcov hrimV h b
  rim_handle := D.rim_handle
  rim_region := D.rim_region
  rim_label := D.rim_label
  rim_disjoint := D.rim_disjoint
  external_region_disjoint := D.external_region_disjoint
  external_handle_disjoint := D.external_handle_disjoint
  external_edgeCircle_disjoint := D.external_edgeCircle_disjoint
  external_torusSeam_disjoint := D.external_torusSeam_disjoint
  external_sphereSeam_disjoint i _ :=
    ((D.disjoint_interior_image_vertex (hext i)).mono_left hSk).symm.mono_left (D.external_owned i)
  rim_external_disjoint := D.rim_external_disjoint
  rim_torusSeam_disjoint := D.rim_torusSeam_disjoint
  rim_sphereSeam_disjoint h b _ := hrimS h b
  sphereSeam_region_disjoint _ := (D.disjoint_interior_image_region k).mono_left hSk
  sphereSeam_handle_disjoint _ h := (D.disjoint_interior_image_handle k h).mono_left hSk

section VSplitFacts

variable {D} (hσ : D.sphereSeamCount = 0) (k : Fin D.vertexCount) (V₁ V₂ : Vertex W)
  (S : SphereSeam W) (side : Fin D.faceCount → Bool)
  (μ : S.zeroSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (hcov : V₁.image ∪ V₂.image = (D.vertex k).image)
  (hint : Disjoint (interior V₁.image) (interior V₂.image))
  (hS₁ : ∀ z s, s ≤ 0 → -1 < s → S.collar (z, s) ∈ V₁.image)
  (hS₂ : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, s) ∈ V₂.image)
  (hSk : S.collar.target ⊆ interior (D.vertex k).image)
  (htor : ∀ c b, D.torusSide c b ≠ some k) (hext : ∀ i, D.externalOwner i ≠ k)
  (hB₁ : V₁.boundaryImage =
    (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = true), D.face f) ∪
      S.zeroSphere)
  (hB₂ : V₂.boundaryImage =
    (⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k) (_ : side f = false), D.face f) ∪
      S.zeroSphere)
  (hfS : ∀ f, Disjoint (D.face f) S.zeroSphere)
  (hrimV : ∀ h b {p}, D.handleEnd h b = k → p ∈ (D.rimChart h b).source → p.2.2 ≤ 0 →
    D.rimChart h b p ∈ (cond (side (D.handleFace h b)) V₁ V₂).image)
  (hrimS : ∀ h b, Disjoint (D.rimChart h b).target S.collar.target)

theorem vsplit_vertex :
    (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV hrimS).vertex =
      D.vsplitVertex k V₁ V₂ := rfl

theorem vsplit_sphereSeamCount :
    (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).sphereSeamCount = 1 := rfl

/-- The rim-product clause is carried by the generic split. -/
theorem RimProduct.vsplit (hD : D.RimProduct) :
    (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).RimProduct :=
  hD

/-- No closed zero vertex is created when the two new vertices are not closed zero pieces. -/
theorem vsplit_ne_closedZero (hnz : ∀ j C, D.vertex j ≠ .closedZero C)
    (h₁ : ∀ C, V₁ ≠ .closedZero C) (h₂ : ∀ C, V₂ ≠ .closedZero C)
    (j : Fin (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).vertexCount) (C : ClosedZeroPiece W) :
    (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).vertex j ≠ .closedZero C := by
  have key : ∀ j' : Fin (D.vertexCount + 1), D.vsplitVertex k V₁ V₂ j' ≠ .closedZero C := by
    intro j'
    rcases Fin.eq_castSucc_or_eq_last j' with ⟨a, rfl⟩ | rfl
    · by_cases ha : a = k
      · rw [ha, vsplitVertex_castSucc_self]
        exact h₁ C
      · rw [D.vsplitVertex_castSucc k V₁ V₂ ha]
        exact hnz a C
    · rw [vsplitVertex_last]
      exact h₂ C
  exact key j

/-- The bad vertices of the generic split off its seam are bad vertices of `D` other than `k`. -/
theorem filter_badVertexSet_vsplit_subset :
    ((D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).badVertexSet.filter fun j =>
      ∀ b, j ≠ (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
        hrimS).sphereSide ⟨0, Nat.one_pos⟩ b) ⊆
      (D.badVertexSet.erase k).map Fin.castSuccEmb := by
  intro j hj
  rw [Finset.mem_filter] at hj
  obtain ⟨hjb, hside⟩ := hj
  obtain ⟨hnb, f, hfo, hfk, φ, hφ⟩ := mem_badVertexSet_iff.mp hjb
  have h1 : j ≠ Fin.castSucc k := hside true
  have h2 : j ≠ Fin.last _ := hside false
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · have ha : a ≠ k := fun h => h1 (congrArg Fin.castSucc h)
    refine Finset.mem_map.mpr ⟨a, Finset.mem_erase.mpr ⟨ha, ?_⟩, rfl⟩
    rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b, rfl⟩
    · change D.splitFaceKind hσ (Fin.castAdd 2 f') = _ at hfk
      rw [splitFaceKind_castAdd] at hfk
      change D.vsplitFaceOwner k side (Fin.castAdd 2 f') = _ at hfo
      rw [vsplitFaceOwner_castAdd] at hfo
      have hf'o : D.faceOwner f' = a := by
        rcases D.vsplitOwnerOld_cases k side f' with ⟨-, ho⟩ | ⟨-, -, ho⟩ | ⟨-, -, ho⟩
        · rw [ho] at hfo
          exact Fin.castSucc_inj.mp hfo
        · rw [ho] at hfo
          exact (ha (Fin.castSucc_inj.mp hfo).symm).elim
        · rw [ho] at hfo
          exact (Fin.castSucc_ne_last a hfo.symm).elim
      obtain ⟨φ', hφ'⟩ := D.exists_faceModel_of_vsplitFaceModel S μ f' hφ
      refine mem_badVertexSet_iff.mpr ⟨?_, f', hf'o,
        FaceKind.eq_of_liftNoSphere_eq_partitioned hfk, φ', hφ'⟩
      rw [← D.vsplitVertex_castSucc k V₁ V₂ ha]
      exact hnb
    · change D.splitFaceKind hσ (D.splitNewFace b) = _ at hfk
      rw [splitFaceKind_splitNewFace] at hfk
      cases hfk
  · exact (h2 rfl).elim

/-- **The count of a generic split.** -/
theorem card_filter_badVertexSet_vsplit (hk : k ∈ D.badVertexSet) :
    ((D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS).badVertexSet.filter fun j =>
      ∀ b, j ≠ (D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
        hrimS).sphereSide ⟨0, Nat.one_pos⟩ b).card + 1 ≤ D.badVertexCount := by
  have h1 := Finset.card_le_card (filter_badVertexSet_vsplit_subset hσ k V₁ V₂ S side μ hcov hint
    hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV hrimS)
  have h3 : ((D.badVertexSet.erase k).map Fin.castSuccEmb).card = D.badVertexCount - 1 := by
    rw [Finset.card_map, Finset.card_erase_of_mem hk, card_badVertexSet]
  have h4 := h1.trans_eq h3
  have h2 : 0 < D.badVertexCount := by
    rw [← card_badVertexSet]
    exact Finset.card_pos.mpr ⟨k, hk⟩
  omega

include hσ μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV hrimS in
/-- **Consumer: the output format of N2a / N3a from a generic split.** -/
theorem exists_vsplit_output (hk : k ∈ D.badVertexSet) (hnz : ∀ j C, D.vertex j ≠ .closedZero C)
    (h₁ : ∀ C, V₁ ≠ .closedZero C) (h₂ : ∀ C, V₂ ≠ .closedZero C) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤
        D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) :=
  ⟨D.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV hrimS,
    ⟨0, Nat.one_pos⟩, rfl,
    card_filter_badVertexSet_vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS
      hrimV hrimS hk,
    vsplit_ne_closedZero hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV
      hrimS hnz h₁ h₂,
    RimProduct.vsplit hσ k V₁ V₂ S side μ hcov hint hS₁ hS₂ hSk htor hext hB₁ hB₂ hfS hrimV hrimS⟩

end VSplitFacts

end DecompositionCertificate

end GC.GraphManifold.Assembly
