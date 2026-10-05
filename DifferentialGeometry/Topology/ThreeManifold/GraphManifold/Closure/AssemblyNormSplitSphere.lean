import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitTools
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRimShrinkApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct


/-!
# FC42 normalization, packet N3a: the split certificate `D″` of an `S² × I` vertex

Lane ASM-NRM3 (route of `build-logs/resume/state-ASM-NRM.md`, "D″ for N3a"; tools in
`AssemblyNormSplitTools.lean`). For a certificate `D` without sphere seams, a vertex
`k = .slim P (.sphereInterval e)` and rim charts avoiding the middle zone `P (e (S² × [1/4, 3/4]))`
(arranged by N1, `exists_shrinkRims_avoiding_interior`):

* `DecompositionCertificate.splitSphereInterval`: the certificate on the SAME `W, E` in which `k`
  is split along its middle sphere into two distinct vertices (lower half at `castSucc k`, upper
  half at the new last index; same piece type and model `e`, maps reparametrized by `t ↦ t/2`,
  `t ↦ (1 + t)/2`) with the one registered sphere seam `P.middleSeam e`; the old faces keep their
  index (a face of `k` goes to the half of its end sphere), the two sides of the middle sphere are
  the two new faces; handles, edge circles, circle region, torus seams, ports, arcs, loops and rim
  charts are those of `D`. Every field is proved (`splitVertex_disjoint`, `splitFace_exhausted`,
  `splitFace_disjoint` — the only non-disjoint pair is the two new faces, the allowed V4 exception —,
  `splitRim_vertex` — the vertex side of a rim chart at `k` lies in one half —, …).
* What it keeps and counts: `RimProduct.splitSphereInterval` (rim charts and handles unchanged),
  `splitSphereInterval_ne_closedZero`, and `card_filter_badVertexSet_splitSphereInterval`: the bad
  vertices off the new seam inject into the bad vertices of `D` other than `k`.
* `standardSphereCertificate_not_split`: why the split is not instantiated on the S³ inhabitant
  (X118): its hypotheses fail there (one sphere seam, no bad vertex).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- Face kinds of a certificate without sphere seams, read with any number of sphere seams. -/
def FaceKind.liftNoSphere {n t s : ℕ} (hs : s = 0) (s' : ℕ) : FaceKind n t s → FaceKind n t s'
  | .external i => .external i
  | .torusSeam c b => .torusSeam c b
  | .sphereSeam c _ => (Fin.cast hs c).elim0
  | .partitioned => .partitioned

namespace FaceKind

variable {n t s s' : ℕ} {hs : s = 0}

theorem eq_of_liftNoSphere_eq_partitioned {x : FaceKind n t s}
    (h : x.liftNoSphere hs s' = .partitioned) : x = .partitioned := by
  cases x with
  | external i => cases h
  | torusSeam c b => cases h
  | sphereSeam c b => exact (Fin.cast hs c).elim0
  | partitioned => rfl

theorem eq_of_liftNoSphere_eq_external {x : FaceKind n t s} {i : Fin n}
    (h : x.liftNoSphere hs s' = .external i) : x = .external i := by
  cases x with
  | external j => cases h; rfl
  | torusSeam c b => cases h
  | sphereSeam c b => exact (Fin.cast hs c).elim0
  | partitioned => cases h

theorem eq_of_liftNoSphere_eq_torusSeam {x : FaceKind n t s} {c : Fin t} {b : Bool}
    (h : x.liftNoSphere hs s' = .torusSeam c b) : x = .torusSeam c b := by
  cases x with
  | external j => cases h
  | torusSeam d β => cases h; rfl
  | sphereSeam d β => exact (Fin.cast hs d).elim0
  | partitioned => cases h

theorem liftNoSphere_ne_sphereSeam (x : FaceKind n t s) (c : Fin s') (b : Bool) :
    x.liftNoSphere hs s' ≠ .sphereSeam c b := by
  cases x with
  | external j => exact fun h => by cases h
  | torusSeam d β => exact fun h => by cases h
  | sphereSeam d β => exact (Fin.cast hs d).elim0
  | partitioned => exact fun h => by cases h

end FaceKind

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

section SplitData

variable (k : Fin D.vertexCount) (P : PieceEmbedding W)
  (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)

/-- The vertices of the split: vertex `k` becomes the lower half (index `castSucc k`), a new last
vertex is the upper half, every other vertex is unchanged. -/
def splitVertex (j : Fin (D.vertexCount + 1)) : Vertex W :=
  if h : (j : ℕ) < D.vertexCount then
    if (⟨j, h⟩ : Fin D.vertexCount) = k then .slim (P.sphereHalf e true) (.sphereInterval e)
    else D.vertex ⟨j, h⟩
  else .slim (P.sphereHalf e false) (.sphereInterval e)

/-- The vertex of `D` containing a vertex of the split. -/
def splitBase (j : Fin (D.vertexCount + 1)) : Fin D.vertexCount :=
  if h : (j : ℕ) < D.vertexCount then ⟨j, h⟩ else k

/-- The two sides of the middle seam: the lower half (`true`) and the upper half (`false`). -/
def splitSide (b : Bool) : Fin (D.vertexCount + 1) :=
  cond b (Fin.castSucc k) (Fin.last _)

/-- The faces of the split: the old faces, then the middle sphere twice (its two sides). -/
def splitFace (f : Fin (D.faceCount + 2)) : Set W.Carrier :=
  if h : (f : ℕ) < D.faceCount then D.face ⟨f, h⟩ else P.sphereLevel e iccMid

/-- The two new face indices (the sides `true` / `false` of the middle seam). -/
def splitNewFace (b : Bool) : Fin (D.faceCount + 2) :=
  ⟨D.faceCount + cond b 0 1, by cases b <;> simp⟩

/-- The face models of the split. -/
def splitFaceModel (f : Fin (D.faceCount + 2)) :
    (D.splitFace P e f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕
      (D.splitFace P e f ≃ₜ Circle × Circle) :=
  if h : (f : ℕ) < D.faceCount then
    have hf : D.splitFace P e f = D.face ⟨f, h⟩ := dite_eq_left h
    (D.faceModel ⟨f, h⟩).map (fun φ => (Homeomorph.setCongr hf).trans φ)
      (fun ψ => (Homeomorph.setCongr hf).trans ψ)
  else
    have hf : D.splitFace P e f = P.sphereLevel e iccMid := dite_eq_right h
    .inl ((Homeomorph.setCongr hf).trans (P.sphereLevelHomeomorph e iccMid))

/-- The face kinds of the split (`D` has no sphere seam). -/
def splitFaceKind (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2)) :
    FaceKind n D.torusSeamCount 1 :=
  if h : (f : ℕ) < D.faceCount then (D.faceKind ⟨f, h⟩).liftNoSphere hσ 1
  else .sphereSeam 0 (decide ((f : ℕ) = D.faceCount))

open Classical in
/-- The owner of an old face in the split: a face of `k` goes to the half containing it. -/
def splitOwnerOld (f : Fin D.faceCount) : Fin (D.vertexCount + 1) :=
  if D.faceOwner f = k then
    (if D.face f = P.sphereLevel e iccZero then Fin.castSucc k else Fin.last _)
  else Fin.castSucc (D.faceOwner f)

/-- The face owners of the split. -/
def splitFaceOwner (f : Fin (D.faceCount + 2)) : Fin (D.vertexCount + 1) :=
  if h : (f : ℕ) < D.faceCount then D.splitOwnerOld k P e ⟨f, h⟩
  else D.splitSide k (decide ((f : ℕ) = D.faceCount))

/-! ### Evaluation lemmas -/

theorem splitVertex_castSucc {j : Fin D.vertexCount} (hj : j ≠ k) :
    D.splitVertex k P e (Fin.castSucc j) = D.vertex j := by
  unfold splitVertex
  rw [dite_eq_left (show ((Fin.castSucc j : Fin _) : ℕ) < D.vertexCount from j.isLt)]
  exact ite_eq_right hj

theorem splitVertex_castSucc_self :
    D.splitVertex k P e (Fin.castSucc k) = .slim (P.sphereHalf e true) (.sphereInterval e) := by
  unfold splitVertex
  rw [dite_eq_left (show ((Fin.castSucc k : Fin _) : ℕ) < D.vertexCount from k.isLt)]
  exact ite_eq_left rfl

theorem splitVertex_last :
    D.splitVertex k P e (Fin.last _) = .slim (P.sphereHalf e false) (.sphereInterval e) := by
  unfold splitVertex
  exact dite_eq_right (by simp)

theorem splitBase_castSucc (j : Fin D.vertexCount) : D.splitBase k (Fin.castSucc j) = j := by
  unfold splitBase
  exact dite_eq_left (show ((Fin.castSucc j : Fin _) : ℕ) < D.vertexCount from j.isLt)

theorem splitBase_last : D.splitBase k (Fin.last _) = k := by
  unfold splitBase
  exact dite_eq_right (by simp)

theorem splitFace_castAdd (f : Fin D.faceCount) : D.splitFace P e (Fin.castAdd 2 f) = D.face f := by
  unfold splitFace
  exact dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)

theorem splitFace_splitNewFace (b : Bool) :
    D.splitFace P e (D.splitNewFace b) = P.sphereLevel e iccMid := by
  unfold splitFace
  exact dite_eq_right (by cases b <;> simp [splitNewFace])

theorem splitFaceKind_castAdd (hσ : D.sphereSeamCount = 0) (f : Fin D.faceCount) :
    D.splitFaceKind hσ (Fin.castAdd 2 f) = (D.faceKind f).liftNoSphere hσ 1 := by
  unfold splitFaceKind
  exact dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)

theorem splitFaceKind_splitNewFace (hσ : D.sphereSeamCount = 0) (b : Bool) :
    D.splitFaceKind hσ (D.splitNewFace b) = .sphereSeam 0 b := by
  unfold splitFaceKind
  rw [dite_eq_right (by cases b <;> simp [splitNewFace])]
  cases b <;> simp [splitNewFace]

theorem splitFaceOwner_castAdd (f : Fin D.faceCount) :
    D.splitFaceOwner k P e (Fin.castAdd 2 f) = D.splitOwnerOld k P e f := by
  unfold splitFaceOwner
  exact dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)

theorem splitFaceOwner_splitNewFace (b : Bool) :
    D.splitFaceOwner k P e (D.splitNewFace b) = D.splitSide k b := by
  unfold splitFaceOwner
  rw [dite_eq_right (by cases b <;> simp [splitNewFace])]
  cases b <;> simp [splitNewFace]

theorem splitOwnerOld_of_ne {f : Fin D.faceCount} (hf : D.faceOwner f ≠ k) :
    D.splitOwnerOld k P e f = Fin.castSucc (D.faceOwner f) := by
  unfold splitOwnerOld
  exact ite_eq_right hf

theorem splitFace_cases (f : Fin (D.faceCount + 2)) :
    (∃ f', f = Fin.castAdd 2 f') ∨ ∃ b, f = D.splitNewFace b := by
  by_cases h : (f : ℕ) < D.faceCount
  · exact Or.inl ⟨⟨f, h⟩, Fin.ext rfl⟩
  · right
    by_cases h' : (f : ℕ) = D.faceCount
    · exact ⟨true, Fin.ext (by simp [splitNewFace, h'])⟩
    · exact ⟨false, Fin.ext (by simp [splitNewFace]; omega)⟩

theorem splitNewFace_ne_castAdd (b : Bool) (f : Fin D.faceCount) :
    D.splitNewFace b ≠ Fin.castAdd 2 f := by
  intro h
  have h' := congrArg Fin.val h
  simp only [splitNewFace, Fin.val_castAdd] at h'
  have := f.isLt
  omega

theorem splitNewFace_injective : Injective D.splitNewFace := by
  intro b b' h
  have h' := congrArg Fin.val h
  cases b <;> cases b' <;> simp_all [splitNewFace]

theorem exists_faceModel_of_splitFaceModel (f : Fin D.faceCount)
    {φ : D.splitFace P e (Fin.castAdd 2 f) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (h : D.splitFaceModel P e (Fin.castAdd 2 f) = .inl φ) :
    ∃ φ' : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl φ' := by
  unfold splitFaceModel at h
  rw [dite_eq_left (show ((Fin.castAdd 2 f : Fin _) : ℕ) < D.faceCount from f.isLt)] at h
  rcases hm : D.faceModel f with φ' | ψ'
  · exact ⟨φ', rfl⟩
  · exfalso
    change Sum.map _ _ (D.faceModel f) = _ at h
    rw [hm] at h
    cases h

end SplitData

/-! ### The split vertices -/

section SplitGeometry

variable {D} {k : Fin D.vertexCount} {P : PieceEmbedding W}
  {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}

theorem image_splitVertex_subset (hv : D.vertex k = .slim P (.sphereInterval e))
    (j : Fin (D.vertexCount + 1)) :
    (D.splitVertex k P e j).image ⊆ (D.vertex (D.splitBase k j)).image := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [splitBase_castSucc]
    by_cases hj : j' = k
    · subst hj
      rw [splitVertex_castSucc_self, image_eq_of_sphereInterval hv]
      exact P.range_sphereHalf_subset e true
    · rw [D.splitVertex_castSucc k P e hj]
  · rw [splitBase_last, splitVertex_last, image_eq_of_sphereInterval hv]
    exact P.range_sphereHalf_subset e false

theorem iUnion_image_splitVertex (hv : D.vertex k = .slim P (.sphereInterval e)) :
    ⋃ j, (D.splitVertex k P e j).image = ⋃ j, (D.vertex j).image := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => (image_splitVertex_subset hv j).trans
      (subset_iUnion (fun i => (D.vertex i).image) _)
  · refine iUnion_subset fun j => ?_
    by_cases hj : j = k
    · subst hj
      intro x hx
      rw [image_eq_of_sphereInterval hv, ← P.range_sphereHalf_union e] at hx
      rcases hx with hx | hx
      · refine mem_iUnion.mpr ⟨Fin.castSucc j, ?_⟩
        rw [splitVertex_castSucc_self]
        exact hx
      · refine mem_iUnion.mpr ⟨Fin.last _, ?_⟩
        rw [splitVertex_last]
        exact hx
    · rw [← D.splitVertex_castSucc k P e hj]
      exact subset_iUnion (fun i => (D.splitVertex k P e i).image) _

theorem splitVertex_disjoint (hv : D.vertex k = .slim P (.sphereInterval e)) :
    Pairwise fun i j => Disjoint (interior (D.splitVertex k P e i).image)
      (interior (D.splitVertex k P e j).image) := by
  intro i j hij
  by_cases hb : D.splitBase k i = D.splitBase k j
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [splitBase_castSucc, splitBase_castSucc] at hb
      exact (hij (congrArg _ hb)).elim
    · rw [splitBase_castSucc, splitBase_last] at hb
      subst hb
      rw [splitVertex_castSucc_self, splitVertex_last]
      exact P.disjoint_interior_sphereHalf e
    · rw [splitBase_last, splitBase_castSucc] at hb
      subst hb
      rw [splitVertex_castSucc_self, splitVertex_last]
      exact (P.disjoint_interior_sphereHalf e).symm
    · exact (hij rfl).elim
  · exact (D.vertex_disjoint hb).mono (interior_mono (image_splitVertex_subset hv i))
      (interior_mono (image_splitVertex_subset hv j))

theorem mem_splitTorusSide (hv : D.vertex k = .slim P (.sphereInterval e))
    (c : Fin D.torusSeamCount) (β : Bool) {x : W.Carrier}
    (hx : x ∈ (D.torusSide c β).elim D.circ.region fun j => (D.vertex j).image) :
    x ∈ ((D.torusSide c β).map Fin.castSucc).elim D.circ.region
      fun j => (D.splitVertex k P e j).image := by
  cases hs : D.torusSide c β with
  | none =>
    rw [hs] at hx
    exact hx
  | some a =>
    rw [hs] at hx
    have ha : a ≠ k := fun h => torusSide_ne_of_sphereInterval hv c β (hs.trans (congrArg some h))
    change x ∈ (D.splitVertex k P e (Fin.castSucc a)).image
    rw [D.splitVertex_castSucc k P e ha]
    exact hx

theorem boundaryImage_splitVertex_castSucc_self :
    (D.splitVertex k P e (Fin.castSucc k)).boundaryImage =
      P.sphereLevel e iccZero ∪ P.sphereLevel e iccMid := by
  rw [splitVertex_castSucc_self]
  exact P.image_boundary_sphereHalf_true e

theorem boundaryImage_splitVertex_last :
    (D.splitVertex k P e (Fin.last _)).boundaryImage =
      P.sphereLevel e iccMid ∪ P.sphereLevel e iccOne := by
  rw [splitVertex_last]
  exact P.image_boundary_sphereHalf_false e

/-! ### The split faces -/

theorem iccZero_ne_iccOne : iccZero ≠ iccOne := fun h => by
  have := congrArg Subtype.val h
  norm_num [iccZero, iccOne] at this

/-- The three cases of the owner of an old face. -/
theorem splitOwnerOld_cases (hv : D.vertex k = .slim P (.sphereInterval e)) (f : Fin D.faceCount) :
    (D.faceOwner f ≠ k ∧ D.splitOwnerOld k P e f = Fin.castSucc (D.faceOwner f)) ∨
      (D.faceOwner f = k ∧ D.face f = P.sphereLevel e iccZero ∧
        D.splitOwnerOld k P e f = Fin.castSucc k) ∨
      (D.faceOwner f = k ∧ D.face f = P.sphereLevel e iccOne ∧
        D.splitOwnerOld k P e f = Fin.last _) := by
  by_cases hf : D.faceOwner f = k
  · by_cases h0 : D.face f = P.sphereLevel e iccZero
    · exact Or.inr (Or.inl ⟨hf, h0, by simp [splitOwnerOld, hf, h0]⟩)
    · have h1 : D.face f = P.sphereLevel e iccOne :=
        (face_eq_sphereLevel_of_sphereInterval hv f hf).resolve_left h0
      exact Or.inr (Or.inr ⟨hf, h1, by simp [splitOwnerOld, hf, h0]⟩)
  · exact Or.inl ⟨hf, D.splitOwnerOld_of_ne k P e hf⟩

theorem splitFace_exhausted (hv : D.vertex k = .slim P (.sphereInterval e))
    (j : Fin (D.vertexCount + 1)) :
    (⋃ (f : Fin (D.faceCount + 2)) (_ : D.splitFaceOwner k P e f = j), D.splitFace P e f) =
      (D.splitVertex k P e j).boundaryImage := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨f, hfj, hx⟩
    rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b, rfl⟩
    · rw [splitFace_castAdd] at hx
      rw [splitFaceOwner_castAdd] at hfj
      rcases splitOwnerOld_cases hv f' with ⟨hne, ho⟩ | ⟨-, h0, ho⟩ | ⟨-, h1, ho⟩
      · rw [← hfj, ho, D.splitVertex_castSucc k P e hne]
        exact D.face_subset_boundaryImage f' hx
      · rw [← hfj, ho, boundaryImage_splitVertex_castSucc_self]
        exact Or.inl (h0 ▸ hx)
      · rw [← hfj, ho, boundaryImage_splitVertex_last]
        exact Or.inr (h1 ▸ hx)
    · rw [splitFace_splitNewFace] at hx
      rw [splitFaceOwner_splitNewFace] at hfj
      rw [← hfj]
      cases b
      · change x ∈ (D.splitVertex k P e (Fin.last _)).boundaryImage
        rw [boundaryImage_splitVertex_last]
        exact Or.inl hx
      · change x ∈ (D.splitVertex k P e (Fin.castSucc k)).boundaryImage
        rw [boundaryImage_splitVertex_castSucc_self]
        exact Or.inr hx
  · intro hx
    rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
    · by_cases ha : a = k
      · subst ha
        rw [boundaryImage_splitVertex_castSucc_self] at hx
        rcases hx with hx | hx
        · obtain ⟨f, hfo, hf⟩ := exists_face_eq_sphereLevel hv (Or.inl rfl)
          refine ⟨Fin.castAdd 2 f, ?_, by rw [splitFace_castAdd, hf]; exact hx⟩
          rw [splitFaceOwner_castAdd]
          simp [splitOwnerOld, hfo, hf]
        · exact ⟨D.splitNewFace true, by rw [splitFaceOwner_splitNewFace]; rfl,
            by rw [splitFace_splitNewFace]; exact hx⟩
      · rw [D.splitVertex_castSucc k P e ha, ← D.face_exhausted] at hx
        obtain ⟨f, hx⟩ := mem_iUnion.mp hx
        obtain ⟨hfo, hx⟩ := mem_iUnion.mp hx
        refine ⟨Fin.castAdd 2 f, ?_, by rw [splitFace_castAdd]; exact hx⟩
        rw [splitFaceOwner_castAdd, D.splitOwnerOld_of_ne k P e (hfo ▸ ha), hfo]
    · rw [boundaryImage_splitVertex_last] at hx
      rcases hx with hx | hx
      · exact ⟨D.splitNewFace false, by rw [splitFaceOwner_splitNewFace]; rfl,
          by rw [splitFace_splitNewFace]; exact hx⟩
      · obtain ⟨f, hfo, hf⟩ := exists_face_eq_sphereLevel hv (Or.inr rfl)
        refine ⟨Fin.castAdd 2 f, ?_, by rw [splitFace_castAdd, hf]; exact hx⟩
        have h0 : D.face f ≠ P.sphereLevel e iccZero := by
          rw [hf]
          intro h
          obtain ⟨y, hy⟩ := P.sphereLevel_nonempty e iccOne
          have hy0 : y ∈ P.sphereLevel e iccZero := h ▸ hy
          exact Set.disjoint_left.mp (P.disjoint_sphereLevel e iccZero_ne_iccOne) hy0 hy
        rw [splitFaceOwner_castAdd]
        simp [splitOwnerOld, hfo, h0]

theorem splitFace_disjoint (hσ : D.sphereSeamCount = 0)
    (hv : D.vertex k = .slim P (.sphereInterval e)) (f f' : Fin (D.faceCount + 2)) (hne : f ≠ f')
    (hS : ∀ c b, ¬ (D.splitFaceKind hσ f = .sphereSeam c b ∧
      D.splitFaceKind hσ f' = .sphereSeam c (!b)))
    (hT : ∀ c b, ¬ (D.splitFaceKind hσ f = .torusSeam c b ∧
      D.splitFaceKind hσ f' = .torusSeam c (!b))) :
    Disjoint (D.splitFace P e f) (D.splitFace P e f') := by
  rcases D.splitFace_cases f with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases D.splitFace_cases f' with ⟨a', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFace_castAdd, splitFace_castAdd]
    refine D.face_disjoint a a' (fun h => hne (congrArg _ h)) (fun c _ _ => (Fin.cast hσ c).elim0)
      fun c β ⟨h1, h2⟩ => hT c β ⟨?_, ?_⟩
    · rw [splitFaceKind_castAdd, h1]
      rfl
    · rw [splitFaceKind_castAdd, h2]
      rfl
  · rw [splitFace_castAdd, splitFace_splitNewFace]
    exact disjoint_face_sphereLevel_mid hv a
  · rw [splitFace_castAdd, splitFace_splitNewFace]
    exact (disjoint_face_sphereLevel_mid hv a').symm
  · have hbb : b' = !b := by
      cases b <;> cases b' <;> first | rfl | exact (hne rfl).elim
    exact (hS 0 b ⟨D.splitFaceKind_splitNewFace hσ b,
      by rw [hbb, D.splitFaceKind_splitNewFace hσ]⟩).elim

theorem splitRim_vertex (hv : D.vertex k = .slim P (.sphereInterval e))
    (hrim : ∀ h b, Disjoint (D.rimChart h b).target (P.middleZone e))
    (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart h b).source) :
    D.rimChart h b p ∈
        (D.splitVertex k P e (D.splitFaceOwner k P e (Fin.castAdd 2 (D.handleFace h b)))).image ↔
      p.2.2 ≤ 0 := by
  have hown := D.handleFace_owner h b
  rw [splitFaceOwner_castAdd]
  rcases splitOwnerOld_cases hv (D.handleFace h b) with ⟨hne, ho⟩ | ⟨hk, h0, ho⟩ | ⟨hk, h1, ho⟩
  · rw [ho, D.splitVertex_castSucc k P e hne, hown]
    exact D.rim_vertex h b hp
  · rw [ho, splitVertex_castSucc_self]
    have hk' : D.handleEnd h b = k := hown ▸ hk
    refine ⟨fun hx => (D.rim_vertex h b hp).mp ?_, fun hp2 =>
      rimChart_mem_sphereHalf hv hk' (hrim h b) true h0 hp hp2⟩
    rw [hk', image_eq_of_sphereInterval hv]
    exact P.range_sphereHalf_subset e true hx
  · rw [ho, splitVertex_last]
    have hk' : D.handleEnd h b = k := hown ▸ hk
    refine ⟨fun hx => (D.rim_vertex h b hp).mp ?_, fun hp2 =>
      rimChart_mem_sphereHalf hv hk' (hrim h b) false h1 hp hp2⟩
    rw [hk', image_eq_of_sphereInterval hv]
    exact P.range_sphereHalf_subset e false hx

theorem splitFace_external (hσ : D.sphereSeamCount = 0)
    (hv : D.vertex k = .slim P (.sphereInterval e)) (f : Fin (D.faceCount + 2)) (i : Fin n)
    (hk : D.splitFaceKind hσ f = .external i) :
    D.splitFace P e f = range (E.torusMap i) ∧
      Fin.castSucc (D.externalOwner i) = D.splitFaceOwner k P e f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b, rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    obtain ⟨h1, h2⟩ := D.face_external f' i (FaceKind.eq_of_liftNoSphere_eq_external hk)
    have hne : D.faceOwner f' ≠ k := fun h => externalOwner_ne_of_sphereInterval hv i (h2.trans h)
    rw [splitFace_castAdd, splitFaceOwner_castAdd, D.splitOwnerOld_of_ne k P e hne, h2]
    exact ⟨h1, rfl⟩
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem splitFace_torusSeam (hσ : D.sphereSeamCount = 0)
    (hv : D.vertex k = .slim P (.sphereInterval e)) (f : Fin (D.faceCount + 2))
    (c : Fin D.torusSeamCount) (b : Bool) (hk : D.splitFaceKind hσ f = .torusSeam c b) :
    D.splitFace P e f = range (fun t => (D.torusSeam c).collar (t, 0)) ∧
      (D.torusSide c b).map Fin.castSucc = some (D.splitFaceOwner k P e f) := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    obtain ⟨h1, h2⟩ := D.face_torusSeam f' c b (FaceKind.eq_of_liftNoSphere_eq_torusSeam hk)
    have hne : D.faceOwner f' ≠ k := fun h =>
      torusSide_ne_of_sphereInterval hv c b (h2.trans (congrArg some h))
    rw [splitFace_castAdd, splitFaceOwner_castAdd, D.splitOwnerOld_of_ne k P e hne, h2]
    exact ⟨h1, rfl⟩
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem splitTorusSeam_face (hσ : D.sphereSeamCount = 0)
    (hv : D.vertex k = .slim P (.sphereInterval e)) (c : Fin D.torusSeamCount) (b : Bool)
    (j : Fin (D.vertexCount + 1)) (hs : (D.torusSide c b).map Fin.castSucc = some j) :
    ∃ f, D.splitFaceOwner k P e f = j ∧ D.splitFaceKind hσ f = .torusSeam c b := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b a ha
  have hne : D.faceOwner f ≠ k := fun h =>
    torusSide_ne_of_sphereInterval hv c b (ha.trans (congrArg some (hfo.symm.trans h)))
  refine ⟨Fin.castAdd 2 f, ?_, ?_⟩
  · rw [splitFaceOwner_castAdd, D.splitOwnerOld_of_ne k P e hne, hfo]
  · rw [splitFaceKind_castAdd, hfk]
    rfl

theorem splitFace_sphereSeam (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (c : Fin 1) (b : Bool) (hk : D.splitFaceKind hσ f = .sphereSeam c b) :
    D.splitFace P e f = range (fun z => (P.middleSeam e).collar (z, 0)) ∧
      D.splitSide k b = D.splitFaceOwner k P e f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    exact (FaceKind.liftNoSphere_ne_sphereSeam _ c b hk).elim
  · rw [splitFaceKind_splitNewFace] at hk
    simp only [FaceKind.sphereSeam.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    rw [splitFace_splitNewFace, splitFaceOwner_splitNewFace]
    exact ⟨(P.middleSeam_zeroSphere e).symm, rfl⟩

theorem splitFace_partition (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (hk : D.splitFaceKind hσ f = .partitioned) :
    (⋃ (h : Fin D.handleCount) (b : Bool) (_ : Fin.castAdd 2 (D.handleFace h b) = f),
        (D.handle h).endDisk b) ∪
      (⋃ (j : Fin D.arcFaceCount) (_ : Fin.castAdd 2 (D.arcOwner j) = f), D.arcFace j) ∪
      (⋃ (j : Fin D.loopFaceCount) (_ : Fin.castAdd 2 (D.loopOwner j) = f), D.loopFace j) =
      D.splitFace P e f := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    simp only [Fin.castAdd_inj, splitFace_castAdd]
    exact D.face_partition f' (FaceKind.eq_of_liftNoSphere_eq_partitioned hk)
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

theorem splitFace_region_inter (hσ : D.sphereSeamCount = 0) (f : Fin (D.faceCount + 2))
    (hk : D.splitFaceKind hσ f = .partitioned) :
    D.splitFace P e f ∩ D.circ.region =
      (⋃ (j : Fin D.arcFaceCount) (_ : Fin.castAdd 2 (D.arcOwner j) = f), D.arcFace j) ∪
        (⋃ (j : Fin D.loopFaceCount) (_ : Fin.castAdd 2 (D.loopOwner j) = f), D.loopFace j) := by
  rcases D.splitFace_cases f with ⟨f', rfl⟩ | ⟨b', rfl⟩
  · rw [splitFaceKind_castAdd] at hk
    simp only [Fin.castAdd_inj, splitFace_castAdd]
    exact D.face_region_inter f' (FaceKind.eq_of_liftNoSphere_eq_partitioned hk)
  · rw [splitFaceKind_splitNewFace] at hk
    cases hk

end SplitGeometry

/-! ### The split certificate -/

/-- **N3a: the split of an `S² × I` vertex at its middle sphere.** For a certificate without sphere
seams and a vertex `k = .slim P (.sphereInterval e)` whose rim charts avoid the middle zone
`P (e (S² × [1/4, 3/4]))`: vertex `k` is replaced by its lower half (index `castSucc k`) and a new last
vertex, its upper half (same piece type and model `e`, map reparametrized in `t`); the middle sphere
`t = 1/2` is the one registered sphere seam (collar `(z, s) ↦ P (e (z, 1/2 + s/4))`, side `true` =
lower half); the faces are the old ones (a face of `k` goes to the half of its end sphere) and the
two sides of the middle sphere. Handles, edge circles, the circle region, torus seams, ports, arcs,
loops and rim charts are those of `D`. -/
def splitSphereInterval (hσ : D.sphereSeamCount = 0) {k : Fin D.vertexCount}
    {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex k = .slim P (.sphereInterval e))
    (hrim : ∀ h b, Disjoint (D.rimChart h b).target (P.middleZone e)) :
    DecompositionCertificate W E where
  external_exhausted := D.external_exhausted
  vertexCount := D.vertexCount + 1
  vertex := D.splitVertex k P e
  handleCount := D.handleCount
  handle := D.handle
  edgeCircleCount := D.edgeCircleCount
  edgeCircle := D.edgeCircle
  circ := D.circ
  cover := by
    rw [iUnion_image_splitVertex hv]
    exact D.cover
  vertex_disjoint := splitVertex_disjoint hv
  handle_disjoint := D.handle_disjoint
  edgeCircle_disjoint := D.edgeCircle_disjoint
  vertex_handle_disjoint j h := (D.vertex_handle_disjoint (D.splitBase k j) h).mono_left
    (interior_mono (image_splitVertex_subset hv j))
  edgeCircle_vertex_disjoint c j := (D.edgeCircle_vertex_disjoint c (D.splitBase k j)).mono_right
    (interior_mono (image_splitVertex_subset hv j))
  edgeCircle_handle_disjoint := D.edgeCircle_handle_disjoint
  circ_vertex_disjoint j := (D.circ_vertex_disjoint (D.splitBase k j)).mono_right
    (interior_mono (image_splitVertex_subset hv j))
  circ_handle_disjoint := D.circ_handle_disjoint
  circ_edgeCircle_disjoint := D.circ_edgeCircle_disjoint
  vertical_fibre := D.vertical_fibre
  edgeCircle_vertical := D.edgeCircle_vertical
  torusSeamCount := D.torusSeamCount
  torusSeam := D.torusSeam
  torusSide c b := (D.torusSide c b).map Fin.castSucc
  torusSide_neg c t s h1 h2 := mem_splitTorusSide hv c true (D.torusSide_neg c t s h1 h2)
  torusSide_pos c t s h1 h2 := mem_splitTorusSide hv c false (D.torusSide_pos c t s h1 h2)
  torusSeam_disjoint := D.torusSeam_disjoint
  sphereSeamCount := 1
  sphereSeam _ := P.middleSeam e
  sphereSide _ b := D.splitSide k b
  sphereSide_neg _ z s h1 h2 := by
    change _ ∈ (D.splitVertex k P e (Fin.castSucc k)).image
    rw [splitVertex_castSucc_self]
    exact P.middleSeam_collar_mem_sphereHalf_true e z h1 h2
  sphereSide_pos _ z s h1 h2 := by
    change _ ∈ (D.splitVertex k P e (Fin.last _)).image
    rw [splitVertex_last]
    exact P.middleSeam_collar_mem_sphereHalf_false e z h1 h2
  sphereSeam_disjoint c d hcd := (hcd (Subsingleton.elim c d)).elim
  sphere_torus_seam_disjoint _ d := (middleSeam_target_disjoint hv).2.2.2.2 d
  externalOwner i := Fin.castSucc (D.externalOwner i)
  external_owned i := by
    rw [D.splitVertex_castSucc k P e (externalOwner_ne_of_sphereInterval hv i)]
    exact D.external_owned i
  faceCount := D.faceCount + 2
  face := D.splitFace P e
  faceOwner := D.splitFaceOwner k P e
  faceModel := D.splitFaceModel P e
  face_exhausted := splitFace_exhausted hv
  faceKind := D.splitFaceKind hσ
  face_disjoint := splitFace_disjoint hσ hv
  face_external := splitFace_external hσ hv
  external_face i := by
    obtain ⟨f, hf⟩ := D.external_face i
    refine ⟨Fin.castAdd 2 f, ?_⟩
    rw [splitFaceKind_castAdd, hf]
    rfl
  face_torusSeam := splitFace_torusSeam hσ hv
  torusSeam_face := splitTorusSeam_face hσ hv
  face_sphereSeam := splitFace_sphereSeam hσ
  sphereSeam_face c b := ⟨D.splitNewFace b, by rw [splitFaceOwner_splitNewFace], by
    rw [splitFaceKind_splitNewFace, Subsingleton.elim c 0]⟩
  handleEnd h b := D.splitFaceOwner k P e (Fin.castAdd 2 (D.handleFace h b))
  handleFace h b := Fin.castAdd 2 (D.handleFace h b)
  handleFace_owner _ _ := rfl
  handleFace_kind h b := by
    rw [splitFaceKind_castAdd, D.handleFace_kind]
    rfl
  handleEnd_face h b := by
    rw [splitFace_castAdd]
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
  face_partition := splitFace_partition hσ
  face_region_inter := splitFace_region_inter hσ
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
  rim_vertex h b := splitRim_vertex hv hrim h b
  rim_handle := D.rim_handle
  rim_region := D.rim_region
  rim_label := D.rim_label
  rim_disjoint := D.rim_disjoint
  external_region_disjoint := D.external_region_disjoint
  external_handle_disjoint := D.external_handle_disjoint
  external_edgeCircle_disjoint := D.external_edgeCircle_disjoint
  external_torusSeam_disjoint := D.external_torusSeam_disjoint
  external_sphereSeam_disjoint i _ :=
    ((middleSeam_target_disjoint hv).2.1 (D.externalOwner i)
      (externalOwner_ne_of_sphereInterval hv i)).symm.mono_left (D.external_owned i)
  rim_external_disjoint := D.rim_external_disjoint
  rim_torusSeam_disjoint := D.rim_torusSeam_disjoint
  rim_sphereSeam_disjoint h b _ := (hrim h b).mono_right (P.middleSeam_target_subset_middleZone e)
  sphereSeam_region_disjoint _ := (middleSeam_target_disjoint hv).2.2.2.1
  sphereSeam_handle_disjoint _ h := (middleSeam_target_disjoint hv).2.2.1 h

/-! ### What the split keeps and what it counts -/

section SplitFacts

variable {D} (hσ : D.sphereSeamCount = 0) {k : Fin D.vertexCount} {P : PieceEmbedding W}
  {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
  (hv : D.vertex k = .slim P (.sphereInterval e))
  (hrim : ∀ h b, Disjoint (D.rimChart h b).target (P.middleZone e))

theorem splitSphereInterval_vertex :
    (D.splitSphereInterval hσ hv hrim).vertex = D.splitVertex k P e := rfl

theorem splitSphereInterval_sphereSeamCount :
    (D.splitSphereInterval hσ hv hrim).sphereSeamCount = 1 := rfl

theorem splitSphereInterval_sphereSeam (c : Fin (D.splitSphereInterval hσ hv hrim).sphereSeamCount) :
    (D.splitSphereInterval hσ hv hrim).sphereSeam c = P.middleSeam e := rfl

theorem splitSphereInterval_sphereSide (c : Fin (D.splitSphereInterval hσ hv hrim).sphereSeamCount)
    (b : Bool) : (D.splitSphereInterval hσ hv hrim).sphereSide c b = D.splitSide k b := rfl

theorem splitSphereInterval_rimChart : (D.splitSphereInterval hσ hv hrim).rimChart = D.rimChart :=
  rfl

theorem splitSphereInterval_handle : (D.splitSphereInterval hσ hv hrim).handle = D.handle := rfl

/-- The rim-product clause is carried: the rim charts and handles of the split are those of `D`. -/
theorem RimProduct.splitSphereInterval (hD : D.RimProduct) :
    (D.splitSphereInterval hσ hv hrim).RimProduct :=
  hD

/-- No closed zero vertex is created. -/
theorem splitSphereInterval_ne_closedZero (hnz : ∀ j C, D.vertex j ≠ .closedZero C)
    (j : Fin (D.splitSphereInterval hσ hv hrim).vertexCount) (C : ClosedZeroPiece W) :
    (D.splitSphereInterval hσ hv hrim).vertex j ≠ .closedZero C := by
  have key : ∀ j' : Fin (D.vertexCount + 1), D.splitVertex k P e j' ≠ .closedZero C := by
    intro j'
    rcases Fin.eq_castSucc_or_eq_last j' with ⟨a, rfl⟩ | rfl
    · by_cases ha : a = k
      · rw [ha, splitVertex_castSucc_self]
        exact fun h => by cases h
      · rw [D.splitVertex_castSucc k P e ha]
        exact hnz a C
    · rw [splitVertex_last]
      exact fun h => by cases h
  exact key j

/-- **The bad vertices of the split off the new seam are bad vertices of `D` other than `k`.** -/
theorem filter_badVertexSet_splitSphereInterval_subset :
    ((D.splitSphereInterval hσ hv hrim).badVertexSet.filter fun j =>
      ∀ b, j ≠ (D.splitSphereInterval hσ hv hrim).sphereSide ⟨0, Nat.one_pos⟩ b) ⊆
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
      change D.splitFaceOwner k P e (Fin.castAdd 2 f') = _ at hfo
      rw [splitFaceOwner_castAdd] at hfo
      have hf'o : D.faceOwner f' = a := by
        rcases splitOwnerOld_cases hv f' with ⟨-, ho⟩ | ⟨-, -, ho⟩ | ⟨-, -, ho⟩
        · rw [ho] at hfo
          exact Fin.castSucc_inj.mp hfo
        · rw [ho] at hfo
          exact (ha (Fin.castSucc_inj.mp hfo).symm).elim
        · rw [ho] at hfo
          exact (Fin.castSucc_ne_last a hfo.symm).elim
      obtain ⟨φ', hφ'⟩ := D.exists_faceModel_of_splitFaceModel P e f' hφ
      refine mem_badVertexSet_iff.mpr ⟨?_, f', hf'o,
        FaceKind.eq_of_liftNoSphere_eq_partitioned hfk, φ', hφ'⟩
      rw [← D.splitVertex_castSucc k P e ha]
      exact hnb
    · change D.splitFaceKind hσ (D.splitNewFace b) = _ at hfk
      rw [splitFaceKind_splitNewFace] at hfk
      cases hfk
  · exact (h2 rfl).elim

/-- **The count of N3a**: the bad vertices of the split off the new seam are at most `b(D) - 1`. -/
theorem card_filter_badVertexSet_splitSphereInterval (hk : k ∈ D.badVertexSet) :
    ((D.splitSphereInterval hσ hv hrim).badVertexSet.filter fun j =>
      ∀ b, j ≠ (D.splitSphereInterval hσ hv hrim).sphereSide ⟨0, Nat.one_pos⟩ b).card + 1 ≤
      D.badVertexCount := by
  have h1 := Finset.card_le_card (filter_badVertexSet_splitSphereInterval_subset hσ hv hrim)
  have h3 : ((D.badVertexSet.erase k).map Fin.castSuccEmb).card = D.badVertexCount - 1 := by
    rw [Finset.card_map, Finset.card_erase_of_mem hk, card_badVertexSet]
  have h4 := h1.trans_eq h3
  have h2 : 0 < D.badVertexCount := by
    rw [← card_badVertexSet]
    exact Finset.card_pos.mpr ⟨k, hk⟩
  omega

end SplitFacts

end DecompositionCertificate

/-! ## The S³ inhabitant (Codex X118) -/

/-- **Why the split is not instantiated on the S³ inhabitant of X118**: its hypotheses fail there —
the inhabitant has one sphere seam (the split needs none) and no bad vertex (the split needs a bad
`S² × I` vertex; its two vertices are balls). -/
theorem standardSphereCertificate_not_split :
    standardSphereCertificate.{u}.sphereSeamCount ≠ 0 ∧
      standardSphereCertificate.{u}.badVertexSet = ∅ :=
  ⟨one_ne_zero, badVertexSet_standardSphereCertificate⟩

end GC.GraphManifold.Assembly
