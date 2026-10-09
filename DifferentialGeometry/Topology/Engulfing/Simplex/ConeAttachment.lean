import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexMembrane
import DifferentialGeometry.Topology.Engulfing.Simplex.AdjoinSimplex
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry Metric
open scoped ContinuousMap BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev ConeSpace (E : Type*) := WithLp 2 (E × ℝ)

def coneInclusion : E →ₗ[ℝ] ConeSpace E :=
  (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm.toLinearMap.comp (LinearMap.inl ℝ E ℝ)

def coneProjection : ConeSpace E →ₗ[ℝ] E :=
  (LinearMap.fst ℝ E ℝ).comp (WithLp.linearEquiv 2 ℝ (E × ℝ)).toLinearMap

def coneHeight : ConeSpace E →ₗ[ℝ] ℝ :=
  (LinearMap.snd ℝ E ℝ).comp (WithLp.linearEquiv 2 ℝ (E × ℝ)).toLinearMap

def coneApex : ConeSpace E := WithLp.toLp 2 (0, 1)

@[simp] theorem coneProjection_inclusion (x : E) : coneProjection (coneInclusion x) = x := rfl
@[simp] theorem coneHeight_inclusion (x : E) : coneHeight (coneInclusion x) = 0 := rfl
@[simp] theorem coneProjection_apex : coneProjection (coneApex : ConeSpace E) = 0 := rfl
@[simp] theorem coneHeight_apex : coneHeight (coneApex : ConeSpace E) = 1 := rfl

theorem coneInclusion_injective : Function.Injective (coneInclusion : E → ConeSpace E) :=
  Function.LeftInverse.injective coneProjection_inclusion

def coneVertices {m : ℕ} (v : Fin m → E) : Fin (m + 1) → ConeSpace E :=
  Fin.snoc (fun i => coneInclusion (v i)) coneApex

@[simp] theorem coneVertices_castSucc {m : ℕ} (v : Fin m → E) (i : Fin m) :
    coneVertices v i.castSucc = coneInclusion (v i) := by simp [coneVertices]
@[simp] theorem coneVertices_last {m : ℕ} (v : Fin m → E) :
    coneVertices v (Fin.last m) = coneApex := by simp [coneVertices]

theorem coneVertices_independent {m : ℕ} (v : Fin m → E)
    (hv : AffineIndependent ℝ v) : AffineIndependent ℝ (coneVertices v) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hpoint i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hpoint
  have hl : w (Fin.last m) = 0 := by
    have h := congrArg (coneHeight : ConeSpace E → ℝ) hpoint
    simpa [map_sum, Fin.sum_univ_castSucc] using h
  have hw₀ : ∑ j : Fin m, w j.castSucc = 0 := by
    simpa [Fin.sum_univ_castSucc, hl] using hw
  have hv₀ : ∑ j : Fin m, w j.castSucc • v j = 0 := by
    have h := congrArg (coneProjection : ConeSpace E → E) hpoint
    simpa [map_sum, Fin.sum_univ_castSucc] using h
  refine Fin.lastCases hl (fun j => ?_) i
  exact hv.eq_zero_of_sum_eq_zero hw₀ hv₀ j (Finset.mem_univ j)

theorem coneHeight_simplexPoint {m : ℕ} (v : Fin m → E) (w : Fin (m + 1) → ℝ) :
    coneHeight (simplexPoint (coneVertices v) w) = w (Fin.last m) := by
  simp [simplexPoint, map_sum, Fin.sum_univ_castSucc]

theorem simplexFacet_coneVertices_last {m : ℕ} (v : Fin m → E) :
    simplexFacet (coneVertices v) (Fin.last m) =
      coneInclusion '' convexHull ℝ (range v) := by
  have himage : coneVertices v '' ({Fin.last m}ᶜ : Set (Fin (m + 1))) =
      coneInclusion '' range v := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i hi
      · simp
      · intro _
        exact ⟨v j, mem_range_self j, (coneVertices_castSucc v j).symm⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j.castSucc, by simp, coneVertices_castSucc v j⟩
  rw [simplexFacet, himage, ← (coneInclusion : E →ₗ[ℝ] ConeSpace E).image_convexHull]

theorem cone_inter_inclusion {m : ℕ} (v : Fin m → E)
    (hv : AffineIndependent ℝ v) (A : Set E) (hbase : convexHull ℝ (range v) ⊆ A) :
    (coneInclusion '' A) ∩ convexHull ℝ (range (coneVertices v)) =
      simplexFacet (coneVertices v) (Fin.last m) := by
  apply Subset.antisymm
  · rintro x ⟨⟨y, hy, hxy⟩, hx⟩
    rw [← simplexPoint_image_simplex (coneVertices v)] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    apply (simplexPoint_mem_facet_iff _ (coneVertices_independent v hv) hw _).mpr
    rw [← coneHeight_simplexPoint v w, ← hxy, coneHeight_inclusion]
  · intro x hx
    refine ⟨?_, simplexFacet_subset_convexHull _ _ hx⟩
    rw [simplexFacet_coneVertices_last] at hx
    exact image_mono hbase hx

theorem simplexBoundary_reindex {ι κ : Type*} [Finite ι] [Nonempty ι]
    [Finite κ] [Nonempty κ] (v : κ → E) (e : ι ≃ κ) :
    simplexBoundary (v ∘ e) = simplexBoundary v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  have hfacet : ∀ i, simplexFacet (v ∘ e) i = simplexFacet v (e i) := by
    intro i
    unfold simplexFacet
    apply congrArg (convexHull ℝ)
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, by simpa using hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨e.symm j, ?_, by simp⟩
      simpa [Equiv.symm_apply_eq] using hj
  simp only [simplexBoundary, hfacet]
  exact e.surjective.iUnion_comp _

def coneBaseIndex (m : ℕ) : Fin m ≃ {i : Fin (m + 1) // i ≠ Fin.last m} :=
  Equiv.ofBijective (fun i => ⟨i.castSucc, by simp⟩) ⟨by
    intro i j hij
    exact Fin.castSucc_injective m (congrArg Subtype.val hij), by
    rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    exact ⟨j, rfl⟩⟩

theorem simplexBoundary_cone_base {m : ℕ} [NeZero m] (v : Fin m → E) :
    simplexBoundary (facetVertices (coneVertices v) (Fin.last m)) =
      coneInclusion '' simplexBoundary v := by
  have : Nonempty {i : Fin (m + 1) // i ≠ Fin.last m} :=
    ⟨coneBaseIndex m 0⟩
  rw [← simplexBoundary_reindex _ (coneBaseIndex m)]
  have hvertices : facetVertices (coneVertices v) (Fin.last m) ∘ coneBaseIndex m =
      fun i => coneInclusion (v i) := by
    funext i
    exact coneVertices_castSucc v i
  rw [hvertices]
  simp only [simplexBoundary, simplexFacet, image_iUnion]
  apply congrArg (fun F : Fin m → Set (ConeSpace E) => ⋃ i, F i)
  funext i
  rw [(coneInclusion : E →ₗ[ℝ] ConeSpace E).image_convexHull, image_image]

variable [DecidableEq E] [DecidableEq (ConeSpace E)]

def coneBaseComplex (K : SimplicialComplex ℝ E) : SimplicialComplex ℝ (ConeSpace E) :=
  injectiveImageComplex K coneInclusion
    (fun _ _ => ⟨coneInclusion.toAffineMap, fun _ _ => rfl⟩) coneInclusion_injective.injOn

omit [DecidableEq E] in
theorem coneBaseComplex_finite_faces (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    (coneBaseComplex K).faces.Finite := by
  classical
  exact injectiveImageComplex_finite_faces K hK _ _ _

omit [DecidableEq E] in
@[simp] theorem coneBaseComplex_space (K : SimplicialComplex ℝ E) :
    (coneBaseComplex K).space = coneInclusion '' K.space := by
  classical
  exact injectiveImageComplex_space K _ _ _

omit [DecidableEq E] in
theorem coneBaseComplex_face_card_le (K : SimplicialComplex ℝ E) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∀ s ∈ (coneBaseComplex K).faces, s.card ≤ d + 1 := by
  classical
  rintro _ ⟨s, hs, rfl⟩
  rw [Finset.card_image_of_injective _ coneInclusion_injective]
  exact hd s hs

def coneBaseHomeomorph (K : SimplicialComplex ℝ E) : K.space ≃ₜ (coneBaseComplex K).space := by
  let i : K.space → (coneBaseComplex K).space := fun x =>
    ⟨coneInclusion x.1, by
      rw [coneBaseComplex_space]
      exact mem_image_of_mem _ x.2⟩
  let p : (coneBaseComplex K).space → K.space := fun x => ⟨coneProjection x.1, by
    have hx : x.1 ∈ coneInclusion '' K.space := by
      simpa only [coneBaseComplex_space] using x.2
    obtain ⟨y, hy, hxy⟩ := hx
    simpa [← hxy] using hy⟩
  refine
    { toFun := i
      invFun := p
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro x
    exact Subtype.ext (coneProjection_inclusion x.1)
  · intro x
    apply Subtype.ext
    have hx : x.1 ∈ coneInclusion '' K.space := by
      simpa only [coneBaseComplex_space] using x.2
    obtain ⟨y, hy, hxy⟩ := hx
    change coneInclusion (coneProjection x.1) = x.1
    simp [← hxy]
  · exact (coneInclusion.continuous_of_finiteDimensional.comp
      continuous_subtype_val).subtype_mk _
  · exact (coneProjection.continuous_of_finiteDimensional.comp
      continuous_subtype_val).subtype_mk _

omit [DecidableEq E] in
theorem exists_attached_cone_membrane {q d : ℕ} {M : Type*} [TopologicalSpace M]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (v : Fin (q + 2) → E) (hv : AffineIndependent ℝ v)
    (hbase : convexHull ℝ (range v) ⊆ K.space)
    (U : Set M) (f : C(K.space, M))
    (hboundary : ∀ x : K.space, x.1 ∈ simplexBoundary v → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 2))) 1, M), b.Nullhomotopic) :
    ∃ T J : SimplicialComplex ℝ (ConeSpace E),
      T.faces.Finite ∧ (∀ s ∈ T.faces, s.card ≤ max d (q + 2) + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ T.faces ∧ J.space = coneInclusion '' K.space ∧
      simplicialRefines J (coneBaseComplex K) ∧
      ∃ (hspace : T.space = coneInclusion '' K.space ∪ convexHull ℝ (range (coneVertices v)))
        (F : C(T.space, M)),
        (∀ x : K.space, F ⟨coneInclusion x.1,
          hspace.symm ▸ (show coneInclusion x.1 ∈ coneInclusion '' K.space ∪
            convexHull ℝ (range (coneVertices v)) from Or.inl (mem_image_of_mem _ x.2))⟩ = f x) ∧
        (∀ x : (coneSplit (Fin.last (q + 2))).lowerRoof (coneVertices v),
          F ⟨x.1, hspace.symm ▸ (show x.1 ∈ coneInclusion '' K.space ∪
            convexHull ℝ (range (coneVertices v)) from Or.inr
              ((coneSplit _).lowerRoof_subset_simplex _ x.2))⟩ ∈ U) := by
  classical
  let f₀ : C((coneBaseComplex K).space, M) := f.comp
    ⟨(coneBaseHomeomorph K).symm, (coneBaseHomeomorph K).symm.continuous⟩
  have hattach : (coneBaseComplex K).space ∩ convexHull ℝ (range (coneVertices v)) =
      simplexFacet (coneVertices v) (Fin.last (q + 2)) := by
    rw [coneBaseComplex_space]
    exact cone_inter_inclusion v hv K.space hbase
  have hb₀ : ∀ x : (coneBaseComplex K).space,
      x.1 ∈ simplexBoundary (facetVertices (coneVertices v) (Fin.last (q + 2))) →
        f₀ x ∈ U := by
    intro x hx
    rw [simplexBoundary_cone_base] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    apply hboundary ((coneBaseHomeomorph K).symm x)
    change coneProjection x.1 ∈ simplexBoundary v
    simpa [← hxy] using hy
  obtain ⟨T, J, hT, hdim, hJ, hJT, hJS, href, hspace, F, hF₀, hF₁⟩ :=
    exists_affine_cone_membrane_on_finite_complex (coneBaseComplex K)
      (coneBaseComplex_finite_faces K hK) (coneBaseComplex_face_card_le K hd)
      (coneVertices v) (coneVertices_independent v hv) (Fin.last (q + 2))
      hattach U f₀ hb₀ hU hM
  have hspace' : T.space = coneInclusion '' K.space ∪
      convexHull ℝ (range (coneVertices v)) := by simpa only [coneBaseComplex_space] using hspace
  refine ⟨T, J, hT, hdim, hJ, hJT, hJS.trans (coneBaseComplex_space K), href,
    hspace', F, ?_, hF₁⟩
  intro x
  exact hF₀ (coneBaseHomeomorph K x)

def coneVertexSet {m : ℕ} (v : Fin m → E) : Finset (ConeSpace E) :=
  Finset.univ.image (coneVertices v)

def coneBaseVertexSet {m : ℕ} (v : Fin m → E) : Finset (ConeSpace E) :=
  (Finset.univ.image v).image coneInclusion

omit [DecidableEq E] in
@[simp] theorem convexHull_coneVertexSet {m : ℕ} (v : Fin m → E) :
    convexHull ℝ (coneVertexSet v : Set (ConeSpace E)) =
      convexHull ℝ (range (coneVertices v)) := by
  classical
  simp [coneVertexSet]

@[simp] theorem convexHull_coneBaseVertexSet {m : ℕ} (v : Fin m → E) :
    convexHull ℝ (coneBaseVertexSet v : Set (ConeSpace E)) =
      coneInclusion '' convexHull ℝ (range v) := by
  rw [coneBaseVertexSet, Finset.coe_image, ← coneInclusion.image_convexHull]
  simp

omit [DecidableEq E] in
theorem coneVertexSet_independent {m : ℕ} (v : Fin m → E) (hv : AffineIndependent ℝ v) :
    AffineIndependent ℝ ((↑) : coneVertexSet v → ConeSpace E) := by
  classical
  have h := (coneVertices_independent v hv).range
  have heq : range (coneVertices v) = (coneVertexSet v : Set (ConeSpace E)) := by
    simp [coneVertexSet]
  rwa [heq] at h

theorem coneBaseVertexSet_subset {m : ℕ} (v : Fin m → E) :
    coneBaseVertexSet v ⊆ coneVertexSet v := by
  rintro x hx
  obtain ⟨_, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, coneVertices_castSucc v i⟩

theorem coneBaseVertexSet_mem {m : ℕ} (K : SimplicialComplex ℝ E) (v : Fin m → E)
    (hf : Finset.univ.image v ∈ K.faces) : coneBaseVertexSet v ∈ (coneBaseComplex K).faces :=
  ⟨_, hf, rfl⟩

theorem cone_face_attachment {m : ℕ} (K : SimplicialComplex ℝ E) (v : Fin m → E)
    (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    (coneBaseComplex K).space ∩ convexHull ℝ (coneVertexSet v : Set (ConeSpace E)) =
      convexHull ℝ (coneBaseVertexSet v : Set (ConeSpace E)) := by
  rw [coneBaseComplex_space, convexHull_coneVertexSet, convexHull_coneBaseVertexSet,
    ← simplexFacet_coneVertices_last]
  apply cone_inter_inclusion v hv K.space
  simpa using K.convexHull_subset_space hf

def coneAttachmentComplex {m : ℕ} (K : SimplicialComplex ℝ E) (v : Fin m → E)
    (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    SimplicialComplex ℝ (ConeSpace E) :=
  adjoinSimplexAlongFace (coneBaseComplex K) (coneVertexSet v) (coneBaseVertexSet v)
    (coneVertexSet_independent v hv) (coneBaseVertexSet_mem K v hf)
    (coneBaseVertexSet_subset v) (cone_face_attachment K v hv hf)

theorem coneAttachmentComplex_finite_faces {m : ℕ} (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (v : Fin m → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces) : (coneAttachmentComplex K v hv hf).faces.Finite :=
  AdjoinSimplexAlongFace.finite_faces _ _ _ _ _ _ _ (coneBaseComplex_finite_faces K hK)

theorem coneAttachmentComplex_old_faces {m : ℕ} (K : SimplicialComplex ℝ E)
    (v : Fin m → E) (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    (coneBaseComplex K).faces ⊆ (coneAttachmentComplex K v hv hf).faces :=
  AdjoinSimplexAlongFace.old_faces_subset _ _ _ _ _ _ _

theorem coneAttachmentComplex_cone_face {m : ℕ} (K : SimplicialComplex ℝ E)
    (v : Fin m → E) (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    coneVertexSet v ∈ (coneAttachmentComplex K v hv hf).faces :=
  AdjoinSimplexAlongFace.simplex_mem_faces _ _ _ _ _ _ _

@[simp] theorem coneAttachmentComplex_space {m : ℕ} (K : SimplicialComplex ℝ E)
    (v : Fin m → E) (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    (coneAttachmentComplex K v hv hf).space =
      coneInclusion '' K.space ∪ convexHull ℝ (range (coneVertices v)) := by
  unfold coneAttachmentComplex
  rw [AdjoinSimplexAlongFace.space, coneBaseComplex_space, convexHull_coneVertexSet]

theorem coneAttachmentComplex_face_card_le {m d : ℕ} (K : SimplicialComplex ℝ E)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (v : Fin m → E)
    (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    ∀ s ∈ (coneAttachmentComplex K v hv hf).faces, s.card ≤ max d m + 1 := by
  apply AdjoinSimplexAlongFace.face_card_le _ _ _ _ _ _ _
    (coneBaseComplex_face_card_le K hd)
  exact Finset.card_image_le.trans (by simp)

theorem coneAttachmentComplex_expansion {m : ℕ} (K : SimplicialComplex ℝ E)
    (v : Fin m → E) (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces)
    (s : SimplexSplit (Fin (m + 1))) :
    FiniteSimplexExpansionIn (coneAttachmentComplex K v hv hf)
      (s.lowerRoof (coneVertices v)) (convexHull ℝ (range (coneVertices v))) := by
  have hB : ProperSimplexRoof (coneVertexSet v) (s.right.image (coneVertices v)) := by
    refine ⟨Finset.image_subset_image (Finset.subset_univ _), s.right_nonempty.image _, ?_⟩
    obtain ⟨i, hi⟩ := s.left_nonempty
    refine ⟨coneVertices v i, Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩⟩
    intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    have heq := (coneVertices_independent v hv).injective hji
    subst j
    exact (Finset.mem_compl.mp hj) hi
  have h := FiniteSimplexExpansionIn.simplex_of_properRoof
    (coneAttachmentComplex_cone_face K v hv hf) hB
  rw [convexHull_coneVertexSet] at h
  change FiniteSimplexExpansionIn _
    (simplexRoof (Finset.univ.image (coneVertices v)) (s.right.image (coneVertices v))) _ at h
  rw [simplexRoof_image_vertices _ (coneVertices_independent v hv)] at h
  exact h

def coneAttachmentSourceMap {m : ℕ} (K : SimplicialComplex ℝ E)
    (v : Fin m → E) (hv : AffineIndependent ℝ v) (hf : Finset.univ.image v ∈ K.faces) :
    C(K.space, (coneAttachmentComplex K v hv hf).space) := by
  let i : K.space → (coneAttachmentComplex K v hv hf).space := fun x =>
    ⟨coneInclusion x.1, by
      rw [coneAttachmentComplex_space]
      exact Or.inl (mem_image_of_mem _ x.2)⟩
  exact ⟨i, (coneInclusion.continuous_of_finiteDimensional.comp
    continuous_subtype_val).subtype_mk _⟩

theorem exists_face_cone_membrane {q : ℕ} {M : Type*} [TopologicalSpace M]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin (q + 2) → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces)
    (U : Set M) (f : C(K.space, M))
    (hboundary : ∀ x : K.space, x.1 ∈ simplexBoundary v → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 2))) 1, M), b.Nullhomotopic) :
    ∃ F : C((coneAttachmentComplex K v hv hf).space, M),
      (∀ x : K.space, F (coneAttachmentSourceMap K v hv hf x) = f x) ∧
      ∀ x : (coneAttachmentComplex K v hv hf).space,
        x.1 ∈ (coneSplit (Fin.last (q + 2))).lowerRoof (coneVertices v) → F x ∈ U := by
  let f₀ : C((coneBaseComplex K).space, M) := f.comp
    ⟨(coneBaseHomeomorph K).symm, (coneBaseHomeomorph K).symm.continuous⟩
  have hbase : convexHull ℝ (range v) ⊆ K.space := by
    simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using K.convexHull_subset_space hf
  have hattach : (coneBaseComplex K).space ∩ convexHull ℝ (range (coneVertices v)) =
      simplexFacet (coneVertices v) (Fin.last (q + 2)) := by
    rw [coneBaseComplex_space]
    exact cone_inter_inclusion v hv K.space hbase
  have hb₀ : ∀ x : (coneBaseComplex K).space,
      x.1 ∈ simplexBoundary (facetVertices (coneVertices v) (Fin.last (q + 2))) →
        f₀ x ∈ U := by
    intro x hx
    rw [simplexBoundary_cone_base] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    apply hboundary ((coneBaseHomeomorph K).symm x)
    change coneProjection x.1 ∈ simplexBoundary v
    simpa [← hxy] using hy
  obtain ⟨G, hG₀, hG₁⟩ := exists_affine_cone_membrane_glue
    (coneVertices v) (coneVertices_independent v hv) (Fin.last (q + 2))
    ((coneBaseComplex_finite_faces K hK).isCompact_biUnion
      (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)) hattach U f₀ hb₀ hU hM
  have hspace : (coneAttachmentComplex K v hv hf).space =
      (coneBaseComplex K).space ∪ convexHull ℝ (range (coneVertices v)) := by
    rw [coneAttachmentComplex_space, coneBaseComplex_space]
  let F : C((coneAttachmentComplex K v hv hf).space, M) := G.comp
    ⟨fun x => ⟨x.1, hspace ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  refine ⟨F, fun x => hG₀ (coneBaseHomeomorph K x), ?_⟩
  intro x hx
  exact hG₁ ⟨x.1, hx⟩

omit [DecidableEq E] [DecidableEq (ConeSpace E)] in
theorem coneHeight_mem_unitInterval {m : ℕ} (v : Fin m → E)
    {x : ConeSpace E} (hx : x ∈ convexHull ℝ (range (coneVertices v))) :
    coneHeight x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  apply convexHull_min (t := coneHeight ⁻¹' Set.Icc (0 : ℝ) 1) ?_
    ((convex_Icc (0 : ℝ) 1).linear_preimage coneHeight) hx
  rintro _ ⟨i, rfl⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

omit [DecidableEq E] [DecidableEq (ConeSpace E)] in
theorem cone_vertex_roof (v : Fin 1 → E) :
    (coneSplit (Fin.last 1)).lowerRoof (coneVertices v) = {coneApex} := by
  classical
  have hr : (coneSplit (Fin.last 1)).right = {0} := by decide
  rw [SimplexSplit.lowerRoof, hr]
  simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
  have hverts : coneVertices v '' ({0}ᶜ : Set (Fin 2)) = {coneApex} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i = Fin.last 1 := by fin_cases i <;> simp_all
      exact hi' ▸ coneVertices_last v
    · intro hx
      rcases hx with rfl
      exact ⟨Fin.last 1, by decide, coneVertices_last v⟩
  rw [simplexFacet, hverts, convexHull_singleton]

theorem exists_vertex_cone_membrane {M : Type*} [TopologicalSpace M] [PathConnectedSpace M]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin 1 → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces)
    (U : Set M) (hU : U.Nonempty) (f : C(K.space, M)) :
    ∃ F : C((coneAttachmentComplex K v hv hf).space, M),
      (∀ x : K.space, F (coneAttachmentSourceMap K v hv hf x) = f x) ∧
      ∀ x : (coneAttachmentComplex K v hv hf).space,
        x.1 ∈ (coneSplit (Fin.last 1)).lowerRoof (coneVertices v) → F x ∈ U := by
  let x₀ : K.space := ⟨v 0, K.subset_space hf
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)⟩
  obtain ⟨y, hy⟩ := hU
  obtain ⟨p⟩ := PathConnectedSpace.joined (f x₀) y
  let f₀ : C((coneBaseComplex K).space, M) := f.comp
    ⟨(coneBaseHomeomorph K).symm, (coneBaseHomeomorph K).symm.continuous⟩
  let H : C(convexHull ℝ (range (coneVertices v)), M) := p.toContinuousMap.comp
    ⟨fun x => ⟨coneHeight x.1, coneHeight_mem_unitInterval v x.2⟩,
      (coneHeight.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _⟩
  have hrange : range v = {v 0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact congrArg v (Subsingleton.elim i 0)
    · rintro rfl
      exact mem_range_self 0
  have hbase : convexHull ℝ (range v) ⊆ K.space := by
    simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using K.convexHull_subset_space hf
  have hagree : ∀ (x : ConeSpace E) (hxA : x ∈ (coneBaseComplex K).space)
      (hxB : x ∈ convexHull ℝ (range (coneVertices v))), f₀ ⟨x, hxA⟩ = H ⟨x, hxB⟩ := by
    intro x hxA hxB
    have hxI : x ∈ (coneInclusion '' K.space) ∩ convexHull ℝ (range (coneVertices v)) :=
      ⟨by simpa only [coneBaseComplex_space] using hxA, hxB⟩
    rw [cone_inter_inclusion v hv K.space hbase, simplexFacet_coneVertices_last,
      hrange, convexHull_singleton, image_singleton] at hxI
    have hxeq : x = coneInclusion (v 0) := hxI
    subst x
    change f x₀ = p 0
    exact p.source.symm
  obtain ⟨G, hG₀, hG₁⟩ := exists_continuousMap_compact_union
    ((coneBaseComplex_finite_faces K hK).isCompact_biUnion
      (fun s _ => s.finite_toSet.isCompact_convexHull ℝ))
    ((finite_range (coneVertices v)).isCompact_convexHull ℝ) f₀ H hagree
  have hspace : (coneAttachmentComplex K v hv hf).space =
      (coneBaseComplex K).space ∪ convexHull ℝ (range (coneVertices v)) := by
    rw [coneAttachmentComplex_space, coneBaseComplex_space]
  let F : C((coneAttachmentComplex K v hv hf).space, M) := G.comp
    ⟨fun x => ⟨x.1, hspace ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  refine ⟨F, fun x => hG₀ (coneBaseHomeomorph K x), ?_⟩
  intro x hx
  rw [cone_vertex_roof] at hx
  have hxeq : x.1 = coneApex := hx
  have hxcone : x.1 ∈ convexHull ℝ (range (coneVertices v)) := by
    rw [hxeq, ← coneVertices_last v]
    exact subset_convexHull ℝ _ (mem_range_self _)
  have heq : F x = H ⟨x.1, hxcone⟩ := hG₁ ⟨x.1, hxcone⟩
  rw [heq]
  change p ⟨coneHeight x.1, _⟩ ∈ U
  have ht : (⟨coneHeight x.1, coneHeight_mem_unitInterval v hxcone⟩ : Set.Icc (0 : ℝ) 1) = 1 := by
    apply Subtype.ext
    simp [hxeq]
  rw [ht, p.target]
  exact hy

end

end DifferentialGeometry.Topology.Engulfing
