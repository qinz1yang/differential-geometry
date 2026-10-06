import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceStandardParam

/-!
# BD0, generic part: a piece embedding from a smooth-embedded product (S-BCG-ROWS2 G26)

Draft 74 §3.2 / D74-16: the cusp piece of `CuspCores` and its `product` are ONE whole-core product.
Given a subset `X ⊆ W` with a charted structure over `𝓡∂ 3` (the concrete sublevel structure of the
BCG06 core), a smooth diffeomorphism `D : T² × [0,1] ≅ X` and the SMOOTH EMBEDDING of the composite
`val ∘ D` into `W` (E4c, lane O-CROSS), this file builds

* `mfderiv_val_bijective_of_product_BGR`: the inclusion `X → W` has bijective differentials
  (injective by the embedding, bijective by dimension `3 = 3`);
* **`pieceOfProduct_BGR`**: a `PieceEmbedding W` with `Piece = X`, `map = val`;
* `connectedComponentIn_eq_of_closed_pair_BGR` (generic): a component of `U ∪ V` through `U` is `U`
  when `U`, `V` are closed, disjoint and `U` is connected;
* `range_end_of_product_BGR`: an end slice of the product is the corresponding labelled set;
* **`exists_modelFaces_of_product_BGR`**: the two model boundary faces of the piece are the two end
  slices of the product (the six `CuspCores` model-face fields).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold.Assembly
  GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem iccEnd_true_val_BGR : ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) = 1 := by simp [iccEnd]

theorem iccEnd_false_val_BGR : ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) = 0 := by simp [iccEnd]

section Generic

variable {W : CompactCarrier.{0}} {X : Set W.Carrier} [ChartedSpace (EuclideanHalfSpace 3) X]
  [IsManifold (𝓡∂ 3) ∞ X]

omit [IsManifold (𝓡∂ 3) ∞ X] in
/-- **The inclusion of a smooth-embedded product has bijective differentials**: the differential of
`val ∘ D` is injective (smooth embedding), `D` is a diffeomorphism, and both tangent spaces have
dimension `3`. -/
theorem mfderiv_val_bijective_of_product_BGR
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1) X ∞)
    (hemb : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞
      (fun p => (D p : W.Carrier))) (q : X) :
    Bijective (mfderiv (𝓡∂ 3) W.model (fun y : X => (y : W.Carrier)) q) := by
  have hDs : MDifferentiableAt (𝓡∂ 3) (torusModel.prod (𝓡∂ 1)) D.symm q :=
    D.symm.contMDiff.mdifferentiableAt (by simp)
  have hE : MDifferentiableAt (torusModel.prod (𝓡∂ 1)) W.model
      (fun p => (D p : W.Carrier)) (D.symm q) :=
    hemb.isImmersion.contMDiff.mdifferentiableAt (by simp)
  have hinj : Injective (mfderiv (𝓡∂ 3) W.model (fun y : X => (y : W.Carrier)) q) := by
    have hfun : (fun y : X => (y : W.Carrier)) =
        (fun p => (D p : W.Carrier)) ∘ D.symm := by
      funext y
      simp
    have h2 := mfderiv_comp_injective_ZSP35 (f := D.symm)
      (g := fun p => (D p : W.Carrier)) hDs
      (by simpa using hE) (diffeomorph_mfderiv_injective_ZSP35 D.symm q)
      (by simpa using hemb.isImmersion.mfderiv_injective (by simp) (D.symm q))
    rw [← hfun] at h2
    exact h2
  refine ⟨hinj, ?_⟩
  have := (LinearMap.injective_iff_surjective
    (f := (mfderiv (𝓡∂ 3) W.model (fun y : X => (y : W.Carrier)) q).toLinearMap)).mp hinj
  exact this

/-- **The piece of a smooth-embedded product** (`Piece = X`, `map = val`): `X` compact, with the
concrete charted structure, the product `D` and the embedding of `val ∘ D`. -/
def pieceOfProduct_BGR (hX : IsCompact X)
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1) X ∞)
    (hval : ContMDiff (𝓡∂ 3) W.model ∞ (fun y : X => (y : W.Carrier)))
    (hemb : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞
      (fun p => (D p : W.Carrier))) : PieceEmbedding W :=
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  haveI : ConnectedSpace X := D.surjective.connectedSpace D.continuous
  { Piece := X
    map := Subtype.val
    smooth := hval
    mfderiv_bijective := mfderiv_val_bijective_of_product_BGR D hemb
    injective := Subtype.val_injective }

omit [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] in
/-- **Components of a union of two disjoint closed sets**: the connected component of `U ∪ V`
through a point of the closed connected set `U` is `U`. -/
theorem connectedComponentIn_eq_of_closed_pair_BGR {Y : Type*} [TopologicalSpace Y]
    {A U V : Set Y} (hA : A = U ∪ V) (hUc : IsClosed U) (hVc : IsClosed V) (hd : Disjoint U V)
    (hU : IsConnected U) {x : Y} (hx : x ∈ U) : connectedComponentIn A x = U := by
  refine Subset.antisymm ?_
    (hU.isPreconnected.subset_connectedComponentIn hx (hA ▸ subset_union_left))
  have hxA : x ∈ A := hA ▸ Or.inl hx
  have hC := isPreconnected_connectedComponentIn (F := A) (x := x)
  have hsub : connectedComponentIn A x ⊆ U ∪ V := hA ▸ connectedComponentIn_subset A x
  have hdisj : connectedComponentIn A x ∩ (U ∩ V) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hd]
    simp
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC) U V hUc hVc hsub hdisj with h | h
  · exact h
  · exact absurd (h (mem_connectedComponentIn hxA)) (Set.disjoint_left.mp hd hx)

omit [IsManifold (𝓡∂ 3) ∞ X] in
/-- **An end slice of a product is a subset of the core characterized by its second coordinate**:
if `E ⊆ X` and `D p ∈ E ↔ p.2 = e`, then `D(T² × {e}) = E`. -/
theorem range_end_of_product_BGR
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1) X ∞)
    {E : Set W.Carrier} (e : Icc (0 : ℝ) 1) (hEX : E ⊆ X)
    (hDE : ∀ p, (D p : W.Carrier) ∈ E ↔ (p.2 : ℝ) = (e : ℝ)) :
    (range fun t : Torus => (D (t, e) : W.Carrier)) = E := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (hDE (t, e)).mpr rfl
  · intro hx
    obtain ⟨p, hp⟩ := D.surjective ⟨x, hEX hx⟩
    have hpx : (D p : W.Carrier) = x := congrArg Subtype.val hp
    rw [← hpx] at hx
    have hp2 : p.2 = e := Subtype.ext ((hDE p).mp hx)
    refine ⟨p.1, ?_⟩
    have hpe : p = (p.1, e) := Prod.ext rfl hp2
    rw [← hpx, hpe]

/-- **The two model boundary faces of the piece are the two end slices of the product**
(the six `CuspCores` model-face fields): with the manifold boundary of `X` equal to
`(∂_bW) ∪ H_b` (`hbd`) and the product ends `T² × {0} ↦ ∂_bW`, `T² × {1} ↦ H_b`
(`h0`, `h1`), the actual components of the model boundary of `pieceOfProduct_BGR` are exactly
`D(T² × {1})` (internal) and `D(T² × {0})` (external). -/
theorem exists_modelFaces_of_product_BGR (hX : IsCompact X)
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1) X ∞)
    (hval : ContMDiff (𝓡∂ 3) W.model ∞ (fun y : X => (y : W.Carrier)))
    (hemb : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)))
    {Comp Front : Set W.Carrier}
    (hbd : ∀ y : X, (𝓡∂ 3).IsBoundaryPoint y ↔
      ((y : W.Carrier) ∈ Comp ∨ (y : W.Carrier) ∈ Front))
    (h0 : ∀ p, (D p : W.Carrier) ∈ Comp ↔ (p.2 : ℝ) = 0)
    (h1 : ∀ p, (D p : W.Carrier) ∈ Front ↔ (p.2 : ℝ) = 1) :
    ∃ F0 F1 : ModelBoundaryFace (pieceOfProduct_BGR hX D hval hemb),
      F1.1 = range (fun t : Torus => D (t, iccEnd true)) ∧
      F0.1 = range (fun t : Torus => D (t, iccEnd false)) ∧
      ∀ F : ModelBoundaryFace (pieceOfProduct_BGR hX D hval hemb), F = F1 ∨ F = F0 := by
  change ∃ F0 F1 : ActualComponent ((𝓡∂ 3).boundary X), F1.1 = _ ∧ F0.1 = _ ∧ ∀ F, F = F1 ∨ F = F0
  let B0 : Set X := range (fun t : Torus => D (t, iccEnd false))
  let B1 : Set X := range (fun t : Torus => D (t, iccEnd true))
  have hc0 : Continuous (fun t : Torus => D (t, iccEnd false)) :=
    D.continuous.comp (continuous_id.prodMk continuous_const)
  have hc1 : Continuous (fun t : Torus => D (t, iccEnd true)) :=
    D.continuous.comp (continuous_id.prodMk continuous_const)
  have hB0c : IsClosed B0 := (isCompact_range hc0).isClosed
  have hB1c : IsClosed B1 := (isCompact_range hc1).isClosed
  have hB0 : IsConnected B0 := isConnected_range hc0
  have hB1 : IsConnected B1 := isConnected_range hc1
  have hdisj : Disjoint B1 B0 := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have h2 := congrArg (fun p : Torus × Icc (0 : ℝ) 1 => (p.2 : ℝ)) (D.injective ht')
    simp only [iccEnd_true_val_BGR, iccEnd_false_val_BGR] at h2
    norm_num at h2
  have hbound : (𝓡∂ 3).boundary X = B1 ∪ B0 := by
    ext y
    obtain ⟨p, rfl⟩ := D.surjective y
    change (𝓡∂ 3).IsBoundaryPoint (D p) ↔ _
    rw [hbd, h0, h1]
    constructor
    · rintro (h | h)
      · refine Or.inr ⟨p.1, ?_⟩
        have hp : p = (p.1, iccEnd false) :=
          Prod.ext rfl (Subtype.ext (by rw [h, iccEnd_false_val_BGR]))
        exact congrArg D hp.symm
      · refine Or.inl ⟨p.1, ?_⟩
        have hp : p = (p.1, iccEnd true) :=
          Prod.ext rfl (Subtype.ext (by rw [h, iccEnd_true_val_BGR]))
        exact congrArg D hp.symm
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · exact Or.inr (by rw [← D.injective ht]; exact iccEnd_true_val_BGR)
      · exact Or.inl (by rw [← D.injective ht]; exact iccEnd_false_val_BGR)
  obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
  have hx0 : D (t₀, iccEnd false) ∈ (𝓡∂ 3).boundary X := by
    rw [hbound]
    exact Or.inr ⟨t₀, rfl⟩
  have hx1 : D (t₀, iccEnd true) ∈ (𝓡∂ 3).boundary X := by
    rw [hbound]
    exact Or.inl ⟨t₀, rfl⟩
  have hcomp1 : ∀ x ∈ B1, connectedComponentIn ((𝓡∂ 3).boundary X) x = B1 := fun x hx =>
    connectedComponentIn_eq_of_closed_pair_BGR hbound hB1c hB0c hdisj hB1 hx
  have hcomp0 : ∀ x ∈ B0, connectedComponentIn ((𝓡∂ 3).boundary X) x = B0 := fun x hx =>
    connectedComponentIn_eq_of_closed_pair_BGR (hbound.trans (Set.union_comm _ _)) hB0c hB1c
      hdisj.symm hB0 hx
  refine ⟨ActualComponent.of hx0, ActualComponent.of hx1, hcomp1 _ ⟨t₀, rfl⟩,
    hcomp0 _ ⟨t₀, rfl⟩, ?_⟩
  intro F
  obtain ⟨C, x, hx, rfl⟩ := F
  have hxU : x ∈ B1 ∪ B0 := hbound ▸ hx
  rcases hxU with h | h
  · left
    apply Subtype.ext
    change connectedComponentIn _ x = connectedComponentIn _ _
    rw [hcomp1 x h, hcomp1 _ ⟨t₀, rfl⟩]
  · right
    apply Subtype.ext
    change connectedComponentIn _ x = connectedComponentIn _ _
    rw [hcomp0 x h, hcomp0 _ ⟨t₀, rfl⟩]

end Generic

end DifferentialGeometry.Geometry.Collapse
