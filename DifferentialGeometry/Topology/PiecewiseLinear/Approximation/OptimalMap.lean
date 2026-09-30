import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.PolyhedralIntersection

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology _root_.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineMap_injOn_affineSpan_of_independent {s : Finset E} (hs : s.Nonempty)
    (A : E →ᵃ[ℝ] F) (hA : AffineIndependent ℝ (fun v : s => A v)) :
    Set.InjOn A (affineSpan ℝ (s : Set E)) := by
  classical
  let : Nonempty s := hs.to_subtype
  let p : s → F := fun v => A v
  have himage : AffineIndependent ℝ ((↑) : s.image A → F) := by
    have heq : range p = (s.image A : Set F) := by
      ext y
      simp only [p, mem_range, Finset.mem_coe, Finset.mem_image]
      exact ⟨fun ⟨v, hv⟩ => ⟨v.1, v.2, hv⟩, fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, h⟩⟩
    have hh : AffineIndependent ℝ ((↑) : range p → F) := hA.range
    rw [heq] at hh
    exact hh
  obtain ⟨B, hB⟩ := exists_affineMap_of_affineIndependent himage
    (fun y => (Function.invFun p y).1)
  have hBA (v : E) (hv : v ∈ s) : B (A v) = v := by
    rw [hB _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)]
    have hi := Function.leftInverse_invFun hA.injective (⟨v, hv⟩ : s)
    exact congrArg Subtype.val hi
  have hid : Set.EqOn (B.comp A) (AffineMap.id ℝ E) (affineSpan ℝ (s : Set E)) :=
    AffineMap.eqOn_affineSpan hBA
  intro x hx y hy hxy
  exact (hid hx).symm.trans ((congrArg B hxy).trans (hid hy))

variable [FiniteDimensional ℝ E]

theorem interpolateVertices_image_face (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s : K.faces) :
    interpolateVertices K hK w '' (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)) =
      convexHull ℝ (w '' (s.1 : Set E)) := by
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w s
  have himage : A '' (s.1 : Set E) = w '' (s.1 : Set E) := image_congr hA
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact interpolateVertices_mem_convexHull K hK w s x hx
  · intro y hy
    rw [← himage, ← A.image_convexHull] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, K.convexHull_subset_space s.2 hx⟩, hx, ?_⟩
    exact (hf _ hx).trans hxy

theorem interpolateVertices_injOn_face (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s : K.faces) (hw : AffineIndependent ℝ (fun v : s.1 => w v)) :
    Set.InjOn (interpolateVertices K hK w)
      (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)) := by
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w s
  have hAi : AffineIndependent ℝ (fun v : s.1 => A v) := by
    convert hw using 1
    funext v
    exact hA v v.2
  have hinj := affineMap_injOn_affineSpan_of_independent
    (K.nonempty_of_mem_faces s.2) A hAi
  intro x hx y hy hxy
  apply Subtype.ext
  apply hinj (convexHull_subset_affineSpan _ hx) (convexHull_subset_affineSpan _ hy)
  rwa [hf x hx, hf y hy] at hxy

omit [FiniteDimensional ℝ E] in
theorem face_vertices_subset (K : SimplicialComplex ℝ E) (s : K.faces) :
    (s.1 : Set E) ⊆ K.vertices := by
  intro v hv
  exact K.down_closed s.2 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

theorem exists_generalPosition_interpolant {n : ℕ} (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (g : C(K.space, EuclideanSpace ℝ (Fin n))) {ε δ : ℝ}
    (hε : 0 < ε)
    (hg : ∀ (s : K.faces) (x y : K.space),
      x.1 ∈ convexHull ℝ (s.1 : Set E) → y.1 ∈ convexHull ℝ (s.1 : Set E) →
        ‖g x - g y‖ < δ) :
    ∃ w : E → EuclideanSpace ℝ (Fin n),
      (∀ s : Finset E, (s : Set E) ⊆ K.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun v : s => w v)) ∧
      ∀ x : K.space, ‖interpolateVertices K hK w x - g x‖ < ε + δ := by
  classical
  have hV : K.vertices.Finite := by
    rw [K.vertices_eq]
    exact hK.biUnion (fun s _ => s.finite_toSet)
  let v : E → EuclideanSpace ℝ (Fin n) :=
    fun x => if hx : x ∈ K.space then g ⟨x, hx⟩ else 0
  have hv (x : K.space) : v x.1 = g x := dite_eq_left x.2
  obtain ⟨w, hw, -, hgp⟩ := exists_generalPositionOn hV.toFinset v (fun _ => ε)
    (fun _ _ => hε)
  refine ⟨w, ?_, ?_⟩
  · intro s hs hcard
    exact hgp s (fun i hi => hV.mem_toFinset.mpr (hs hi)) hcard
  · apply interpolateVertices_norm_sub_lt K hK w g _ hg
    intro x hx
    have hnear := hw x (hV.mem_toFinset.mpr hx)
    rwa [hv ⟨x, K.vertices_subset_space hx⟩] at hnear

theorem interpolateVertices_optimal_intersection {n : ℕ} (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun v : r => w v))
    (s t : K.faces) (hs : s.1.card ≤ n + 1) (ht : t.1.card ≤ n + 1) :
    let S := interpolateVertices K hK w '' (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E))
    let T := interpolateVertices K hK w '' (Subtype.val ⁻¹' convexHull ℝ (t.1 : Set E))
    S ∩ T = convexHull ℝ (w '' ((s.1 : Set E) ∩ (t.1 : Set E))) ∨
      ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        S ∩ T ⊆ P ∧ Module.finrank ℝ P.direction + n + 2 ≤ s.1.card + t.1.card := by
  classical
  dsimp only
  rw [interpolateVertices_image_face, interpolateVertices_image_face]
  have hu : inGeneralPositionOn (s.1 ∪ t.1) w := by
    intro r hr hc
    apply hgp r _ hc
    intro v hv
    rcases Finset.mem_union.mp (hr hv) with hvs | hvt
    · exact face_vertices_subset K s hvs
    · exact face_vertices_subset K t hvt
  by_cases hsmall : (s.1 ∪ t.1).card ≤ n + 1
  · left
    simpa only [Finset.coe_inter] using hu.convexHull_inter
      Finset.subset_union_left Finset.subset_union_right hsmall
  right
  have hlarge : n + 1 ≤ (s.1 ∪ t.1).card := by omega
  by_cases hmeet : (convexHull ℝ (w '' (s.1 : Set E)) ∩
      convexHull ℝ (w '' (t.1 : Set E))).Nonempty
  · obtain ⟨P, hP, hdim⟩ := hu.exists_affineSubspace_convexHull_inter
      Finset.subset_union_left Finset.subset_union_right hs ht hlarge hmeet
    exact ⟨P, hP, hdim.le⟩
  · refine ⟨⊥, ?_, ?_⟩
    · exact fun _ hx => False.elim (hmeet ⟨_, hx⟩)
    · have hcard := Finset.card_union_le s.1 t.1
      have hz : Module.finrank ℝ
          (⊥ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))).direction = 0 := by simp
      rw [hz]
      omega

end DifferentialGeometry.Topology.Engulfing
