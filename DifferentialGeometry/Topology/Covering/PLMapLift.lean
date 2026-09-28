/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.PLTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X]
  (K : Geometry.SimplicialComplex ℝ E) (p : X → K.space)
  [Finite (coveringVertex K p)]

open Classical in
private noncomputable def coveringSingletonFaceData (v : coveringVertex K p) :
    CoveringFaceData K p {v} where
  face := by simpa only [Finset.image_singleton] using v.singleton_base_mem_faces
  lift := ContinuousMap.const _ v.1
  projection := by
    intro x
    apply Subtype.ext
    have hx : (x : E) = coveringVertex.base v := by
      simpa only [Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using x.2
    exact hx.symm
  vertices := by
    intro w hw
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst w
    rfl

open Classical in
theorem coveringVertexPoint_mem_vertices (v : coveringVertex K p) :
    coveringVertexPoint K p v ∈ (coveringComplex K p).vertices := by
  exact (mem_coveringComplex_faces_iff K p).mpr
    ⟨{v}, ⟨coveringSingletonFaceData K p v⟩, by simp only [Finset.image_singleton]⟩

open Classical in
theorem coveringSpaceHomeomorph_vertexPoint [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) :
    coveringSpaceHomeomorph K p hp
        ⟨coveringVertexPoint K p v, (coveringComplex K p).vertices_subset_space
          (coveringVertexPoint_mem_vertices K p v)⟩ = v.1 := by
  let s : Finset (coveringVertex K p) := {v}
  let q := s.image (coveringVertexPoint K p)
  let d : CoveringGeometricFaceData K p q :=
    ⟨s, coveringSingletonFaceData K p v, rfl⟩
  have hq : q ∈ (coveringComplex K p).faces := ⟨s, ⟨d.data⟩, rfl⟩
  have hz : coveringVertexPoint K p v ∈ convexHull ℝ (q : Set _) :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v, Finset.mem_singleton_self v, rfl⟩)
  rw [coveringSpaceHomeomorph_apply, coveringSpaceMap_eq_face K p hp hq d hz]
  rfl

variable [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem exists_simplicialMap_lift_of_continuousMap
    (A : Geometry.SimplicialComplex ℝ F) [Finite A.faces] (φ : F → E)
    (hφ : ∀ s ∈ A.faces, s.image φ ∈ K.faces) (hp : IsCoveringMap p)
    (g : C(A.space, X)) (hg : ∀ x, (p (g x) : E) = simplicialMap A φ x) :
    ∃ (ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))
      (hψ : ∀ s ∈ A.faces, s.image ψ ∈ (coveringComplex K p).faces),
      (∀ v ∈ A.vertices, coveringBaseVertex K p (ψ v) = φ v) ∧
      EqOn (coveringBaseMap K p ∘ simplicialMap A ψ) (simplicialMap A φ) A.space ∧
      ∀ x : A.space, coveringSpaceHomeomorph K p hp
        ⟨simplicialMap A ψ x, simplicialMap_mapsTo A (coveringComplex K p) ψ hψ x.2⟩ = g x := by
  have hφv {v : F} (hv : v ∈ A.vertices) : φ v ∈ K.vertices := by
    change ({φ v} : Finset E) ∈ K.faces
    simpa only [Finset.image_singleton] using hφ {v} hv
  let V : A.vertices → coveringVertex K p := fun v =>
    ⟨g ⟨v, A.vertices_subset_space v.2⟩, by
      rw [hg, simplicialMap_vertex A φ v.2]
      exact hφv v.2⟩
  have hV (v : A.vertices) : coveringVertex.base (V v) = φ v := by
    change (p (g ⟨v, A.vertices_subset_space v.2⟩) : E) = φ v
    rw [hg, simplicialMap_vertex A φ v.2]
  let ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) := fun v =>
    if hv : v ∈ A.vertices then coveringVertexPoint K p (V ⟨v, hv⟩) else 0
  have hψv {v : F} (hv : v ∈ A.vertices) :
      ψ v = coveringVertexPoint K p (V ⟨v, hv⟩) := by simp only [ψ, dite_eq_left hv]
  have hbase : ∀ v ∈ A.vertices, coveringBaseVertex K p (ψ v) = φ v := by
    intro v hv
    rw [hψv hv, coveringBaseVertex_point, hV]
  have hfaces : ∀ s ∈ A.faces, s.image ψ ∈ (coveringComplex K p).faces := by
    intro s hs
    have hsv {v : F} (hv : v ∈ s) : v ∈ A.vertices :=
      A.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    obtain ⟨a, ha⟩ := A.nonempty_of_mem_faces hs
    let a₀ : convexHull ℝ (s : Set F) := ⟨a, subset_convexHull ℝ _ ha⟩
    let b₀ : convexHull ℝ ((s.image φ : Finset E) : Set E) :=
      ⟨φ a, subset_convexHull ℝ _ (Finset.mem_image_of_mem φ ha)⟩
    let f : C(convexHull ℝ (s : Set F), convexHull ℝ ((s.image φ : Finset E) : Set E)) :=
      ⟨fun x => ⟨simplicialMap A φ x, simplicialMap_mem_convexHull_image A φ hs x.2⟩,
        (((isPiecewiseAffineOn_simplicialMap A φ).continuousOn.mono
          (A.convexHull_subset_space hs)).domRestrict).subtype_mk _⟩
    let g₀ := g.comp (faceInclusion A hs)
    have h₀ : p (g₀ a₀) = faceInclusion K (hφ s hs) b₀ := by
      apply Subtype.ext
      change (p (g ⟨a, _⟩) : E) = φ a
      rw [hg, simplicialMap_vertex A φ (hsv ha)]
    obtain ⟨j, ⟨hj, hja⟩, -⟩ :=
      DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
        hp (hφ s hs) b₀ (g₀ a₀) h₀
    let _ : PreconnectedSpace (convexHull ℝ (s : Set F)) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_convexHull ℝ (s : Set F)).isPreconnected
    have hcomp : p ∘ (j ∘ f) = p ∘ g₀ := by
      funext x
      apply Subtype.ext
      have h := congrArg Subtype.val (congrFun hj (f x))
      exact h.trans (hg (faceInclusion A hs x)).symm
    have hinit : j (f a₀) = g₀ a₀ := by
      have hf : f a₀ = b₀ := Subtype.ext (simplicialMap_vertex A φ (hsv ha))
      rw [hf, hja]
    have heq := hp.eq_of_comp_eq (j.continuous.comp f.continuous) g₀.continuous hcomp a₀ hinit
    let c := coveringFaceVertices (hφ s hs) j hj
    let d := coveringFaceDataOfLift (hφ s hs) j hj
    let q := c.image (coveringVertexPoint K p)
    have hq : q ∈ (coveringComplex K p).faces := ⟨c, ⟨d⟩, rfl⟩
    have hsub : s.image ψ ⊆ q := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have hvφ := Finset.mem_image_of_mem φ hv
      let w := coveringVertexOfLift (hφ s hs) j hj ⟨φ v, hvφ⟩
      have hwc : w ∈ c := Finset.mem_image.mpr
        ⟨⟨φ v, hvφ⟩, Finset.mem_attach _ _, rfl⟩
      have hwV : w = V ⟨v, hsv hv⟩ := by
        apply Subtype.ext
        have hf : f ⟨v, subset_convexHull ℝ _ hv⟩ =
            ⟨φ v, subset_convexHull ℝ _ hvφ⟩ :=
          Subtype.ext (simplicialMap_vertex A φ (hsv hv))
        have h := congrFun heq ⟨v, subset_convexHull ℝ _ hv⟩
        change j (f ⟨v, subset_convexHull ℝ _ hv⟩) = g ⟨v, _⟩ at h
        rw [hf] at h
        exact h
      rw [hψv (hsv hv), ← hwV]
      exact Finset.mem_image_of_mem (coveringVertexPoint K p) hwc
    exact (coveringComplex K p).down_closed hq hsub (Finset.image_nonempty.mpr ⟨a, ha⟩)
  have hproj : EqOn (coveringBaseMap K p ∘ simplicialMap A ψ) (simplicialMap A φ) A.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hx
    obtain ⟨q, hq⟩ := exists_affineMap_eqOn_coveringBaseMap K p (hfaces s hs)
    have hpts : ∀ v ∈ s, q (ψ v) = φ v := by
      intro v hv
      have hvA : v ∈ A.vertices :=
        A.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hvL : ψ v ∈ (coveringComplex K p).vertices :=
        (coveringComplex K p).down_closed (hfaces s hs)
          (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem ψ hv))
          (Finset.singleton_nonempty _)
      rw [← hq (subset_convexHull ℝ _ (Finset.mem_image_of_mem ψ hv))]
      change simplicialMap (coveringComplex K p) (coveringBaseVertex K p) (ψ v) = φ v
      rw [simplicialMap_vertex _ _ hvL, hbase v hvA]
    change coveringBaseMap K p (simplicialMap A ψ x) = simplicialMap A φ x
    rw [hq (simplicialMap_mem_convexHull_image A ψ hs hxs), simplicialMap_eq_of_mem A ψ hs hxs,
      affineMap_apply_sum_smul_comp q ψ (sum_weights hxs), simplicialMap_eq_of_mem A φ hs hxs]
    exact Finset.sum_congr rfl fun v hv => by rw [hpts v hv]
  let e := coveringSpaceHomeomorph K p hp
  let g' : C(A.space, X) :=
    ⟨fun x => e ⟨simplicialMap A ψ x, simplicialMap_mapsTo A (coveringComplex K p) ψ hfaces x.2⟩,
      e.continuous.comp
        (((isPiecewiseAffineOn_simplicialMap A ψ).continuousOn.domRestrict).subtype_mk _)⟩
  have hg' : ∀ x : A.space, p (g' x) = p (g x) := by
    intro x
    apply Subtype.ext
    exact (coveringSpaceMap_projection K p _).trans ((hproj x.2).trans (hg x).symm)
  have hv' {v : F} (hv : v ∈ A.vertices) :
      g' ⟨v, A.vertices_subset_space hv⟩ = g ⟨v, A.vertices_subset_space hv⟩ := by
    change e ⟨simplicialMap A ψ v, _⟩ = _
    simp only [simplicialMap_vertex A ψ hv, hψv hv]
    exact coveringSpaceHomeomorph_vertexPoint K p hp (V ⟨v, hv⟩)
  refine ⟨ψ, hfaces, hbase, hproj, ?_⟩
  intro x
  obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp x.2
  obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces hs
  let _ : PreconnectedSpace (convexHull ℝ (s : Set F)) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_convexHull ℝ (s : Set F)).isPreconnected
  let i := faceInclusion A hs
  have hcomp : p ∘ (g' ∘ i) = p ∘ (g ∘ i) := funext fun y => hg' (i y)
  have hinit : g' (i ⟨v, subset_convexHull ℝ _ hv⟩) = g (i ⟨v, subset_convexHull ℝ _ hv⟩) :=
    hv' (A.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have heq := hp.eq_of_comp_eq (g'.continuous.comp i.continuous)
    (g.continuous.comp i.continuous) hcomp ⟨v, subset_convexHull ℝ _ hv⟩ hinit
  exact congrFun heq ⟨x, hxs⟩

open Classical in
theorem exists_simplicialMap_lift_of_isPLBall
    (A : Geometry.SimplicialComplex ℝ F) [Finite A.faces] {n : ℕ} (hA : IsPLBall n A.space)
    (φ : F → E) (hφ : ∀ s ∈ A.faces, s.image φ ∈ K.faces) (hp : IsCoveringMap p)
    (x₀ : A.space) (e₀ : X)
    (h₀ : p e₀ = ⟨simplicialMap A φ x₀, simplicialMap_mapsTo A K φ hφ x₀.2⟩) :
    ∃ (ψ : F → EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))
      (hψ : ∀ s ∈ A.faces, s.image ψ ∈ (coveringComplex K p).faces),
      (∀ v ∈ A.vertices, coveringBaseVertex K p (ψ v) = φ v) ∧
      EqOn (coveringBaseMap K p ∘ simplicialMap A ψ) (simplicialMap A φ) A.space ∧
      coveringSpaceHomeomorph K p hp
        ⟨simplicialMap A ψ x₀, simplicialMap_mapsTo A (coveringComplex K p) ψ hψ x₀.2⟩ = e₀ := by
  let f : C(A.space, K.space) :=
    ⟨fun x => ⟨simplicialMap A φ x, simplicialMap_mapsTo A K φ hφ x.2⟩,
      ((isPiecewiseAffineOn_simplicialMap A φ).continuousOn.domRestrict).subtype_mk _⟩
  obtain ⟨g, ⟨hg, hg₀⟩, -⟩ := hp.exists_unique_lift_of_isPLBall hA f x₀ e₀ h₀
  have hg' : ∀ x, (p (g x) : E) = simplicialMap A φ x := fun x =>
    congrArg Subtype.val (congrFun hg x)
  obtain ⟨ψ, hψ, hbase, hproj, hreal⟩ :=
    exists_simplicialMap_lift_of_continuousMap K p A φ hφ hp g hg'
  exact ⟨ψ, hψ, hbase, hproj, (hreal x₀).trans hg₀⟩

end DifferentialGeometry.Topology.PiecewiseLinear
