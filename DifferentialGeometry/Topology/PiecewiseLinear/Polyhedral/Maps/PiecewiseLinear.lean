import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.LocallyFinite

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology _root_.Geometry
open scoped ContinuousMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_affineMap_of_affineIndependent {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (w : E → F) :
    ∃ A : E →ᵃ[ℝ] F, ∀ v ∈ s, A v = w v := by
  classical
  obtain ⟨t, hst, ht, htop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ E :=
    { toFun := Subtype.val
      ind' := ht
      tot' := by simpa only [Subtype.range_coe] using htop }
  let j : s → t := fun v => ⟨v.1, hst v.2⟩
  have hj : Function.Injective j := fun v u h =>
    Subtype.ext (congrArg (fun z : t => z.1) h)
  let A : E →ᵃ[ℝ] F := ∑ v : s,
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (w v)).toAffineMap.comp (b.coord (j v))
  refine ⟨A, fun v hv => ?_⟩
  let v' : s := ⟨v, hv⟩
  have hc (u : s) : b.coord (j u) v = if u = v' then 1 else 0 := by
    change b.coord (j u) (b (j v')) = _
    rw [b.coord_apply]
    simp only [hj.eq_iff]
  have heval : A v = ∑ u : s, b.coord (j u) v • w u := by
    let ev : (E →ᵃ[ℝ] F) →+ F :=
      { toFun := fun B => B v
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact map_sum ev _ _
  rw [heval]
  simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rfl

variable [FiniteDimensional ℝ E]

structure VertexInterpolation (K : SimplicialComplex ℝ E) (w : E → F) where
  toContinuousMap : C(K.space, F)
  faceMap : K.faces → E →ᵃ[ℝ] F
  faceMap_vertex : ∀ (s : K.faces) (v : E), v ∈ s.1 → faceMap s v = w v
  eq_faceMap : ∀ (s : K.faces) (x : K.space),
    x.1 ∈ convexHull ℝ (s.1 : Set E) → toContinuousMap x = faceMap s x.1

noncomputable def vertexInterpolation (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) : VertexInterpolation K w := by
  classical
  letI : Fintype K.faces := hK.fintype
  choose A hA using (fun s : K.faces => exists_affineMap_of_affineIndependent (K.indep s.2) w)
  have agree (s t : K.faces) {x : E}
      (hs : x ∈ convexHull ℝ (s.1 : Set E)) (ht : x ∈ convexHull ℝ (t.1 : Set E)) :
      A s x = A t x := by
    apply AffineMap.eqOn_affineSpan (s := (s.1 : Set E) ∩ (t.1 : Set E))
      (fun v hv => (hA s v hv.1).trans (hA t v hv.2).symm)
    exact convexHull_subset_affineSpan _ (K.inter_subset_convexHull s.2 t.2 ⟨hs, ht⟩)
  have chooseFace (x : K.space) : ∃ s : K.faces, x.1 ∈ convexHull ℝ (s.1 : Set E) := by
    obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
    exact ⟨⟨s, hs⟩, hx⟩
  choose face hface using chooseFace
  let f : K.space → F := fun x => A (face x) x.1
  have f_eq (s : K.faces) (x : K.space) (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) :
      f x = A s x.1 := agree (face x) s (hface x) hx
  let C (s : K.faces) : Set K.space := Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)
  have hcover : ⋃ s, C s = univ := by
    ext x
    exact iff_true_intro (mem_iUnion.mpr ⟨face x, hface x⟩)
  have hclosed (s : K.faces) : IsClosed (C s) :=
    (s.1.finite_toSet.isClosed_convexHull ℝ).preimage continuous_subtype_val
  have hcontinuous (s : K.faces) : ContinuousOn f (C s) :=
    ((A s).continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
      (fun x hx => f_eq s x hx)
  have hf : Continuous f :=
    (locallyFinite_of_finite C).continuous hcover hclosed hcontinuous
  exact ⟨⟨f, hf⟩, A, hA, f_eq⟩

noncomputable def interpolateVertices (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) : C(K.space, F) := (vertexInterpolation K hK w).toContinuousMap

theorem interpolateVertices_affineOn (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s : K.faces) :
    ∃ A : E →ᵃ[ℝ] F, (∀ v ∈ s.1, A v = w v) ∧
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s.1 : Set E) → interpolateVertices K hK w x = A x.1 :=
  ⟨(vertexInterpolation K hK w).faceMap s,
    (vertexInterpolation K hK w).faceMap_vertex s,
    (vertexInterpolation K hK w).eq_faceMap s⟩

theorem interpolateVertices_vertex (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (v : E) (hv : v ∈ K.vertices) :
    interpolateVertices K hK w ⟨v, K.vertices_subset_space hv⟩ = w v := by
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w ⟨{v}, hv⟩
  rw [hf _ (by simp)]
  exact hA v (Finset.mem_singleton_self v)

theorem interpolateVertices_mem_convexHull (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s : K.faces) (x : K.space) (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) :
    interpolateVertices K hK w x ∈ convexHull ℝ (w '' (s.1 : Set E)) := by
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w s
  rw [hf x hx]
  have heq : A '' (s.1 : Set E) = w '' (s.1 : Set E) := image_congr hA
  rw [← heq, ← A.image_convexHull]
  exact mem_image_of_mem A hx

theorem interpolateVertices_norm_sub_lt_of_face (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → F) (s : K.faces) (x : K.space)
    (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) (y : F) {ε : ℝ}
    (hw : ∀ v ∈ s.1, ‖w v - y‖ < ε) :
    ‖interpolateVertices K hK w x - y‖ < ε := by
  have hball : w '' (s.1 : Set E) ⊆ ball y ε := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_ball_iff_norm.mpr (hw v hv)
  exact mem_ball_iff_norm.mp ((convexHull_min hball (convex_ball y ε))
    (interpolateVertices_mem_convexHull K hK w s x hx))

theorem interpolateVertices_norm_sub_lt (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (g : C(K.space, F)) {ε δ : ℝ}
    (hw : ∀ (v : E) (hv : v ∈ K.vertices),
      ‖w v - g ⟨v, K.vertices_subset_space hv⟩‖ < ε)
    (hg : ∀ (s : K.faces) (x y : K.space),
      x.1 ∈ convexHull ℝ (s.1 : Set E) → y.1 ∈ convexHull ℝ (s.1 : Set E) →
        ‖g x - g y‖ < δ) (x : K.space) :
    ‖interpolateVertices K hK w x - g x‖ < ε + δ := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  apply interpolateVertices_norm_sub_lt_of_face K hK w ⟨s, hs⟩ x hx (g x)
  intro v hv
  have hvv : v ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let v' : K.space := ⟨v, K.vertices_subset_space hvv⟩
  have hv' : v'.1 ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hv
  calc
    ‖w v - g x‖ ≤ ‖w v - g v'‖ + ‖g v' - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε + δ := add_lt_add (hw v hvv) (hg ⟨s, hs⟩ v' x hv' hx)

end DifferentialGeometry.Topology.Engulfing
