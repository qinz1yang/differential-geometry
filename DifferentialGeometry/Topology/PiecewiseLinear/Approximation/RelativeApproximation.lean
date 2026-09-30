import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Perturbation.VertexPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.PiecewiseApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.RelativeEmbedding

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology NNReal ContinuousMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem interpolateVertices_sub (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v w : E → F) (x : K.space) :
    interpolateVertices K hK (fun a => w a - v a) x =
      interpolateVertices K hK w x - interpolateVertices K hK v x := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨A, hA, hAv⟩ := interpolateVertices_affineOn K hK v ⟨s, hs⟩
  obtain ⟨B, hB, hBw⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  rw [hAv x hx, hBw x hx, interpolateVertices_eq_affineMap K hK _ ⟨s, hs⟩
    (B - A) (fun a ha => by simp [hA a ha, hB a ha]) x hx]
  rfl

theorem interpolateVertices_norm_sub_le (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (v w : E → F) {δ : ℝ}
    (hw : ∀ a ∈ K.vertices, ‖w a - v a‖ ≤ δ) (x : K.space) :
    ‖interpolateVertices K hK w x - interpolateVertices K hK v x‖ ≤ δ := by
  rw [← interpolateVertices_sub]
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  have hball : (fun a => w a - v a) '' (s : Set E) ⊆ closedBall 0 δ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hw a (face_vertices_subset K ⟨s, hs⟩ ha))
  exact mem_closedBall_zero_iff.mp ((convexHull_min hball (convex_closedBall 0 δ))
    (interpolateVertices_mem_convexHull K hK _ ⟨s, hs⟩ x hx))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] in
theorem exists_lift_vertex_assignment {V : Set E} {v w : E → F}
    (hv : InjOn v V) {δ : ℝ≥0} (hw : ∀ a ∈ V, ‖w a - v a‖ ≤ δ) :
    ∃ W : F → F, (∀ a ∈ V, W (v a) = w a) ∧
      (∀ y ∉ v '' V, W y = y) ∧ (∀ y, ‖W y - y‖ ≤ δ) := by
  classical
  let W : F → F := fun y => if hy : y ∈ v '' V then w hy.choose else y
  have heq (y : F) (hy : y ∈ v '' V) : W y = w hy.choose := dite_eq_left hy
  refine ⟨W, ?_, fun y hy => dite_eq_right hy, ?_⟩
  · intro a ha
    have hmem : v a ∈ v '' V := mem_image_of_mem v ha
    rw [heq _ hmem]
    exact congrArg w (hv hmem.choose_spec.1 ha hmem.choose_spec.2)
  · intro y
    by_cases hy : y ∈ v '' V
    · rw [heq y hy]
      calc
        ‖w hy.choose - y‖ = ‖w hy.choose - v hy.choose‖ :=
          congrArg (fun z => ‖w hy.choose - z‖) hy.choose_spec.2.symm
        _ ≤ δ := hw _ hy.choose_spec.1
    · simp only [W, dite_eq_right hy, sub_self, norm_zero]
      exact δ.coe_nonneg

variable [FiniteDimensional ℝ F]

theorem interpolateVertices_comp_on_face
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite)
    (v w : E → F) (W : F → F) (s : K.faces) (t : T.faces)
    (hst : (t.1 : Set F) = v '' (s.1 : Set E)) (hW : ∀ a ∈ s.1, W (v a) = w a)
    (x : K.space) (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) :
    ∃ hxT : interpolateVertices K hK v x ∈ T.space,
      interpolateVertices T hT W ⟨interpolateVertices K hK v x, hxT⟩ =
        interpolateVertices K hK w x := by
  classical
  have himage : interpolateVertices K hK v x ∈
      convexHull ℝ (t.1 : Set F) := by
    rw [hst]
    exact interpolateVertices_mem_convexHull K hK v s x hx
  let hxT := T.convexHull_subset_space t.2 himage
  refine ⟨hxT, ?_⟩
  obtain ⟨A, hA, hAv⟩ := interpolateVertices_affineOn K hK v s
  obtain ⟨B, hB, hBW⟩ := interpolateVertices_affineOn T hT W t
  calc
    interpolateVertices T hT W ⟨interpolateVertices K hK v x, hxT⟩ =
        B (interpolateVertices K hK v x) := hBW _ himage
    _ = B (A x.1) := congrArg B (hAv x hx)
    _ = interpolateVertices K hK w x := by
      symm
      apply interpolateVertices_eq_affineMap K hK w s (B.comp A) _ x hx
      intro a ha
      change B (A a) = w a
      have hat : v a ∈ t.1 := by
        change v a ∈ (t.1 : Set F)
        rw [hst]
        exact mem_image_of_mem v ha
      rw [hA a ha, hB _ hat, hW a ha]

theorem exists_relative_generalPosition_interpolant {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L ≤ K)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hconv : Convex ℝ T.space)
    (v : E → EuclideanSpace ℝ (Fin n)) (hv : InjOn v L.vertices)
    (hfaces : ∀ s ∈ L.faces, ∃ t ∈ T.faces,
      (t : Set (EuclideanSpace ℝ (Fin n))) = v '' (s : Set E))
    (hinterior : v '' L.vertices ⊆ interior T.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
      (∀ s : Finset E, (s : Set E) ⊆ K.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : K.space, x.1 ∈ L.space →
        H (interpolateVertices K hK w x) = interpolateVertices K hK v x) ∧
      (∀ x : K.space,
        ‖H (interpolateVertices K hK w x) - interpolateVertices K hK v x‖ < ε) ∧
      (∀ y ∉ interior T.space, H y = y) ∧
      (∀ y, ‖H y - y‖ < ε) := by
  classical
  obtain ⟨C, hC⟩ := exists_vertex_perturbation_constant T hT hconv
  let δ : ℝ≥0 := min (C + 1)⁻¹ ⟨ε / 3, by positivity⟩
  have hδ : 0 < δ := by
    apply lt_min
    · positivity
    · change (0 : ℝ) < ε / 3
      positivity
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδbound : (δ : ℝ) ≤ ε / 3 := min_le_right _ _
  have hsmall : δ * C < 1 := calc
    δ * C ≤ (C + 1)⁻¹ * C := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    _ < 1 := (inv_mul_lt_one₀ (by positivity : 0 < C + 1)).mpr (by simp)
  have hV : K.vertices.Finite := by
    rw [K.vertices_eq]
    exact hK.biUnion (fun s _ => s.finite_toSet)
  obtain ⟨w, hw, -, hgp⟩ := exists_generalPositionOn hV.toFinset v (fun _ => (δ : ℝ))
    (fun _ _ => hδreal)
  have hwbound (a : E) (ha : a ∈ K.vertices) : ‖w a - v a‖ ≤ δ :=
    (hw a (hV.mem_toFinset.mpr ha)).le
  have hVL : L.vertices ⊆ K.vertices := fun _ ha => hLK ha
  obtain ⟨W, hW, hWfix, hWnorm⟩ := exists_lift_vertex_assignment hv
    (fun a ha => hwbound a (hVL ha))
  have hWboundary (y : EuclideanSpace ℝ (Fin n)) (_hy : y ∈ T.vertices)
      (hyf : y ∈ frontier T.space) : W y = y := by
    apply hWfix y
    exact fun hy => hyf.2 (hinterior hy)
  obtain ⟨J, hJ, hJfix, -, -, hJinvnorm⟩ := hC δ hsmall W
    (fun y _ => hWnorm y) hWboundary
  refine ⟨w, J.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hcard
    exact hgp s (fun a ha => hV.mem_toFinset.mpr (hs ha)) hcard
  · intro x hxL
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxL
    obtain ⟨t, ht, hst⟩ := hfaces s hs
    obtain ⟨hxT, hcomp⟩ := interpolateVertices_comp_on_face K hK T hT v w W
      ⟨s, hLK hs⟩ ⟨t, ht⟩ hst (fun a ha => hW a (face_vertices_subset L ⟨s, hs⟩ ha)) x hxs
    have heq : J (interpolateVertices K hK v x) = interpolateVertices K hK w x :=
      (hJ ⟨_, hxT⟩).trans hcomp
    rw [← heq, J.symm_apply_apply]
  · intro x
    calc
      ‖J.symm (interpolateVertices K hK w x) - interpolateVertices K hK v x‖ ≤
          ‖J.symm (interpolateVertices K hK w x) - interpolateVertices K hK w x‖ +
          ‖interpolateVertices K hK w x - interpolateVertices K hK v x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (δ : ℝ) + δ := add_le_add (hJinvnorm _)
        (interpolateVertices_norm_sub_le K hK v w hwbound x)
      _ < ε := by linarith
  · intro y hy
    apply J.injective
    rw [J.apply_symm_apply, hJfix y hy]
  · intro y
    exact (hJinvnorm y).trans_lt (by linarith)

noncomputable def correctedInterpolant (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (H : F ≃ₜ F) : C(K.space, F) :=
  ⟨fun x => H (interpolateVertices K hK w x),
    H.continuous.comp (interpolateVertices K hK w).continuous⟩

omit [FiniteDimensional ℝ F] in
@[simp]
theorem correctedInterpolant_apply (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (H : F ≃ₜ F) (x : K.space) :
    correctedInterpolant K hK w H x = H (interpolateVertices K hK w x) := rfl

omit [FiniteDimensional ℝ F] in
theorem correctedInterpolant_injOn_face (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (H : F ≃ₜ F) (s : K.faces)
    (hw : AffineIndependent ℝ (fun a : s.1 => w a)) :
    InjOn (correctedInterpolant K hK w H)
      (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)) := by
  intro x hx y hy hxy
  apply interpolateVertices_injOn_face K hK w s hw hx hy
  exact H.injective hxy

theorem correctedInterpolant_optimal_intersection {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun a : r => w a))
    (s t : K.faces) (hs : s.1.card ≤ n + 1) (ht : t.1.card ≤ n + 1) :
    let S := correctedInterpolant K hK w H '' (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E))
    let T := correctedInterpolant K hK w H '' (Subtype.val ⁻¹' convexHull ℝ (t.1 : Set E))
    S ∩ T = H '' convexHull ℝ (w '' ((s.1 : Set E) ∩ (t.1 : Set E))) ∨
      ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        S ∩ T ⊆ H '' (P : Set (EuclideanSpace ℝ (Fin n))) ∧
          Module.finrank ℝ P.direction + n + 2 ≤ s.1.card + t.1.card := by
  have himage (r : K.faces) : correctedInterpolant K hK w H ''
      (Subtype.val ⁻¹' convexHull ℝ (r.1 : Set E)) =
      H '' (interpolateVertices K hK w '' (Subtype.val ⁻¹' convexHull ℝ (r.1 : Set E))) := by
    rw [Set.image_image]
    rfl
  dsimp only
  rw [himage s, himage t, ← Set.image_inter H.injective]
  rcases interpolateVertices_optimal_intersection K hK w hgp s t hs ht with heq | ⟨P, hP, hdim⟩
  · exact Or.inl (congrArg (fun S => H '' S) heq)
  · exact Or.inr ⟨P, image_mono hP, hdim⟩

theorem exists_relative_corrected_approximation_of_face_oscillation {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L ≤ K)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hconv : Convex ℝ T.space)
    (g : C(K.space, EuclideanSpace ℝ (Fin n))) (v : E → EuclideanSpace ℝ (Fin n))
    (hvertex : ∀ (a : E) (ha : a ∈ K.vertices), g ⟨a, K.vertices_subset_space ha⟩ = v a)
    (hv : InjOn v L.vertices)
    (hfaces : ∀ s ∈ L.faces, ∃ t ∈ T.faces,
      (t : Set (EuclideanSpace ℝ (Fin n))) = v '' (s : Set E))
    (hinterior : v '' L.vertices ⊆ interior T.space)
    (hPL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → g x = A x.1)
    {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ (s : K.faces) (x y : K.space),
      x.1 ∈ convexHull ℝ (s.1 : Set E) → y.1 ∈ convexHull ℝ (s.1 : Set E) →
        ‖g x - g y‖ < ε / 2) :
    ∃ (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
      (∀ s : Finset E, (s : Set E) ⊆ K.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : K.space, x.1 ∈ L.space → correctedInterpolant K hK w H x = g x) ∧
      (∀ x : K.space, ‖correctedInterpolant K hK w H x - g x‖ < ε) ∧
      (∀ y ∉ interior T.space, H y = y) := by
  obtain ⟨w, H, hgp, hrel, hnear, hfix, -⟩ := exists_relative_generalPosition_interpolant
    K hK L hLK T hT hconv v hv hfaces hinterior (show 0 < ε / 2 by positivity)
  have hrelative (x : K.space) (hxL : x.1 ∈ L.space) :
      interpolateVertices K hK v x = g x := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxL
    obtain ⟨A, hA⟩ := hPL s hs
    rw [hA x hxs]
    apply interpolateVertices_eq_affineMap K hK v ⟨s, hLK hs⟩ A _ x hxs
    intro a ha
    have haK := face_vertices_subset K ⟨s, hLK hs⟩ ha
    exact (hA ⟨a, K.vertices_subset_space haK⟩ (subset_convexHull ℝ _ ha)).symm.trans
      (hvertex a haK)
  have hinterp (x : K.space) : ‖interpolateVertices K hK v x - g x‖ < ε / 2 := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
    apply interpolateVertices_norm_sub_lt_of_face K hK v ⟨s, hs⟩ x hxs (g x)
    intro a ha
    have haK := face_vertices_subset K ⟨s, hs⟩ ha
    rw [← hvertex a haK]
    exact hosc ⟨s, hs⟩ ⟨a, K.vertices_subset_space haK⟩ x
      (subset_convexHull ℝ _ ha) hxs
  refine ⟨w, H, hgp, fun x hx => (hrel x hx).trans (hrelative x hx), ?_, hfix⟩
  intro x
  calc
    ‖correctedInterpolant K hK w H x - g x‖ ≤
        ‖correctedInterpolant K hK w H x - interpolateVertices K hK v x‖ +
        ‖interpolateVertices K hK v x - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hnear x) (hinterp x)
    _ = ε := add_halves ε

theorem exists_relative_interpolant_of_embedded_subcomplex_with_correction_control {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (v : E → EuclideanSpace ℝ (Fin n))
    (hv : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn v A (convexHull ℝ (s : Set E)))
    (hinj : InjOn v L.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
      (Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))),
      Q.faces.Finite ∧
      (∀ s : Finset E, (s : Set E) ⊆ K.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : K.space, x.1 ∈ L.space → correctedInterpolant K hK w H x = v x.1) ∧
      (∀ x : K.space,
        ‖correctedInterpolant K hK w H x - interpolateVertices K hK v x‖ < ε) ∧
      (∀ x : K.space, interpolateVertices K hK w x ∈ Q.space) ∧
      (∀ t ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
        EqOn H A (convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin n))))) ∧
      (∀ y, ‖H y - y‖ < ε) ∧ (∀ y, ‖H.symm y - y‖ < ε) := by
  classical
  let F := EuclideanSpace ℝ (Fin n)
  have hL : L.faces.Finite := hK.subset hLK
  have hLspace : L.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK hs) hxs
  have hvinterp (x : K.space) (hx : x.1 ∈ L.space) :
      interpolateVertices K hK v x = v x.1 := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨A, hA⟩ := hv s hs
    exact (interpolateVertices_eq_affineMap K hK v ⟨s, hLK hs⟩ A
      (fun a ha => (hA (subset_convexHull ℝ _ ha)).symm) x hxs).trans (hA hxs).symm
  let S := injectiveImageComplex L v hv hinj
  have hS : S.faces.Finite := injectiveImageComplex_finite_faces L hL v hv hinj
  have hSspace : S.space = v '' L.space := injectiveImageComplex_space L v hv hinj
  have hcompact : IsCompact (range (interpolateVertices K hK v)) := by
    let : CompactSpace K.space := isCompact_iff_compactSpace.mp
      (isCompact_space_of_finite_faces K hK)
    exact isCompact_range (interpolateVertices K hK v).continuous
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : F)).mp hcompact.isBounded
  obtain ⟨T, J, hT, hconv, hinterior, -, hJT, hJspace, hJref⟩ :=
    exists_finite_convex_complex_containing_bounded S hS (closedBall (0 : F) (R + 1))
      isBounded_closedBall
  have hJspace' : J.space = v '' L.space := hJspace.trans hSspace
  have hJref' : ∀ t ∈ J.faces, ∃ s ∈ L.faces,
      convexHull ℝ (t : Set F) ⊆ v '' convexHull ℝ (s : Set E) := by
    intro t ht
    obtain ⟨r, ⟨s, hs, rfl⟩, htr⟩ := hJref t ht
    obtain ⟨A, hA⟩ := hv s hs
    refine ⟨s, hs, ?_⟩
    rw [image_convexHull_eq_of_eqOn_affineMap v A hA]
    simpa only [Finset.coe_image] using htr
  have hSint : v '' L.space ⊆ interior T.space := by
    rw [← hSspace]
    exact subset_union_left.trans hinterior
  obtain ⟨C, hC⟩ := exists_embedding_perturbation_constant L v hv hinj T hT hconv J
    hJT hJspace' hJref' hSint
  let δ : ℝ≥0 := min (C + 1)⁻¹ (min 1 ⟨ε / 3, by positivity⟩)
  have hδ : 0 < δ := by
    apply lt_min
    · positivity
    · apply lt_min zero_lt_one
      change (0 : ℝ) < ε / 3
      positivity
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1 : (δ : ℝ) ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : (δ : ℝ) ≤ ε / 3 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : δ * C < 1 := calc
    δ * C ≤ (C + 1)⁻¹ * C := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    _ < 1 := (inv_mul_lt_one₀ (by positivity : 0 < C + 1)).mpr (by simp)
  have hV : K.vertices.Finite := by
    rw [K.vertices_eq]
    exact hK.biUnion (fun s _ => s.finite_toSet)
  obtain ⟨w, hw, -, hgp⟩ := exists_generalPositionOn hV.toFinset v (fun _ => (δ : ℝ))
    (fun _ _ => hδreal)
  have hwbound (a : E) (ha : a ∈ K.vertices) : ‖w a - v a‖ ≤ δ :=
    (hw a (hV.mem_toFinset.mpr ha)).le
  let u : E → F := fun x => if hx : x ∈ K.space then interpolateVertices K hK w ⟨x, hx⟩ else 0
  have hueq (x : E) (hx : x ∈ K.space) : u x = interpolateVertices K hK w ⟨x, hx⟩ :=
    dite_eq_left hx
  have huaff : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn u A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, -, hA⟩ := interpolateVertices_affineOn K hK w ⟨s, hLK hs⟩
    exact ⟨A, fun x hx => (hueq x (K.convexHull_subset_space (hLK hs) hx)).trans (hA _ hx)⟩
  have hunear (x : E) (hx : x ∈ L.space) : ‖u x - v x‖ ≤ δ := by
    rw [hueq x (hLspace hx), ← hvinterp ⟨x, hLspace hx⟩ hx]
    exact interpolateVertices_norm_sub_le K hK v w hwbound _
  obtain ⟨P, W, hPfixed, hPinterp, -, hPspace, -, hPinv⟩ := hC δ hsmall u huaff hunear
  obtain ⟨Q, hQ, hQspace, hQaff, -⟩ :=
    exists_image_complex_inverse_affine_of_interpolate T hT W P hPinterp
  have hHsmall : ∀ y, ‖P.symm y - y‖ < ε := by
    intro y
    exact (hPinv y).trans_lt (hδε.trans_lt (by linarith))
  refine ⟨w, P.symm, Q, hQ, ?_, ?_, ?_, ?_, hQaff, hHsmall, ?_⟩
  · intro s hs hcard
    exact hgp s (fun a ha => hV.mem_toFinset.mpr (hs ha)) hcard
  · intro x hx
    change P.symm (interpolateVertices K hK w x) = v x.1
    rw [← hueq x.1 x.2, ← hPfixed x.1 hx, P.symm_apply_apply]
  · intro x
    change ‖P.symm (interpolateVertices K hK w x) - interpolateVertices K hK v x‖ < ε
    calc
      _ ≤ ‖P.symm (interpolateVertices K hK w x) - interpolateVertices K hK w x‖ +
          ‖interpolateVertices K hK w x - interpolateVertices K hK v x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (δ : ℝ) + δ := add_le_add (hPinv _) (interpolateVertices_norm_sub_le K hK v w hwbound x)
      _ < ε := by linarith
  · intro x
    rw [hQspace, hPspace]
    apply interior_subset (hinterior (Or.inr ?_))
    apply mem_closedBall_zero_iff.mpr
    have hvR : ‖interpolateVertices K hK v x‖ < R := mem_ball_zero_iff.mp
      (hR (mem_range_self x))
    have he := interpolateVertices_norm_sub_le K hK v w hwbound x
    have hn := norm_le_norm_sub_add (interpolateVertices K hK w x) (interpolateVertices K hK v x)
    linarith
  · intro y
    have he := hHsmall (P y)
    simpa only [Homeomorph.symm_symm, P.symm_apply_apply, norm_sub_rev] using he

theorem exists_relative_interpolant_of_embedded_subcomplex {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (v : E → EuclideanSpace ℝ (Fin n))
    (hv : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn v A (convexHull ℝ (s : Set E)))
    (hinj : InjOn v L.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
      (Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))),
      Q.faces.Finite ∧
      (∀ s : Finset E, (s : Set E) ⊆ K.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : K.space, x.val ∈ L.space → correctedInterpolant K hK w H x = v x.val) ∧
      (∀ x : K.space, ‖correctedInterpolant K hK w H x - interpolateVertices K hK v x‖ < ε) ∧
      (∀ x : K.space, interpolateVertices K hK w x ∈ Q.space) ∧
      (∀ t ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
        EqOn H A (convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin n))))) := by
  obtain ⟨w, H, Q, hQ, hgp, hrel, hnear, hmap, hHaff, _, _⟩ :=
    exists_relative_interpolant_of_embedded_subcomplex_with_correction_control K hK L hLK v hv hinj hε
  exact ⟨w, H, Q, hQ, hgp, hrel, hnear, hmap, hHaff⟩

theorem exists_subdivision_correctedInterpolant
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (w : E → F) (H : F ≃ₜ F)
    (Q : SimplicialComplex ℝ F) (hQ : Q.faces.Finite)
    (hmap : ∀ x : K.space, interpolateVertices K hK w x ∈ Q.space)
    (hH : ∀ t ∈ Q.faces, ∃ A : F →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (t : Set F)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = K.space ∧
      simplicialRefines R K ∧ (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
      ∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F,
        ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → correctedInterpolant K hK w H x = A x.1 := by
  classical
  let u : E → F := fun x => if hx : x ∈ K.space then interpolateVertices K hK w ⟨x, hx⟩ else 0
  have hueq (x : E) (hx : x ∈ K.space) : u x = interpolateVertices K hK w ⟨x, hx⟩ :=
    dite_eq_left hx
  have huaff : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn u A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, -, hA⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
    exact ⟨A, fun x hx => (hueq x (K.convexHull_subset_space hs hx)).trans (hA _ hx)⟩
  have huQ : MapsTo u K.space Q.space := fun x hx => by rw [hueq x hx]; exact hmap _
  obtain ⟨R, hR, hspace, href, hdim, hPL⟩ :=
    exists_subdivision_piecewise_affine_comp K hK u huaff Q hQ huQ H hH hd
  refine ⟨R, hR, hspace, href, hdim, ?_⟩
  intro s hs
  obtain ⟨A, hA⟩ := hPL s hs
  refine ⟨A, fun x hx => ?_⟩
  change H (interpolateVertices K hK w x) = A x.1
  rw [← hueq x.1 x.2]
  exact hA hx

theorem exists_relative_piecewise_affine_approximation {n d : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (g : C(K.space, EuclideanSpace ℝ (Fin n)))
    (hPL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → g x = A x.1)
    (hinj : InjOn g (Subtype.val ⁻¹' L.space)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : SimplicialComplex ℝ E) (hP : P.faces.Finite) (hspace : P.space = K.space)
      (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
      simplicialRefines P K ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      (∀ s : Finset E, (s : Set E) ⊆ P.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : P.space, x.1 ∈ L.space →
        correctedInterpolant P hP w H x = g (Homeomorph.setCongr hspace x)) ∧
      (∀ x : P.space,
        ‖correctedInterpolant P hP w H x - g (Homeomorph.setCongr hspace x)‖ < ε) ∧
      ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = P.space ∧
        simplicialRefines R P ∧ (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ x : P.space, x.1 ∈ convexHull ℝ (s : Set E) →
            correctedInterpolant P hP w H x = A x.1 := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 2) (by positivity)
  obtain ⟨P₀, hP₀, hspace₀, href₀, hmesh, hdim₀⟩ :=
    exists_fine_subdivision_of_face_card_le K hK hd hδ
  have hL : L.faces.Finite := hK.subset hLK
  have hLspace : L.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK hs) hxs
  have hLP₀ : L.space ⊆ P₀.space := hspace₀.symm ▸ hLspace
  obtain ⟨P, J, hP, hPP₀, hPP₀ref, hPdim, -, hJP, hJspace, hJref⟩ :=
    exists_subdivision_containing_complex P₀ L hP₀ hL hLP₀ hdim₀
  let hspace : P.space = K.space := hPP₀.trans hspace₀
  let gP : C(P.space, EuclideanSpace ℝ (Fin n)) :=
    g.comp ⟨Homeomorph.setCongr hspace, (Homeomorph.setCongr hspace).continuous⟩
  let v : E → EuclideanSpace ℝ (Fin n) :=
    fun x => if hx : x ∈ K.space then g ⟨x, hx⟩ else 0
  have hveq (x : E) (hx : x ∈ K.space) : v x = g ⟨x, hx⟩ := dite_eq_left hx
  have hvJ : ∀ s ∈ J.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn v A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJref s hs
    obtain ⟨A, hA⟩ := hPL t ht
    refine ⟨A, fun x hx => ?_⟩
    have hxK := K.convexHull_subset_space (hLK ht) (hst hx)
    exact (hveq x hxK).trans (hA ⟨x, hxK⟩ (hst hx))
  have hvInj : InjOn v J.space := by
    intro x hx y hy hxy
    have hxL : x ∈ L.space := hJspace ▸ hx
    have hyL : y ∈ L.space := hJspace ▸ hy
    rw [hveq x (hLspace hxL), hveq y (hLspace hyL)] at hxy
    exact congrArg Subtype.val (hinj (x₁ := ⟨x, hLspace hxL⟩)
      (x₂ := ⟨y, hLspace hyL⟩) hxL hyL hxy)
  obtain ⟨w, H, Q, hQ, hgp, hrel, hnear, hmap, hHaff⟩ :=
    exists_relative_interpolant_of_embedded_subcomplex P hP J hJP v hvJ hvInj
      (show 0 < ε / 2 by positivity)
  have hvertex (a : E) (ha : a ∈ P.vertices) :
      v a = gP ⟨a, P.vertices_subset_space ha⟩ := by
    exact hveq a (hspace ▸ P.vertices_subset_space ha)
  have hosc (s : P.faces) (x y : P.space)
      (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) (hy : y.1 ∈ convexHull ℝ (s.1 : Set E)) :
      ‖gP x - gP y‖ < ε / 2 := by
    rw [← dist_eq_norm]
    apply hgδ
    change dist x.1 y.1 < δ
    obtain ⟨t, ht, hst⟩ := hPP₀ref s.1 s.2
    exact (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      (hst hx) (hst hy)).trans_lt (hmesh t ht)
  have happrox (x : P.space) : ‖interpolateVertices P hP v x - gP x‖ < ε / 2 := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
    apply interpolateVertices_norm_sub_lt_of_face P hP v ⟨s, hs⟩ x hxs (gP x)
    intro a ha
    have haP := face_vertices_subset P ⟨s, hs⟩ ha
    rw [hvertex a haP]
    exact hosc ⟨s, hs⟩ ⟨a, P.vertices_subset_space haP⟩ x
      (subset_convexHull ℝ _ ha) hxs
  refine ⟨P, hP, hspace, w, H, hPP₀ref.trans href₀, hPdim, hgp, ?_, ?_,
    exists_subdivision_correctedInterpolant P hP w H Q hQ hmap hHaff hPdim⟩
  · intro x hx
    exact (hrel x (hJspace.symm ▸ hx)).trans (hveq x.1 (hspace ▸ x.2))
  · intro x
    change ‖correctedInterpolant P hP w H x - gP x‖ < ε
    calc
      _ ≤ ‖correctedInterpolant P hP w H x - interpolateVertices P hP v x‖ +
          ‖interpolateVertices P hP v x - gP x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hnear x) (happrox x)
      _ = ε := add_halves ε

end DifferentialGeometry.Topology.Engulfing
