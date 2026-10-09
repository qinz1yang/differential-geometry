/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Star
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
noncomputable def carrierFace (K : Geometry.SimplicialComplex ℝ E) (x : E) : Finset E :=
  if h : x ∈ K.space then Classical.choose (exists_face_mem_openSimplex K h) else ∅

theorem carrierFace_spec {K : Geometry.SimplicialComplex ℝ E} {x : E} (hx : x ∈ K.space) :
    carrierFace K x ∈ K.faces ∧ x ∈ openSimplex (carrierFace K x) := by
  rw [carrierFace, dite_eq_left hx]
  exact Classical.choose_spec (exists_face_mem_openSimplex K hx)

theorem carrierFace_mem {K : Geometry.SimplicialComplex ℝ E} {x : E} (hx : x ∈ K.space) :
    carrierFace K x ∈ K.faces :=
  (carrierFace_spec hx).1

theorem mem_openSimplex_carrierFace {K : Geometry.SimplicialComplex ℝ E} {x : E}
    (hx : x ∈ K.space) : x ∈ openSimplex (carrierFace K x) :=
  (carrierFace_spec hx).2

theorem mem_convexHull_carrierFace {K : Geometry.SimplicialComplex ℝ E} {x : E}
    (hx : x ∈ K.space) : x ∈ convexHull ℝ ((carrierFace K x : Finset E) : Set E) :=
  openSimplex_subset_convexHull _ (mem_openSimplex_carrierFace hx)

theorem carrierFace_subset {K : Geometry.SimplicialComplex ℝ E} {x : E} (hx : x ∈ K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hxs : x ∈ convexHull ℝ (s : Set E)) :
    carrierFace K x ⊆ s :=
  face_subset_of_mem_openSimplex_of_mem_convexHull K (carrierFace_mem hx) hs
    (mem_openSimplex_carrierFace hx) hxs

theorem weights_eq_of_subset [DecidableEq E] {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s) {x : E}
    (hxt : x ∈ convexHull ℝ (t : Set E)) :
    ∀ v ∈ s, weights s x v = if v ∈ t then weights t x v else 0 := by
  have hxs : x ∈ convexHull ℝ (s : Set E) := convexHull_mono (Finset.coe_subset.mpr hts) hxt
  refine weights_eq hs hxs ?_ ?_
  · rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hts]
    exact sum_weights hxt
  · simp_rw [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hts]
    exact sum_weights_smul hxt

theorem weights_eq_of_subset_of_mem {s t : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (hts : t ⊆ s) {x : E} (hxt : x ∈ convexHull ℝ (t : Set E)) {v : E} (hv : v ∈ t) :
    weights s x v = weights t x v := by
  classical
  rw [weights_eq_of_subset hs hts hxt v (hts hv), ite_eq_left hv]

theorem weights_eq_zero_of_subset_of_notMem {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s) {x : E}
    (hxt : x ∈ convexHull ℝ (t : Set E)) {v : E} (hvs : v ∈ s) (hvt : v ∉ t) :
    weights s x v = 0 := by
  classical
  rw [weights_eq_of_subset hs hts hxt v hvs, ite_eq_right hvt]

noncomputable def simplicialMap (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) (x : E) : F :=
  ∑ v ∈ carrierFace K x, weights (carrierFace K x) x v • φ v

theorem simplicialMap_eq_of_mem (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) {s : Finset E}
    (hs : s ∈ K.faces) {x : E} (hxs : x ∈ convexHull ℝ (s : Set E)) :
    simplicialMap K φ x = ∑ v ∈ s, weights s x v • φ v := by
  classical
  have hx : x ∈ K.space := K.convexHull_subset_space hs hxs
  have hts := carrierFace_subset hx hs hxs
  have hxt := mem_convexHull_carrierFace hx
  unfold simplicialMap
  symm
  refine (Finset.sum_subset hts fun v hv hvt => ?_).symm.trans ?_
  · rw [weights_eq_zero_of_subset_of_notMem (K.indep hs) hts hxt hv hvt, zero_smul]
  · exact Finset.sum_congr rfl fun v hv => by
      rw [weights_eq_of_subset_of_mem (K.indep hs) hts hxt hv]

theorem simplicialMap_vertex (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) {v : E}
    (hv : {v} ∈ K.faces) : simplicialMap K φ v = φ v := by
  have hmem : v ∈ convexHull ℝ (({v} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v))
  rw [simplicialMap_eq_of_mem K φ hv hmem]
  have h1 : weights {v} v v = 1 := by
    have := sum_weights hmem
    rwa [Finset.sum_singleton] at this
  rw [Finset.sum_singleton, h1, one_smul]

theorem exists_affineMap_eqOn_simplicialMap [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ A : E →ᵃ[ℝ] F, EqOn (simplicialMap K φ) A (convexHull ℝ (s : Set E)) := by
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn (K.indep hs) φ
  refine ⟨A, fun x hx => ?_⟩
  rw [simplicialMap_eq_of_mem K φ hs hx]
  have hw := sum_weights hx
  have h1 : ∑ v ∈ s, weights s x v • v = s.affineCombination ℝ id (weights s x) :=
    (Finset.affineCombination_eq_linear_combination s id (weights s x) hw).symm
  have h2 : ∑ v ∈ s, weights s x v • A v = s.affineCombination ℝ (A ∘ id) (weights s x) :=
    (Finset.affineCombination_eq_linear_combination s (A ∘ id) (weights s x) hw).symm
  calc ∑ v ∈ s, weights s x v • φ v
      = ∑ v ∈ s, weights s x v • A v := Finset.sum_congr rfl fun v hv => by rw [hA v hv]
    _ = A (∑ v ∈ s, weights s x v • v) := by
        rw [h1, h2, Finset.map_affineCombination s id (weights s x) hw A]
    _ = A x := by rw [sum_weights_smul hx]

theorem isPiecewiseAffineOn_simplicialMap [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ : E → F) :
    IsPiecewiseAffineOn (simplicialMap K φ) K.space :=
  isPiecewiseAffineOn_space_of_forall_face K fun _ hs =>
    exists_affineMap_eqOn_simplicialMap K φ hs

theorem simplicialMap_mem_convexHull_image [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E)
    (φ : E → F) {s : Finset E} (hs : s ∈ K.faces) {x : E} (hxs : x ∈ convexHull ℝ (s : Set E)) :
    simplicialMap K φ x ∈ convexHull ℝ ((s.image φ : Finset F) : Set F) := by
  rw [simplicialMap_eq_of_mem K φ hs hxs]
  exact (convex_convexHull ℝ _).sum_mem (fun v hv => weights_nonneg hxs hv) (sum_weights hxs)
    fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hv))

theorem simplicialMap_mapsTo [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ F) (φ : E → F) (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    MapsTo (simplicialMap K φ) K.space L.space := fun _ hx =>
  L.convexHull_subset_space (hφ _ (carrierFace_mem hx))
    (simplicialMap_mem_convexHull_image K φ (carrierFace_mem hx) (mem_convexHull_carrierFace hx))

theorem simplicialMap_simplicialMap [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ F) (φ : E → F) (ψ : F → E)
    (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) (hψφ : ∀ s ∈ K.faces, ∀ v ∈ s, ψ (φ v) = v)
    {x : E} (hx : x ∈ K.space) : simplicialMap L ψ (simplicialMap K φ x) = x := by
  classical
  have hs : carrierFace K x ∈ K.faces := carrierFace_mem hx
  have hxs : x ∈ convexHull ℝ ((carrierFace K x : Finset E) : Set E) :=
    mem_convexHull_carrierFace hx
  set s := carrierFace K x with hsdef
  have hinj : ∀ v ∈ s, ∀ w ∈ s, φ v = φ w → v = w := fun v hv w hw h => by
    rw [← hψφ s hs v hv, ← hψφ s hs w hw, h]
  have ht : s.image φ ∈ L.faces := hφ s hs
  have hfx : simplicialMap K φ x = ∑ v ∈ s, weights s x v • φ v :=
    simplicialMap_eq_of_mem K φ hs hxs
  have hfxt : simplicialMap K φ x ∈ convexHull ℝ ((s.image φ : Finset F) : Set F) :=
    simplicialMap_mem_convexHull_image K φ hs hxs
  have hwt : ∀ u ∈ s.image φ, weights (s.image φ) (simplicialMap K φ x) u = weights s x (ψ u) := by
    refine weights_eq (L.indep ht) hfxt ?_ ?_
    · rw [Finset.sum_image hinj, ← sum_weights hxs]
      exact Finset.sum_congr rfl fun v hv => by rw [hψφ s hs v hv]
    · rw [Finset.sum_image hinj, hfx]
      exact Finset.sum_congr rfl fun v hv => by rw [hψφ s hs v hv]
  rw [simplicialMap_eq_of_mem L ψ ht hfxt, Finset.sum_congr rfl fun u hu => by rw [hwt u hu],
    Finset.sum_image hinj]
  conv_rhs => rw [← sum_weights_smul hxs]
  exact Finset.sum_congr rfl fun v hv => by rw [hψφ s hs v hv]

theorem isPLHomeomorphOn_simplicialMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces] (φ : E → F) (ψ : F → E)
    (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) (hψ : ∀ t ∈ L.faces, t.image ψ ∈ K.faces)
    (hψφ : ∀ s ∈ K.faces, ∀ v ∈ s, ψ (φ v) = v) (hφψ : ∀ t ∈ L.faces, ∀ u ∈ t, φ (ψ u) = u) :
    IsPLHomeomorphOn (simplicialMap K φ) K.space L.space := by
  have hinv : InvOn (simplicialMap L ψ) (simplicialMap K φ) K.space L.space :=
    ⟨fun _ hx => simplicialMap_simplicialMap K L φ ψ hφ hψφ hx,
      fun _ hy => simplicialMap_simplicialMap L K ψ φ hψ hφψ hy⟩
  have hbij : BijOn (simplicialMap K φ) K.space L.space :=
    hinv.bijOn (simplicialMap_mapsTo K L φ hφ) (simplicialMap_mapsTo L K ψ hψ)
  refine ⟨hbij, isPiecewiseAffineOn_simplicialMap K φ,
    (isPiecewiseAffineOn_simplicialMap L ψ).congr fun y hy => ?_⟩
  have h1 := hbij.invOn_invFunOn
  exact hbij.injOn (hbij.surjOn.mapsTo_invFunOn hy) (simplicialMap_mapsTo L K ψ hψ hy)
    ((h1.2 hy).trans (hinv.2 hy).symm)

end DifferentialGeometry.Topology.PiecewiseLinear
