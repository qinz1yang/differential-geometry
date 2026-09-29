/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_min_of_chain {α : Type*} {d : Finset (Finset α)}
    (hd : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) (hne : d.Nonempty) : ∃ m ∈ d, ∀ s ∈ d, m ⊆ s := by
  obtain ⟨m, hm, hmin⟩ := d.exists_min_image Finset.card hne
  refine ⟨m, hm, fun s hs => ?_⟩
  rcases hd s hs m hm with hsm | hms
  · exact (Finset.eq_of_subset_of_card_le hsm (hmin s hs)).ge
  · exact hms

theorem centroid_eq_sum (s : Finset E) (hs : s.Nonempty) :
    s.centroid ℝ id = ∑ v ∈ s, (s.card : ℝ)⁻¹ • v := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hs)]
  exact Finset.sum_congr rfl fun v _ => by rw [Finset.centroidWeights_apply]; rfl

theorem weights_centroid [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {s : Finset E} (hsT : s ⊆ T) (hs : s.Nonempty)
    {v : E} (hv : v ∈ T) :
    weights T (s.centroid ℝ id) v = if v ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hmem : s.centroid ℝ id ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hsT)
      (openSimplex_subset_convexHull s (centroid_mem_openSimplex hs))
  have h₁ : ∑ u ∈ T, (if u ∈ s then (s.card : ℝ)⁻¹ else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsT, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ hcard.ne']
  have h₂ : ∑ u ∈ T, (if u ∈ s then (s.card : ℝ)⁻¹ else 0) • u = s.centroid ℝ id := by
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsT]
    exact (centroid_eq_sum s hs).symm
  exact weights_eq hT hmem h₁ h₂ v hv

theorem weights_sum_centroid [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {μ : Finset E → ℝ} (hμ₀ : ∀ s ∈ d, 0 ≤ μ s)
    (hμ₁ : ∑ s ∈ d, μ s = 1) {v : E} (hv : v ∈ T) :
    weights T (∑ s ∈ d, μ s • s.centroid ℝ id) v =
      ∑ s ∈ d, if v ∈ s then μ s * (s.card : ℝ)⁻¹ else 0 := by
  have hp : ∀ s ∈ d, s.centroid ℝ id ∈ convexHull ℝ (T : Set E) := fun s hs =>
    convexHull_mono (Finset.coe_subset.mpr (hd s hs).2)
      (openSimplex_subset_convexHull s (centroid_mem_openSimplex (hd s hs).1))
  rw [weights_sum_smul hT d hp hμ₀ hμ₁ v hv]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [weights_centroid hT (hd s hs).2 (hd s hs).1 hv, mul_ite, mul_zero]

theorem weights_sum_centroid_le_of_mem_min {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {m : Finset E} (hm : m ∈ d) (hmin : ∀ s ∈ d, m ⊆ s)
    {μ : Finset E → ℝ} (hμ₀ : ∀ s ∈ d, 0 ≤ μ s) (hμ₁ : ∑ s ∈ d, μ s = 1) {v v₀ : E}
    (hv : v ∈ T) (hv₀ : v₀ ∈ m) :
    weights T (∑ s ∈ d, μ s • s.centroid ℝ id) v ≤
      weights T (∑ s ∈ d, μ s • s.centroid ℝ id) v₀ := by
  classical
  rw [weights_sum_centroid hT hd hμ₀ hμ₁ hv,
    weights_sum_centroid hT hd hμ₀ hμ₁ ((hd m hm).2 hv₀)]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [ite_eq_left (hmin s hs hv₀)]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hμ₀ s hs) (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem weights_sum_centroid_lt_of_notMem_min {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {m : Finset E} (hm : m ∈ d) (hmin : ∀ s ∈ d, m ⊆ s)
    {μ : Finset E → ℝ} (hμ₀ : ∀ s ∈ d, 0 ≤ μ s) (hμ₁ : ∑ s ∈ d, μ s = 1) (hμm : 0 < μ m)
    {v v₀ : E} (hv : v ∈ T) (hvm : v ∉ m) (hv₀ : v₀ ∈ m) :
    weights T (∑ s ∈ d, μ s • s.centroid ℝ id) v <
      weights T (∑ s ∈ d, μ s • s.centroid ℝ id) v₀ := by
  classical
  rw [weights_sum_centroid hT hd hμ₀ hμ₁ hv,
    weights_sum_centroid hT hd hμ₀ hμ₁ ((hd m hm).2 hv₀)]
  refine Finset.sum_lt_sum (fun s hs => ?_) ⟨m, hm, ?_⟩
  · rw [ite_eq_left (hmin s hs hv₀)]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hμ₀ s hs) (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [ite_eq_right hvm, ite_eq_left hv₀]
    exact mul_pos hμm (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hd m hm).1)))

theorem exists_weights_of_mem_openSimplex_image [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hdf : IsFlag (simplexComplex T hT) d) {x : E}
    (hx : x ∈ openSimplex (d.image fun s => s.centroid ℝ id)) :
    ∃ μ : Finset E → ℝ, (∀ s ∈ d, 0 < μ s) ∧ ∑ s ∈ d, μ s = 1 ∧
      ∑ s ∈ d, μ s • s.centroid ℝ id = x :=
  (mem_openSimplex_image_iff (hdf.injOn (simplexComplex T hT)
    (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT)))).mp hx

theorem weights_lt_of_notMem_min [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hdf : IsFlag (simplexComplex T hT) d) {m : Finset E} (hm : m ∈ d)
    (hmin : ∀ s ∈ d, m ⊆ s) {x : E}
    (hx : x ∈ openSimplex (d.image fun s => s.centroid ℝ id)) :
    ∀ v ∈ T, v ∉ m → ∀ v₀ ∈ m, weights T x v < weights T x v₀ := by
  obtain ⟨μ, hμ₀, hμ₁, hμx⟩ := exists_weights_of_mem_openSimplex_image hT hdf hx
  have hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T := fun s hs =>
    (mem_simplexComplex_faces_iff T hT).mp (hdf.mem_faces hs)
  intro v hv hvm v₀ hv₀
  rw [← hμx]
  exact weights_sum_centroid_lt_of_notMem_min hT hd hm hmin (fun s hs => (hμ₀ s hs).le) hμ₁
    (hμ₀ m hm) hv hvm hv₀

theorem weights_eq_of_mem_min [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hdf : IsFlag (simplexComplex T hT) d) {m : Finset E} (hm : m ∈ d)
    (hmin : ∀ s ∈ d, m ⊆ s) {x : E}
    (hx : x ∈ openSimplex (d.image fun s => s.centroid ℝ id)) :
    ∀ v ∈ m, ∀ v₀ ∈ m, weights T x v = weights T x v₀ := by
  obtain ⟨μ, hμ₀, hμ₁, hμx⟩ := exists_weights_of_mem_openSimplex_image hT hdf hx
  have hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T := fun s hs =>
    (mem_simplexComplex_faces_iff T hT).mp (hdf.mem_faces hs)
  intro v hv v₀ hv₀
  rw [← hμx, weights_sum_centroid hT hd (fun s hs => (hμ₀ s hs).le) hμ₁ ((hd m hm).2 hv),
    weights_sum_centroid hT hd (fun s hs => (hμ₀ s hs).le) hμ₁ ((hd m hm).2 hv₀)]
  exact Finset.sum_congr rfl fun s hs => by rw [ite_eq_left (hmin s hs hv), ite_eq_left (hmin s hs hv₀)]

def faceNeighborhoodFaces [DecidableEq E] (T : Finset E) (f : Finset E) : Set (Finset E) :=
  {u | ∃ d : Finset (Finset E), (∀ s ∈ d, s.Nonempty ∧ s ⊆ T) ∧
    (∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) ∧ d.Nonempty ∧ (∀ s ∈ d, (s ∩ f).Nonempty) ∧
    u = d.image fun s => s.centroid ℝ id}

theorem faceNeighborhoodFaces_subset [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    faceNeighborhoodFaces T f ⊆ (barycentricSubdivision (simplexComplex T hT)).faces := by
  rintro u ⟨d, hd, hchain, hne, -, rfl⟩
  exact ⟨d, ⟨fun s hs => hd s hs, hchain⟩, hne, rfl⟩

def faceNeighborhood [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (f : Finset E) : Geometry.SimplicialComplex ℝ E where
  faces := faceNeighborhoodFaces T f
  isRelLowerSet_faces := by
    rintro u ⟨d, hd, hchain, hne, hmeet, rfl⟩
    refine ⟨hne.image _, fun u' hu' hu'ne => ?_⟩
    refine ⟨d.filter fun s => s.centroid ℝ id ∈ u',
      fun s hs => hd s (Finset.mem_of_mem_filter s hs),
      fun s hs t ht => hchain s (Finset.mem_of_mem_filter s hs) t (Finset.mem_of_mem_filter t ht),
      ?_, fun s hs => hmeet s (Finset.mem_of_mem_filter s hs), (image_filter_mem_eq hu').symm⟩
    obtain ⟨p, hp⟩ := hu'ne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hu' hp)
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩⟩
  indep hs := (barycentricSubdivision (simplexComplex T hT)).indep
    (faceNeighborhoodFaces_subset T hT f hs)
  inter_subset_convexHull hs ht :=
    (barycentricSubdivision (simplexComplex T hT)).inter_subset_convexHull
      (faceNeighborhoodFaces_subset T hT f hs) (faceNeighborhoodFaces_subset T hT f ht)

theorem mem_faceNeighborhood_faces_iff [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) {u : Finset E} :
    u ∈ (faceNeighborhood T hT f).faces ↔ ∃ d : Finset (Finset E),
      (∀ s ∈ d, s.Nonempty ∧ s ⊆ T) ∧ (∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) ∧ d.Nonempty ∧
        (∀ s ∈ d, (s ∩ f).Nonempty) ∧ u = d.image fun s => s.centroid ℝ id := Iff.rfl

theorem faceNeighborhood_faces_subset [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    (faceNeighborhood T hT f).faces ⊆ (barycentricSubdivision (simplexComplex T hT)).faces :=
  faceNeighborhoodFaces_subset T hT f

theorem faceNeighborhood_faces_finite [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    (faceNeighborhood T hT f).faces.Finite := by
  refine (Set.toFinite ((((T.powerset.image fun s => s.centroid ℝ id).powerset) :
    Finset (Finset E)) : Set (Finset E))).subset ?_
  rintro u ⟨d, hd, -, -, -, rfl⟩
  refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun p hp => ?_)
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr (hd s hs).2)

theorem mem_faceNeighborhood_space_iff [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
    {x : E} :
    x ∈ (faceNeighborhood T hT f).space ↔
      x ∈ convexHull ℝ (T : Set E) ∧ ∃ v ∈ f, ∀ w ∈ T, weights T x w ≤ weights T x v := by
  obtain ⟨v₁, hv₁⟩ := hf
  have hTne : T.Nonempty := ⟨v₁, hfT hv₁⟩
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := (faceNeighborhood T hT f).mem_space_iff.mp hx
    obtain ⟨d, hd, hchain, hne, hmeet, rfl⟩ := hu
    have hflag : IsFlag (simplexComplex T hT) d := ⟨fun s hs => hd s hs, hchain⟩
    refine ⟨convexHull_image_subset (simplexComplex T hT)
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT)) hflag
      (fun s hs => (hd s hs).2) hxu, ?_⟩
    obtain ⟨m, hm, hmin⟩ := exists_min_of_chain hchain hne
    obtain ⟨v, hv⟩ := hmeet m hm
    rw [Finset.mem_inter] at hv
    refine ⟨v, hv.2, ?_⟩
    obtain ⟨w, hw₀, hw₁, hwx⟩ := mem_convexHull_iff_exists_weights.mp hxu
    have hinj : Set.InjOn (fun s : Finset E => s.centroid ℝ id) (d : Set (Finset E)) :=
      hflag.injOn (simplexComplex T hT)
        (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))
    have himg₁ : ∑ p ∈ d.image fun s => s.centroid ℝ id, w p =
        ∑ s ∈ d, w (s.centroid ℝ id) := Finset.sum_image hinj
    have himg₂ : ∑ p ∈ d.image fun s => s.centroid ℝ id, w p • p =
        ∑ s ∈ d, w (s.centroid ℝ id) • s.centroid ℝ id := Finset.sum_image hinj
    have hμ₀ : ∀ s ∈ d, 0 ≤ w (s.centroid ℝ id) := fun s hs =>
      hw₀ _ (Finset.mem_image_of_mem _ hs)
    have hμx : ∑ s ∈ d, w (s.centroid ℝ id) • s.centroid ℝ id = x := himg₂.symm.trans hwx
    intro q hq
    rw [← hμx]
    exact weights_sum_centroid_le_of_mem_min hT hd hm hmin hμ₀ (himg₁.symm.trans hw₁) hq hv.1
  · rintro ⟨hxT, v, hvf, hmax⟩
    have hxsp : x ∈ (barycentricSubdivision (simplexComplex T hT)).space := by
      rw [(barycentricSubdivision_isSubdivision (simplexComplex T hT)).space_eq]
      exact (simplexComplex T hT).convexHull_subset_space ⟨hTne, Finset.Subset.refl T⟩ hxT
    obtain ⟨u, hu, hxu⟩ :=
      exists_face_mem_openSimplex (barycentricSubdivision (simplexComplex T hT)) hxsp
    obtain ⟨d, hflag, hne, rfl⟩ := (mem_derived_faces_iff (simplexComplex T hT)
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))).mp hu
    have hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T := fun s hs =>
      (mem_simplexComplex_faces_iff T hT).mp (hflag.mem_faces hs)
    obtain ⟨m, hm, hmin⟩ := exists_min_of_chain hflag.2 hne
    have hvm : v ∈ m := by
      by_contra hvm
      obtain ⟨v₀, hv₀⟩ := (hd m hm).1
      exact absurd (hmax v₀ ((hd m hm).2 hv₀))
        (not_le.mpr (weights_lt_of_notMem_min hT hflag hm hmin hxu v (hfT hvf) hvm v₀ hv₀))
    refine (faceNeighborhood T hT f).mem_space_iff.mpr
      ⟨d.image fun s => s.centroid ℝ id, ⟨d, hd, hflag.2, hne, fun s hs =>
        ⟨v, Finset.mem_inter.mpr ⟨hmin s hs hvm, hvf⟩⟩, rfl⟩, ?_⟩
    exact openSimplex_subset_convexHull _ hxu

end DifferentialGeometry.Topology.PiecewiseLinear
