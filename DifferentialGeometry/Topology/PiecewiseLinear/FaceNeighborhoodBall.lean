/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights
import DifferentialGeometry.Topology.PiecewiseLinear.RadialProjection
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def faceRadialFrontierFaces [DecidableEq E] (T : Finset E) (f : Finset E) : Set (Finset E) :=
  {u | ∃ d : Finset (Finset E), (∀ s ∈ d, s.Nonempty ∧ s ⊆ T) ∧
    (∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) ∧ d.Nonempty ∧ (∀ s ∈ d, (s ∩ f).Nonempty) ∧
    ((∀ s ∈ d, (s ∩ (T \ f)).Nonempty) ∨ ∃ v ∈ f, ∀ s ∈ d, v ∉ s) ∧
    u = d.image fun s => s.centroid ℝ id}

theorem faceRadialFrontierFaces_subset [DecidableEq E] (T : Finset E) (f : Finset E) :
    faceRadialFrontierFaces T f ⊆ faceNeighborhoodFaces T f := by
  rintro u ⟨d, hd, hchain, hne, hmeet, -, rfl⟩
  exact ⟨d, hd, hchain, hne, hmeet, rfl⟩

def faceRadialFrontier [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (f : Finset E) : Geometry.SimplicialComplex ℝ E where
  faces := faceRadialFrontierFaces T f
  isRelLowerSet_faces := by
    rintro u ⟨d, hd, hchain, hne, hmeet, htype, rfl⟩
    refine ⟨hne.image _, fun u' hu' hu'ne => ?_⟩
    refine ⟨d.filter fun s => s.centroid ℝ id ∈ u',
      fun s hs => hd s (Finset.mem_of_mem_filter s hs),
      fun s hs t ht => hchain s (Finset.mem_of_mem_filter s hs) t (Finset.mem_of_mem_filter t ht),
      ?_, fun s hs => hmeet s (Finset.mem_of_mem_filter s hs), ?_,
      (image_filter_mem_eq hu').symm⟩
    · obtain ⟨q, hq⟩ := hu'ne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hu' hq)
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hq⟩⟩
    · rcases htype with hM | ⟨v, hvf, hv⟩
      · exact Or.inl fun s hs => hM s (Finset.mem_of_mem_filter s hs)
      · exact Or.inr ⟨v, hvf, fun s hs => hv s (Finset.mem_of_mem_filter s hs)⟩
  indep hs := (faceNeighborhood T hT f).indep (faceRadialFrontierFaces_subset T f hs)
  inter_subset_convexHull hs ht :=
    (faceNeighborhood T hT f).inter_subset_convexHull (faceRadialFrontierFaces_subset T f hs)
      (faceRadialFrontierFaces_subset T f ht)

theorem mem_faceRadialFrontier_faces_iff [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) {u : Finset E} :
    u ∈ (faceRadialFrontier T hT f).faces ↔ ∃ d : Finset (Finset E),
      (∀ s ∈ d, s.Nonempty ∧ s ⊆ T) ∧ (∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) ∧ d.Nonempty ∧
        (∀ s ∈ d, (s ∩ f).Nonempty) ∧
        ((∀ s ∈ d, (s ∩ (T \ f)).Nonempty) ∨ ∃ v ∈ f, ∀ s ∈ d, v ∉ s) ∧
        u = d.image fun s => s.centroid ℝ id := Iff.rfl

theorem faceRadialFrontier_faces_subset [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    (faceRadialFrontier T hT f).faces ⊆ (faceNeighborhood T hT f).faces :=
  faceRadialFrontierFaces_subset T f

theorem faceRadialFrontier_faces_finite [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    (faceRadialFrontier T hT f).faces.Finite :=
  (faceNeighborhood_faces_finite T hT f).subset (faceRadialFrontier_faces_subset T hT f)

theorem faceRadialFrontier_space_subset [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (f : Finset E) :
    (faceRadialFrontier T hT f).space ⊆ (faceNeighborhood T hT f).space := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ := (faceRadialFrontier T hT f).mem_space_iff.mp hx
  exact (faceNeighborhood T hT f).convexHull_subset_space
    (faceRadialFrontier_faces_subset T hT f hu) hxu

theorem weights_sum_centroid_of_sum_eq_one [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {a : Finset E → ℝ} (ha : ∑ s ∈ d, a s = 1)
    (hx : ∑ s ∈ d, a s • s.centroid ℝ id ∈ convexHull ℝ (T : Set E)) {v : E} (hv : v ∈ T) :
    weights T (∑ s ∈ d, a s • s.centroid ℝ id) v =
      ∑ s ∈ d, if v ∈ s then a s * (s.card : ℝ)⁻¹ else 0 := by
  have hcard : ∀ s ∈ d, ((s.card : ℝ)) ≠ 0 := fun s hs =>
    (Nat.cast_pos.mpr (Finset.card_pos.mpr (hd s hs).1)).ne'
  refine weights_eq hT hx (w := fun u => ∑ s ∈ d, if u ∈ s then a s * (s.card : ℝ)⁻¹ else 0)
    ?_ ?_ v hv
  · rw [Finset.sum_comm, ← ha]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hd s hs).2, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, mul_comm (s.card : ℝ) (a s), mul_assoc, mul_inv_cancel₀ (hcard s hs), mul_one]
  · simp_rw [Finset.sum_smul, Finset.sum_comm (s := T)]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp_rw [ite_smul, zero_smul, mul_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hd s hs).2, ← Finset.smul_sum,
      centroid_eq_sum s (hd s hs).1]

theorem centroid_mem_convexHull_of_subset {T : Finset E} {f : Finset E} (hfT : f ⊆ T)
    (hf : f.Nonempty) : f.centroid ℝ id ∈ convexHull ℝ (T : Set E) :=
  convexHull_mono (Finset.coe_subset.mpr hfT)
    (openSimplex_subset_convexHull f (centroid_mem_openSimplex hf))

theorem weights_centroid_of_mem {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) {v : E} (hv : v ∈ f) :
    weights T (f.centroid ℝ id) v = (f.card : ℝ)⁻¹ := by
  classical
  rw [weights_centroid hT hfT hf (hfT hv), ite_eq_left hv]

theorem weights_centroid_of_notMem {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) {v : E} (hv : v ∈ T) (hvf : v ∉ f) :
    weights T (f.centroid ℝ id) v = 0 := by
  classical
  rw [weights_centroid hT hfT hf hv, ite_eq_right hvf]

theorem exists_weights_of_mem_convexHull_image [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {x : E}
    (hx : x ∈ convexHull ℝ ((d.image fun s => s.centroid ℝ id : Finset E) : Set E)) :
    ∃ μ : Finset E → ℝ, (∀ s ∈ d, 0 ≤ μ s) ∧ ∑ s ∈ d, μ s = 1 ∧
      ∑ s ∈ d, μ s • s.centroid ℝ id = x := by
  obtain ⟨w, hw₀, hw₁, hwx⟩ := mem_convexHull_iff_exists_weights.mp hx
  have hinj : Set.InjOn (fun s : Finset E => s.centroid ℝ id) (d : Set (Finset E)) :=
    (injOn_faces_of_mem_openSimplex (simplexComplex T hT)
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))).mono
      fun s hs => hd s (Finset.mem_coe.mp hs)
  have h₁ : ∑ p ∈ d.image fun s => s.centroid ℝ id, w p = ∑ s ∈ d, w (s.centroid ℝ id) :=
    Finset.sum_image hinj
  have h₂ : ∑ p ∈ d.image fun s => s.centroid ℝ id, w p • p =
      ∑ s ∈ d, w (s.centroid ℝ id) • s.centroid ℝ id := Finset.sum_image hinj
  exact ⟨fun s => w (s.centroid ℝ id), fun s hs => hw₀ _ (Finset.mem_image_of_mem _ hs),
    h₁.symm.trans hw₁, h₂.symm.trans hwx⟩

theorem weights_le_of_mem_convexHull_image [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {m : Finset E} (hm : m ∈ d) (hmin : ∀ s ∈ d, m ⊆ s)
    {x : E} (hx : x ∈ convexHull ℝ ((d.image fun s => s.centroid ℝ id : Finset E) : Set E))
    {v v₀ : E} (hv : v ∈ T) (hv₀ : v₀ ∈ m) : weights T x v ≤ weights T x v₀ := by
  obtain ⟨μ, hμ₀, hμ₁, hμx⟩ := exists_weights_of_mem_convexHull_image hT hd hx
  rw [← hμx]
  exact weights_sum_centroid_le_of_mem_min hT hd hm hmin hμ₀ hμ₁ hv hv₀

theorem weights_eq_zero_of_mem_convexHull_image [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {d : Finset (Finset E)}
    (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) {x : E}
    (hx : x ∈ convexHull ℝ ((d.image fun s => s.centroid ℝ id : Finset E) : Set E)) {v : E}
    (hv : v ∈ T) (hvd : ∀ s ∈ d, v ∉ s) : weights T x v = 0 := by
  obtain ⟨μ, hμ₀, hμ₁, hμx⟩ := exists_weights_of_mem_convexHull_image hT hd hx
  rw [← hμx, weights_sum_centroid hT hd hμ₀ hμ₁ hv]
  exact Finset.sum_eq_zero fun s hs => ite_eq_right (hvd s hs)

theorem exists_of_mem_faceRadialFrontier_space [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) {x : E}
    (hx : x ∈ (faceRadialFrontier T hT f).space) :
    (∃ w ∈ T \ f, ∀ v ∈ T, weights T x v ≤ weights T x w) ∨ ∃ v ∈ f, weights T x v = 0 := by
  obtain ⟨u, ⟨d, hd, hchain, hne, -, htype, rfl⟩, hxu⟩ :=
    (faceRadialFrontier T hT f).mem_space_iff.mp hx
  rcases htype with hM | ⟨v, hvf, hvd⟩
  · obtain ⟨m, hm, hmin⟩ := exists_min_of_chain hchain hne
    obtain ⟨w, hw⟩ := hM m hm
    rw [Finset.mem_inter] at hw
    exact Or.inl ⟨w, hw.2,
      fun v hv => weights_le_of_mem_convexHull_image hT hd hm hmin hxu hv hw.1⟩
  · exact Or.inr ⟨v, hvf, weights_eq_zero_of_mem_convexHull_image hT hd hxu (hfT hvf) hvd⟩

theorem notMem_faceRadialFrontier_space [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) :
    f.centroid ℝ id ∉ (faceRadialFrontier T hT f).space := by
  intro hp
  have hk : (0 : ℝ) < (f.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hf)
  obtain ⟨v₀, hv₀⟩ := id hf
  rcases exists_of_mem_faceRadialFrontier_space hT hfT hp with ⟨w, hw, hmax⟩ | ⟨v, hvf, hv0⟩
  · rw [Finset.mem_sdiff] at hw
    have h1 := hmax v₀ (hfT hv₀)
    rw [weights_centroid_of_mem hT hfT hf hv₀,
      weights_centroid_of_notMem hT hfT hf hw.1 hw.2] at h1
    exact absurd h1 (not_le.mpr (inv_pos.mpr hk))
  · rw [weights_centroid_of_mem hT hfT hf hvf] at hv0
    exact (inv_pos.mpr hk).ne' hv0

theorem not_radial_lt_one_faceRadialFrontier [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
    {x y : E} (hx : x ∈ (faceRadialFrontier T hT f).space)
    (hy : y ∈ (faceRadialFrontier T hT f).space) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hyx : y = f.centroid ℝ id + t • (x - f.centroid ℝ id)) : False := by
  have hk : (0 : ℝ) < (f.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hf)
  have hkpos : (0 : ℝ) < (f.card : ℝ)⁻¹ := inv_pos.mpr hk
  have hp : f.centroid ℝ id ∈ convexHull ℝ (T : Set E) := centroid_mem_convexHull_of_subset hfT hf
  obtain ⟨hxT, v₁, hv₁f, hv₁max⟩ := (mem_faceNeighborhood_space_iff hT hfT hf).mp
    (faceRadialFrontier_space_subset T hT f hx)
  have hcombo : ∀ v ∈ T,
      weights T y v = (1 - t) * weights T (f.centroid ℝ id) v + t * weights T x v := by
    intro v hv
    rw [hyx, add_smul_sub_eq_combo]
    exact weights_combo hT hp hxT (by linarith) ht0.le (by ring) v hv
  rcases exists_of_mem_faceRadialFrontier_space hT hfT hy with ⟨w, hw, hmax⟩ | ⟨v, hvf, hv0⟩
  · rw [Finset.mem_sdiff] at hw
    have h1 := hmax v₁ (hfT hv₁f)
    rw [hcombo v₁ (hfT hv₁f), hcombo w hw.1, weights_centroid_of_mem hT hfT hf hv₁f,
      weights_centroid_of_notMem hT hfT hf hw.1 hw.2] at h1
    have h2 := hv₁max w hw.1
    linarith [mul_pos (show (0 : ℝ) < 1 - t by linarith) hkpos,
      mul_nonneg ht0.le (sub_nonneg.mpr h2)]
  · rw [hcombo v (hfT hvf), weights_centroid_of_mem hT hfT hf hvf] at hv0
    linarith [mul_pos (show (0 : ℝ) < 1 - t by linarith) hkpos,
      mul_nonneg ht0.le (weights_nonneg hxT (hfT hvf))]

theorem isRadiallyInjective_faceRadialFrontier [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) :
    IsRadiallyInjective (f.centroid ℝ id) (faceRadialFrontier T hT f).space := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_faceRadialFrontier hT hfT hf hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = f.centroid ℝ id + t⁻¹ • (y - f.centroid ℝ id) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_faceRadialFrontier hT hfT hf hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem notMem_of_faceRadialFrontier_type [DecidableEq E] {T f : Finset E}
    {d : Finset (Finset E)}
    (htype : (∀ s ∈ d, (s ∩ (T \ f)).Nonempty) ∨ ∃ v ∈ f, ∀ s ∈ d, v ∉ s) : f ∉ d := by
  intro hfd
  rcases htype with hM | ⟨v, hvf, hvd⟩
  · obtain ⟨w, hw⟩ := hM f hfd
    rw [Finset.mem_inter, Finset.mem_sdiff] at hw
    exact hw.2.2 hw.1
  · exact hvd f hfd hvf

theorem centroid_notMem_image [DecidableEq E] {T f : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hfT : f ⊆ T) (hf : f.Nonempty)
    {d : Finset (Finset E)} (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T) (hfd : f ∉ d) :
    f.centroid ℝ id ∉ d.image fun s => s.centroid ℝ id := by
  intro hmem
  obtain ⟨s, hs, hsf⟩ := Finset.mem_image.mp hmem
  have hinj := injOn_faces_of_mem_openSimplex (simplexComplex T hT)
    (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))
  have hsf' : s = f := hinj (hd s hs) ⟨hf, hfT⟩ hsf
  exact hfd (hsf' ▸ hs)

theorem affineIndependent_insert_centroid [DecidableEq E] {T f : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hfT : f ⊆ T) (hf : f.Nonempty)
    {d : Finset (Finset E)} (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T)
    (hchain : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) (hne : d.Nonempty)
    (hmeet : ∀ s ∈ d, (s ∩ f).Nonempty)
    (htype : (∀ s ∈ d, (s ∩ (T \ f)).Nonempty) ∨ ∃ v ∈ f, ∀ s ∈ d, v ∉ s)
    (hindep : AffineIndependent ℝ ((↑) : (d.image fun s => s.centroid ℝ id) → E)) :
    AffineIndependent ℝ
      ((↑) : {x // x ∈ insert (f.centroid ℝ id) (d.image fun s => s.centroid ℝ id)} → E) := by
  have hk : (0 : ℝ) < (f.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hf)
  have hp := centroid_notMem_image hT hfT hf hd (notMem_of_faceRadialFrontier_type htype)
  rw [affineIndependent_insert_iff hp hindep]
  rintro ⟨b, hb1, hbp⟩
  have hinj : Set.InjOn (fun s : Finset E => s.centroid ℝ id) (d : Set (Finset E)) :=
    (injOn_faces_of_mem_openSimplex (simplexComplex T hT)
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))).mono
      fun s hs => hd s (Finset.mem_coe.mp hs)
  have e₁ : ∑ p ∈ d.image fun s => s.centroid ℝ id, b p = ∑ s ∈ d, b (s.centroid ℝ id) :=
    Finset.sum_image hinj
  have e₂ : ∑ p ∈ d.image fun s => s.centroid ℝ id, b p • p =
      ∑ s ∈ d, b (s.centroid ℝ id) • s.centroid ℝ id := Finset.sum_image hinj
  have h1 : ∑ s ∈ d, b (s.centroid ℝ id) = 1 := e₁.symm.trans hb1
  have h2 : ∑ s ∈ d, b (s.centroid ℝ id) • s.centroid ℝ id = f.centroid ℝ id :=
    e₂.symm.trans hbp
  have hmem : ∑ s ∈ d, b (s.centroid ℝ id) • s.centroid ℝ id ∈ convexHull ℝ (T : Set E) := by
    rw [h2]
    exact centroid_mem_convexHull_of_subset hfT hf
  have hw : ∀ v ∈ T, weights T (f.centroid ℝ id) v =
      ∑ s ∈ d, if v ∈ s then b (s.centroid ℝ id) * (s.card : ℝ)⁻¹ else 0 := fun v hv => by
    rw [← h2]
    exact weights_sum_centroid_of_sum_eq_one hT hd h1 hmem hv
  rcases htype with hM | ⟨v, hvf, hvd⟩
  · obtain ⟨m, hm, hmin⟩ := exists_min_of_chain hchain hne
    obtain ⟨v, hv⟩ := hmeet m hm
    rw [Finset.mem_inter] at hv
    obtain ⟨w, hwm⟩ := hM m hm
    rw [Finset.mem_inter, Finset.mem_sdiff] at hwm
    have g₁ := hw v (hfT hv.2)
    have g₂ := hw w hwm.2.1
    rw [weights_centroid_of_mem hT hfT hf hv.2,
      Finset.sum_congr rfl fun s hs => ite_eq_left (hmin s hs hv.1)] at g₁
    rw [weights_centroid_of_notMem hT hfT hf hwm.2.1 hwm.2.2,
      Finset.sum_congr rfl fun s hs => ite_eq_left (hmin s hs hwm.1)] at g₂
    exact (inv_pos.mpr hk).ne' (g₁.trans g₂.symm)
  · have g₁ := hw v (hfT hvf)
    rw [weights_centroid_of_mem hT hfT hf hvf,
      Finset.sum_congr rfl fun s hs => ite_eq_right (hvd s hs), Finset.sum_const_zero] at g₁
    exact (inv_pos.mpr hk).ne' g₁

theorem isConeBase_faceRadialFrontier [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) :
    IsConeBase (f.centroid ℝ id) (faceRadialFrontier T hT f) where
  notMem_space := notMem_faceRadialFrontier_space hT hfT hf
  indep := by
    rintro u hu
    obtain ⟨d, hd, hchain, hne, hmeet, htype, rfl⟩ := hu
    have h : AffineIndependent ℝ ((↑) : ((insert (f.centroid ℝ id)
        (d.image fun s => s.centroid ℝ id) : Finset E) : Set E) → E) :=
      affineIndependent_insert_centroid hT hfT hf hd hchain hne hmeet htype
        ((faceRadialFrontier T hT f).indep ⟨d, hd, hchain, hne, hmeet, htype, rfl⟩)
    rwa [Finset.coe_insert] at h
  radial := isRadiallyInjective_faceRadialFrontier hT hfT hf

theorem smul_add_smul_sub_smul_eq {A B : E} {k r n : ℝ} (hk : k ≠ 0) (hr : r ≠ 0) (hn : n ≠ 0)
    (hc : r + k = n) : k⁻¹ • A + (n / r) • (n⁻¹ • (B + A) - k⁻¹ • A) = r⁻¹ • B := by
  subst hc
  have h1 : k⁻¹ + (r + k) / r * (r + k)⁻¹ - (r + k) / r * k⁻¹ = 0 := by
    field_simp
    ring
  have h2 : (r + k) / r * (r + k)⁻¹ = r⁻¹ := by
    field_simp
  have expand : k⁻¹ • A + ((r + k) / r) • ((r + k)⁻¹ • (B + A) - k⁻¹ • A)
      = (k⁻¹ + (r + k) / r * (r + k)⁻¹ - (r + k) / r * k⁻¹) • A
        + ((r + k) / r * (r + k)⁻¹) • B := by
    simp only [smul_sub, smul_add, smul_smul, add_smul, sub_smul]
    abel
  rw [expand, h1, h2, zero_smul, zero_add]

theorem centroid_sdiff_eq_add_smul_sub [DecidableEq E] {s f : Finset E} (hfs : f ⊆ s)
    (hf : f.Nonempty) (hne : f ≠ s) :
    f.centroid ℝ id + ((s.card : ℝ) / ((s \ f).card : ℝ)) • (s.centroid ℝ id - f.centroid ℝ id)
      = (s \ f).centroid ℝ id := by
  have hg : (s \ f).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => hne (Finset.Subset.antisymm hfs h)
  have hs : s.Nonempty := hf.mono hfs
  have hcard : ((s \ f).card : ℝ) + (f.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hfs
  have hsum : ∑ v ∈ s \ f, v + ∑ v ∈ f, v = ∑ v ∈ s, v := Finset.sum_sdiff hfs
  have hAf : ∑ v ∈ f, ((f.card : ℝ))⁻¹ • v = ((f.card : ℝ))⁻¹ • ∑ v ∈ f, v := Finset.smul_sum.symm
  have hAs : ∑ v ∈ s, ((s.card : ℝ))⁻¹ • v = ((s.card : ℝ))⁻¹ • ∑ v ∈ s, v := Finset.smul_sum.symm
  have hAg : ∑ v ∈ s \ f, (((s \ f).card : ℝ))⁻¹ • v
      = (((s \ f).card : ℝ))⁻¹ • ∑ v ∈ s \ f, v := Finset.smul_sum.symm
  rw [centroid_eq_sum f hf, centroid_eq_sum s hs, centroid_eq_sum (s \ f) hg, hAf, hAs, hAg,
    ← hsum]
  exact smul_add_smul_sub_smul_eq (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hf).ne')
    (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hg).ne')
    (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hs).ne') hcard

theorem exists_max_of_chain {α : Type*} {d : Finset (Finset α)}
    (hd : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) (hne : d.Nonempty) : ∃ m ∈ d, ∀ s ∈ d, s ⊆ m := by
  obtain ⟨m, hm, hmax⟩ := d.exists_max_image Finset.card hne
  refine ⟨m, hm, fun s hs => ?_⟩
  rcases hd s hs m hm with hsm | hms
  · exact hsm
  · exact (Finset.eq_of_subset_of_card_le hms (hmax s hs)).ge

theorem exists_ray_centroid_mem_convexHull [DecidableEq E] {f s τ : Finset E} (hfs : f ⊆ s)
    (hf : f.Nonempty) (hne : f ≠ s) (hsub : s \ f ⊆ τ) :
    ∃ σ : ℝ, 0 < σ ∧
      f.centroid ℝ id + σ • (s.centroid ℝ id - f.centroid ℝ id) ∈ convexHull ℝ (τ : Set E) := by
  have hg : (s \ f).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => hne (Finset.Subset.antisymm hfs h)
  have hs : s.Nonempty := hf.mono hfs
  refine ⟨(s.card : ℝ) / ((s \ f).card : ℝ), div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
    (Nat.cast_pos.mpr (Finset.card_pos.mpr hg)), ?_⟩
  rw [centroid_sdiff_eq_add_smul_sub hfs hf hne]
  exact convexHull_mono (Finset.coe_subset.mpr hsub)
    (openSimplex_subset_convexHull _ (centroid_mem_openSimplex hg))

theorem exists_ray_of_mem_image [DecidableEq E] {f τ : Finset E} {d : Finset (Finset E)}
    (hf : f.Nonempty) (hd : ∀ s ∈ d, s.Nonempty) (hfd : f ∉ d)
    (hsub : ∀ s ∈ d, ¬ f ⊆ s → s ⊆ τ) (hsub' : ∀ s ∈ d, f ⊆ s → s \ f ⊆ τ) {z : E}
    (hz : z ∈ d.image fun s => s.centroid ℝ id) :
    ∃ σ : ℝ, 0 < σ ∧
      f.centroid ℝ id + σ • (z - f.centroid ℝ id) ∈ convexHull ℝ (τ : Set E) := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
  by_cases hfs : f ⊆ s
  · exact exists_ray_centroid_mem_convexHull hfs hf (fun h => hfd (by rw [h]; exact hs))
      (hsub' s hs hfs)
  · refine ⟨1, one_pos, ?_⟩
    rw [one_smul, add_sub_cancel]
    exact convexHull_mono (Finset.coe_subset.mpr (hsub s hs hfs))
      (openSimplex_subset_convexHull _ (centroid_mem_openSimplex (hd s hs)))

theorem exists_adapted_face [DecidableEq E] {T f : Finset E} (hf : f.Nonempty)
    {d : Finset (Finset E)} (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T)
    (hchain : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) (hne : d.Nonempty)
    (htype : (∀ s ∈ d, (s ∩ (T \ f)).Nonempty) ∨ ∃ v ∈ f, ∀ s ∈ d, v ∉ s) :
    ∃ τ : Finset E, (τ.Nonempty ∧ τ ⊆ T ∧ ¬ f ⊆ τ) ∧
      ∀ z ∈ d.image fun s => s.centroid ℝ id, ∃ σ : ℝ, 0 < σ ∧
        f.centroid ℝ id + σ • (z - f.centroid ℝ id) ∈ convexHull ℝ (τ : Set E) := by
  classical
  obtain ⟨u, hu, htop⟩ := exists_max_of_chain hchain hne
  have hfd : f ∉ d := notMem_of_faceRadialFrontier_type htype
  by_cases hk : (d.filter fun s => ¬ f ⊆ s).Nonempty
  · obtain ⟨sk, hsk, hskmax⟩ := exists_max_of_chain
      (fun s hs t ht => hchain s (Finset.mem_of_mem_filter s hs) t (Finset.mem_of_mem_filter t ht))
      hk
    obtain ⟨hskd, hskf⟩ := Finset.mem_filter.mp hsk
    obtain ⟨v, hvf, hvsk⟩ := Finset.not_subset.mp hskf
    refine ⟨sk ∪ (u \ f), ⟨(hd sk hskd).1.mono Finset.subset_union_left,
      Finset.union_subset (hd sk hskd).2 (Finset.sdiff_subset.trans (hd u hu).2), ?_⟩, ?_⟩
    · intro hsub
      rcases Finset.mem_union.mp (hsub hvf) with h | h
      · exact hvsk h
      · exact (Finset.mem_sdiff.mp h).2 hvf
    · refine fun z hz => exists_ray_of_mem_image hf (fun s hs => (hd s hs).1) hfd
        (fun s hs hfs => ?_) (fun s hs _ => ?_) hz
      · exact (hskmax s (Finset.mem_filter.mpr ⟨hs, hfs⟩)).trans Finset.subset_union_left
      · exact (Finset.sdiff_subset_sdiff (htop s hs) (Finset.Subset.refl f)).trans
          Finset.subset_union_right
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hk
    have hall : ∀ s ∈ d, f ⊆ s := fun s hs => not_not.mp (hk hs)
    have hM : ∀ s ∈ d, (s ∩ (T \ f)).Nonempty := by
      rcases htype with h | ⟨v, hvf, hvd⟩
      · exact h
      · exact absurd (hall u hu hvf) (hvd u hu)
    obtain ⟨w, hw⟩ := hM u hu
    rw [Finset.mem_inter, Finset.mem_sdiff] at hw
    refine ⟨u \ f, ⟨⟨w, Finset.mem_sdiff.mpr ⟨hw.1, hw.2.2⟩⟩,
      Finset.sdiff_subset.trans (hd u hu).2, ?_⟩, ?_⟩
    · intro hsub
      obtain ⟨v, hvf⟩ := id hf
      exact (Finset.mem_sdiff.mp (hsub hvf)).2 hvf
    · refine fun z hz => exists_ray_of_mem_image hf (fun s hs => (hd s hs).1) hfd
        (fun s hs hfs => absurd (hall s hs) hfs)
        (fun s hs _ => Finset.sdiff_subset_sdiff (htop s hs) (Finset.Subset.refl f)) hz

theorem mem_convexHull_ray_and_weights {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p x : E} (hp : p ∈ convexHull ℝ (T : Set E)) (hx : x ∈ convexHull ℝ (T : Set E)) {σ : ℝ}
    (hσ : ∀ v ∈ T, 0 ≤ (1 - σ) * weights T p v + σ * weights T x v) :
    p + σ • (x - p) ∈ convexHull ℝ (T : Set E) ∧ ∀ v ∈ T,
      weights T (p + σ • (x - p)) v = (1 - σ) * weights T p v + σ * weights T x v := by
  have hsum : ∑ v ∈ T, ((1 - σ) * weights T p v + σ * weights T x v) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_weights hp, sum_weights hx,
      mul_one, mul_one]
    ring
  have hsmul : ∑ v ∈ T, ((1 - σ) * weights T p v + σ * weights T x v) • v = p + σ • (x - p) := by
    simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sum_weights_smul hp,
      sum_weights_smul hx, ← add_smul_sub_eq_combo]
  have hmem : p + σ • (x - p) ∈ convexHull ℝ (T : Set E) :=
    mem_convexHull_iff_exists_weights.mpr
      ⟨fun v => (1 - σ) * weights T p v + σ * weights T x v, hσ, hsum, hsmul⟩
  exact ⟨hmem, weights_eq hT hmem
    (w := fun v => (1 - σ) * weights T p v + σ * weights T x v) hsum hsmul⟩

theorem mem_faceRadialFrontier_space_of_frontier [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
    {y : E} (hy : y ∈ (faceNeighborhood T hT f).space)
    (hfront : (∃ v ∈ f, weights T y v = 0) ∨
      ∃ w ∈ T \ f, ∀ u ∈ T, weights T y u ≤ weights T y w) :
    y ∈ (faceRadialFrontier T hT f).space := by
  obtain ⟨hyT, v₁, hv₁f, hv₁max⟩ := (mem_faceNeighborhood_space_iff hT hfT hf).mp hy
  have hTne : T.Nonempty := ⟨v₁, hfT hv₁f⟩
  have hysp : y ∈ (barycentricSubdivision (simplexComplex T hT)).space := by
    rw [(barycentricSubdivision_isSubdivision (simplexComplex T hT)).space_eq]
    exact (simplexComplex T hT).convexHull_subset_space ⟨hTne, Finset.Subset.refl T⟩ hyT
  obtain ⟨u, hu, hyu⟩ :=
    exists_face_mem_openSimplex (barycentricSubdivision (simplexComplex T hT)) hysp
  obtain ⟨d, hflag, hne, rfl⟩ := (mem_derived_faces_iff (simplexComplex T hT)
    (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT))).mp hu
  have hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ T := fun s hs =>
    (mem_simplexComplex_faces_iff T hT).mp (hflag.mem_faces hs)
  obtain ⟨m, hm, hmin⟩ := exists_min_of_chain hflag.2 hne
  have hmem_min : ∀ z ∈ T, (∀ u ∈ T, weights T y u ≤ weights T y z) → z ∈ m := by
    intro z hz hzmax
    by_contra hzm
    obtain ⟨v₀, hv₀⟩ := (hd m hm).1
    exact absurd (hzmax v₀ ((hd m hm).2 hv₀))
      (not_le.mpr (weights_lt_of_notMem_min hT hflag hm hmin hyu z hz hzm v₀ hv₀))
  have hmeet : ∀ s ∈ d, (s ∩ f).Nonempty := fun s hs =>
    ⟨v₁, Finset.mem_inter.mpr ⟨hmin s hs (hmem_min v₁ (hfT hv₁f) hv₁max), hv₁f⟩⟩
  refine (faceRadialFrontier T hT f).mem_space_iff.mpr
    ⟨d.image fun s => s.centroid ℝ id, ⟨d, hd, hflag.2, hne, hmeet, ?_, rfl⟩,
      openSimplex_subset_convexHull _ hyu⟩
  rcases hfront with ⟨v, hvf, hv0⟩ | ⟨w, hw, hwmax⟩
  · refine Or.inr ⟨v, hvf, fun s hs hvs => ?_⟩
    obtain ⟨μ, hμ₀, hμ₁, hμy⟩ := exists_weights_of_mem_openSimplex_image hT hflag hyu
    have hpos : 0 < weights T y v := by
      rw [← hμy, weights_sum_centroid hT hd (fun t ht => (hμ₀ t ht).le) hμ₁ (hfT hvf)]
      refine Finset.sum_pos' (fun t ht => ?_) ⟨s, hs, ?_⟩
      · split_ifs
        · exact mul_nonneg (hμ₀ t ht).le (inv_nonneg.mpr (Nat.cast_nonneg _))
        · exact le_rfl
      · rw [ite_eq_left hvs]
        exact mul_pos (hμ₀ s hs) (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hd s hs).1)))
    exact absurd hv0 hpos.ne'
  · rw [Finset.mem_sdiff] at hw
    exact Or.inl fun s hs => ⟨w, Finset.mem_inter.mpr
      ⟨hmin s hs (hmem_min w hw.1 hwmax), Finset.mem_sdiff.mpr hw⟩⟩

theorem exists_ray_mem_faceRadialFrontier_space [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
    (hfne : f ≠ T) {x : E} (hx : x ∈ convexHull ℝ (T : Set E)) (hxp : x ≠ f.centroid ℝ id) :
    ∃ σ : ℝ, 0 < σ ∧
      f.centroid ℝ id + σ • (x - f.centroid ℝ id) ∈ (faceRadialFrontier T hT f).space ∧
      (x ∈ (faceNeighborhood T hT f).space → 1 ≤ σ) := by
  have hk : (0 : ℝ) < (f.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hf)
  have hkinv : (0 : ℝ) < (f.card : ℝ)⁻¹ := inv_pos.mpr hk
  have hp : f.centroid ℝ id ∈ convexHull ℝ (T : Set E) := centroid_mem_convexHull_of_subset hfT hf
  have hg : (T \ f).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => hfne (Finset.Subset.antisymm hfT h)
  have hone : ∑ _v ∈ f, ((f.card : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hk.ne']
  obtain ⟨vc, hvc, hcmin⟩ := Finset.exists_min_image f (weights T x) hf
  obtain ⟨va, hva, hamax⟩ := Finset.exists_max_image f (weights T x) hf
  obtain ⟨wb, hwb, hbmax⟩ := Finset.exists_max_image (T \ f) (weights T x) hg
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min (weights T x vc - (f.card : ℝ)⁻¹)
      (weights T x va - weights T x wb - (f.card : ℝ)⁻¹) := ⟨_, rfl⟩
  have hbnd₁ : β ≤ weights T x vc - (f.card : ℝ)⁻¹ := by
    rw [hβdef]
    exact min_le_left _ _
  have hbnd₂ : β ≤ weights T x va - weights T x wb - (f.card : ℝ)⁻¹ := by
    rw [hβdef]
    exact min_le_right _ _
  have hβneg : β < 0 := by
    by_contra hcon'
    have hcon : 0 ≤ β := not_lt.mp hcon'
    have hall : ∀ v ∈ f, (f.card : ℝ)⁻¹ ≤ weights T x v := fun v hv => by
      have := hcmin v hv
      linarith
    have hsumf : (1 : ℝ) ≤ ∑ v ∈ f, weights T x v := by
      rw [← hone]
      exact Finset.sum_le_sum hall
    have hsumT : ∑ v ∈ T \ f, weights T x v + ∑ v ∈ f, weights T x v = 1 := by
      rw [Finset.sum_sdiff hfT]
      exact sum_weights hx
    have hnn : ∀ w ∈ T \ f, 0 ≤ weights T x w := fun w hw =>
      weights_nonneg hx (Finset.mem_sdiff.mp hw).1
    have hgsum : ∑ v ∈ T \ f, weights T x v = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    have hfsum : ∑ v ∈ f, weights T x v = 1 := by linarith
    have hzero : ∑ v ∈ f, (weights T x v - (f.card : ℝ)⁻¹) = 0 := by
      rw [Finset.sum_sub_distrib, hfsum, hone, sub_self]
    have hg0 : ∀ w ∈ T \ f, weights T x w = 0 :=
      fun w hw => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hgsum w hw
    have hf0 : ∀ v ∈ f, weights T x v = (f.card : ℝ)⁻¹ := fun v hv => by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun u hu => sub_nonneg.mpr (hall u hu))).mp hzero v hv
      linarith
    refine hxp (((sum_weights_smul hx).symm.trans (Finset.sum_congr rfl fun v hv => ?_)).trans
      (sum_weights_smul hp))
    by_cases hvf : v ∈ f
    · rw [hf0 v hvf, weights_centroid_of_mem hT hfT hf hvf]
    · rw [hg0 v (Finset.mem_sdiff.mpr ⟨hv, hvf⟩), weights_centroid_of_notMem hT hfT hf hv hvf]
  obtain ⟨σ, hσ0, hkey⟩ : ∃ σ : ℝ, 0 < σ ∧ (f.card : ℝ)⁻¹ + σ * β = 0 := by
    have hβ0 : β ≠ 0 := ne_of_lt hβneg
    refine ⟨(f.card : ℝ)⁻¹ / (-β), div_pos hkinv (neg_pos.mpr hβneg), ?_⟩
    field_simp
    ring
  have hW : ∀ v ∈ T, 0 ≤ (1 - σ) * weights T (f.centroid ℝ id) v + σ * weights T x v := by
    intro v hv
    by_cases hvf : v ∈ f
    · rw [weights_centroid_of_mem hT hfT hf hvf]
      have h2 : β ≤ weights T x v - (f.card : ℝ)⁻¹ := by
        have := hcmin v hvf
        linarith
      linarith [mul_le_mul_of_nonneg_left h2 hσ0.le]
    · rw [weights_centroid_of_notMem hT hfT hf hv hvf]
      linarith [mul_nonneg hσ0.le (weights_nonneg hx hv)]
  obtain ⟨hmem, hwts⟩ := mem_convexHull_ray_and_weights hT hp hx hW
  have hD : f.centroid ℝ id + σ • (x - f.centroid ℝ id) ∈ (faceNeighborhood T hT f).space := by
    refine (mem_faceNeighborhood_space_iff hT hfT hf).mpr ⟨hmem, va, hva, fun w hw => ?_⟩
    rw [hwts w hw, hwts va (hfT hva), weights_centroid_of_mem hT hfT hf hva]
    by_cases hwf : w ∈ f
    · rw [weights_centroid_of_mem hT hfT hf hwf]
      linarith [mul_le_mul_of_nonneg_left (hamax w hwf) hσ0.le]
    · rw [weights_centroid_of_notMem hT hfT hf hw hwf]
      linarith [mul_le_mul_of_nonneg_left (hbmax w (Finset.mem_sdiff.mpr ⟨hw, hwf⟩)) hσ0.le,
        mul_le_mul_of_nonneg_left hbnd₂ hσ0.le]
  have hfront : (∃ v ∈ f, weights T (f.centroid ℝ id + σ • (x - f.centroid ℝ id)) v = 0) ∨
      ∃ w ∈ T \ f, ∀ u ∈ T, weights T (f.centroid ℝ id + σ • (x - f.centroid ℝ id)) u
        ≤ weights T (f.centroid ℝ id + σ • (x - f.centroid ℝ id)) w := by
    rcases min_choice (weights T x vc - (f.card : ℝ)⁻¹)
      (weights T x va - weights T x wb - (f.card : ℝ)⁻¹) with h | h
    · refine Or.inl ⟨vc, hvc, ?_⟩
      have hβ' : σ * β = σ * (weights T x vc - (f.card : ℝ)⁻¹) := by rw [hβdef, h]
      rw [hwts vc (hfT hvc), weights_centroid_of_mem hT hfT hf hvc]
      linarith
    · refine Or.inr ⟨wb, hwb, fun u hu => ?_⟩
      have hβ' : σ * β = σ * (weights T x va - weights T x wb - (f.card : ℝ)⁻¹) := by
        rw [hβdef, h]
      rw [hwts u hu, hwts wb (Finset.mem_sdiff.mp hwb).1,
        weights_centroid_of_notMem hT hfT hf (Finset.mem_sdiff.mp hwb).1
          (Finset.mem_sdiff.mp hwb).2]
      by_cases huf : u ∈ f
      · rw [weights_centroid_of_mem hT hfT hf huf]
        linarith [mul_le_mul_of_nonneg_left (hamax u huf) hσ0.le]
      · rw [weights_centroid_of_notMem hT hfT hf hu huf]
        linarith [mul_le_mul_of_nonneg_left (hbmax u (Finset.mem_sdiff.mpr ⟨hu, huf⟩)) hσ0.le]
  refine ⟨σ, hσ0, mem_faceRadialFrontier_space_of_frontier hT hfT hf hD hfront, fun hxD => ?_⟩
  by_contra hcon'
  have hcon : σ < 1 := not_le.mp hcon'
  obtain ⟨-, v₁, hv₁f, hv₁max⟩ := (mem_faceNeighborhood_space_iff hT hfT hf).mp hxD
  have hβge : -(f.card : ℝ)⁻¹ ≤ β := by
    rw [hβdef, le_min_iff]
    refine ⟨by linarith [weights_nonneg hx (hfT hvc)], ?_⟩
    have h1 := hamax v₁ hv₁f
    have h2 := hv₁max wb (Finset.mem_sdiff.mp hwb).1
    linarith
  linarith [mul_lt_mul_of_pos_right hcon (neg_pos.mpr hβneg)]

theorem exists_ray_mem_faceRadialFrontier_space_of_mem_simplexAvoiding [DecidableEq E]
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T)
    (hf : f.Nonempty) (hfne : f ≠ T) {x : E} (hx : x ∈ (simplexAvoiding T hT {f}).space) :
    ∃ σ : ℝ, 0 < σ ∧
      f.centroid ℝ id + σ • (x - f.centroid ℝ id) ∈ (faceRadialFrontier T hT f).space := by
  have hxT : x ∈ convexHull ℝ (T : Set E) := simplexAvoiding_space_subset T hT {f} hx
  obtain ⟨v, hvf, hv0⟩ := exists_weights_eq_zero_of_mem_simplexAvoiding_space hT
    (Finset.mem_singleton_self f) hfT hx
  have hne : x ≠ f.centroid ℝ id := by
    intro h
    rw [h, weights_centroid_of_mem hT hfT hf hvf] at hv0
    exact (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hf) : (0 : ℝ) < f.card)).ne' hv0
  obtain ⟨σ, hσ0, hmem, -⟩ := exists_ray_mem_faceRadialFrontier_space hT hfT hf hfne hxT hne
  exact ⟨σ, hσ0, hmem⟩

theorem faceNeighborhood_space_eq_coneComplex [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
    (hfne : f ≠ T) : (faceNeighborhood T hT f).space
      = (coneComplex (isConeBase_faceRadialFrontier hT hfT hf)).space := by
  have hk : (0 : ℝ) < (f.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hf)
  have hp : f.centroid ℝ id ∈ convexHull ℝ (T : Set E) := centroid_mem_convexHull_of_subset hfT hf
  ext y
  rw [mem_coneComplex_space_iff]
  constructor
  · intro hy
    by_cases hyp : y = f.centroid ℝ id
    · exact Or.inl hyp
    · obtain ⟨hyT, -⟩ := (mem_faceNeighborhood_space_iff hT hfT hf).mp hy
      obtain ⟨σ, hσ0, hmem, hσ1⟩ := exists_ray_mem_faceRadialFrontier_space hT hfT hf hfne hyT hyp
      refine Or.inr ⟨f.centroid ℝ id + σ • (y - f.centroid ℝ id), hmem, σ⁻¹, inv_pos.mpr hσ0,
        inv_le_one_of_one_le₀ (hσ1 hy), ?_⟩
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hσ0.ne', one_smul, add_sub_cancel]
  · rintro (rfl | ⟨z, hz, s, hs0, hs1, rfl⟩)
    · refine (mem_faceNeighborhood_space_iff hT hfT hf).mpr ⟨hp, ?_⟩
      obtain ⟨v, hvf⟩ := id hf
      refine ⟨v, hvf, fun w hw => ?_⟩
      by_cases hwf : w ∈ f
      · exact le_of_eq ((weights_centroid_of_mem hT hfT hf hwf).trans
          (weights_centroid_of_mem hT hfT hf hvf).symm)
      · rw [weights_centroid_of_notMem hT hfT hf hw hwf, weights_centroid_of_mem hT hfT hf hvf]
        exact (inv_pos.mpr hk).le
    · obtain ⟨hzT, v₁, hv₁f, hv₁max⟩ := (mem_faceNeighborhood_space_iff hT hfT hf).mp
        (faceRadialFrontier_space_subset T hT f hz)
      have hcombo : ∀ v ∈ T, weights T (f.centroid ℝ id + s • (z - f.centroid ℝ id)) v
          = (1 - s) * weights T (f.centroid ℝ id) v + s * weights T z v := by
        intro v hv
        rw [add_smul_sub_eq_combo]
        exact weights_combo hT hp hzT (by linarith) hs0.le (by ring) v hv
      have hmemT : f.centroid ℝ id + s • (z - f.centroid ℝ id) ∈ convexHull ℝ (T : Set E) := by
        rw [add_smul_sub_eq_combo]
        exact (convex_convexHull ℝ (T : Set E)) hp hzT (by linarith) hs0.le (by ring)
      refine (mem_faceNeighborhood_space_iff hT hfT hf).mpr ⟨hmemT, v₁, hv₁f, fun w hw => ?_⟩
      rw [hcombo w hw, hcombo v₁ (hfT hv₁f), weights_centroid_of_mem hT hfT hf hv₁f]
      have h1 := hv₁max w hw
      by_cases hwf : w ∈ f
      · rw [weights_centroid_of_mem hT hfT hf hwf]
        linarith [mul_le_mul_of_nonneg_left h1 hs0.le]
      · rw [weights_centroid_of_notMem hT hfT hf hw hwf]
        linarith [mul_le_mul_of_nonneg_left h1 hs0.le,
          mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) (inv_pos.mpr hk).le]

theorem isPLBall_faceNeighborhood_space [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2)
    {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty) (hfT' : f ≠ T) :
    IsPLBall (n + 1) (faceNeighborhood T hT f).space := by
  have hcone := isConeBase_faceRadialFrontier hT hfT hf
  have : Finite (faceRadialFrontier T hT f).faces :=
    (faceRadialFrontier_faces_finite T hT f).to_subtype
  have hadapt : ∀ u ∈ (faceRadialFrontier T hT f).faces, ∃ τ ∈ (simplexAvoiding T hT {f}).faces,
      ∀ w ∈ u, ∃ s : ℝ, 0 < s ∧
        f.centroid ℝ id + s • (w - f.centroid ℝ id) ∈ convexHull ℝ (τ : Set E) := by
    rintro u ⟨d, hd, hchain, hne, hmeet, htype, rfl⟩
    obtain ⟨τ, ⟨hτne, hτT, hτf⟩, hray⟩ := exists_adapted_face hf hd hchain hne htype
    refine ⟨τ, ⟨hτne, hτT, fun σ hσ => ?_⟩, hray⟩
    rw [Finset.mem_singleton.mp hσ]
    exact hτf
  have hsurj : ∀ x ∈ (simplexAvoiding T hT {f}).space, ∃ s : ℝ, 0 < s ∧
      f.centroid ℝ id + s • (x - f.centroid ℝ id) ∈ (faceRadialFrontier T hT f).space :=
    fun x hx => exists_ray_mem_faceRadialFrontier_space_of_mem_simplexAvoiding hT hfT hf hfT' hx
  obtain ⟨φ, hφ⟩ := exists_isPLHomeomorphOn_of_radial (f.centroid ℝ id)
    (simplexAvoiding T hT {f}) (faceRadialFrontier T hT f)
    (isRadiallyInjective_simplexAvoiding hT (Finset.mem_singleton_self f) hfT
      (centroid_mem_openSimplex hf)) hcone hadapt hsurj
  have hball : IsPLBall n (simplexAvoiding T hT {f}).space :=
    isPLBall_simplexAvoiding_singleton hT hcard hfT hf hfT'
  rw [faceNeighborhood_space_eq_coneComplex hT hfT hf hfT']
  exact hcone.isPLBall_of_isPLBall (hball.of_isPLHomeomorphOn hφ.symm)

end DifferentialGeometry.Topology.PiecewiseLinear
