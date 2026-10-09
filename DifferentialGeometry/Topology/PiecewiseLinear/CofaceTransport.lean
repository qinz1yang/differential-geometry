/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CofaceSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem affineMap_mul_neg_of_distinct_cofaces_of_affineOn_faces [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) {f : E → F}
    (hAff : ∀ t ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (t : Set E)))
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ F)
    {a b : E} (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (haK : insert a s ∈ K.faces) (hbK : insert b s ∈ K.faces)
    (ℓ : F →ᵃ[ℝ] ℝ) (hℓ : ℓ.linear ≠ 0) (hzero : EqOn (ℓ ∘ f) (fun _ => 0) (s : Set E)) :
    ℓ (f a) * ℓ (f b) < 0 := by
  have hsm := simplicialMap_eq_of_forall_affineOn K f hAff
  have hind : ∀ t ∈ K.faces, AffineIndependent ℝ ((↑) : {u // u ∈ t.image f} → F) := by
    intro t ht
    obtain ⟨A, hA⟩ := hAff t ht
    have himg : t.image f = t.image A :=
      Finset.image_congr fun v hv => hA (subset_convexHull ℝ _ hv)
    rw [himg]
    refine affineIndependent_image_of_injOn_convexHull A (K.indep ht) ?_
    intro x hx y hy hxy
    exact hinj (K.convexHull_subset_space ht hx) (K.convexHull_subset_space ht hy)
      (by rw [hA hx, hA hy, hxy])
  have hsmInj : InjOn (simplicialMap K f) K.space := by
    intro x hx y hy hxy
    exact hinj hx hy (by rwa [hsm hx, hsm hy] at hxy)
  let L := simplicialImage K f hind hsmInj
  have hsL : s.image f ∈ L.faces := ⟨s, hs, rfl⟩
  have hsSpace : (s : Set E) ⊆ K.space :=
    (subset_convexHull ℝ _).trans (K.convexHull_subset_space hs)
  have haSpace : a ∈ K.space :=
    K.convexHull_subset_space haK (subset_convexHull ℝ _ (Finset.mem_insert_self a s))
  have hbSpace : b ∈ K.space :=
    K.convexHull_subset_space hbK (subset_convexHull ℝ _ (Finset.mem_insert_self b s))
  have haImage : f a ∉ s.image f := by
    rintro h
    obtain ⟨v, hv, hfa⟩ := Finset.mem_image.mp h
    exact ha ((hinj (hsSpace hv) haSpace hfa) ▸ hv)
  have hbImage : f b ∉ s.image f := by
    rintro h
    obtain ⟨v, hv, hfb⟩ := Finset.mem_image.mp h
    exact hb ((hinj (hsSpace hv) hbSpace hfb) ▸ hv)
  have habImage : f a ≠ f b := fun h => hab (hinj haSpace hbSpace h)
  have haL : insert (f a) (s.image f) ∈ L.faces :=
    ⟨insert a s, haK, by rw [Finset.image_insert]⟩
  have hbL : insert (f b) (s.image f) ∈ L.faces :=
    ⟨insert b s, hbK, by rw [Finset.image_insert]⟩
  have hc : (s.image f).card = Module.finrank ℝ F :=
    (Finset.card_image_of_injOn (hinj.mono hsSpace)).trans hcard
  apply affineMap_mul_neg_of_distinct_cofaces_of_card_eq_finrank L hsL hc
    haImage hbImage habImage haL hbL ℓ hℓ
  rintro y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  exact hzero hv

universe u

open Classical in
theorem PLPieceIn.affineMap_mul_neg_of_distinct_cofaces_in_chart
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {P : Set X} (T : PLPieceIn E n X P)
    (K : Geometry.SimplicialComplex ℝ E) (hspace : K.space ⊆ T.complex.space)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hchart : MapsTo T.map K.space e.source)
    (hAff : ∀ t ∈ K.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn (e ∘ T.map) A (convexHull ℝ (t : Set E)))
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = n)
    {a b : E} (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (haK : insert a s ∈ K.faces) (hbK : insert b s ∈ K.faces)
    (ℓ : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ) (hℓ : ℓ.linear ≠ 0)
    (hzero : EqOn (ℓ ∘ e ∘ T.map) (fun _ => 0) (s : Set E)) :
    ℓ (e (T.map a)) * ℓ (e (T.map b)) < 0 := by
  exact affineMap_mul_neg_of_distinct_cofaces_of_affineOn_faces K hAff
    (e.injOn.comp (T.bijOn.injOn.mono hspace) hchart) hs
    (hcard.trans finrank_euclideanSpace_fin.symm) ha hb hab haK hbK ℓ hℓ hzero

end DifferentialGeometry.Topology.PiecewiseLinear
