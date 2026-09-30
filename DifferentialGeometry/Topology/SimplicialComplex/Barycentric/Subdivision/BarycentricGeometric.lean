import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricRestriction

namespace DifferentialGeometry.Topology.Engulfing

open Set

variable {E : Type*} [DecidableEq E]

def liftFace (V s : Finset E) : Finset V := s.subtype (· ∈ V)

@[simp]
theorem mem_liftFace (V s : Finset E) (x : V) : x ∈ liftFace V s ↔ x.1 ∈ s :=
  Finset.mem_subtype

theorem liftFace_map (V : Finset E) {s : Finset E} (hs : s ⊆ V) :
    (liftFace V s).map (Function.Embedding.subtype (· ∈ V)) = s :=
  Finset.subtype_map_of_mem hs

theorem liftFace_injective_on (V : Finset E) {s t : Finset E} (hs : s ⊆ V) (ht : t ⊆ V)
    (heq : liftFace V s = liftFace V t) : s = t := by
  have h := congrArg (fun a : Finset V => a.map (Function.Embedding.subtype (· ∈ V))) heq
  simpa only [liftFace_map V hs, liftFace_map V ht] using h

theorem liftFace_mono (V : Finset E) {s t : Finset E} (hst : s ⊆ t) :
    liftFace V s ⊆ liftFace V t := by
  intro x hx
  exact (mem_liftFace V t x).mpr (hst ((mem_liftFace V s x).mp hx))

theorem liftFace_subset_iff (V : Finset E) {s t : Finset E} (hs : s ⊆ V) :
    liftFace V s ⊆ liftFace V t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    exact (mem_liftFace V t ⟨x, hs hx⟩).mp (h ((mem_liftFace V s _).mpr hx))
  · exact liftFace_mono V

variable [AddCommGroup E] [Module ℝ E]

theorem centroid_liftFace (V : Finset E) {s : Finset E} (hs : s ⊆ V) :
    (liftFace V s).centroid ℝ (Subtype.val : V → E) = s.centroid ℝ id := by
  have h := (liftFace V s).centroid_map ℝ (Function.Embedding.subtype (· ∈ V)) id
  simpa only [liftFace_map V hs, Function.comp_def, Function.Embedding.coe_subtype,
    id_eq] using h.symm

def liftChain (V : Finset E) (C : Finset (Finset E)) : Finset (Finset V) :=
  C.image (liftFace V)

omit [AddCommGroup E] [Module ℝ E] in
theorem isFaceChain.liftChain {C : Finset (Finset E)} (hC : isFaceChain C)
    (V : Finset E) (hV : ∀ s ∈ C, s ⊆ V) : isFaceChain (liftChain V C) := by
  constructor
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨x, hx⟩ := hC.1 t ht
    exact ⟨⟨x, hV t ht hx⟩, (mem_liftFace _ _ _).mpr hx⟩
  · intro s hs t ht
    obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    exact (hC.2 s₀ hs₀ t₀ ht₀).imp (liftFace_mono V) (liftFace_mono V)

theorem chainCentroids_liftChain (V : Finset E) (C : Finset (Finset E))
    (hV : ∀ s ∈ C, s ⊆ V) :
    chainCentroids (Subtype.val : V → E) (liftChain V C) = chainCentroids id C := by
  classical
  ext x
  simp only [mem_chainCentroids]
  constructor
  · rintro ⟨s, hs, hcentroid⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨t, ht, (centroid_liftFace V (hV t ht)).symm.trans hcentroid⟩
  · rintro ⟨s, hs, hcentroid⟩
    exact ⟨liftFace V s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      (centroid_liftFace V (hV s hs)).trans hcentroid⟩

omit [AddCommGroup E] [Module ℝ E] in
theorem liftChain_inter (V : Finset E) (C D : Finset (Finset E))
    (hC : ∀ s ∈ C, s ⊆ V) (hD : ∀ s ∈ D, s ⊆ V) :
    liftChain V (C ∩ D) = liftChain V C ∩ liftChain V D := by
  ext s
  simp only [liftChain, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht.1, rfl⟩, ⟨t, ht.2, rfl⟩⟩
  · rintro ⟨⟨t, ht, hts⟩, ⟨u, hu, hus⟩⟩
    have htu : t = u := liftFace_injective_on V (hC t ht) (hD u hu) (hts.trans hus.symm)
    exact ⟨t, ⟨ht, htu ▸ hu⟩, hts⟩

omit [AddCommGroup E] [Module ℝ E] in
theorem liftChain_filter_subset (V : Finset E) (C : Finset (Finset E))
    (hC : ∀ s ∈ C, s ⊆ V) (T : Finset E) :
    (liftChain V C).filter (fun s => s ⊆ liftFace V T) =
      liftChain V (C.filter (fun s => s ⊆ T)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨hs, hsub⟩ := Finset.mem_filter.mp hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨t,
      Finset.mem_filter.mpr ⟨ht, (liftFace_subset_iff V (hC t ht)).mp hsub⟩, rfl⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨ht, hsub⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩, liftFace_mono V hsub⟩

omit [DecidableEq E] in
theorem isFaceChain.affineIndependent_chainCentroids_of_subset {C : Finset (Finset E)}
    (hC : isFaceChain C) (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (hCV : ∀ s ∈ C, s ⊆ V) : AffineIndependent ℝ ((↑) : chainCentroids id C → E) := by
  classical
  have h := (hC.liftChain V hCV).affineIndependent_chainCentroids hV
  rwa [chainCentroids_liftChain V C hCV] at h

theorem isFaceChain.convexHull_chainCentroids_inter_of_subset {C D : Finset (Finset E)}
    (hC : isFaceChain C) (hD : isFaceChain D) (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (hCV : ∀ s ∈ C, s ⊆ V) (hDV : ∀ s ∈ D, s ⊆ V) :
    convexHull ℝ (chainCentroids id C : Set E) ∩ convexHull ℝ (chainCentroids id D : Set E) =
      convexHull ℝ (chainCentroids id (C ∩ D) : Set E) := by
  have h := (hC.liftChain V hCV).convexHull_chainCentroids_inter hV (hD.liftChain V hDV)
  rw [chainCentroids_liftChain V C hCV, chainCentroids_liftChain V D hDV,
    ← liftChain_inter V C D hCV hDV,
    chainCentroids_liftChain V (C ∩ D) (fun s hs => hCV s (Finset.mem_inter.mp hs).1)] at h
  exact h

theorem isFaceChain.convexHull_chainCentroids_inter_affineSpan_of_subset
    {C : Finset (Finset E)} (hC : isFaceChain C) (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) (hCV : ∀ s ∈ C, s ⊆ V)
    (T : Finset E) (hTV : T ⊆ V) :
    convexHull ℝ (chainCentroids id C : Set E) ∩ (affineSpan ℝ (T : Set E) : Set E) =
      convexHull ℝ (chainCentroids id (C.filter (fun s => s ⊆ T)) : Set E) := by
  have h := (hC.liftChain V hCV).convexHull_chainCentroids_inter_affineSpan hV (liftFace V T)
  have himage : (Subtype.val : V → E) '' (liftFace V T : Set V) = (T : Set E) := by
    have heq := congrArg (fun s : Finset E => (s : Set E)) (liftFace_map V hTV)
    simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using heq
  rw [chainCentroids_liftChain V C hCV, himage, liftChain_filter_subset V C hCV T,
    chainCentroids_liftChain V (C.filter (fun s => s ⊆ T))
      (fun s hs => hCV s (Finset.mem_filter.mp hs).1)] at h
  exact h

end DifferentialGeometry.Topology.Engulfing
