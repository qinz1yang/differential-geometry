import DifferentialGeometry.Topology.SimplicialComplex.Stellar.HyperplaneRestriction
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.FineSubdivision

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem centroid_injective_on_faces (K : SimplicialComplex ℝ E) :
    InjOn (fun s : Finset E => s.centroid ℝ id) K.faces := by
  classical
  intro s hs t ht heq
  by_contra hne
  have hCs : isFaceChain ({s} : Finset (Finset E)) := by
    simpa [isFaceChain] using K.nonempty_of_mem_faces hs
  have hCt : isFaceChain ({t} : Finset (Finset E)) := by
    simpa [isFaceChain] using K.nonempty_of_mem_faces ht
  have h := hCs.convexHull_chainCentroids_inter_of_complex K hCt
    (Finset.singleton_nonempty s) (Finset.singleton_nonempty t)
    (by simpa using hs) (by simpa using ht)
  have hm : s.centroid ℝ id ∈ convexHull ℝ (chainCentroids id ({s} : Finset (Finset E)) : Set E) ∩
      convexHull ℝ (chainCentroids id ({t} : Finset (Finset E)) : Set E) := by
    constructor
    · exact subset_convexHull ℝ _ (mem_chainCentroids.mpr ⟨s, by simp, rfl⟩)
    · exact subset_convexHull ℝ _ (mem_chainCentroids.mpr ⟨t, by simp, heq.symm⟩)
  rw [h] at hm
  have hempty : ({s} : Finset (Finset E)) ∩ {t} = ∅ := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, hst⟩
    exact hne hst
  simp [hempty, chainCentroids] at hm

def skeleton (K : SimplicialComplex ℝ E) (r : ℕ) : SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ s.card ≤ r + 1}
  isRelLowerSet_faces := fun _ hs => ⟨K.nonempty_of_mem_faces hs.1,
    fun _ hts ht => ⟨K.down_closed hs.1 hts ht, (Finset.card_le_card hts).trans hs.2⟩⟩
  indep := fun hs => K.indep hs.1
  inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1

def lowCentroids (K : SimplicialComplex ℝ E) (r : ℕ) : Set E :=
  {x | ∃ s ∈ K.faces, s.card ≤ r + 1 ∧ s.centroid ℝ id = x}

omit [DecidableEq E] in
theorem centroid_mem_lowCentroids_iff (K : SimplicialComplex ℝ E) (r : ℕ)
    {s : Finset E} (hs : s ∈ K.faces) :
    s.centroid ℝ id ∈ lowCentroids K r ↔ s.card ≤ r + 1 := by
  classical
  constructor
  · rintro ⟨t, ht, hcard, heq⟩
    exact centroid_injective_on_faces K ht hs heq ▸ hcard
  · intro hcard
    exact ⟨s, hs, hcard, rfl⟩

theorem vertexRestriction_lowCentroids_space (K : SimplicialComplex ℝ E) (r : ℕ) :
    (vertexRestriction (barycentricSubdivision K) (lowCentroids K r)).space =
      (skeleton K r).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨⟨C, hCne, hC, hCK, rfl⟩, hlow⟩, hxs⟩ :=
      SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
    have hVsmall := (centroid_mem_lowCentroids_iff K r (hCK V hVC)).mp
      (hlow (mem_chainCentroids.mpr ⟨V, hVC, rfl⟩))
    exact (skeleton K r).convexHull_subset_space ⟨hCK V hVC, hVsmall⟩
      (hC.convexHull_chainCentroids_subset V hCV hxs)
  · intro x hx
    rw [← barycentricSubdivision_space (skeleton K r)] at hx
    obtain ⟨s, ⟨C, hCne, hC, hCK, rfl⟩, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact (vertexRestriction (barycentricSubdivision K) (lowCentroids K r)).convexHull_subset_space
      ⟨⟨C, hCne, hC, fun t ht => (hCK t ht).1, rfl⟩, by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := mem_chainCentroids.mp hv
        exact ⟨t, (hCK t ht).1, (hCK t ht).2, rfl⟩⟩ hxs

theorem isFaceChain.card_le_interval {ι : Type*}
    {C : Finset (Finset ι)} (hC : isFaceChain C) {a b : ℕ}
    (hcard : ∀ s ∈ C, a ≤ s.card ∧ s.card ≤ b) : C.card ≤ b + 1 - a := by
  classical
  have hmap : MapsTo Finset.card (C : Set (Finset ι)) (Finset.Icc a b : Finset ℕ) :=
    fun s hs => Finset.mem_Icc.mpr (hcard s hs)
  have hinj : (C : Set (Finset ι)).InjOn Finset.card := by
    intro s hs t ht heq
    rcases hC.2 s hs t ht with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst heq.ge
    · exact (Finset.eq_of_subset_of_card_le hts heq.le).symm
  simpa using Finset.card_le_card_of_injOn Finset.card hmap hinj

theorem vertexRestriction_dual_face_card_le (K : SimplicialComplex ℝ E) (r : ℕ)
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∀ s ∈ (vertexRestriction (barycentricSubdivision K) (lowCentroids K r)ᶜ).faces,
      s.card ≤ n - r := by
  classical
  rintro s ⟨⟨C, hCne, hC, hCK, rfl⟩, hhigh⟩
  have hcard : ∀ t ∈ C, r + 2 ≤ t.card ∧ t.card ≤ n + 1 := by
    intro t ht
    have hn := hhigh (mem_chainCentroids.mpr ⟨t, ht, rfl⟩)
    have hgt : ¬ t.card ≤ r + 1 := fun h => hn
      ((centroid_mem_lowCentroids_iff K r (hCK t ht)).mpr h)
    exact ⟨by omega, hd t (hCK t ht)⟩
  have hchain : C.card ≤ n - r := by
    have h := hC.card_le_interval hcard
    omega
  have himage : (chainCentroids (id : E → E) C).card ≤ C.card := by
    unfold chainCentroids
    exact @Finset.card_image_le (Finset E) E C (fun t => t.centroid ℝ id) (Classical.decEq E)
  exact himage.trans hchain

theorem vertexRestriction_low_face_card_le (K : SimplicialComplex ℝ E) (r : ℕ) :
    ∀ s ∈ (vertexRestriction (barycentricSubdivision K) (lowCentroids K r)).faces,
      s.card ≤ r + 1 := by
  classical
  rintro s ⟨⟨C, hCne, hC, hCK, rfl⟩, hlow⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have hVsmall := (centroid_mem_lowCentroids_iff K r (hCK V hVC)).mp
    (hlow (mem_chainCentroids.mpr ⟨V, hVC, rfl⟩))
  have himage : (chainCentroids (id : E → E) C).card ≤ C.card := by
    unfold chainCentroids
    exact @Finset.card_image_le (Finset E) E C (fun t => t.centroid ℝ id) (Classical.decEq E)
  exact himage.trans ((hC.card_le_parent hCV).trans hVsmall)

end DifferentialGeometry.Topology.Engulfing
