import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import DifferentialGeometry.Topology.PiecewiseLinear.FaceNeighborhoodBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : Finset E}
  (hT : AffineIndependent ℝ ((↑) : T → E))

include hT in
theorem weights_vertex {u : E} (hu : u ∈ T) : weights T u u = 1 := by
  classical
  have h := weights_eq hT (subset_convexHull ℝ _ (Finset.mem_coe.mpr hu))
    (w := fun x => if x = u then (1 : ℝ) else 0) (by rw [Finset.sum_ite_eq' T u]; simp [hu])
    (by simp only [ite_smul, one_smul, zero_smul]; rw [Finset.sum_ite_eq' T u]; simp [hu]) u hu
  rw [h, if_pos rfl]

variable [FiniteDimensional ℝ E] [DecidableEq E] {f : Finset E} (hfT : f ⊆ T) (hf : f.Nonempty)
  (hfne : f ≠ T)

include hT hfT hf hfne

theorem exists_isPLHomeomorphOn_faceRadialFrontier :
    ∃ φ : E → E, IsPLHomeomorphOn φ (faceRadialFrontier T hT f).space
      (simplexAvoiding T hT {f}).space := by
  have hfinR := (faceRadialFrontier_faces_finite T hT f).to_subtype
  refine exists_isPLHomeomorphOn_of_radial (f.centroid ℝ id) (simplexAvoiding T hT {f})
    (faceRadialFrontier T hT f)
    (isRadiallyInjective_simplexAvoiding hT (Finset.mem_singleton_self f) hfT
      (centroid_mem_openSimplex hf))
    (isConeBase_faceRadialFrontier hT hfT hf) ?_ ?_
  · rintro u ⟨d, hd, hchain, hne, -, htype, rfl⟩
    obtain ⟨τ, ⟨hτne, hτT, hfτ⟩, hτ⟩ := exists_adapted_face hf hd hchain hne htype
    refine ⟨τ, ⟨hτne, hτT, ?_⟩, hτ⟩
    intro σ hσ
    rw [Finset.mem_singleton] at hσ
    subst hσ
    exact hfτ
  · intro x hx
    exact exists_ray_mem_faceRadialFrontier_space_of_mem_simplexAvoiding hT hfT hf hfne hx

omit [FiniteDimensional ℝ E] hfne in
theorem centroid_notMem_erase {v : E} (hv : v ∈ f) : f.centroid ℝ id ∉ T.erase v := by
  intro hmem
  have hpT : f.centroid ℝ id ∈ T := Finset.mem_of_mem_erase hmem
  have h1 : weights T (f.centroid ℝ id) (f.centroid ℝ id) = 1 := weights_vertex hT hpT
  by_cases hpf : f.centroid ℝ id ∈ f
  · rw [weights_centroid_of_mem hT hfT hf hpf] at h1
    have hcard : f.card = 1 := by
      have := inv_eq_one.mp h1
      exact_mod_cast this
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    subst ha
    rw [Finset.mem_singleton] at hpf hv
    rw [hpf, hv] at hmem
    exact Finset.notMem_erase a T hmem
  · rw [weights_centroid_of_notMem hT hfT hf hpT hpf] at h1
    exact zero_ne_one h1

omit [FiniteDimensional ℝ E] hfne in
theorem coneComplex_simplexAvoiding_singleton_space :
    (coneComplex (isConeBase_simplexAvoiding hT (Finset.mem_singleton_self f) hfT
      (centroid_mem_openSimplex hf))).space = convexHull ℝ (T : Set E) := by
  have hp : f.centroid ℝ id ∈ convexHull ℝ (T : Set E) := centroid_mem_convexHull_of_subset hfT hf
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (rfl | ⟨z, hz, s, hs0, hs1, rfl⟩)
    · exact hp
    · rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) hp (simplexAvoiding_space_subset T hT _ hz) (by linarith)
        hs0.le (by ring)
  · intro hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase_of_mem_openSimplex hT hfT
      (centroid_mem_openSimplex hf) hx
    rcases exists_combo_of_mem_convexHull_insert (centroid_notMem_erase hT hfT hf hv) hxv with
      rfl | ⟨z, hz, s, hs0, hs1, rfl⟩
    · exact Or.inl rfl
    · rcases (T.erase v).eq_empty_or_nonempty with he | hne
      · rw [he, Finset.coe_empty, convexHull_empty] at hz
        exact hz.elim
      · refine Or.inr ⟨z, (simplexAvoiding T hT {f}).convexHull_subset_space
          ⟨hne, Finset.erase_subset v T, ?_⟩ hz, s, hs0, hs1, rfl⟩
        intro σ hσ
        rw [Finset.mem_singleton] at hσ
        subst hσ
        exact fun h => Finset.notMem_erase v T (h hv)

theorem isPLBall_geometricLink_faceNeighborhood_centroid {n : ℕ} (hcard : T.card = n + 2) :
    IsPLBall n (SimplicialComplex.geometricLink (faceNeighborhood T hT f)
      {T.centroid ℝ id}).space := by
  obtain ⟨φ, hφ⟩ := exists_isPLHomeomorphOn_faceRadialFrontier hT hfT hf hfne
  have hfinR := (faceRadialFrontier_faces_finite T hT f).to_subtype
  have hfinU := (simplexAvoiding_faces_finite T hT {f}).to_subtype
  have hfinD := (faceNeighborhood_faces_finite T hT f).to_subtype
  obtain ⟨g, hg, hgR, -, -⟩ := exists_isPLHomeomorphOn_coneComplex
    (isConeBase_faceRadialFrontier hT hfT hf)
    (isConeBase_simplexAvoiding hT (Finset.mem_singleton_self f) hfT (centroid_mem_openSimplex hf))
    hφ
  rw [← faceNeighborhood_space_eq_coneComplex hT hfT hf hfne,
    coneComplex_simplexAvoiding_singleton_space hT hfT hf] at hg
  have hTne : T.Nonempty := hf.mono hfT
  have hg' : IsPLHomeomorphOn (Function.invFunOn g (faceNeighborhood T hT f).space)
      (simplexComplex T hT).space (faceNeighborhood T hT f).space := by
    rw [simplexComplex_space T hT hTne]
    exact hg.symm
  obtain ⟨w, hwT, hwf⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hfT, hfne⟩)
  have hchain : ∀ s ∈ ({T} : Finset (Finset E)), ∀ t ∈ ({T} : Finset (Finset E)), s ⊆ t ∨ t ⊆ s :=
    fun s hs t ht => Or.inl ((Finset.mem_singleton.mp hs).trans
      (Finset.mem_singleton.mp ht).symm ▸ Finset.Subset.refl _)
  have hu : {T.centroid ℝ id} ∈ (faceNeighborhood T hT f).faces :=
    ⟨{T}, fun s hs => (Finset.mem_singleton.mp hs).symm ▸ ⟨hTne, subset_rfl⟩, hchain,
      Finset.singleton_nonempty T, fun s hs => (Finset.mem_singleton.mp hs).symm ▸
        hf.mono (Finset.subset_inter hfT (Finset.Subset.refl f)), by rw [Finset.image_singleton]⟩
  have hR : T.centroid ℝ id ∈ (faceRadialFrontier T hT f).space := by
    refine (faceRadialFrontier T hT f).convexHull_subset_space
      ⟨{T}, fun s hs => (Finset.mem_singleton.mp hs).symm ▸ ⟨hTne, subset_rfl⟩, hchain,
        Finset.singleton_nonempty T, fun s hs => (Finset.mem_singleton.mp hs).symm ▸
          hf.mono (Finset.subset_inter hfT (Finset.Subset.refl f)),
        Or.inl fun s hs => (Finset.mem_singleton.mp hs).symm ▸
          ⟨w, Finset.mem_inter.mpr ⟨hwT, Finset.mem_sdiff.mpr ⟨hwT, hwf⟩⟩⟩,
        by rw [Finset.image_singleton]⟩ (subset_convexHull ℝ _ (by simp))
  have hD : T.centroid ℝ id ∈ (faceNeighborhood T hT f).space :=
    faceRadialFrontier_space_subset T hT f hR
  rw [isPLBall_geometricLink_iff_of_isPLHomeomorphOn_simplexComplex _ hT hcard hg' hu]
  refine ⟨g (T.centroid ℝ id), ?_, hg.1.injOn.leftInvOn_invFunOn hD⟩
  rw [hgR hR]
  have hφU : φ (T.centroid ℝ id) ∈ (simplexAvoiding T hT {f}).space := hφ.1.mapsTo hR
  obtain ⟨s, hs, hφs⟩ := (simplexAvoiding T hT {f}).mem_space_iff.mp hφU
  exact (simplexBoundary T hT).convexHull_subset_space
    ⟨hs.2.1, hs.1, fun h => hs.2.2 f (Finset.mem_singleton_self f) (h ▸ hfT)⟩ hφs

end DifferentialGeometry.Topology.PiecewiseLinear
