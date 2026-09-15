import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision [FiniteDimensional ℝ E]
    {n : ℕ} (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hR : IsSubdivision R K)
    {x : E} (hxR : {x} ∈ R.faces) :
    IsPLBall n (SimplicialComplex.geometricLink R {x}).space ↔ x ∈ (boundaryComplex (n + 1) K).space := by
  have hxK : x ∈ K.space := hR.space_eq ▸ R.subset_space hxR (Finset.mem_singleton_self x)
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxK
  have hxB : x ∈ (boundaryComplex (n + 1) K).space ↔ s ∈ (boundaryComplex (n + 1) K).faces := by
    constructor
    · intro hx
      by_contra hnot
      exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) K) hs hnot hxs hx
    · intro hsB
      exact (boundaryComplex (n + 1) K).convexHull_subset_space hsB (openSimplex_subset_convexHull s hxs)
  have hspos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
  have hcardle := hK.card_le K hs
  by_cases hkn : k ≤ n
  · rcases hK.isPLSphere_or_isPLBall_geometricLink K hs hk hkn with hsphere | hball
    · have hsphereR : IsPLSphere n (SimplicialComplex.geometricLink R {x}).space := by
        have h := isPLSphere_geometricLink_of_isPLSphere_geometricLink K hs hxs hR hxR hk hsphere
        rwa [show k + (n - k) = n by omega] at h
      constructor
      · intro hballR
        exact (hballR.not_isPLSphere hsphereR).elim
      · intro hx
        have hballS := ((hK.mem_boundaryComplex_faces_iff K).mp (hxB.mp hx)).2.2
        rw [hk, show n + 1 - (k + 1) = n - k by omega] at hballS
        exact (hballS.not_isPLSphere hsphere).elim
    · have hballR : IsPLBall n (SimplicialComplex.geometricLink R {x}).space := by
        have h := isPLBall_geometricLink_of_isPLBall_geometricLink K hs hxs hR hxR hk hball
        rwa [show k + (n - k) = n by omega] at h
      have hsB : s ∈ (boundaryComplex (n + 1) K).faces :=
        (hK.mem_boundaryComplex_faces_iff K).mpr ⟨hs, by omega, by
          rwa [hk, show n + 1 - (k + 1) = n - k by omega]⟩
      exact ⟨fun _ => hxB.mpr hsB, fun _ => hballR⟩
  · have hsc : s.card = n + 2 := by omega
    have hsphereR := isPLSphere_geometricLink_of_forall_card_le K (fun t ht => hK.card_le K ht)
      hs hsc hxs hR hxR
    constructor
    · intro hballR
      exact (hballR.not_isPLSphere hsphereR).elim
    · intro hx
      have hbound := ((hK.mem_boundaryComplex_faces_iff K).mp (hxB.mp hx)).2.1
      omega

open Classical in
theorem boundaryComplex_space_subset_frontier_of_finrank [FiniteDimensional ℝ E] {n : ℕ}
    [hdec : DecidableEq E]
    (hn : Module.finrank ℝ E = n + 1) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    (boundaryComplex (n + 1) K).space ⊆ frontier K.space := by
  have hdec' : hdec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hdec
  intro x hx
  refine ⟨subset_closure (boundaryComplex_space_subset (n + 1) K hx), ?_⟩
  intro hxint
  obtain ⟨R, hR, hRfin, hxR⟩ := exists_isSubdivision_singleton_mem K
    (boundaryComplex_space_subset (n + 1) K hx)
  have : Finite R.faces := hRfin.to_subtype
  have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
    K R hK hR hxR).mpr hx
  have hnhds : R.space ∈ nhds x := by
    rw [hR.space_eq]
    exact mem_interior_iff_mem_nhds.mp hxint
  exact hball.not_isPLSphere (isPLSphere_geometricLink_of_mem_nhds hn R hxR hnhds)

open Classical in
theorem boundaryComplex_space_of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hR : IsSubdivision R K) :
    (boundaryComplex (n + 1) R).space = (boundaryComplex (n + 1) K).space := by
  ext x
  by_cases hxK : x ∈ K.space
  · obtain ⟨T, hT, hTfinite, hxT⟩ := exists_isSubdivision_singleton_mem R (hR.space_eq.symm ▸ hxK)
    have : Finite T.faces := hTfinite.to_subtype
    exact (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision R T
      (hK.of_isSubdivision hR) hT hxT).symm.trans
        (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K T hK (hT.trans hR) hxT)
  · constructor
    · intro hx
      exact (hxK (hR.space_eq ▸ boundaryComplex_space_subset (n + 1) R hx)).elim
    · intro hx
      exact (hxK (boundaryComplex_space_subset (n + 1) K hx)).elim

open Classical in
theorem mem_boundaryComplex_space_iff_of_isPLHomeomorphOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) {x : E} (hx : x ∈ K.space) :
    f x ∈ (boundaryComplex (n + 1) L).space ↔ x ∈ (boundaryComplex (n + 1) K).space := by
  obtain ⟨K₀, hK₀, hK₀finite, hx₀⟩ := exists_isSubdivision_singleton_mem K hx
  have : Finite K₀.faces := hK₀finite.to_subtype
  have hf₀ : IsPLHomeomorphOn f K₀.space L.space := by rwa [hK₀.space_eq]
  obtain ⟨K₁, L₁, ψ, hK₁, hK₁finite, hL₁, hL₁finite, hiso, _⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn K₀ L hf₀
  have : Finite K₁.faces := hK₁finite.to_subtype
  have : Finite L₁.faces := hL₁finite.to_subtype
  have hx₁ : {x} ∈ K₁.faces := hK₁.singleton_mem hx₀
  have hfx₁ : {f x} ∈ L₁.faces := hiso.singleton_mem hx₁
  have : Finite (SimplicialComplex.geometricLink K₁ {x}).faces :=
    (hK₁finite.subset (SimplicialComplex.geometricLink_le K₁ {x})).to_subtype
  have : Finite (SimplicialComplex.geometricLink L₁ {f x}).faces :=
    (hL₁finite.subset (SimplicialComplex.geometricLink_le L₁ {f x})).to_subtype
  have hlink := (hiso.geometricLink hx₁).isPLHomeomorphOn
  have hball : IsPLBall n (SimplicialComplex.geometricLink L₁ {f x}).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K₁ {x}).space :=
    ⟨fun h => h.of_isPLHomeomorphOn hlink.symm, fun h => h.of_isPLHomeomorphOn hlink⟩
  exact (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision L L₁
    (hK.of_isPLHomeomorphOn hf) hL₁ hfx₁).symm.trans
      (hball.trans (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K K₁ hK (hK₁.trans hK₀) hx₁))

open Classical in
theorem boundaryComplex_space_of_isPLHomeomorphOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) :
    (boundaryComplex (n + 1) L).space = f '' (boundaryComplex (n + 1) K).space := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn (boundaryComplex_space_subset (n + 1) L hy)
    exact ⟨x, (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K L hK hf hx).mp hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K L hK hf
      (boundaryComplex_space_subset (n + 1) K hx)).mpr hx

end DifferentialGeometry.Topology.PiecewiseLinear
