import DifferentialGeometry.Topology.PiecewiseLinear.TriangulationExistence
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialZero

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem card_le_finrank_succ_of_mem_faces [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) :
    s.card ≤ Module.finrank ℝ E + 1 := by
  have h := (K.indep hs).card_le_finrank_succ
  rw [Fintype.card_coe] at h
  exact h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

theorem mem_closedStar_self (K : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ K.faces) :
    v ∈ closedStar K v :=
  mem_biUnion (x := ({v} : Finset E))
    ⟨hv, subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v))⟩
    (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v)))

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem exists_isSubdivision_closedStar_subset
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {g : E → X}
    (hg : ContinuousOn g K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ v, {v} ∈ K'.faces → ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
        closedStar K' v ⊆ g ⁻¹' e.source := by
  classical
  have hU : ∀ x : X, ∃ U : Set E, IsOpen U ∧
      g ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩ K.space = U ∩ K.space :=
    fun x => continuousOn_iff'.mp hg _ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  choose U hUopen hUeq using hU
  have hcover : K.space ⊆ ⋃ x : X, U x := by
    intro y hy
    have hmem : y ∈ g ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (g y)).source ∩ K.space :=
      ⟨mem_chart_source _ (g y), hy⟩
    rw [hUeq] at hmem
    exact mem_iUnion.mpr ⟨g y, hmem.1⟩
  obtain ⟨K', hK', hfin, hstars⟩ := exists_isSubdivision_closedStars_subset_cover K U
    (fun x => (hUopen x).preimage continuous_subtype_val) hcover
  refine ⟨K', hK', hfin, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := hstars {v} hv
  refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) x, chart_mem_atlas _ x, fun y hy => ?_⟩
  have hyK : y ∈ K.space := hK'.space_eq ▸ closedStar_subset_space K' v hy
  have hmem : y ∈ U x ∩ K.space :=
    ⟨hx (mem_iUnion₂.mpr ⟨v, Finset.mem_singleton_self v, hy⟩), hyK⟩
  rw [← hUeq] at hmem
  exact hmem.1

theorem PLPieceIn.isPLSphere_geometricLink [FiniteDimensional ℝ E] [DecidableEq E] {m : ℕ}
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]
    [T2Space X] (T : PLPieceIn E (m + 1) X univ) {v : E} (hv : {v} ∈ T.complex.faces)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1))))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin (m + 1))) X)
    (hstar : closedStar T.complex v ⊆ T.map ⁻¹' e.source) :
    IsPLSphere m (SimplicialComplex.geometricLink T.complex {v}).space := by
  classical
  have hfin := T.finite_faces.to_subtype
  have hfinSt := (starComplex_faces_finite T.complex v).to_subtype
  have hStspace := starComplex_space T.complex v hv
  have hvSt := singleton_mem_starComplex T.complex v hv
  have hvK : v ∈ T.complex.space :=
    T.complex.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hplSt : IsPiecewiseAffineOn (e ∘ T.map) (starComplex T.complex v).space := by
    refine (T.isPiecewiseAffineOn_chart e he).mono_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space (starComplex T.complex v)) ?_
    rw [hStspace]
    intro x hx
    exact ⟨closedStar_subset_space _ _ hx, hstar hx⟩
  have hinjSt : InjOn (e ∘ T.map) (starComplex T.complex v).space := by
    rw [hStspace]
    exact e.injOn.comp (T.bijOn.injOn.mono (closedStar_subset_space _ _)) hstar
  obtain ⟨St', hSt', hfinSt', hAff⟩ := hplSt.exists_isSubdivision_affineOn_faces _
  have hfinSt'' := hfinSt'.to_subtype
  have hsimp : EqOn (simplicialMap St' (e ∘ T.map)) (e ∘ T.map) St'.space :=
    simplicialMap_eq_of_forall_affineOn St' _ hAff
  have hinjSt' : InjOn (e ∘ T.map) St'.space := by
    rw [hSt'.space_eq]
    exact hinjSt
  have hinj' : InjOn (simplicialMap St' (e ∘ T.map)) St'.space :=
    fun x hx y hy hxy => hinjSt' hx hy (by rw [← hsimp hx, ← hsimp hy]; exact hxy)
  have hind : ∀ s ∈ St'.faces, AffineIndependent ℝ
      ((↑) : {u // u ∈ s.image (e ∘ T.map)} → EuclideanSpace ℝ (Fin (m + 1))) := fun s hs => by
    obtain ⟨Af, hAf⟩ := hAff s hs
    have himgs : s.image (e ∘ T.map) = s.image Af :=
      Finset.image_congr fun w hw => hAf (subset_convexHull ℝ _ hw)
    rw [himgs]
    refine affineIndependent_image_of_injOn_convexHull Af (St'.indep hs) fun x hx y hy hxy =>
      hinjSt' (St'.convexHull_subset_space hs hx) (St'.convexHull_subset_space hs hy) ?_
    rw [hAf hx, hAf hy]
    exact hxy
  obtain ⟨φ', hφ'⟩ := exists_isGlueIso_simplicialImage St' (e ∘ T.map) hind hinj'
  have hfinL := (simplicialImage_faces_finite St' (e ∘ T.map) hind hinj').to_subtype
  have hvSt' : {v} ∈ St'.faces := hSt'.singleton_mem hvSt
  have hgv : T.map v ∈ e.source := hstar (mem_closedStar_self T.complex hv)
  have hLnhds : (simplicialImage St' (e ∘ T.map) hind hinj').space ∈ 𝓝 ((e ∘ T.map) v) := by
    rw [simplicialImage_space, hsimp.image_eq, hSt'.space_eq, hStspace]
    obtain ⟨O, hO, hvO, hOsub⟩ := mem_nhdsWithin.mp (closedStar_mem_nhdsWithin T.complex v)
    have hψ : ContinuousOn (Function.invFunOn T.map T.complex.space ∘ e.symm) e.target := by
      have h := (T.isPiecewiseAffineOn_chart_symm e he).continuousOn
      rwa [preimage_univ, inter_univ] at h
    have hN : IsOpen (e.target ∩ (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' O) :=
      hψ.isOpen_inter_preimage e.open_target hO
    refine Filter.mem_of_superset (hN.mem_nhds ⟨e.map_source hgv, ?_⟩) ?_
    · change Function.invFunOn T.map T.complex.space (e.symm (e (T.map v))) ∈ O
      rw [e.left_inv hgv, T.bijOn.injOn.leftInvOn_invFunOn hvK]
      exact hvO
    · rintro y ⟨hy, hyO⟩
      have hy' : Function.invFunOn T.map T.complex.space (e.symm y) ∈ T.complex.space :=
        T.bijOn.surjOn.mapsTo_invFunOn (mem_univ _)
      refine ⟨Function.invFunOn T.map T.complex.space (e.symm y), hOsub ⟨hyO, hy'⟩, ?_⟩
      change e (T.map (Function.invFunOn T.map T.complex.space (e.symm y))) = y
      rw [T.bijOn.invOn_invFunOn.2 (mem_univ _), e.right_inv hy]
  have hL := isPLSphere_geometricLink_of_mem_nhds finrank_euclideanSpace_fin
    (simplicialImage St' (e ∘ T.map) hind hinj') (hφ'.singleton_mem hvSt') hLnhds
  have hSt'sphere := hφ'.isPLSphere_geometricLink hvSt' hL
  rw [isPLSphere_geometricLink_iff_of_isSubdivision hSt' hvSt, geometricLink_starComplex]
    at hSt'sphere
  exact hSt'sphere

theorem PLPieceIn.exists_isSubdivision_isCombinatorialManifold_succ [FiniteDimensional ℝ E]
    {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]
    [T2Space X] (T : PLPieceIn E (m + 1) X univ) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' T.complex ∧ K'.faces.Finite ∧
      IsCombinatorialManifold (m + 1) K' := by
  classical
  have hfin := T.finite_faces.to_subtype
  obtain ⟨K', hK', hfin', hstar⟩ :=
    exists_isSubdivision_closedStar_subset (n := m + 1) T.complex T.continuousOn
  refine ⟨K', hK', hfin', fun v hv => ?_⟩
  obtain ⟨e, he, hsub⟩ := hstar v hv
  exact (T.subdivide K' hK' hfin').isPLSphere_geometricLink hv e he hsub

theorem PLPieceIn.isCombinatorialManifold_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) X] [T2Space X] (T : PLPieceIn E 0 X univ) :
    IsCombinatorialManifold 0 T.complex := by
  classical
  intro v hv
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  rw [SimplicialComplex.mem_geometricLink_singleton] at ht
  obtain ⟨⟨w, hw⟩, hvt, hins⟩ := ht
  have hvw : v ≠ w := fun h => hvt (h ▸ hw)
  have hedge : ({v, w} : Finset E) ∈ T.complex.faces := by
    refine T.complex.down_closed hins ?_ (Finset.insert_nonempty _ _)
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hw
  have hsub : convexHull ℝ (({v, w} : Finset E) : Set E) ⊆ T.complex.space :=
    T.complex.convexHull_subset_space hedge
  have hconn : IsPreconnected (T.map '' convexHull ℝ (({v, w} : Finset E) : Set E)) :=
    (convex_convexHull ℝ _).isPreconnected.image _ (T.continuousOn.mono hsub)
  have hvmem : v ∈ convexHull ℝ (({v, w} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hwmem : w ∈ convexHull ℝ (({v, w} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self w)))
  have hopen : IsOpen ({T.map v} : Set X) := by
    have hsrc : (chartAt (EuclideanSpace ℝ (Fin 0)) (T.map v)).source = {T.map v} := by
      apply Subset.antisymm
      · intro y hy
        have := subsingleton_euclideanSpace_zero
        exact (chartAt (EuclideanSpace ℝ (Fin 0)) (T.map v)).injOn hy (mem_chart_source _ _)
          (Subsingleton.elim _ _)
      · rintro y rfl
        exact mem_chart_source _ _
    rw [← hsrc]
    exact (chartAt (EuclideanSpace ℝ (Fin 0)) (T.map v)).open_source
  have hclopen : IsClopen ({T.map v} : Set X) := ⟨isClosed_singleton, hopen⟩
  have himg := hconn.subset_isClopen hclopen ⟨T.map v, ⟨v, hvmem, rfl⟩, rfl⟩
  have hw' : T.map w ∈ ({T.map v} : Set X) := himg ⟨w, hwmem, rfl⟩
  rw [mem_singleton_iff] at hw'
  exact hvw (T.bijOn.injOn (hsub hvmem) (hsub hwmem) hw'.symm)

theorem exists_pLTriangulation_isCombinatorialManifold [CompactSpace X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid n)] :
    ∃ T : PLTriangulation n X, IsCombinatorialManifold n T.complex := by
  obtain ⟨T⟩ := exists_pLPiece_univ (n := n) (X := X)
  cases n with
  | zero => exact ⟨T.toPLTriangulation, T.piece.isCombinatorialManifold_zero⟩
  | succ m =>
    obtain ⟨K', hK', hfin', hcomb⟩ := T.piece.exists_isSubdivision_isCombinatorialManifold_succ
    exact ⟨(⟨T.ambientDim, T.piece.subdivide K' hK' hfin'⟩ : PLPiece (m + 1) X univ).toPLTriangulation,
      hcomb⟩

theorem plManifoldTriangulation (n : ℕ) : PLManifoldTriangulation n := by
  intro X _ _ _ _ _ C hG
  let _ := C
  have : HasGroupoid X (plGroupoid n) := hG
  exact exists_pLTriangulation_isCombinatorialManifold

end DifferentialGeometry.Topology.PiecewiseLinear
