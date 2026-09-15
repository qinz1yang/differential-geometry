import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart
import DifferentialGeometry.Topology.Simplex.BallCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def stdClosedTarget (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {y | (∀ i, 0 ≤ WithLp.ofLp y i) ∧ ∑ i, WithLp.ofLp y i ≤ 1}

private theorem interior_stdClosedTarget (n : ℕ) :
    interior (stdClosedTarget n) = stdTarget n := by
  let e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ (Fin (n + 1) → ℝ) :=
    PiLp.homeomorph 2 fun _ : Fin (n + 1) => ℝ
  have htarget : stdClosedTarget n = e ⁻¹' DifferentialGeometry.Simplex.coordinateSimplex (n + 1) := by
    rfl
  rw [htarget, ← e.preimage_interior,
    DifferentialGeometry.Simplex.interior_coordinateSimplex]
  rfl

private theorem stdProj_mem_stdClosedTarget (n : ℕ) {x : Fin (n + 2) → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin (n + 2))) : stdProj n x ∈ stdClosedTarget n := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [ofLp_stdProj]
    exact hx.1 _
  · simp_rw [ofLp_stdProj]
    have hsum := hx.2
    rw [Fin.sum_univ_castSucc] at hsum
    linarith [hx.1 (Fin.last (n + 1))]

private theorem mem_interior_image_of_isPLHomeomorphOn_stdSimplex
    {n : ℕ} {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P)
    {x : Fin (n + 2) → ℝ} (hx : x ∈ openSimplex (stdVertices n)) :
    f x ∈ interior P := by
  let g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => f (stdLift n y)
  have hgcont : ContinuousOn g (stdTarget n) :=
    hf.isPiecewiseAffineOn.continuousOn.comp (continuous_stdLift n).continuousOn
      fun y hy => openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy)
  have hginj : InjOn g (stdTarget n) := by
    intro y hy z hz hyz
    have hlift := hf.bijOn.injOn
      (openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy))
      (openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hz)) hyz
    simpa only [stdProj_stdLift] using congrArg (stdProj n) hlift
  have hgopen : IsOpen (g '' stdTarget n) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image
      (isOpen_stdTarget n) hgcont hginj
  have hsub : g '' stdTarget n ⊆ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hf.bijOn.mapsTo
      (openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy))
  apply interior_maximal hsub hgopen
  refine ⟨stdProj n x, stdProj_mem_stdTarget n hx, ?_⟩
  change f (stdLift n (stdProj n x)) = f x
  rw [stdLift_stdProj_of_mem n hx]

private theorem not_mem_interior_of_mem_boundaryComplex_of_isPLBall
    {n : ℕ} [DecidableEq (EuclideanSpace ℝ (Fin (n + 1)))]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    [Finite K.faces] (hK : IsPLBall (n + 1) K.space) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ (boundaryComplex (n + 1) K).space) : x ∉ interior K.space := by
  obtain ⟨f, hf⟩ := hK
  rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hf] at hx
  obtain ⟨y, hyB, rfl⟩ := hx
  intro hyint
  let g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z => stdProj n (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) z)
  have hgcont : ContinuousOn g (interior K.space) :=
    (continuous_stdProj n).comp_continuousOn
      (hf.isPiecewiseAffineOn_invFunOn.continuousOn.mono interior_subset)
  have hginj : InjOn g (interior K.space) := by
    intro z hz w hw hzw
    have hzK : z ∈ K.space := interior_subset hz
    have hwK : w ∈ K.space := interior_subset hw
    have hzinv := hf.bijOn.surjOn.mapsTo_invFunOn hzK
    have hwinv := hf.bijOn.surjOn.mapsTo_invFunOn hwK
    have hliftz := stdLift_stdProj n hzinv.2
    have hliftw := stdLift_stdProj n hwinv.2
    have hinveq : Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) z =
        Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) w := by
      calc
        Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) z =
            stdLift n (stdProj n (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) z)) :=
          hliftz.symm
        _ = stdLift n (stdProj n
            (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) w)) := by
          exact congrArg (stdLift n) hzw
        _ = Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) w := hliftw
    calc
      z = f (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) z) :=
        (hf.bijOn.invOn_invFunOn.2 hzK).symm
      _ = f (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) w) := congrArg f hinveq
      _ = w := hf.bijOn.invOn_invFunOn.2 hwK
  have hgopen : IsOpen (g '' interior K.space) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image isOpen_interior hgcont hginj
  have hsub : g '' interior K.space ⊆ stdClosedTarget n := by
    rintro _ ⟨z, hz, rfl⟩
    exact stdProj_mem_stdClosedTarget n (hf.bijOn.surjOn.mapsTo_invFunOn (interior_subset hz))
  have hgy : g (f y) ∈ interior (stdClosedTarget n) :=
    interior_maximal hsub hgopen ⟨f y, hyint, rfl⟩
  rw [interior_stdClosedTarget] at hgy
  have hyS : y ∈ stdSimplex ℝ (Fin (n + 2)) := simplexBoundary_stdVertices_space_subset n hyB
  have hinv := hf.bijOn.invOn_invFunOn.1 hyS
  change stdProj n (Function.invFunOn f (stdSimplex ℝ (Fin (n + 2))) (f y)) ∈ stdTarget n at hgy
  rw [hinv] at hgy
  have hopen : y ∈ openSimplex (stdVertices n) := by
    rw [← stdLift_stdProj n (x := y) hyS.2]
    exact stdLift_mem_openSimplex n hgy
  rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)] at hyB
  exact notMem_boundary_of_mem_openSimplex (stdVertices_affineIndependent n) hopen hyB

private theorem IsSubdivision.isPLHomeomorphOn_id [FiniteDimensional ℝ E]
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (h : IsSubdivision K' K) : IsPLHomeomorphOn id K.space K'.space := by
  have hpa : IsPiecewiseAffineOn (id : E → E) K.space :=
    isPiecewiseAffineOn_space_of_forall_face K fun _ _ =>
      ⟨AffineMap.id ℝ E, fun _ _ => rfl⟩
  have hinv : IsPiecewiseAffineOn (Function.invFunOn id K.space) K.space :=
    hpa.congr fun y hy => (bijOn_id K.space).invOn_invFunOn.1 hy
  rw [h.space_eq]
  exact ⟨bijOn_id K.space, hpa, hinv⟩

open Classical in
private theorem mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {x : E} (hx : {x} ∈ K.faces) :
    x ∈ (boundaryComplex (n + 1) K).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K {x}).space := by
  constructor
  · intro hxB
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex (n + 1) K).mem_space_iff.mp hxB
    have hxs' : x ∈ s :=
      mem_of_mem_convexHull_of_singleton_mem K hx
        (boundaryComplex_faces_subset (n + 1) K hs) hxs
    have hsingle : {x} ∈ (boundaryComplex (n + 1) K).faces :=
      (boundaryComplex (n + 1) K).down_closed hs
        (Finset.singleton_subset_iff.mpr hxs') (Finset.singleton_nonempty x)
    simpa using ((hK.mem_boundaryComplex_faces_iff K).mp hsingle).2.2
  · intro hball
    exact (boundaryComplex (n + 1) K).convexHull_subset_space
      ((hK.mem_boundaryComplex_faces_iff K).mpr ⟨hx, by simp, by simpa using hball⟩)
      (subset_convexHull ℝ _ (by simp))

open Classical in
private theorem not_mem_interior_space_of_isPLBall_geometricLink
    {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    [Finite K.faces] {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : {x} ∈ K.faces)
    (hball : IsPLBall n
      (@SimplicialComplex.geometricLink _ _ _ _ _ _ (Classical.decEq _) K {x}).space) :
    x ∉ interior K.space := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  intro hxint
  have hstarNhds : closedStar K x ∈ 𝓝 x :=
    closedStar_mem_nhds K (mem_interior_iff_mem_nhds.mp hxint)
  let L := starComplex K x
  have hLfin : L.faces.Finite := starComplex_faces_finite K x
  let _ : Finite L.faces := hLfin.to_subtype
  have hxL : {x} ∈ L.faces := singleton_mem_starComplex K x hx
  have hlinkL : IsPLBall n (SimplicialComplex.geometricLink L {x}).space := by
    rw [geometricLink_starComplex]
    exact hball
  have hLB : x ∈ (boundaryComplex (n + 1) L).space :=
    (boundaryComplex (n + 1) L).convexHull_subset_space
      (mem_boundaryComplex_faces_of_isPLBall (n + 1) L hxL (by simp) (by simpa using hlinkL))
      (subset_convexHull ℝ _ (by simp))
  have hLball : IsPLBall (n + 1) L.space := by
    rw [starComplex_space K x hx, closedStar_eq_coneComplex_space K hx]
    exact (isConeBase_geometricLink K).isPLBall_of_isPLBall hball
  have hnot := not_mem_interior_of_mem_boundaryComplex_of_isPLBall L hLball hLB
  apply hnot
  rw [starComplex_space K x hx]
  exact mem_interior_iff_mem_nhds.mpr hstarNhds

open Classical in
private theorem frontier_space_subset_boundaryComplex_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    frontier K.space ⊆
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space := by
  classical
  have hclosed : IsClosed K.space := (isPolyhedron_space K).isCompact.isClosed
  intro x hx
  rw [hclosed.frontier_eq] at hx
  obtain ⟨K', hK', hfin', hx'⟩ := exists_isSubdivision_singleton_mem K hx.1
  let _ : Finite K'.faces := hfin'.to_subtype
  have hman := hK.of_isSubdivision hK'
  have hid := hK'.isPLHomeomorphOn_id
  rcases hman x hx' with hsph | hball
  · exfalso
    apply hx.2
    have hxi : x ∈ interior (closedStar K' x) := by
      obtain ⟨g, hg, -, hgc⟩ := exists_starHomeo K' hx' hsph
      have h := mem_interior_image_of_isPLHomeomorphOn_stdSimplex hg
        (stdCenter_mem_openSimplex n)
      simpa only [hgc] using h
    have hxi' := interior_mono (closedStar_subset_space K' x) hxi
    rwa [hK'.space_eq] at hxi'
  · have hxB' :=
      (mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton K' hman hx').mpr hball
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K K' hK hid hx.1).mp hxB'

open Classical in
private theorem exists_isSubdivision_singleton_mem_boundaryComplex_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hxB : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space) :
    ∃ K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      IsSubdivision K' K ∧ K'.faces.Finite ∧ {x} ∈ K'.faces ∧
        x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K').space := by
  classical
  obtain ⟨s, hs, hxs⟩ :=
    (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).mem_space_iff.mp hxB
  have hxK : x ∈ K.space := K.convexHull_subset_space hs.1 hxs
  obtain ⟨K', hK', hfin', hx'⟩ := exists_isSubdivision_singleton_mem K hxK
  refine ⟨K', hK', hfin', hx', ?_⟩
  let _ : Finite K'.faces := hfin'.to_subtype
  have hid := hK'.isPLHomeomorphOn_id
  exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K K' hK hid hxK).mpr hxB

open Classical in
private theorem not_mem_interior_space_of_mem_boundaryComplex_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hxB : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space) :
    x ∉ interior K.space := by
  classical
  obtain ⟨K', hK', hfin', hx', hxB'⟩ :=
    exists_isSubdivision_singleton_mem_boundaryComplex_space hK hxB
  let _ : Finite K'.faces := hfin'.to_subtype
  have hman := hK.of_isSubdivision hK'
  have hball :=
    (mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton K' hman hx').mp hxB'
  intro hxint
  have hxint' : x ∈ interior K'.space := by
    rwa [hK'.space_eq]
  exact not_mem_interior_space_of_isPLBall_geometricLink K' hx' hball hxint'

open Classical in
private theorem boundaryComplex_space_subset_frontier_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space ⊆
      frontier K.space := by
  classical
  have hclosed : IsClosed K.space := (isPolyhedron_space K).isCompact.isClosed
  intro x hxB
  obtain ⟨s, hs, hxs⟩ :=
    (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).mem_space_iff.mp hxB
  rw [hclosed.frontier_eq]
  exact ⟨K.convexHull_subset_space hs.1 hxs,
    not_mem_interior_space_of_mem_boundaryComplex_space hK hxB⟩

open Classical in
theorem frontier_space_eq_boundaryComplex_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    frontier K.space =
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space :=
  Subset.antisymm (frontier_space_subset_boundaryComplex_space hK)
    (boundaryComplex_space_subset_frontier_space hK)

open Classical in
private theorem mem_interior_map_iff_not_mem_boundaryComplex_space_of_piece
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X] [T2Space X] {P : Set X}
    (T : PLPieceIn F (n + 1) X P)
    (hT : IsCombinatorialManifoldWithBoundary (n + 1) T.complex)
    {x : F} (hx : x ∈ T.complex.space) :
    T.map x ∈ interior P ↔
      x ∉ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) T.complex).space := by
  classical
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨K₁, hK₁, hfin₁, hx₁⟩ := exists_isSubdivision_singleton_mem T.complex hx
  let _ : Finite K₁.faces := hfin₁.to_subtype
  have hcont₁ : ContinuousOn T.map K₁.space := by
    rw [hK₁.space_eq]
    exact T.continuousOn
  obtain ⟨K₂, hK₂, hfin₂, hstar⟩ :=
    exists_isSubdivision_closedStar_subset (n := n + 1) K₁ hcont₁
  let _ : Finite K₂.faces := hfin₂.to_subtype
  have hsub : IsSubdivision K₂ T.complex := hK₂.trans hK₁
  have hx₂ : {x} ∈ K₂.faces := hK₂.singleton_mem hx₁
  let T₂ := T.subdivide K₂ hsub hfin₂
  have hman₂ : IsCombinatorialManifoldWithBoundary (n + 1) K₂ :=
    hT.of_isSubdivision hsub
  have hboundary :
      x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) T.complex).space ↔
        x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K₂).space := by
    simpa using (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn T.complex K₂ hT
      hsub.isPLHomeomorphOn_id hx).symm
  obtain ⟨e, he, hstarx⟩ := hstar x hx₂
  constructor
  · intro hxint hxB
    have hball :=
      (mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton K₂ hman₂ hx₂).mp
        (hboundary.mp hxB)
    have hxK₂ : x ∈ K₂.space := hsub.space_eq ▸ hx
    have hnhds : T₂.map '' closedStar K₂ x ∈ 𝓝 (T₂.map x) :=
      T₂.image_mem_nhds_of_mem_nhds hxK₂ (mem_interior_iff_mem_nhds.mp hxint)
        (closedStar_mem_nhdsWithin K₂ x)
    have hsphere := T₂.isPLSphere_geometricLink_of_image_mem_nhds hx₂ e he hstarx hnhds
    exact hball.not_isPLSphere hsphere
  · intro hxnotB
    rcases hman₂ x hx₂ with hsphere | hball
    · let c := vertexChart K₂ hx₂ hsphere
      let g : EuclideanSpace ℝ (Fin (n + 1)) → X :=
        fun y => T₂.map (c.symm y).1
      have hcsymm : ContinuousOn (fun y => (c.symm y).1) c.target :=
        continuous_subtype_val.comp_continuousOn c.continuousOn_symm
      have hgcont : ContinuousOn g c.target :=
        T₂.continuousOn.comp hcsymm fun y hy => (c.symm y).2
      have hginj : InjOn g c.target := by
        intro y hy z hz hyz
        apply c.symm.injOn hy hz
        apply Subtype.ext
        exact T₂.bijOn.injOn (c.symm y).2 (c.symm z).2 hyz
      have hgopen : IsOpen (g '' c.target) :=
        DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
          (E := EuclideanSpace ℝ (Fin (n + 1))) c.open_target hgcont hginj
      have hgsub : g '' c.target ⊆ P := by
        rintro _ ⟨y, hy, rfl⟩
        exact T₂.bijOn.mapsTo (c.symm y).2
      have hxK₂ : x ∈ K₂.space := hsub.space_eq ▸ hx
      have hxc : (⟨x, hxK₂⟩ : K₂.space) ∈ c.source := by
        rw [vertexChart_source]
        exact (mem_openStar_iff K₂ hx₂).mpr (Or.inl rfl)
      apply interior_maximal hgsub hgopen
      refine ⟨c ⟨x, hxK₂⟩, c.map_source hxc, ?_⟩
      change T₂.map (c.symm (c ⟨x, hxK₂⟩)).1 = T₂.map x
      rw [c.left_inv hxc]
    · exfalso
      apply hxnotB
      apply hboundary.mpr
      exact (mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton K₂ hman₂ hx₂).mpr
        hball

open Classical in
theorem frontier_eq_polyhedralBoundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X] [T2Space X]
    [HasGroupoid X (plGroupoid (n + 1))] {P : Set X}
    (h : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P) :
    frontier P = polyhedralBoundary (n + 1) P h := by
  classical
  have hclosed : IsClosed P := h.isCompact.isClosed
  let T := Classical.choose h
  have hT : IsCombinatorialManifoldWithBoundary (n + 1) T.piece.complex :=
    Classical.choose_spec h
  rw [hclosed.frontier_eq, polyhedralBoundary_eq_of_piece h T]
  ext y
  constructor
  · rintro ⟨hyP, hyint⟩
    obtain ⟨x, hx, rfl⟩ := T.piece.bijOn.surjOn hyP
    refine ⟨x, ?_, rfl⟩
    by_contra hxnotB
    exact hyint
      ((mem_interior_map_iff_not_mem_boundaryComplex_space_of_piece T.piece hT hx).mpr hxnotB)
  · rintro ⟨x, hxB, rfl⟩
    obtain ⟨s, hs, hxs⟩ :=
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) T.piece.complex).mem_space_iff.mp hxB
    have hx : x ∈ T.piece.complex.space := T.piece.complex.convexHull_subset_space hs.1 hxs
    refine ⟨T.piece.bijOn.mapsTo hx, ?_⟩
    intro hxint
    exact (mem_interior_map_iff_not_mem_boundaryComplex_space_of_piece T.piece hT hx).mp hxint hxB

open Classical in
private theorem closedStar_barycentricSubdivision_inter_space_eq
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {x : E} (hxL : {x} ∈ L.faces) :
    closedStar (barycentricSubdivision K) x ∩ L.space =
      closedStar (barycentricSubdivision L) x := by
  classical
  have hLK : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces :=
    barycentricSubdivision_faces_subset hL
  have hxK : {x} ∈ K.faces := hL hxL
  have hxKb : {x} ∈ (barycentricSubdivision K).faces :=
    (barycentricSubdivision_isSubdivision K).singleton_mem hxK
  apply Subset.antisymm
  · rintro y ⟨hyK, hyL⟩
    obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hyK
    have hxu' : x ∈ u :=
      mem_of_mem_convexHull_of_singleton_mem (barycentricSubdivision K) hxKb hu hxu
    have hyLb : y ∈ (barycentricSubdivision L).space := by
      rw [(barycentricSubdivision_isSubdivision L).space_eq]
      exact hyL
    obtain ⟨v, hv, hyv⟩ := (barycentricSubdivision L).mem_space_iff.mp hyLb
    have hyuv : y ∈ convexHull ℝ (((u ∩ v : Finset E) : Set E)) :=
      by simpa only [Finset.coe_inter] using
        (barycentricSubdivision K).inter_subset_convexHull hu (hLK hv) ⟨hyu, hyv⟩
    have huvne : (u ∩ v).Nonempty := nonempty_of_mem_convexHull hyuv
    have huvL : u ∩ v ∈ (barycentricSubdivision L).faces :=
      (barycentricSubdivision L).down_closed hv Finset.inter_subset_right huvne
    obtain ⟨D, hD, hDne, huvD⟩ := huvL
    have hxs : ∀ s ∈ D, {x} ⊆ s := by
      intro s hs
      have hcsuv : s.centroid ℝ id ∈ u ∩ v := by
        rw [huvD]
        exact Finset.mem_image_of_mem _ hs
      have hcomp := subset_or_subset_of_centroid_mem_face K hxK (hL (hD.mem_faces hs)) hu
        (by simpa only [Finset.centroid_singleton, id_eq] using hxu')
        (Finset.mem_inter.mp hcsuv).1
      rcases hcomp with h | h
      · exact h
      · rcases Finset.subset_singleton_iff.mp h with hempty | heq
        · exact ((L.nonempty_of_mem_faces (hD.mem_faces hs)).ne_empty hempty).elim
        · rw [heq]
    have hins : insert x (u ∩ v) ∈ (barycentricSubdivision L).faces := by
      have hflag := hD.insert_of_subset hxL hxs
      have hface : (insert {x} D).image (fun s => s.centroid ℝ id) ∈
          (barycentricSubdivision L).faces :=
        ⟨insert {x} D, hflag, Finset.insert_nonempty _ _, rfl⟩
      simpa only [Finset.image_insert, Finset.centroid_singleton, id_eq, ← huvD] using hface
    exact mem_iUnion₂.mpr ⟨insert x (u ∩ v),
      ⟨hins, subset_convexHull ℝ _ (Finset.mem_insert_self _ _)⟩,
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hyuv⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨u, ⟨hLK hu, hxu⟩, hyu⟩
    · rw [← (barycentricSubdivision_isSubdivision L).space_eq]
      exact closedStar_subset_space (barycentricSubdivision L) x hy

open Classical in
private theorem boundaryComplex_space_eq_of_isSubdivision [FiniteDimensional ℝ E]
    {n : ℕ} {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (h : IsSubdivision K' K) :
    (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K').space =
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space := by
  classical
  ext x
  constructor
  · intro hxB
    obtain ⟨s, hs, hxs⟩ :=
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K').mem_space_iff.mp hxB
    have hxK : x ∈ K.space := h.space_eq ▸ K'.convexHull_subset_space hs.1 hxs
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K K' hK
      h.isPLHomeomorphOn_id hxK).mp hxB
  · intro hxB
    obtain ⟨s, hs, hxs⟩ :=
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).mem_space_iff.mp hxB
    have hxK : x ∈ K.space := K.convexHull_subset_space hs.1 hxs
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K K' hK
      h.isPLHomeomorphOn_id hxK).mpr hxB

open Classical in
theorem exists_isPLBall_closedStar_inter_boundary [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    ∀ x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space,
      ∃ C : Set E, IsPLBall (n + 1) C ∧ C ∈ 𝓝[K.space] x ∧
        IsPLBall n (C ∩ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space) := by
  classical
  intro x hxB
  obtain ⟨s, hs, hxs⟩ :=
    (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).mem_space_iff.mp hxB
  have hxK : x ∈ K.space := K.convexHull_subset_space hs.1 hxs
  obtain ⟨K₀, hK₀, hfin₀, hx₀⟩ := exists_isSubdivision_singleton_mem K hxK
  let _ : Finite K₀.faces := hfin₀.to_subtype
  have hxB₀ : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K₀).space :=
    (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn K K₀ hK
      hK₀.isPLHomeomorphOn_id hxK).mpr hxB
  have hman₀ : IsCombinatorialManifoldWithBoundary (n + 1) K₀ := hK.of_isSubdivision hK₀
  let B := @boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K₀
  have hBfin : B.faces.Finite := boundaryComplex_faces_finite (n + 1) K₀
  let _ : Finite B.faces := hBfin.to_subtype
  have hlinkball : IsPLBall n (SimplicialComplex.geometricLink K₀ {x}).space :=
    (mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_singleton K₀ hman₀ hx₀).mp hxB₀
  have hxBface : {x} ∈ B.faces :=
    (hman₀.mem_boundaryComplex_faces_iff K₀).mpr ⟨hx₀, by simp, by simpa using hlinkball⟩
  let K₁ := barycentricSubdivision K₀
  let B₁ := barycentricSubdivision B
  have hK₁fin : K₁.faces.Finite := Set.toFinite _
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  have hB₁fin : B₁.faces.Finite := Set.toFinite _
  let _ : Finite B₁.faces := hB₁fin.to_subtype
  have hxK₁ : {x} ∈ K₁.faces := (barycentricSubdivision_isSubdivision K₀).singleton_mem hx₀
  have hxB₁ : {x} ∈ B₁.faces := (barycentricSubdivision_isSubdivision B).singleton_mem hxBface
  have hlinkball₁ : IsPLBall n (SimplicialComplex.geometricLink K₁ {x}).space :=
    (isPLBall_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision K₀) hx₀).mpr
      hlinkball
  have hCball : IsPLBall (n + 1) (closedStar K₁ x) := by
    rw [closedStar_eq_coneComplex_space K₁ hxK₁]
    exact (isConeBase_geometricLink K₁).isPLBall_of_isPLBall hlinkball₁
  have hCnhds : closedStar K₁ x ∈ 𝓝[K.space] x := by
    rw [← hK₀.space_eq, ← (barycentricSubdivision_isSubdivision K₀).space_eq]
    exact closedStar_mem_nhdsWithin K₁ x
  have hBspace : B.space =
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space :=
    boundaryComplex_space_eq_of_isSubdivision hK hK₀
  have hinter : closedStar K₁ x ∩
      (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space = closedStar B₁ x := by
    rw [← hBspace]
    exact closedStar_barycentricSubdivision_inter_space_eq
      (boundaryComplex_faces_subset (n + 1) K₀) hxBface
  refine ⟨closedStar K₁ x, hCball, hCnhds, ?_⟩
  rw [hinter]
  have hBman : IsCombinatorialManifold n B := isCombinatorialManifold_boundaryComplex K₀ hman₀
  have hB₁man : IsCombinatorialManifold n B₁ :=
    hBman.of_isSubdivision (barycentricSubdivision_isSubdivision B)
  cases n with
  | zero =>
      have hlinkempty := hB₁man x hxB₁
      have hstar : closedStar B₁ x = {x} := by
        rw [closedStar_eq_coneComplex_space B₁ hxB₁]
        ext y
        rw [mem_coneComplex_space_iff, mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨z, hz, s, hs, hs', hy⟩)
          · rfl
          · exfalso
            obtain ⟨t, ht, -⟩ := (SimplicialComplex.geometricLink B₁ {x}).mem_space_iff.mp hz
            rw [hlinkempty] at ht
            exact ht
        · rintro rfl
          exact Or.inl rfl
      rw [hstar]
      have hpoint := isPLBall_convexHull_of_affineIndependent ({x} : Finset E)
        (affineIndependent_of_subsingleton ℝ _) (n := 0) (by simp)
      simpa only [Finset.coe_singleton, convexHull_singleton] using hpoint
  | succ m =>
      exact hB₁man.isPLBall_closedStar hxB₁

end DifferentialGeometry.Topology.PiecewiseLinear
