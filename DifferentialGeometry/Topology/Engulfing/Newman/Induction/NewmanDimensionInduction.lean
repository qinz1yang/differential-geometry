import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanProblem
import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanPreparation
import DifferentialGeometry.Topology.SimplicialComplex.Expansion.SkeletalStages

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {M : Type*} [MetricSpace M] {n p q : ℕ}

theorem newmanConclusion_of_separated_faces
    (hlower : relativeNewmanAt M n p q) (hsingle : singleSimplexNewmanAt M n p q)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : NewmanProblem E M n p (q + 1))
    (hsep : ∀ s ∈ P.target.faces,
      (∀ x : P.source.space, x.1 ∈ convexHull ℝ (s : Set E) → P.map x ∈ P.openSet) ∨
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε := by
  classical
  let R := coveredFaces P.source P.target P.map P.openSet
  let Q := uncoveredFaces P.source P.target P.map P.openSet
  have hH : P.target.faces.Finite := P.source_finite.subset P.target_subcomplex
  have hRH : R.faces ⊆ P.target.faces := coveredFaces_faces_subset _ _ _ _
  have hR : ∀ x : P.source.space, x.1 ∈ R.space → P.map x ∈ P.openSet :=
    fun x hx => image_coveredFaces_subset _ _ _ _ ⟨x, hx, rfl⟩
  have hdimQ : ∀ s ∈ Q.faces, s.card ≤ q + 1 := P.decomposition.uncoveredFaces_card_le
  have hbound : ∀ s ∈ P.target.faces, s ∈ R.faces ∨ s.card ≤ q + 1 := by
    intro s hs
    by_cases hsR : s ∈ R.faces
    · exact Or.inl hsR
    · exact Or.inr (hdimQ s ⟨hs, s, hs, hsR, subset_rfl⟩)
  have havoid : Disjoint (P.map '' (Subtype.val ⁻¹' Q.space)) P.obstacle :=
    image_uncoveredFaces_disjoint _ _ _ hsep
  obtain ⟨δ, hδ, hδavoid⟩ := exists_uncoveredFaces_avoidance_tolerance
    P.source P.target P.source_finite hH P.map P.obstacle_closed havoid
  let H₀ := skeletalStage P.target R (q + 1) ∅
  let P₀ : NewmanProblem E M n p q :=
    { source := P.source
      fixed := P.fixed
      target := H₀
      source_finite := P.source_finite
      fixed_subcomplex := P.fixed_subcomplex
      target_subcomplex := fun s hs => P.target_subcomplex hs.1
      source_dimension := P.source_dimension
      target_dimension := fun s hs => P.target_dimension s hs.1
      map := P.map
      fixed_injective := P.fixed_injective
      obstacle := P.obstacle
      openSet := P.openSet
      obstacle_closed := P.obstacle_closed
      open_openSet := P.open_openSet
      obstacle_subset := P.obstacle_subset
      localData := P.localData
      codimension := P.codimension
      connectivity := P.connectivity
      decomposition := engulfingDecomposition_skeletalStage_empty _ _ _ _ hRH hR q }
  obtain ⟨g₀, h₀, hfix₀, hnear₀, hcover₀, hcompact₀⟩ :=
    hlower E P₀ (min (ε / 2) δ) (lt_min (half_pos hε) hδ)
  let Good : C(P.source.space, M) → Prop := fun g =>
    (∀ x : P.source.space, x.1 ∈ P.fixed.space → g x = P.map x) ∧
    Disjoint (g '' (Subtype.val ⁻¹' Q.space)) P.obstacle
  have hGood₀ : Good g₀ := ⟨hfix₀,
    hδavoid g₀ (fun x => (hnear₀ x).trans_le (min_le_right _ _))⟩
  let : CompactSpace P.source.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces _ P.source_finite)
  have hQcompact : IsCompact (Subtype.val ⁻¹' Q.space : Set P.source.space) :=
    ((isCompact_space_of_finite_faces Q
      (hH.subset (uncoveredFaces_faces_subset _ _ _ _))).isClosed.preimage
        continuous_subtype_val).isCompact
  have hstep : ∀ (F : Finset (Finset E)) (s : Finset E), s ∈ P.target.faces →
      s.card = q + 1 → s ∉ (skeletalStage P.target R (q + 1) F).faces →
      ∀ (g : C(P.source.space, M)) (V : Set M), IsOpen V →
      NewmanConnectivity M V p → Good g →
      P.obstacle ∪ g '' (Subtype.val ⁻¹' (skeletalStage P.target R (q + 1) F).space) ⊆ V →
      g '' (Subtype.val ⁻¹' finiteSimplexBoundary s) ⊆ V →
      ∀ η : ℝ, 0 < η → ∃ (g' : C(P.source.space, M)) (h : M ≃ₜ M),
        Good g' ∧ (∀ x : P.source.space, x.1 ∈ P.fixed.space → g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < η) ∧
        P.obstacle ∪ g' '' (Subtype.val ⁻¹'
          (skeletalStage P.target R (q + 1) (insert s F)).space) ⊆ h '' V ∧
        IsCompact (closure {x | h x ≠ x}) := by
    intro F s hs hcard hnew g V hV hconn hg hcovered _ η hη
    let T := skeletalStage P.target R (q + 1) (insert s F)
    have hfixed : InjOn g (Subtype.val ⁻¹' P.fixed.space) := by
      intro x hx y hy hxy
      apply P.fixed_injective hx hy
      rw [← hg.1 x hx, ← hg.1 y hy]
      exact hxy
    let P₁ : NewmanProblem E M n p (q + 1) :=
      { source := P.source
        fixed := P.fixed
        target := T
        source_finite := P.source_finite
        fixed_subcomplex := P.fixed_subcomplex
        target_subcomplex := fun t ht => P.target_subcomplex ht.1
        source_dimension := P.source_dimension
        target_dimension := fun t ht => P.target_dimension t ht.1
        map := g
        fixed_injective := hfixed
        obstacle := P.obstacle
        openSet := V
        obstacle_closed := P.obstacle_closed
        open_openSet := hV
        obstacle_subset := fun x hx => hcovered (Or.inl hx)
        localData := P.localData.withMap g hg.1
        codimension := P.codimension
        connectivity := hconn
        decomposition := engulfingDecomposition_skeletalStage_insert _ _ _ _ _ hcard g
          (fun x hx => hcovered (Or.inr ⟨x, hx, rfl⟩)) }
    have hsT : s ∈ T.faces :=
      ⟨hs, Or.inr (Or.inr ⟨s, Finset.mem_insert_self _ _, subset_rfl⟩)⟩
    have hother : ∀ t ∈ T.faces, t ≠ s →
        ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → g x ∈ V := by
      intro t ht hts x hx
      have htold := skeletalStage_mem_insert_of_ne P.target R (q + 1) F hcard ht hts
      exact hcovered (Or.inr ⟨x,
        (skeletalStage P.target R (q + 1) F).convexHull_subset_space htold hx, rfl⟩)
    have hsQ : s ∈ Q.faces := by
      refine ⟨hs, s, hs, ?_, subset_rfl⟩
      exact fun hsR => hnew ⟨hs, Or.inl hsR⟩
    have hsavoid : Disjoint (g '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle := by
      apply disjoint_left.mpr
      rintro y ⟨x, hx, rfl⟩ hxX
      exact disjoint_left.mp hg.2 ⟨x, Q.convexHull_subset_space hsQ hx, rfl⟩ hxX
    obtain ⟨τ, hτ, hτcontrol⟩ := exists_perturbation_control g hQcompact
      isOpen_univ P.obstacle_closed (subset_univ _) hg.2
    obtain ⟨g', h, hfix, hnear, hcover, hcompact⟩ :=
      hsingle E P₁ s hsT hcard hother hsavoid (min η τ) (lt_min hη hτ)
    refine ⟨g', h, ⟨?_, ?_⟩, hfix, ?_, hcover, hcompact⟩
    · exact fun x hx => (hfix x hx).trans (hg.1 x hx)
    · exact (hτcontrol g' (fun x _ => (hnear x).trans_le (min_le_right _ _))).2
    · exact fun x => (hnear x).trans_le (min_le_left _ _)
  obtain ⟨g, h, hg, hfix, hnear, hcover, hcompact⟩ := exists_engulfing_of_skeletal_steps
    P.source P.target R P.fixed hH (q + 1) hbound g₀ Good hGood₀
    (h₀.isOpenMap _ P.open_openSet) (fun V => NewmanConnectivity M V p)
    (P.connectivity.image h₀) (fun _ e hconn => hconn.image e) hcover₀ hstep (half_pos hε)
  refine ⟨g, h₀.trans h, hg.1, ?_, ?_, isCompact_closure_moved_trans h₀ h hcompact₀ hcompact⟩
  · intro x
    calc
      dist (g x) (P.map x) ≤ dist (g x) (g₀ x) + dist (g₀ x) (P.map x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hnear x)
        ((hnear₀ x).trans_le (min_le_left _ _))
      _ = ε := add_halves ε
  · intro x hx
    obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hcover hx
    exact ⟨z, hz, hy⟩

theorem relativeNewmanAt_succ
    (hlower : relativeNewmanAt M n p q) (hsingle : singleSimplexNewmanAt M n p q) :
    relativeNewmanAt M n p (q + 1) := by
  intro E _ _ _ P ε hε
  classical
  obtain ⟨N, hsep⟩ := exists_barycentric_subdivision_separating P.source P.source_finite
    P.map P.open_openSet P.obstacle_closed P.obstacle_subset
  let G := barycentricSubdivisionIter P.source N
  let L := barycentricSubdivisionIter P.fixed N
  let H := barycentricSubdivisionIter P.target N
  have hGspace : G.space = P.source.space := barycentricSubdivisionIter_space _ _
  have hLspace : L.space = P.fixed.space := barycentricSubdivisionIter_space _ _
  have hHspace : H.space = P.target.space := barycentricSubdivisionIter_space _ _
  let e : G.space ≃ₜ P.source.space := Homeomorph.setCongr hGspace
  let f : C(G.space, M) := P.map.comp ⟨e, e.continuous⟩
  have hf (x : G.space) : f x = P.map ⟨x.1, hGspace ▸ x.2⟩ := rfl
  have hfixinj : InjOn f (Subtype.val ⁻¹' L.space) := by
    intro x hx y hy hxy
    have hxL : (e x).1 ∈ P.fixed.space := by
      change x.1 ∈ P.fixed.space
      rwa [← hLspace]
    have hyL : (e y).1 ∈ P.fixed.space := by
      change y.1 ∈ P.fixed.space
      rwa [← hLspace]
    exact e.injective (P.fixed_injective hxL hyL hxy)
  let P' : NewmanProblem E M n p (q + 1) :=
    { source := G
      fixed := L
      target := H
      source_finite := barycentricSubdivisionIter_finite_faces _ P.source_finite N
      fixed_subcomplex := barycentricSubdivisionIter_faces_subset P.fixed_subcomplex N
      target_subcomplex := barycentricSubdivisionIter_faces_subset P.target_subcomplex N
      source_dimension := barycentricSubdivisionIter_face_card_le_nat _ P.source_dimension N
      target_dimension := barycentricSubdivisionIter_face_card_le_nat _ P.target_dimension N
      map := f
      fixed_injective := hfixinj
      obstacle := P.obstacle
      openSet := P.openSet
      obstacle_closed := P.obstacle_closed
      open_openSet := P.open_openSet
      obstacle_subset := P.obstacle_subset
      localData := P.localData.refine G L hGspace
        (barycentricSubdivisionIter_refines _ N) (by rw [hLspace]) f hf
      codimension := P.codimension
      connectivity := P.connectivity
      decomposition := P.decomposition.subdivide N f hf }
  have hsep' : ∀ s ∈ P'.target.faces,
      (∀ x : P'.source.space, x.1 ∈ convexHull ℝ (s : Set E) → P'.map x ∈ P'.openSet) ∨
      Disjoint (P'.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P'.obstacle := by
    intro s hs
    rcases hsep s (P'.target_subcomplex hs) with hcovered | havoid
    · exact Or.inl (fun x hx => hcovered (e x) hx)
    · refine Or.inr (disjoint_left.mpr ?_)
      rintro y ⟨x, hx, rfl⟩ hyX
      exact disjoint_left.mp havoid ⟨e x, hx, rfl⟩ hyX
  obtain ⟨g, h, hfix, hnear, hcover, hcompact⟩ :=
    newmanConclusion_of_separated_faces hlower hsingle P' hsep' hε
  let g' : C(P.source.space, M) := g.comp ⟨e.symm, e.symm.continuous⟩
  refine ⟨g', h, ?_, ?_, ?_, hcompact⟩
  · intro x hx
    have hxL : (e.symm x).1 ∈ L.space := by
      rw [hLspace]
      exact hx
    change g (e.symm x) = P.map x
    rw [hfix (e.symm x) hxL]
    change P.map (e (e.symm x)) = P.map x
    rw [e.apply_symm_apply]
  · intro x
    have hnx := hnear (e.symm x)
    change dist (g (e.symm x)) (P.map (e (e.symm x))) < ε at hnx
    change dist (g (e.symm x)) (P.map x) < ε
    simpa only [e.apply_symm_apply] using hnx
  · intro y hy
    rcases hy with hyX | ⟨x, hx, rfl⟩
    · exact hcover (Or.inl hyX)
    · apply hcover
      refine Or.inr ⟨e.symm x, ?_, rfl⟩
      change (e.symm x).1 ∈ H.space
      rw [hHspace]
      exact hx

theorem relativeNewmanAt_of_singleSimplex_steps
    (hstep : ∀ q : ℕ, relativeNewmanAt M n p q → singleSimplexNewmanAt M n p q) :
    ∀ q : ℕ, relativeNewmanAt M n p q := by
  intro q
  induction q with
  | zero => exact relativeNewmanAt_zero M n p
  | succ q ih => exact relativeNewmanAt_succ ih (hstep q ih)

theorem relativeNewmanAt_of_singleSimplex_steps_le
    (hstep : ∀ q : ℕ, q ≤ p → relativeNewmanAt M n p q → singleSimplexNewmanAt M n p q) :
    ∀ q : ℕ, relativeNewmanAt M n p q := by
  apply relativeNewmanAt_of_singleSimplex_steps
  intro q hq
  by_cases hqp : q ≤ p
  · exact hstep q hqp hq
  · exact singleSimplexNewmanAt_of_lt M (by omega)

end DifferentialGeometry.Topology.Engulfing
