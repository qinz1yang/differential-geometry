import DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapSphereFilling
import DifferentialGeometry.Topology.ClosedBallComplement
import DifferentialGeometry.Topology.SphereSeparation.SideClosureDisjoint
import DifferentialGeometry.Topology.ThreeManifold.AntipodalPresentation
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCover
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.LocallyFinite.Frontier
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private theorem disjoint_interior_of_frontier_subset_of_anchor
    {X : Type*} [TopologicalSpace X] {W K U : Set X}
    (hK : IsClosed K) (hKU : K ⊆ U)
    (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier K ⊆ frontier W)
    (hanchor : (W \ U).Nonempty) : Disjoint (interior K) W := by
  have hav : interior W ⊆ (frontier K)ᶜ := by
    intro x hx hxf
    exact (hfront hxf).2 hx
  have hsplit : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [compl_frontier_eq_union_interior,hK.isOpen_compl.interior_eq]
  rcases hconn.subset_or_subset isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) (hav.trans hsplit.subset) with hin | hout
  · have hWK : W ⊆ K := by
      rw [← hregular]
      exact closure_minimal (hin.trans interior_subset) hK
    obtain ⟨x,hxW,hxU⟩ := hanchor
    exact (hxU (hKU (hWK hxW))).elim
  · have hWout : W ⊆ (interior K)ᶜ := by
      rw [← hregular]
      simpa only [closure_compl] using closure_mono hout
    exact disjoint_right.mpr (fun x hxW hxK => hWout hxW hxK)


private theorem finite_fill_eq_of_frontier
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {W Ω : Set X} (K : ι → Set X)
    (hWreg : closure (interior W) = W) (hΩreg : closure (interior Ω) = Ω)
    (hΩconn : IsPreconnected (interior Ω)) (hWne : (interior W).Nonempty)
    (hW : W ⊆ Ω) (hK : ∀ i, IsClosed (K i)) (hKin : ∀ i, K i ⊆ interior Ω)
    (hfront : frontier W = frontier Ω ∪ ⋃ i, frontier (K i))
    (hfill : ∀ i, frontier (K i) ⊆ interior (W ∪ K i)) :
    W ∪ ⋃ i, K i = Ω := by
  let V := W ∪ ⋃ i, K i
  have hVc : IsClosed V := (hWreg ▸ isClosed_closure).union (isClosed_iUnion_of_finite hK)
  have hfrontV : frontier V ⊆ frontier Ω := by
    intro x hx
    have hunion := frontier_union_subset W (⋃ i, K i) hx
    rcases hunion with h | h
    · rcases hfront ▸ h.1 with hxΩ | hxi
      · exact hxΩ
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hxi
        exact (hx.2 (interior_mono (union_subset_union_right W (subset_iUnion K i)) (hfill i hi))).elim
    · have hsub := (locallyFinite_of_finite K).frontier_iUnion_subset h.2
      obtain ⟨i,hi⟩ := mem_iUnion.mp hsub
      exact (hx.2 (interior_mono (union_subset_union_right W (subset_iUnion K i)) (hfill i hi))).elim
  have hVsub : V ⊆ Ω := union_subset hW (iUnion_subset (fun i => (hKin i).trans interior_subset))
  have havoid : Disjoint (interior Ω) (frontier V) :=
    disjoint_interior_frontier.mono_right hfrontV
  obtain ⟨x,hx⟩ := hWne
  have hΩV : interior Ω ⊆ interior V :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hΩconn havoid
      ⟨x,interior_mono hW hx,interior_mono subset_union_left hx⟩
  apply Subset.antisymm hVsub
  rw [← hΩreg]
  exact closure_minimal (hΩV.trans interior_subset) hVc


end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

section

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]

private theorem nonempty_inter_ball_complements_of_antipodal_presentation
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hsurj : Surjective p)
    (hfibers : ∀ x y : S3,
      p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (B₀ B₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hB₀ : Metric.closedBall (0 : E3) 1 ⊆ B₀.source)
    (hB₁ : Metric.closedBall (0 : E3) 1 ⊆ B₁.source) :
    ((B₀ '' Metric.ball (0 : E3) 1)ᶜ ∩
      (B₁ '' Metric.ball (0 : E3) 1)ᶜ).Nonempty := by
  obtain ⟨e₀, _, _⟩ := SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation
    p hp hsurj hfibers
  by_contra h
  have hcover : B₀ '' Metric.closedBall (0 : E3) 1 ∪
      B₁ '' Metric.closedBall (0 : E3) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ B₀ '' Metric.ball (0 : E3) 1
    · exact Or.inl (image_mono Metric.ball_subset_closedBall hx)
    · have hx' : x ∈ B₁ '' Metric.ball (0 : E3) 1 := by
        by_contra hn
        exact h ⟨x, hx, hn⟩
      exact Or.inr (image_mono Metric.ball_subset_closedBall hx')
  let A₀ := B₀.trans e₀.symm.toPartialDiffeomorph
  let A₁ := B₁.trans e₀.symm.toPartialDiffeomorph
  have hA₀ : Metric.closedBall (0 : E3) 1 ⊆ A₀.source :=
    fun x hx => ⟨hB₀ hx, mem_univ _⟩
  have hA₁ : Metric.closedBall (0 : E3) 1 ⊆ A₁.source :=
    fun x hx => ⟨hB₁ hx, mem_univ _⟩
  have hAc : A₀ '' Metric.closedBall (0 : E3) 1 ∪
      A₁ '' Metric.closedBall (0 : E3) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : e₀ x ∈ B₀ '' Metric.closedBall (0 : E3) 1 ∪
        B₁ '' Metric.closedBall (0 : E3) 1 := hcover.symm ▸ mem_univ _
    rcases hx with ⟨y, hy, he⟩ | ⟨y, hy, he⟩
    · exact Or.inl ⟨y, hy, (congrArg e₀.symm he).trans (e₀.symm_apply_apply x)⟩
    · exact Or.inr ⟨y, hy, (congrArg e₀.symm he).trans (e₀.symm_apply_apply x)⟩
  obtain ⟨e, _⟩ := Manifold.exists_sphere_diffeomorph_of_ball_chart_cover
    A₁ A₀ hA₁ hA₀ hAc
  let _ : SimplyConnectedSpace SphericalSpaceFormGroup.antipodal.manifold.Carrier :=
    e.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  exact SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal
    (Classical.choice inferInstance) inferInstance


end

section

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z]
  [PreconnectedSpace Z]

omit [T2Space M] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [PreconnectedSpace Z] in
private theorem interior_ball_side_connected
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hF : B '' closedBall (0 : E3) 1 ⊆ F.source) :
    interior (F '' (B '' closedBall (0 : E3) 1)) = F '' (B '' ball (0 : E3) 1) ∧
      IsConnected (interior (F '' (B '' closedBall (0 : E3) 1))) := by
  have hBi : interior (B '' closedBall (0 : E3) 1) = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hFi : interior (F '' (B '' closedBall (0 : E3) 1)) = F '' (B '' ball (0 : E3) 1) := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    rw [hBi] at h
    exact h.symm
  refine ⟨hFi,?_⟩
  rw [hFi]
  apply IsConnected.image
    (((convex_ball (0 : E3) 1).isConnected ⟨0,by simp⟩).image B
      (B.contMDiffOn_toFun.continuousOn.mono (ball_subset_closedBall.trans hB)))
  exact F.contMDiffOn_toFun.continuousOn.mono ((image_mono ball_subset_closedBall).trans hF)

omit [T2Space M] [IsManifold (𝓡 3) ∞ Z] in
private theorem interior_projective_side_connected
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hF : (B '' ball (0 : E3) 1)ᶜ ⊆ F.source) :
    interior (F '' (B '' ball (0 : E3) 1)ᶜ) = F '' (B '' closedBall (0 : E3) 1)ᶜ ∧
      IsConnected (interior (F '' (B '' ball (0 : E3) 1)ᶜ)) := by
  have hBi : interior (B '' ball (0 : E3) 1)ᶜ = (B '' closedBall (0 : E3) 1)ᶜ := by
    rw [interior_compl,DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB]
  have hFi : interior (F '' (B '' ball (0 : E3) 1)ᶜ) = F '' (B '' closedBall (0 : E3) 1)ᶜ := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    rw [hBi] at h
    exact h.symm
  let _ : LocallyPathConnectedSpace Z := ChartedSpace.locallyPathConnectedSpace E3 Z
  have hconn := (DifferentialGeometry.Topology.isPathConnected_compl_image_closedBall
    B.toOpenPartialHomeomorph (Module.one_lt_rank_of_one_lt_finrank (by simp [E3]))
      (by norm_num : (0 : ℝ) ≤ 1) hB).isConnected
  refine ⟨hFi,?_⟩
  rw [hFi]
  exact hconn.image F (F.contMDiffOn_toFun.continuousOn.mono
    ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hF))


end

section

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z]

theorem exists_pairwise_disjoint_projective_cap_holes_of_spherical_frontier
    {ι : Type*}
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hF : (C '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    {W : Set M} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (e : ι → S2 → M) (he : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (e i))
    (hinside : ∀ i, range (e i) ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ))
    (hfront : ∀ i, range (e i) ⊆ frontier W)
    (houter : (F '' (C '' sphere (0 : E3) 1) ∩ W).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (range (e i)) (range (e j)))) :
    ∃ (K : ι → Set M) (B : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞),
      (∀ i, closedBall (0 : E3) 1 ⊆ (B i).source) ∧
      (∀ i, F '' (B i '' sphere (0 : E3) 1) = range (e i)) ∧
      (∀ i, (B i '' closedBall (0 : E3) 1 ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' closedBall (0 : E3) 1) = K i ∧
        F '' (B i '' ball (0 : E3) 1) = interior (K i)) ∨
        ((B i '' ball (0 : E3) 1)ᶜ ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' ball (0 : E3) 1)ᶜ = K i ∧
        F '' (B i '' closedBall (0 : E3) 1)ᶜ = interior (K i))) ∧
      (∀ i, IsCompact (K i)) ∧ (∀ i, closure (interior (K i)) = K i) ∧
      (∀ i, frontier (K i) = range (e i)) ∧
      (∀ i, K i ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ)) ∧
      (∀ i, IsConnected (interior (K i))) ∧
      (∀ i, Disjoint (interior (K i)) W) ∧
      Pairwise (fun i j => Disjoint (K i) (K j)) ∧
      ∀ i j, F '' (B i '' ball (0 : E3) 1)ᶜ = K i →
        F '' (B j '' ball (0 : E3) 1)ᶜ = K j → i = j := by
  classical
  let _ : ConnectedSpace S3 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E4])) 0 zero_le_one)
  let _ : ConnectedSpace Z := honto.connectedSpace hp.contMDiff.continuous
  let _ : CompactSpace Z := honto.compactSpace hp.contMDiff.continuous
  choose K B hB hBs hmodel hcompact hreg hKfront hKinside using fun i =>
    exists_compact_side_inside_projective_cap_of_sphere_embedding
      p hp honto hfib C F hC hF (e i) (he i) (hinside i)
  have hbranches (i : ι) :
      (B i '' closedBall (0 : E3) 1 ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' closedBall (0 : E3) 1) = K i ∧
        F '' (B i '' ball (0 : E3) 1) = interior (K i)) ∨
      ((B i '' ball (0 : E3) 1)ᶜ ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' ball (0 : E3) 1)ᶜ = K i ∧
        F '' (B i '' closedBall (0 : E3) 1)ᶜ = interior (K i)) := by
    rcases hmodel i with ⟨hKi,hside⟩ | ⟨hKi,hside⟩
    · have hs : B i '' closedBall (0 : E3) 1 ⊆ F.source :=
        hside.trans ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hF)
      exact Or.inl ⟨hside,hKi.symm,(interior_ball_side_connected (B i) F (hB i) hs).1.symm.trans (congrArg interior hKi.symm)⟩
    · have hs : (B i '' ball (0 : E3) 1)ᶜ ⊆ F.source :=
        hside.trans ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hF)
      exact Or.inr ⟨hside,hKi.symm,(interior_projective_side_connected (B i) F (hB i) hs).1.symm.trans (congrArg interior hKi.symm)⟩
  have hconnected (i : ι) : IsConnected (interior (K i)) := by
    rcases hmodel i with ⟨hKi,hside⟩ | ⟨hKi,hside⟩
    · rw [hKi]
      exact (interior_ball_side_connected (B i) F (hB i)
        (hside.trans ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hF))).2
    · rw [hKi]
      exact (interior_projective_side_connected (B i) F (hB i)
        (hside.trans ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hF))).2
  have hCc : IsCompact (C '' ball (0 : E3) 1)ᶜ :=
    (C.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hC)).isClosed_compl.isCompact
  have hparentfront : F '' (C '' sphere (0 : E3) 1) = frontier (F '' (C '' ball (0 : E3) 1)ᶜ) :=
    DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement C F hC hCc hF
  have hanchor : (W \ interior (F '' (C '' ball (0 : E3) 1)ᶜ)).Nonempty := by
    obtain ⟨x,hx,hxW⟩ := houter
    exact ⟨x,hxW,(hparentfront ▸ hx).2⟩
  have hKW (i : ι) : Disjoint (interior (K i)) W :=
    disjoint_interior_of_frontier_subset_of_anchor (hcompact i).isClosed (hKinside i)
      hregular hconn ((hKfront i).subset.trans (hfront i)) hanchor
  have hcl (i : ι) : closure (interior (K i)) = interior (K i) ∪ range (e i) := by
    rw [hreg i,← hKfront i,← closure_eq_interior_union_frontier,(hcompact i).isClosed.closure_eq]
  have hpair := DifferentialGeometry.Topology.SphereSeparation.pairwise_disjoint_closure_of_isOpen_side
    (fun i => isOpen_interior) hconnected
    (fun i => (hfront i).trans ((hregular ▸ isClosed_closure).frontier_subset)) hKW hcl hdis
    (fun i => range_nonempty (e i))
  have hpairK : Pairwise (fun i j => Disjoint (K i) (K j)) :=
    fun i j hij => by simpa only [hreg] using hpair hij
  refine ⟨K,B,hB,hBs,hbranches,hcompact,hreg,hKfront,hKinside,hconnected,hKW,hpairK,?_⟩
  intro i j hi hj
  by_contra hij
  obtain ⟨z,hzi,hzj⟩ := nonempty_inter_ball_complements_of_antipodal_presentation
    p hp honto hfib (B i) (B j) (hB i) (hB j)
  exact disjoint_left.mp (hpairK hij) (hi ▸ mem_image_of_mem F hzi)
    (hj ▸ mem_image_of_mem F hzj)


end

section

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z]

omit [T2Space M] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] in
private theorem sphere_subset_interior_union_of_projective_model_boundary
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hF : B '' sphere (0 : E3) 1 ⊆ F.source)
    {W K R : Set M} (hW : closure (interior W) = W)
    (hK : closure (interior K) = K) (houtside : Disjoint (interior K) W)
    (hR : IsClosed R)
    (hfrontW : frontier W = F '' (B '' sphere (0 : E3) 1) ∪ R)
    (hfrontK : frontier K = F '' (B '' sphere (0 : E3) 1))
    (hdis : Disjoint (F '' (B '' sphere (0 : E3) 1)) R) :
    frontier K ⊆ interior (W ∪ K) := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  let _ : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let shift : (S2 × ℝ) ≃ₜ (S2 × ℝ) :=
    { toFun := fun q => (q.1,1+q.2)
      invFun := fun q => (q.1,q.2-1)
      left_inv := by intro q; ext <;> simp
      right_inv := by intro q; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := shift.transOpenPartialHomeomorph
    (((DifferentialGeometry.Topology.Manifold.spherePolarChart (n := 2) v).trans B).trans F).toOpenPartialHomeomorph
  have hz (q : S2) : T (q,0) = F (B q.val) := by
    change F (B ((1+(0:ℝ)) • q.val)) = _
    simp
  have hs (q : S2) : (q,(0:ℝ)) ∈ T.source := by
    change (q,1+(0:ℝ)) ∈ (((DifferentialGeometry.Topology.Manifold.spherePolarChart (n := 2) v).trans B).trans F).source
    refine ⟨⟨by norm_num [DifferentialGeometry.Topology.Manifold.spherePolarChart],?_⟩,?_⟩
    · change (1+(0:ℝ)) • q.val ∈ B.source
      simpa using hB (sphere_subset_closedBall q.property)
    · change B ((1+(0:ℝ)) • q.val) ∈ F.source
      simpa using hF (mem_image_of_mem B q.property)
  have hrange : range (fun q : S2 => T (q,0)) = F '' (B '' sphere (0 : E3) 1) := by
    simp only [hz]
    change range ((F : Z → M) ∘ (B : E3 → Z) ∘ (Subtype.val : S2 → E3)) = _
    rw [range_comp,range_comp,Subtype.range_val]
  let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) 0 zero_le_one)
  have h := DifferentialGeometry.Topology.fill_of_shared_cylinder_boundary_of_disjoint_interiors
    T hs hW hK (houtside.symm.mono_left interior_subset) hR
    (by rw [hrange];exact hfrontW) (hfrontK.trans hrange.symm) (hrange.symm ▸ hdis)
  rw [hfrontK,← hrange]
  exact h.2.2.2


end

section

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z]

theorem exists_finite_disjoint_projective_cap_holes_of_spherical_frontier
    {ι : Type*} [Finite ι]
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hF : (C '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    {W : Set M} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hW : W ⊆ F '' (C '' ball (0 : E3) 1)ᶜ)
    (e : ι → S2 → M) (he : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (e i))
    (hinside : ∀ i, range (e i) ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ))
    (hfront : frontier W = F '' (C '' sphere (0 : E3) 1) ∪ ⋃ i, range (e i))
    (hdis : Pairwise (fun i j => Disjoint (range (e i)) (range (e j)))) :
    ∃ (K : ι → Set M) (B : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞),
      (∀ i, closedBall (0 : E3) 1 ⊆ (B i).source) ∧
      (∀ i, F '' (B i '' sphere (0 : E3) 1) = range (e i)) ∧
      (∀ i, (B i '' closedBall (0 : E3) 1 ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' closedBall (0 : E3) 1) = K i ∧
        F '' (B i '' ball (0 : E3) 1) = interior (K i)) ∨
        ((B i '' ball (0 : E3) 1)ᶜ ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∧
        F '' (B i '' ball (0 : E3) 1)ᶜ = K i ∧
        F '' (B i '' closedBall (0 : E3) 1)ᶜ = interior (K i))) ∧
      (∀ i, IsCompact (K i)) ∧ (∀ i, closure (interior (K i)) = K i) ∧
      (∀ i, frontier (K i) = range (e i)) ∧
      (∀ i, K i ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ)) ∧
      (∀ i, IsConnected (interior (K i))) ∧
      (∀ i, Disjoint (interior (K i)) W) ∧
      Pairwise (fun i j => Disjoint (K i) (K j)) ∧
      (∀ i j, F '' (B i '' ball (0 : E3) 1)ᶜ = K i →
        F '' (B j '' ball (0 : E3) 1)ᶜ = K j → i = j) ∧
      W ∪ ⋃ i, K i = F '' (C '' ball (0 : E3) 1)ᶜ ∧
      W = F '' (C '' ball (0 : E3) 1)ᶜ \ ⋃ i, interior (K i) := by
  classical
  let _ : ConnectedSpace S3 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E4])) 0 zero_le_one)
  let _ : ConnectedSpace Z := honto.connectedSpace hp.contMDiff.continuous
  let _ : CompactSpace Z := honto.compactSpace hp.contMDiff.continuous
  let Ω := F '' (C '' ball (0 : E3) 1)ᶜ
  have hWc : IsClosed W := hregular ▸ isClosed_closure
  have hΩc0 : IsCompact (C '' ball (0 : E3) 1)ᶜ :=
    (C.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hC)).isClosed_compl.isCompact
  have hΩc : IsCompact Ω := hΩc0.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hF)
  have hΩf : frontier Ω = F '' (C '' sphere (0 : E3) 1) :=
    (DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement C F hC hΩc0 hF).symm
  have hΩreg0 : closure (interior (C '' ball (0 : E3) 1)ᶜ) = (C '' ball (0 : E3) 1)ᶜ := by
    rw [interior_compl,DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC,
      closure_compl]
    have hh := C.toOpenPartialHomeomorph.image_interior_of_subset_source hC
    change C '' interior (closedBall (0 : E3) 1) = interior (C '' closedBall (0 : E3) 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    rw [← hh]
  have hΩreg : closure (interior Ω) = Ω :=
    F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hF hΩreg0 hΩc.isClosed
  have hΩconn : IsPreconnected (interior Ω) :=
    (interior_projective_side_connected C F hC hF).2.isPreconnected
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  have houterW : F '' (C '' sphere (0 : E3) 1) ⊆ W :=
    fun x hx => hWc.frontier_subset (hfront.symm ▸ Or.inl hx)
  have houter : (F '' (C '' sphere (0 : E3) 1) ∩ W).Nonempty :=
    ⟨F (C v),⟨C v,⟨v,v.property,rfl⟩,rfl⟩,houterW ⟨C v,⟨v,v.property,rfl⟩,rfl⟩⟩
  obtain ⟨K,B,hB,hBs,hmodel,hKc,hKr,hKf,hKin,hKconn,hKW,hpair,hunique⟩ :=
    exists_pairwise_disjoint_projective_cap_holes_of_spherical_frontier p hp honto hfib C F hC hF
      hregular hconn e he hinside (fun i x hx => hfront.symm ▸ Or.inr (mem_iUnion.mpr ⟨i,hx⟩)) houter hdis
  have hFbs (i : ι) : B i '' sphere (0 : E3) 1 ⊆ F.source := by
    intro z hz
    rcases hmodel i with h | h
    · exact hF (fun hzC => h.1 (image_mono sphere_subset_closedBall hz) (image_mono ball_subset_closedBall hzC))
    · have hznot : z ∈ (B i '' ball (0 : E3) 1)ᶜ := by
        rcases hz with ⟨w,hw,rfl⟩
        rintro ⟨u,hu,heq⟩
        have hew := (B i).injOn ((hB i) (ball_subset_closedBall hu)) ((hB i) (sphere_subset_closedBall hw)) heq
        exact (mem_ball_zero_iff.mp (hew ▸ hu)).ne (mem_sphere_zero_iff_norm.mp hw)
      exact hF (fun hzC => h.1 hznot (image_mono ball_subset_closedBall hzC))
  have hCsdis (i : ι) : Disjoint (range (e i)) (F '' (C '' sphere (0 : E3) 1)) := by
    rw [← hΩf]
    exact disjoint_interior_frontier.mono_left (hinside i)
  have hfill (i : ι) : frontier (K i) ⊆ interior (W ∪ K i) := by
    let R := F '' (C '' sphere (0 : E3) 1) ∪ ⋃ j : {j // j ≠ i}, range (e j.val)
    have hRc : IsClosed R :=
      (hΩf ▸ isClosed_frontier).union
        (isClosed_iUnion_of_finite fun j => (isCompact_range (he j.val).contMDiff.continuous).isClosed)
    have hfr : frontier W = F '' (B i '' sphere (0 : E3) 1) ∪ R := by
      rw [hfront,hBs i]
      ext x
      constructor
      · rintro (hx | hx)
        · exact Or.inr (Or.inl hx)
        · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
          by_cases hji : j=i
          · exact Or.inl (hji ▸ hj)
          · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩))
      · rintro (hx | hx | hx)
        · exact Or.inr (mem_iUnion.mpr ⟨i,hx⟩)
        · exact Or.inl hx
        · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
          exact Or.inr (mem_iUnion.mpr ⟨j.val,hj⟩)
    have hd : Disjoint (F '' (B i '' sphere (0 : E3) 1)) R := by
      rw [hBs i]
      exact (hCsdis i).union_right (disjoint_iUnion_right.mpr (fun j => hdis j.property.symm))
    exact sphere_subset_interior_union_of_projective_model_boundary (B i) F (hB i) (hFbs i)
      hregular (hKr i) (hKW i) hRc hfr ((hKf i).trans (hBs i).symm) hd
  have hfilled : W ∪ ⋃ i, K i = Ω := by
    apply finite_fill_eq_of_frontier K hregular hΩreg hΩconn
      (closure_nonempty_iff.mp (hregular.symm ▸ (houter.mono fun _ hx => hx.2))) hW
      (fun i => (hKc i).isClosed) hKin
    · rw [hΩf]
      simp only [hKf]
      exact hfront
    · exact hfill
  refine ⟨K,B,hB,hBs,hmodel,hKc,hKr,hKf,hKin,hKconn,hKW,hpair,hunique,hfilled,?_⟩
  apply subset_antisymm
  · intro x hx
    exact ⟨hW hx,fun hh => by obtain ⟨i,hi⟩ := mem_iUnion.mp hh; exact disjoint_left.mp (hKW i) hi hx⟩
  · rintro x ⟨hx,hholes⟩
    have hxV : x ∈ W ∪ ⋃ i, K i := hfilled.symm ▸ (show x ∈ Ω from hx)
    rcases hxV with hx | hx
    · exact hx
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      have hfi : x ∈ frontier (K i) := (mem_frontier_iff_notMem_interior hi).mpr
        (fun hh => hholes (mem_iUnion.mpr ⟨i,hh⟩))
      exact hWc.frontier_subset (hfront.symm ▸ Or.inr (mem_iUnion.mpr ⟨i,hKf i ▸ hfi⟩))


end

end DifferentialGeometry.Topology.ThreeManifold
