import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import DifferentialGeometry.Topology.PuncturedConnected

section
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem capCore_isConnected_image_closedBall
    (F : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (h : Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source) :
    IsConnected (F '' Metric.closedBall (0 : ThreeSpace) 1) :=
  ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩).image (F : ThreeSpace → M)
    (F.contMDiffOn_toFun.continuousOn.mono h)

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CapCore.isCompact_carrier {X : Set M} (c : CapCore X) : IsCompact X := by
  cases c with
  | ball F h hx =>
    rw [← hx]
    exact (isCompact_closedBall (0 : ThreeSpace) 1).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono h)
  | projective Z pr ball hb F hc hx =>
    rw [← hx]
    have hsub : Metric.ball (0 : ThreeSpace) 1 ⊆ ball.source :=
      ((Metric.ball_subset_closedBall :
          Metric.ball (0 : ThreeSpace) 1 ⊆ Metric.closedBall (0 : ThreeSpace) 1).trans
        (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))).trans hb
    have hopen : IsOpen (ball '' Metric.ball (0 : ThreeSpace) 1) :=
      DifferentialGeometry.image_opens_isOpen ball
        (U := ⟨Metric.ball (0 : ThreeSpace) 1, Metric.isOpen_ball⟩) hsub
    exact (hopen.isClosed_compl.isCompact).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono hc)

omit [IsManifold I3 ∞ M] [SigmaCompactSpace M] in
open Metric in
theorem CapCore.closure_interior_carrier {X : Set M} (cap : CapCore X) :
    closure (interior X) = X := by
  have hXclosed : IsClosed X := cap.isCompact_carrier.isClosed
  cases cap with
  | ball F hF hX =>
    rw [← hX] at hXclosed ⊢
    apply F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hF ?_ hXclosed
    rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]
  | projective Z pr b hb F hF hX =>
    have hb1 : closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    have hbint : interior (b '' closedBall (0 : ThreeSpace) 1) =
        b '' Metric.ball (0 : ThreeSpace) 1 := by
      have h := b.toOpenPartialHomeomorph.image_interior_of_subset_source hb1
      change b '' interior (closedBall (0 : ThreeSpace) 1) =
        interior (b '' closedBall (0 : ThreeSpace) 1) at h
      rw [interior_closedBall _ one_ne_zero] at h
      exact h.symm
    have hbreg : closure (interior (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ) =
        (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ := by
      rw [interior_compl,
        DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph b hb1,
        closure_compl, hbint]
    rw [← hX] at hXclosed ⊢
    exact F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hF hbreg hXclosed


omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CapCore.nonempty_carrier {X : Set M} (c : CapCore X) : X.Nonempty := by
  cases c with
  | ball F h hx =>
    rw [← hx]
    exact Set.Nonempty.image F ⟨0, by simp⟩
  | projective Z pr ball hb F hc hx =>
    rw [← hx]
    have hsource : (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace) ∈ ball.source := by
      apply hb
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp [PiLp.norm_single]
    have hdist : dist (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace) (0 : ThreeSpace) = 2 := by
      rw [dist_eq_norm]
      simp [PiLp.norm_single]
    have hnot : ball (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace) ∉
        ball '' Metric.ball (0 : ThreeSpace) 1 := by
      rintro ⟨y, hy, hzy⟩
      have hy1 : y ∈ Metric.closedBall (0 : ThreeSpace) 1 := Metric.ball_subset_closedBall hy
      have hy2 : y ∈ Metric.closedBall (0 : ThreeSpace) 2 :=
        Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hy1
      have hys : y ∈ ball.source := hb hy2
      have hyz : y = (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace) := by
        calc y = ball.symm (ball y) := (ball.left_inv' hys).symm
          _ = ball.symm (ball (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace)) := by rw [hzy]
          _ = (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace) := ball.left_inv' hsource
      rw [hyz, Metric.mem_ball, hdist] at hy
      norm_num at hy
    exact ⟨F (ball (EuclideanSpace.single 0 (2 : ℝ) : ThreeSpace)), _,
      ⟨hnot, rfl⟩⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem capCore_closedBall_self :
    Nonempty (CapCore (M := ThreeSpace) (Metric.closedBall (0 : ThreeSpace) 1)) :=
  ⟨CapCore.ball (PartialDiffeomorph.refl (I := I3) ThreeSpace)
    (by intro x _; trivial)
    (by
      have hid : ((PartialDiffeomorph.refl (I := I3) ThreeSpace : ThreeSpace → ThreeSpace)) =
          id := rfl
      rw [hid, Set.image_id])⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem capCore_image_closedBall (F : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (h : Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source) :
    Nonempty (CapCore (F '' Metric.closedBall (0 : ThreeSpace) 1)) :=
  ⟨CapCore.ball F h rfl⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CapCore.image_of_partialDiffeomorph
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    {X : Set M} (c : CapCore X) (e : PartialDiffeomorph I3 I3 M N ∞) (he : X ⊆ e.source) :
    Nonempty (CapCore (e '' X)) := by
  cases c with
  | ball F h hx =>
    rw [← hx]
    exact ⟨CapCore.ball (PartialDiffeomorph.trans F e)
      (fun y hy => ⟨h hy, he (hx ▸ ⟨y, hy, rfl⟩)⟩) (by rw [Set.image_image]; rfl)⟩
  | projective Z pr ball hb F hc hx =>
    rw [← hx]
    exact ⟨CapCore.projective Z pr ball hb (PartialDiffeomorph.trans F e)
      (fun y hy => ⟨hc hy, he (hx ▸ ⟨y, hy, rfl⟩)⟩) (by rw [Set.image_image]; rfl)⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CapCore.nonempty_preimage_open {X : Set M} (cap : CapCore X)
    (O : TopologicalSpace.Opens M) (hXO : X ⊆ O) :
    Nonempty (CapCore (Subtype.val ⁻¹' X : Set O)) := by
  obtain ⟨x, hx⟩ := cap.nonempty_carrier
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) O
    ⟨⟨x, hXO hx⟩⟩
  have hinc_target : inc.target = (O : Set M) :=
    O.openPartialHomeomorphSubtypeCoe_target _
  have himage : inc.symm '' X = (Subtype.val ⁻¹' X : Set O) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change inc (inc.symm z) ∈ X
      have ht : z ∈ inc.target := hinc_target.symm ▸ hXO hz
      exact (inc.right_inv' ht).symm ▸ hz
    · intro hy
      exact ⟨y.val, hy, inc.left_inv' (mem_univ y)⟩
  rw [← himage]
  apply cap.image_of_partialDiffeomorph inc.symm
  intro y hy
  change y ∈ inc.target
  exact hinc_target.symm ▸ hXO hy


omit [T2Space M] [SigmaCompactSpace M] in
theorem metricDistance_ge_of_not_mem_riemannianBallOf [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I3 M) {x y : M} {r : ℝ}
    (h : y ∉ riemannianBallOf (I := I3) g x r) :
    r ≤ metricDistance g x y :=
  (ENNReal.ofReal_le_iff_le_toReal (riemannianEDistOf_ne_top (I := I3) g x y)).mp
    (not_lt.mp h)

omit [T2Space M] [SigmaCompactSpace M] in
theorem canonicalAlternative_cap_of_tube_disjoint_ball [PreconnectedSpace M]
    {eps C : ℝ} {x : M} {t : ℝ} {U : Set M} {S : SolutionOn (I := I3) (M := M) D}
    (L : LocalCap S eps x t U) {r : ℝ}
    (hr : 10000 / Real.sqrt (S.scalar t x) ≤ r)
    (havoid : ∀ y ∈ L.tube, y ∉ riemannianBallOf (I := I3) (S.base.metric t) x r) :
    Nonempty (CanonicalAlternative S eps C x t U) :=
  ⟨CanonicalAlternative.cap L fun y hy =>
    hr.trans (metricDistance_ge_of_not_mem_riemannianBallOf (S.base.metric t) (havoid y hy))⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem frontier_image_univ_prod_Icc {a b : ℝ} (hab : a ≤ b)
    (Φ : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsub : Set.univ ×ˢ Set.Icc a b ⊆ Φ.source)
    (hci : IsClosed (Φ '' (Set.univ ×ˢ Set.Icc a b))) :
    frontier (Φ '' (Set.univ ×ˢ Set.Icc a b)) = Φ '' (Set.univ ×ˢ ({a, b} : Set ℝ)) := by
  have hImage : Φ.toOpenPartialHomeomorph.IsImage (Set.univ ×ˢ Set.Icc a b)
      (Φ '' (Set.univ ×ˢ Set.Icc a b)) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change Φ '' (Φ.source ∩ (Set.univ ×ˢ Set.Icc a b)) =
      Φ.target ∩ Φ '' (Set.univ ×ˢ Set.Icc a b)
    have ht : Φ '' (Set.univ ×ˢ Set.Icc a b) ⊆ Φ.target := by
      rintro y ⟨x, hx, rfl⟩
      exact Φ.map_source' (hsub hx)
    rw [inter_eq_right.mpr hsub, inter_eq_right.mpr ht]
  have hcs : IsClosed (Set.univ ×ˢ Set.Icc a b : Set Cylinder) :=
    isClosed_univ.prod isClosed_Icc
  have hs0 : frontier (Set.univ ×ˢ Set.Icc a b) ⊆ Φ.source :=
    fun x hx => hsub (hcs.closure_eq ▸ frontier_subset_closure hx)
  have ht0 : frontier (Φ '' (Set.univ ×ˢ Set.Icc a b)) ⊆ Φ '' (Set.univ ×ˢ Set.Icc a b) :=
    fun y hy => hci.closure_eq ▸ frontier_subset_closure hy
  have ht : frontier (Φ '' (Set.univ ×ˢ Set.Icc a b)) ⊆ Φ.target := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := ht0 hy
    exact Φ.map_source' (hsub hx)
  have h := hImage.frontier.image_eq
  change Φ '' (Φ.source ∩ frontier (Set.univ ×ˢ Set.Icc a b)) =
    Φ.target ∩ frontier (Φ '' (Set.univ ×ˢ Set.Icc a b)) at h
  rw [inter_eq_right.mpr hs0, inter_eq_right.mpr ht] at h
  rw [← h, frontier_univ_prod_eq, frontier_Icc hab]

section NeckChain

variable {S : SolutionOn (I := I3) (M := M) D}

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.tube_window_subset_source {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ⊆ nk.map.source := by
  have h1 : (1 : ℝ) < eps⁻¹ := by
    have h : (1 / 11 : ℝ)⁻¹ < eps⁻¹ :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 11) nk.eps_pos).2 nk.eps_small
    norm_num at h
    linarith
  intro y hy
  exact nk.domain ⟨trivial, ⟨by linarith [hy.2.1], by linarith [hy.2.2, h1]⟩⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.self_transition_deriv_pos {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) {z : Cylinder} (hz : z ∈ nk.map.source) :
    0 < fderiv ℝ (fun a : ℝ => (nk.map.symm (nk.map (z.1, a))).2) z.2 1 := by
  have hpre : {a : ℝ | (z.1, a) ∈ nk.map.source} ∈ 𝓝 z.2 :=
    (nk.map.open_source.preimage (by continuity)).mem_nhds hz
  have hev : (fun a : ℝ => (nk.map.symm (nk.map (z.1, a))).2) =ᶠ[𝓝 z.2]
      (fun a : ℝ => a) := by
    refine Filter.eventually_of_mem hpre ?_
    intro a ha
    change (nk.map.symm (nk.map (z.1, a))).2 = a
    exact congrArg Prod.snd (nk.map.left_inv' ha)
  rw [hev.fderiv_eq]
  simp

noncomputable def OrderedNeckChain.single {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    OrderedNeckChain S eps t (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) where
  count := 1
  count_pos := by norm_num
  centers := fun _ => x
  necks := fun _ => nk
  lo := fun _ => 0
  hi := fun _ => 1
  lo_lt_hi := fun _ => by norm_num
  inside := fun _ => nk.tube_window_subset_source
  swept_eq := (Set.iUnion_const _).symm
  transition_increasing := by
    intro i j hij
    simp at hij

noncomputable def OrderedNeckChain.pair {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    OrderedNeckChain S eps t (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) where
  count := 2
  count_pos := by norm_num
  centers := fun _ => x
  necks := fun _ => nk
  lo := fun _ => 0
  hi := fun _ => 1
  lo_lt_hi := fun _ => by norm_num
  inside := fun _ => nk.tube_window_subset_source
  swept_eq := (Set.iUnion_const _).symm
  transition_increasing := by
    intro i j hij z hz _
    exact nk.self_transition_deriv_pos hz

omit [T2Space M] [SigmaCompactSpace M] in
theorem nonempty_orderedNeckChain_of_strongNeck {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    Nonempty (OrderedNeckChain S eps t (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))) :=
  ⟨OrderedNeckChain.single nk⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem OrderedNeckChain.exists_neck_of_mem {eps t : ℝ} {V : Set M}
    (c : OrderedNeckChain S eps t V) {y : M} (hy : y ∈ V) :
    ∃ i : Fin c.count, y ∈ (c.necks i).map '' (Set.univ ×ˢ Set.Icc (c.lo i) (c.hi i)) := by
  rw [c.swept_eq] at hy
  simpa only [Set.mem_iUnion] using hy

omit [SigmaCompactSpace M] in
theorem StrongNeck.frontier_region_eq_union_boundary_spheres {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    frontier nk.region = nk.map '' (Set.univ ×ˢ ({-10} : Set ℝ)) ∪
      nk.map '' (Set.univ ×ˢ ({10} : Set ℝ)) := by
  rw [nk.frontier_region]
  have hset : ({-10, 10} : Set ℝ) = ({-10} : Set ℝ) ∪ {10} := by
    ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  simp only [hset, Set.prod_union, Set.image_union]

omit [SigmaCompactSpace M] in
theorem StrongNeck.frontier_window_eq_union_boundary_spheres {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    frontier (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) =
      nk.map '' (Set.univ ×ˢ ({0} : Set ℝ)) ∪ nk.map '' (Set.univ ×ˢ ({1} : Set ℝ)) := by
  have hsub := nk.tube_window_subset_source
  have hcompact : IsCompact (Set.univ ×ˢ Set.Icc (0 : ℝ) 1 : Set Cylinder) :=
    isCompact_univ.prod isCompact_Icc
  have hci : IsClosed (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (hcompact.image_of_continuousOn (nk.map.contMDiffOn_toFun.continuousOn.mono hsub)).isClosed
  rw [frontier_image_univ_prod_Icc (by norm_num : (0 : ℝ) ≤ 1) nk.map hsub hci]
  have hset : ({0, 1} : Set ℝ) = ({0} : Set ℝ) ∪ {1} := by
    ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  simp only [hset, Set.prod_union, Set.image_union]

omit [T2Space M] [SigmaCompactSpace M] in
theorem OrderedNeckChain.isCompact_swept {eps t : ℝ} {V : Set M}
    (c : OrderedNeckChain S eps t V) : IsCompact V := by
  rw [c.swept_eq]
  exact isCompact_iUnion fun i => (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    ((c.necks i).map.contMDiffOn_toFun.continuousOn.mono (c.inside i))

omit [T2Space M] [SigmaCompactSpace M] in
theorem LocalCap.isCompact_tube {eps : ℝ} {x : M} {t : ℝ} {U : Set M}
    (c : LocalCap S eps x t U) : IsCompact c.tube := c.chain.isCompact_swept

omit [T2Space M] [SigmaCompactSpace M] in
theorem LocalCap.isCompact_carrier {eps t : ℝ} {x : M} {U : Set M}
    (c : LocalCap S eps x t U) : IsCompact U := by
  rw [c.union_eq]
  exact c.core.compact.union c.isCompact_tube

end NeckChain

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {p : M} {U : Set M}

omit [T2Space M] in
theorem LocalCap.tube_depth_of_ball_subset_core_interior
    (cap : LocalCap S eps p t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hball : riemannianBallOf g p r ⊆ interior cap.core.carrier) :
    ∀ y ∈ cap.tube, r ≤ metricDistance g p y := by
  intro y hy
  apply metricDistance_ge_of_not_mem_riemannianBallOf g
  intro hnear
  have hboth : y ∈ cap.core.carrier ∩ cap.tube := ⟨interior_subset (hball hnear), hy⟩
  have hfront : y ∈ frontier cap.core.carrier := cap.overlap_eq ▸ hboth
  exact disjoint_interior_frontier.le_bot ⟨hball hnear, hfront⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end


namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]

theorem CapCore.isConnected_carrier {K : Set M} (cap : CapCore K) : IsConnected K := by
  cases cap with
  | ball F h hK =>
    rw [← hK]
    exact capCore_isConnected_image_closedBall F h
  | projective Z pr b hb F hF hK =>
    let _ : ConnectedSpace (Sphere 3) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
        (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
    let _ : ConnectedSpace Z := pr.onto.connectedSpace pr.smooth.continuous
    let _ : LocallyPathConnectedSpace Z := ChartedSpace.locallyPathConnectedSpace ThreeSpace Z
    have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    have hconn := DifferentialGeometry.Topology.isPathConnected_compl_image_ball
      b.toOpenPartialHomeomorph
        (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace])) hb1
    rw [← hK]
    exact hconn.isConnected.image F (F.contMDiffOn_toFun.continuousOn.mono hF)

section

open Set Metric

theorem CapCore.frontier_nonempty {K : Set M} (cap : CapCore K) : (frontier K).Nonempty := by
  let q : ThreeSpace := EuclideanSpace.single 0 1
  have hq : q ∈ sphere (0 : ThreeSpace) 1 := by simp [q]
  cases cap with
  | ball F hF hK =>
    have hfront : q ∈ frontier (closedBall (0 : ThreeSpace) 1) := by
      rwa [frontier_closedBall _ one_ne_zero]
    have h := (F.toOpenPartialHomeomorph.isImage_image_of_subset_source hF).frontier
    rw [← hK]
    exact ⟨F q, (h.apply_mem_iff (hF (sphere_subset_closedBall hq))).mpr hfront⟩
  | projective Z pr b hb F hF hK =>
    have hb1 : closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    have hfront : b q ∈ frontier (b '' Metric.ball (0 : ThreeSpace) 1) := by
      rw [DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph b hb1]
      exact mem_image_of_mem b hq
    have hopen : IsOpen (b '' Metric.ball (0 : ThreeSpace) 1) :=
      b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans hb1)
    have hmem : b q ∈ (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ := by
      change b q ∉ b '' Metric.ball (0 : ThreeSpace) 1
      simpa only [hopen.interior_eq] using hfront.2
    have h := (F.toOpenPartialHomeomorph.isImage_image_of_subset_source hF).frontier
    rw [← hK]
    refine ⟨F (b q), (h.apply_mem_iff (hF hmem)).mpr ?_⟩
    simpa only [frontier_compl] using hfront

theorem CapCore.ne_univ {K : Set M} (cap : CapCore K) : K ≠ univ := by
  intro hK
  have h := cap.frontier_nonempty
  rw [hK, frontier_univ] at h
  exact not_nonempty_empty h

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
