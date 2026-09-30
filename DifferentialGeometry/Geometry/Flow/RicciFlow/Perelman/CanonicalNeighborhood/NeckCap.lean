import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import DifferentialGeometry.Topology.SphereSeparation.SchoenfliesSides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCompactSides
import DifferentialGeometry.Topology.SphereSeparation.Sides
import DifferentialGeometry.Topology.SphereSeparation.BicollarSliceEmbedding

section

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology (SphereTwo)
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  {e : SphereTwo → M}

def CompactDomain.ofSphereSides
    {A : Set M}
    (he : Manifold.IsSmoothEmbedding I2 I3 ∞ e)
    (d : SphereSides A) (hA : Set.range e = A) : CompactDomain M where
  carrier := closure d.compactSide
  compact := d.isCompact_closure_compactSide
  connected := d.isConnected_compactSide.closure
  regular_closed := by rw [d.interior_closure_compactSide]
  boundary_chart := by
    intro x hx
    have hxA : x ∈ A := by
      simpa only [d.frontier_closure_compactSide] using hx
    have hxrange : x ∈ Set.range e := by
      rw [hA]
      exact hxA
    rcases hxrange with ⟨z, rfl⟩
    have hcharts : Nonempty (EmbeddedSphereSideNormalChart e d.compactSide z) := by
      subst A
      exact compactSideNormalChart_nonempty he d z
    obtain ⟨c⟩ := hcharts
    let φ : PartialDiffeomorph I3 I3 M ThreeSpace ∞ :=
      { c.base.normalForm.codChart.toPartialEquiv with
        open_source := c.base.normalForm.codChart.open_source
        open_target := c.base.normalForm.codChart.open_target
        contMDiffOn_toFun :=
          contMDiffOn_of_mem_maximalAtlas c.base.normalForm.codChart_mem_maximalAtlas
        contMDiffOn_invFun :=
          contMDiffOn_symm_of_mem_maximalAtlas c.base.normalForm.codChart_mem_maximalAtlas }
    let L : ThreeSpace ≃L[ℝ] ThreeSpace :=
      (c.base.normalForm.equiv.symm.trans c.orientation.tangentNormalEquiv).trans
        (ContinuousLinearEquiv.neg ℝ)
    let F : PartialDiffeomorph I3 I3 M ThreeSpace ∞ :=
      (DifferentialGeometry.Topology.PartialDiffeomorph.restrict φ
        c.base.neighborhood c.base.isOpen_neighborhood).trans
          L.toDiffeomorph.toPartialDiffeomorph
    refine ⟨F, ?_, ?_, ?_⟩
    · exact ⟨⟨c.base.neighborhood_subset_codChart_source
        c.base.image_mem_neighborhood, c.base.image_mem_neighborhood⟩, Set.mem_univ _⟩
    · change -(c.coordinate (e z) 0) = 0
      rw [c.coordinate_zero_apply,
        (c.base.normalCoordinate_eq_zero_iff c.base.image_mem_neighborhood).2 ⟨z, rfl⟩]
      cases c.orientation <;> simp [NormalOrientation.orient]
    · intro y hy
      have hyneighborhood : y ∈ c.base.neighborhood := hy.1.2
      change y ∈ closure d.compactSide ↔ -(c.coordinate y 0) ≤ 0
      rw [neg_nonpos]
      exact c.mem_closure_iff_coordinate_nonneg hyneighborhood

@[simp] theorem CompactDomain.ofSphereSides_carrier
    {A : Set M}
    (he : Manifold.IsSmoothEmbedding I2 I3 ∞ e)
    (d : SphereSides A) (hA : Set.range e = A) :
    (CompactDomain.ofSphereSides he d hA).carrier = closure d.compactSide := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology (SphereTwo)
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {v : M}

namespace StrongNeck

def compactSideDomain (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (c : AxialInterval eps⁻¹) :
    CompactDomain M :=
  CompactDomain.ofSphereSides
    (isSmoothEmbedding_bicollarSliceMap nk.bicollar nk.bicollar_isSmoothEmbedding c)
    (nk.bicollarSides ψ c) (range_bicollarSliceMap nk.bicollar c)

@[simp] theorem compactSideDomain_carrier (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (c : AxialInterval eps⁻¹) :
    (nk.compactSideDomain ψ c).carrier = closure (nk.bicollarSides ψ c).compactSide := rfl

theorem bicollar_slice (nk : StrongNeck S eps v t) (a : AxialInterval eps⁻¹) :
    sliceImage nk.bicollar a = nk.map '' (Set.univ ×ˢ ({(a : ℝ)} : Set ℝ)) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, congrArg Subtype.val hp.2⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(p.1, a), ⟨mem_univ _, rfl⟩, ?_⟩
    change nk.map (p.1, (a : ℝ)) = nk.map p
    exact congrArg nk.map (Prod.ext rfl hp.2.symm)

def localCapOfCompactSide (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞)
    (ho : IsAxiallyOriented nk.bicollar (nk.bicollarSides ψ))
    (core : CapCore (closure
      (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide)) (p : M)
    (hp : p ∈ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide) :
    LocalCap S eps p t
      (closure (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∪
        nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) := by
  let _ : T2Space M := ψ.symm.toHomeomorph.t2Space
  have ha : 0 < eps⁻¹ := inv_pos.mpr nk.eps_pos
  have h1 : (1 : ℝ) < eps⁻¹ := by
    have h : (1 / 11 : ℝ)⁻¹ < eps⁻¹ :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 11) nk.eps_pos).2 nk.eps_small
    norm_num at h
    linarith
  let a : AxialInterval eps⁻¹ := axialZero ha
  let b : AxialInterval eps⁻¹ := ⟨1, by linarith, h1⟩
  have hab : a < b := by change (0 : ℝ) < 1; norm_num
  let d := nk.bicollarSides ψ
  let K := nk.compactSideDomain ψ a
  have hK' : K.carrier = closure (d a).compactSide := rfl
  have hfrK : frontier K.carrier = nk.map '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
    rw [hK', (d a).frontier_closure_compactSide, nk.bicollar_slice]
    rfl
  have hord := bicollar_order_of_atZero ha nk.bicollar nk.bicollar_isSmoothEmbedding
    d ⟨(ho.at_zero ha).1, (ho.at_zero ha).2⟩ hab
  have hU : K.carrier ∪ nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) =
      closure (d b).compactSide := by
    rw [hord.2.1, hK', nk.bicollar_closed_slab]
    rfl
  have hfrU : frontier (K.carrier ∪ nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) =
      nk.map '' (Set.univ ×ˢ ({1} : Set ℝ)) := by
    rw [hU, (d b).frontier_closure_compactSide, nk.bicollar_slice]
  refine
    { core := K
      core_inside := ?_
      center_inside := ?_
      coreModel := core
      tube := nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
      tubeMap := nk.map
      tube_domain := nk.tube_window_subset_source
      tube_eq := rfl
      union_eq := rfl
      overlap_eq := ?_
      inner_boundary := hfrK.symm
      outer_boundary := hfrU.symm
      boundary_eq := ?_
      boundaries_disjoint := ?_
      chain := OrderedNeckChain.single nk
      coreBoundaryMap := fun z => nk.map (z, 0)
      core_boundary_eq := fun _ => rfl }
  · change K.carrier ⊆ interior (K.carrier ∪ nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))
    rw [hU, (d b).interior_closure_compactSide, hK']
    exact hord.1.1
  · rw [hK', (d a).interior_closure_compactSide]
    exact hp
  · rw [hK', (d a).frontier_closure_compactSide]
    change closure (d a).compactSide ∩
      nk.map '' (Set.univ ×ˢ Set.Icc (a : ℝ) (b : ℝ)) = sliceImage nk.bicollar a
    rw [← nk.bicollar_closed_slab a b]
    exact ho.compactClosure_inter_closedSlab hab.le
  · change frontier (nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) =
      frontier K.carrier ∪ frontier (K.carrier ∪ nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))
    rw [nk.frontier_window_eq_union_boundary_spheres, hfrK, hfrU]
  · change Disjoint (frontier K.carrier)
      (frontier (K.carrier ∪ nk.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)))
    rw [hfrK, hfrU]
    change Disjoint (nk.map '' (Set.univ ×ˢ ({(a : ℝ)} : Set ℝ)))
      (nk.map '' (Set.univ ×ˢ ({(b : ℝ)} : Set ℝ)))
    rw [← nk.bicollar_slice a, ← nk.bicollar_slice b]
    exact (d b).compactSide_disjoint_sphere.mono_left (ho.slice_subset_later_compact hab)

theorem localCapOfCompactSide_selected_neck (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞)
    (ho : IsAxiallyOriented nk.bicollar (nk.bicollarSides ψ))
    (core : CapCore (closure
      (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide)) (p : M)
    (hp : p ∈ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide) :
    let cap := nk.localCapOfCompactSide ψ ho core p hp
    cap.core.carrier = closure
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      cap.tubeMap = nk.map ∧ cap.chain.count = 1 ∧
      (∀ j : Fin cap.chain.count, cap.chain.centers j = v ∧ cap.chain.necks j = nk ∧
        cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧ v ∈ cap.tube := by
  refine ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩

theorem exists_localCap_of_capCore (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞)
    (core : CapCore (closure
      (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide)) (p : M)
    (hp : p ∈ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide) :
    ∃ (neck : StrongNeck S eps v t) (U : Set M) (cap : LocalCap S eps p t U),
      (neck = nk ∨ neck = nk.axialReflection) ∧
      U = closure (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∪
        neck.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧
      cap.core.carrier = closure
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      cap.tube = neck.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧
      cap.tubeMap = neck.map ∧
      ∃ j : Fin cap.chain.count,
        cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
        cap.chain.lo j = 0 ∧ cap.chain.hi j = 1 ∧ v ∈ cap.tube := by
  obtain ⟨neck, hneck, ho⟩ := nk.exists_axially_oriented ψ
  have hside :
      (neck.bicollarSides ψ (axialZero (inv_pos.mpr neck.eps_pos))).compactSide =
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide := by
    rcases hneck with rfl | rfl
    · rfl
    · exact (nk.axialReflection_bicollar_zero_sides ψ).1
  have hcore : CapCore (closure
      (neck.bicollarSides ψ (axialZero (inv_pos.mpr neck.eps_pos))).compactSide) := by
    rw [hside]
    exact core
  have hp' : p ∈ (neck.bicollarSides ψ (axialZero (inv_pos.mpr neck.eps_pos))).compactSide := by
    rw [hside]
    exact hp
  let cap := neck.localCapOfCompactSide ψ ho hcore p hp'
  refine ⟨neck, _, cap, hneck, ?_, ?_, rfl, rfl, ?_⟩
  · rw [hside]
  · change closure (neck.bicollarSides ψ
      (axialZero (inv_pos.mpr neck.eps_pos))).compactSide = _
    rw [hside]
  · refine ⟨⟨0, by change 0 < 1; norm_num⟩, rfl, HEq.rfl, rfl, rfl, ?_⟩
    exact ⟨(neck.center, 0), ⟨mem_univ _, by norm_num⟩, neck.center_eq⟩

end StrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology (SphereTwo)
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {v : M}

namespace StrongNeck

theorem nonempty_capCore_compactSide (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (c : AxialInterval eps⁻¹) :
    Nonempty (CapCore (closure (nk.bicollarSides ψ c).compactSide)) := by
  let e : SphereTwo → M := bicollarSliceMap nk.bicollar c
  have he : Manifold.IsSmoothEmbedding (𝓡 2) I3 ∞ e :=
    isSmoothEmbedding_bicollarSliceMap nk.bicollar nk.bicollar_isSmoothEmbedding c
  have hSch : smoothSchoenfliesThree := by
    intro f hf
    obtain ⟨F, hF⟩ := DifferentialGeometry.Topology.ThreeManifold.smooth_schoenflies_three f hf
    exact ⟨F.toPartialDiffeomorph, subset_univ _, hF⟩
  obtain ⟨F, d, _, _, hfill⟩ :=
    exists_ball_sphereSides_of_smoothSchoenflies hSch (ψ ∘ e) (he.postcomp_diffeomorph ψ)
  let d' := (nk.bicollarSides ψ c).image ψ.toHomeomorph
  have hindex : ψ.toHomeomorph '' sliceImage nk.bicollar c = range (ψ ∘ e) := by
    change ψ '' sliceImage nk.bicollar c = range (ψ ∘ e)
    rw [range_comp, range_bicollarSliceMap]
  have hside : d.compactSide = ψ '' (nk.bicollarSides ψ c).compactSide := by
    have hunion : d'.compactSide ∪ d'.endSide = (range (ψ ∘ e))ᶜ := by
      rw [d'.union_eq_compl, hindex]
    exact (d.side_sets_unique_of_core_properties d'.compactSide d'.endSide
      d'.isOpen_compactSide d'.isOpen_endSide d'.isConnected_compactSide
      d'.isConnected_endSide d'.disjoint hunion d'.isCompact_closure_compactSide
      d'.not_isCompact_closure_endSide).1.symm
  have hcore : F '' Metric.closedBall (0 : ThreeSpace) 1 =
      ψ '' closure (nk.bicollarSides ψ c).compactSide := by
    rw [← hfill, hside]
    exact (ψ.toHomeomorph.image_closure _).symm
  let G : Diffeomorph I3 I3 ThreeSpace M ∞ := F.trans ψ.symm
  refine ⟨CapCore.ball G.toPartialDiffeomorph (subset_univ _) ?_⟩
  change (ψ.symm ∘ F) '' Metric.closedBall (0 : ThreeSpace) 1 = _
  rw [image_comp, hcore]
  exact ψ.toHomeomorph.symm_image_image _

theorem exists_localCap_of_mem_compactSide (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (p : M)
    (hp : p ∈ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide) :
    ∃ (neck : StrongNeck S eps v t) (U : Set M) (cap : LocalCap S eps p t U),
      (neck = nk ∨ neck = nk.axialReflection) ∧
      U = closure (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∪
        neck.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧
      cap.core.carrier = closure
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      cap.tube = neck.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧
      cap.tubeMap = neck.map ∧
      ∃ j : Fin cap.chain.count,
        cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
        cap.chain.lo j = 0 ∧ cap.chain.hi j = 1 ∧ v ∈ cap.tube := by
  obtain ⟨core⟩ := nk.nonempty_capCore_compactSide ψ (axialZero (inv_pos.mpr nk.eps_pos))
  exact nk.exists_localCap_of_capCore ψ core p hp

end StrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature (RealTimeInterval)
open Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology.SphereSeparation (axialZero)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_busemann_upper_bound_on_compactSide :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [CompleteSpace M] (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
        (eps time : ℝ) (v : M) (nk : StrongNeck S eps v time)
        (psi : Diffeomorph I3 I3 M ThreeSpace ∞),
        (∀ x y : M, dist x y = metricDistance (S.base.metric time) x y) →
        ∀ c : ℝ≥0 → M, Isometry c →
          ∀ x ∈ closure (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide,
            Geometry.Topology.busemann c x ≤ Geometry.Topology.busemann c v +
              C / Real.sqrt (S.scalar time v) := by
  obtain ⟨C, hC, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound.{u}
    neckCoreDiameterBound_holds
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ J S eps time v nk psi hintrinsic c hc x hx
  let _ : SigmaCompactSpace M := psi.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let _ : ConnectedSpace M := psi.toHomeomorph.connectedSpace_iff.mpr inferInstance
  let g := S.base.metric time
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hnorm : Geometry.Riemannian.IsMetricNorm (I := I3) g :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle g
  let : IsRiemannianManifold I3 M := by
    refine ⟨fun y z => ?_⟩
    rw [edist_dist, hintrinsic]
    rw [metricDistance, riemannianEDistOf_eq_riemannianEDist g hnorm]
    exact ENNReal.ofReal_toReal (Geometry.Riemannian.Exponential.riemannianEDist_ne_top y z)
  let side := nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))
  obtain ⟨y, hy, hmax⟩ := Geometry.Topology.exists_busemann_maximum_on_frontier g hnorm hc
    side.isCompact_closure_compactSide side.isConnected_compactSide.nonempty.closure
  have hySphere : y ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [side.frontier_closure_compactSide] at hy
    rw [nk.bicollar_slice] at hy
    exact hy
  have hvSphere : v ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) :=
    ⟨(nk.center, 0), ⟨mem_univ _, rfl⟩, nk.center_eq⟩
  have hslab : nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆
      nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
    apply image_mono
    rintro z ⟨hz, heq⟩
    exact ⟨hz, heq.symm ▸ (by norm_num : (0 : ℝ) ∈ Icc (-10 : ℝ) 10)⟩
  have hd := hdiam M J S eps v time nk y (hslab hySphere) v (hslab hvSphere)
  have hb := (Geometry.Topology.lipschitzWith_busemann hc).dist_le_mul y v
  rw [Real.dist_eq, NNReal.coe_one, one_mul, hintrinsic] at hb
  exact (hmax x hx).trans (by linarith [(abs_le.mp hb).2])

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_busemann_upper_bound_on_localCapOfCompactSide :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [CompleteSpace M] (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
        (eps time : ℝ) (v : M) (nk : StrongNeck S eps v time)
        (psi : Diffeomorph I3 I3 M ThreeSpace ∞)
        (ho : DifferentialGeometry.Topology.SphereSeparation.IsAxiallyOriented
          nk.bicollar (nk.bicollarSides psi))
        (core : CapCore (closure
          (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide))
        (p : M) (hp : p ∈ (nk.bicollarSides psi
          (axialZero (inv_pos.mpr nk.eps_pos))).compactSide),
        (∀ x y : M, dist x y = metricDistance (S.base.metric time) x y) →
        ∀ c : ℝ≥0 → M, Isometry c →
          let cap := nk.localCapOfCompactSide psi ho core p hp
          ∀ x ∈ cap.core.carrier ∪ cap.tube,
            Geometry.Topology.busemann c x ≤ Geometry.Topology.busemann c v +
              C / Real.sqrt (S.scalar time v) := by
  obtain ⟨Cs, hCs, hside⟩ := exists_busemann_upper_bound_on_compactSide.{u}
  obtain ⟨Cd, hCd, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound.{u}
    neckCoreDiameterBound_holds
  refine ⟨max Cs Cd, lt_max_of_lt_left hCs, ?_⟩
  intro M _ _ _ _ J S eps time v nk psi ho core p hp hintrinsic c hc
  dsimp only
  intro x hx
  let _ : SigmaCompactSpace M := psi.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  rcases hx with hx | hx
  · have hb := hside M J S eps time v nk psi hintrinsic c hc x hx
    exact hb.trans (add_le_add_right
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) _)
  · have hcore : x ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩
    have hv : v ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) :=
      ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
    have hd := hdiam M J S eps v time nk x hcore v hv
    have hb := (Geometry.Topology.lipschitzWith_busemann hc).dist_le_mul x v
    rw [Real.dist_eq, NNReal.coe_one, one_mul, hintrinsic] at hb
    have hbound : Geometry.Topology.busemann c x ≤ Geometry.Topology.busemann c v +
        Cd / Real.sqrt (S.scalar time v) := by linarith [(abs_le.mp hb).2]
    exact hbound.trans (add_le_add_right
      (div_le_div_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
