import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonCanonicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParentReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildSimplicityFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreTwoCover

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ ¬ 0 < k ∧ ∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1 :=
  ⟨-1, 1, -1, by norm_num [zsmul_eq_mul], by norm_num, ⟨LinearMap.id, rfl⟩⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TubeSystem

variable {M : Type u} [TopologicalSpace M] (T : TubeSystem M)

namespace PuncturedCoreCutChain

def ofSimplyConnectedComponent (c : ConnectedComponents ↥T.core)
    (h : SimplyConnectedSpace ↥(T.puncturedCoreComponent c)) : T.PuncturedCoreCutChain c where
  n := 0
  W := fun _ => T.puncturedCoreComponent c
  L := fun _ => univ
  R := fun _ => univ
  isOpen_L := fun _ => isOpen_univ
  isOpen_R := fun _ => isOpen_univ
  cover := fun _ => by simp
  next := fun _ => Or.inl (by simp)
  simplyConnected_overlap := fun _ => by
    rw [Set.inter_univ, Set.inter_univ]
    exact h
  pathConnected_left := fun _ => by
    rw [Set.inter_univ]
    let _ : SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := h
    infer_instance
  pathConnected_right := fun _ => by
    rw [Set.inter_univ]
    let _ : SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := h
    infer_instance
  terminal := rfl

end PuncturedCoreCutChain

end TubeSystem

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation :
    E.PuncturedCoreCutChainProducer ↔ E.middleSphereCuttingSeparation :=
  ⟨E.middleSphereCuttingSeparation_of_cutChainProducer, fun h c hpar =>
    ⟨TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent E.trace.tubes
      (E.childCoreComponent c) (h c hpar), h c hpar⟩⟩

theorem childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer :
    E.ChildSimplicityFrontier ↔ E.childCollaredStarCoverProducer ∧ E.PuncturedCoreCutChainProducer := by
  constructor
  · rintro ⟨hcover, hsep⟩
    exact ⟨hcover, E.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation.mpr hsep⟩
  · rintro ⟨hcover, hchain⟩
    exact ⟨hcover, E.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation.mp hchain⟩

theorem not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace
    (c : ConnectedComponents Q.Carrier) (hcore : SimplyConnectedSpace (E.ChildCore c))
    (hcar : ¬ SimplyConnectedSpace (E.ChildCarrier c)) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  fun hd => hcar (E.simplyConnectedSpace_childCarrier_of_collaredStarCover c hcore hd.some)

theorem not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ)
    (hcore : SimplyConnectedSpace (E.ChildCore c)) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  E.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace c hcore
    (not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ E c hne huniv)

theorem not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation
    (hmiddle : E.middleSphereCuttingSeparation) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier]
    {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  E.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ c hne huniv
    ((E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mp (hmiddle c inferInstance))

end SmoothCutCapTransition

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

structure ChildComparisonReducedInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3) where
  Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c
  distanceControl : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    (Kc c).LocalTerminalDistanceControl (Kc c).rfs_whole_parent_map
  convergenceTime : ℝ
  convergenceTime_mem : convergenceTime ∈ Ico (H.time i.castSucc) (H.time i.succ)
  scale : ℝ → ℝ
  scale_one : ∀ s ∈ Ioo convergenceTime (H.time i.succ), 1 ≤ scale s
  scale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1)
  localEDist : G.LocalEDistComparison Kc convergenceTime scale
  multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ
  map_eq : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c
  generator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1
  positive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c

variable {G}

def ChildComparisonInputs.toReducedInputs
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b) : G.ChildComparisonReducedInputs a b where
  Kc := h.Kc
  distanceControl := fun c =>
    ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
      (c := c) h.Kc h.collapse
  convergenceTime := h.convergenceTime
  convergenceTime_mem := h.convergenceTime_mem
  scale := h.scale
  scale_one := h.scale_one
  scale_tendsto := h.scale_tendsto
  localEDist := G.localEDistComparison_of_terminal_comparisons h.Kc h.collapse h.convergence
  multiplier := h.multiplier
  map_eq := h.map_eq
  generator := h.generator
  positive := h.positive

theorem rfs_child_comparison_of_reducedInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (h : G.ChildComparisonReducedInputs a b) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨f, hf, hlen⟩ := G.rfs_child_comparison_metric_of_local_length_comparison h.Kc
    (G.localLengthComparison_of_localEDistComparison h.Kc h.convergenceTime_mem h.localEDist
      h.scale_one h.scale_tendsto)
  refine ⟨f, fun c => ⟨h.Kc c, hf c⟩, fun c => ?_, hlen⟩
  rw [hf c]
  exact (ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (K := h.Kc c) (a c) (b c) (h.distanceControl c) (h.map_eq c) (h.generator c)
    (h.positive c)).2.2.2.1

theorem rfs_child_comparison_of_canonicalReducedInputs
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hdistanceControl : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      (G.canonicalComparisonSupport hSC c).LocalTerminalDistanceControl
        (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison (G.canonicalComparisonSupport hSC) convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_reducedInputs a b
    { Kc := G.canonicalComparisonSupport hSC
      distanceControl := hdistanceControl
      convergenceTime := convergenceTime
      convergenceTime_mem := hconvergenceTime
      scale := scale
      scale_one := hscale_one
      scale_tendsto := hscale_tendsto
      localEDist := hlocalEDist
      multiplier := multiplier
      map_eq := hmap
      generator := hgenerator
      positive := hpositive }

theorem rfs_child_comparison_of_canonicalTerminalInputs
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (s₀ : ℝ) (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (ell : ℝ → ℝ) (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hregion : G.TerminalParentRegionConvexity (G.canonicalComparisonSupport hSC) s₀)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_canonicalReducedInputs hSC a b
    (fun c =>
      ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
        (c := c) (G.canonicalComparisonSupport hSC) hcollapse)
    s₀ hs₀ ell hell htend
    (G.localEDistComparison_of_terminal_comparisons (G.canonicalComparisonSupport hSC) hcollapse
      (G.localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity
        (G.canonicalComparisonSupport hSC) hquad hregion hell))
    multiplier hmap hgenerator hpositive

theorem rfs_child_comparison_of_canonicalUniformConvergence
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (s₀ : ℝ) (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hregion : G.TerminalParentRegionConvexity (G.canonicalComparisonSupport hSC) s₀)
    (huniform : G.TerminalParentUniformConvergence s₀)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    G.exists_quadFormComparison_of_uniformConvergence huniform
  exact G.rfs_child_comparison_of_canonicalTerminalInputs hSC a b hcollapse s₁
    ⟨le_of_lt (lt_of_le_of_lt hs₀.1 hs₁.1), hs₁.2⟩ ell hell htend hquad
    (TerminalParentRegionConvexity.mono G hregion (le_of_lt hs₁.1))
    multiplier hmap hgenerator hpositive

namespace ComparisonSupport

variable {c : ConnectedComponents (H.stage i.succ).Carrier}

theorem rfs_whole_parent_map_class_eq_of_multiplierForm
    (K : G.ComparisonSupport c)
    (a : IntegralHomology (G.Parent c).Carrier 3)
    (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ}
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 K.rfs_whole_parent_map a) = 1)
    (hk : 0 < k) :
    integralHomologyMap 3 K.rfs_whole_parent_map a = b :=
  (DifferentialGeometry.Topology.eq_of_pos_zsmul_and_linearMap_eq_one
    (A := IntegralHomology (G.Child c).Carrier 3)
    ⟨k, hgen.choose, hmap, hk, hgen.choose_spec⟩).1

end ComparisonSupport

theorem rfs_child_comparison_of_localEDistComparison_and_class_generator
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison Kc convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨f, hf, hlen⟩ := G.rfs_child_comparison_metric_of_local_length_comparison Kc
    (G.localLengthComparison_of_localEDistComparison Kc hconvergenceTime hlocalEDist
      hscale_one hscale_tendsto)
  exact ⟨f, fun c => ⟨Kc c, hf c⟩, fun c => by
      rw [hf c]
      exact ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm (Kc c) (a c) (b c)
        (hmap c) (hgenerator c) (hpositive c), hlen⟩

theorem rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison (G.canonicalComparisonSupport hSC) convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_localEDistComparison_and_class_generator
    (G.canonicalComparisonSupport hSC) a b convergenceTime hconvergenceTime scale hscale_one
    hscale_tendsto hlocalEDist multiplier hmap hgenerator hpositive

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected dependencies for {n}: {axs}"
