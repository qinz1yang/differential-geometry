import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaBridge
import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaHomeomorphism
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaContinuity
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction

noncomputable section
open Bundle Manifold Set MeasureTheory Topology ContinuousMap Function
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] in
theorem diskBoundary_eq_topologicalDiskBoundary (θ : Surgery.Topology.Circle) :
    (DifferentialGeometry.Topology.diskBoundary θ : Disk) = diskBoundary θ := rfl

omit [FiniteDimensional ℝ E] in
theorem diskTrace_eq_iff (u : C(Disk, Q)) (γ : ContinuousFreeLoop Q) :
    DifferentialGeometry.Topology.diskTrace u = γ ↔
      ∀ θ : Surgery.Topology.Circle, u (diskBoundary θ) = γ θ := by
  constructor
  · intro h θ
    exact congrFun (congrArg DFunLike.coe h) θ
  · intro h
    exact ContinuousMap.ext h

omit [FiniteDimensional ℝ E] in
theorem mem_spanningDiskCompetitors_iff (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (u : C(Disk, Q)) :
    u ∈ Geometry.spanningDiskCompetitors g γ ↔
      (∀ θ : Surgery.Topology.Circle, u (diskBoundary θ) = γ θ) ∧
        ∃ L : ℝ≥0, ∀ z w : Disk,
          riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w := by
  rw [Geometry.spanningDiskCompetitors, Set.mem_ofPred_eq, diskTrace_eq_iff]

omit [FiniteDimensional ℝ E] in
def toLipschitzContractible (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    Geometry.lipschitzContractibleLoop g :=
  ⟨⟨γ, hctr⟩, hlip⟩

omit [FiniteDimensional ℝ E] in
theorem competitorAreas_eq_spanningDiskAreas (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    competitorAreas g γ = Geometry.spanningDiskAreas g (toLipschitzContractible g γ hctr hlip) := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u.1.map, ?_, (diskArea_eq_riemannianDiskArea g u.1.map).symm⟩
    rw [mem_spanningDiskCompetitors_iff]
    exact ⟨u.2, u.1.isLipschitz⟩
  · rintro ⟨u, hu, rfl⟩
    rw [mem_spanningDiskCompetitors_iff] at hu
    exact ⟨⟨⟨u, hu.2⟩, hu.1⟩, diskArea_eq_riemannianDiskArea g u⟩

omit [FiniteDimensional ℝ E] in
theorem leastArea_eq_leastSpanningArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea g γ hctr hlip =
      Geometry.leastSpanningArea g (toLipschitzContractible g γ hctr hlip) := by
  rw [leastArea, Geometry.leastSpanningArea,
    competitorAreas_eq_spanningDiskAreas g γ hctr hlip]

section Transport

variable [CompactSpace Q] [T3Space Q] [ConnectedSpace Q]

theorem rfs_weak_boundary_trace_riemannian (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle))
    (hψ : IsWeaklyMonotoneCircleMap ψ)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ψ)) (hlip' : IsLipschitzLoop g (γ.comp ψ)) :
    leastArea g (γ.comp ψ) hctr' hlip' = leastArea g γ hctr hlip := by
  obtain ⟨φ, hc, hm, hp, hlift⟩ := hψ
  have hmain := Geometry.leastSpanningArea_comp_weak_boundary g
    (toLipschitzContractible g γ hctr hlip)
    (toLipschitzContractible g (γ.comp ψ) hctr' hlip')
    ψ (f := φ) hc hm hp hlift rfl
  calc leastArea g (γ.comp ψ) hctr' hlip'
      = Geometry.leastSpanningArea g (toLipschitzContractible g (γ.comp ψ) hctr' hlip') :=
        leastArea_eq_leastSpanningArea g (γ.comp ψ) hctr' hlip'
    _ = Geometry.leastSpanningArea g (toLipschitzContractible g γ hctr hlip) := hmain
    _ = leastArea g γ hctr hlip := (leastArea_eq_leastSpanningArea g γ hctr hlip).symm

theorem leastArea_circle_homeomorph_riemannian (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (ψ : Surgery.Topology.Circle ≃ₜ Surgery.Topology.Circle)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ⟨ψ, ψ.continuous⟩))
    (hlip' : IsLipschitzLoop g (γ.comp ⟨ψ, ψ.continuous⟩)) :
    leastArea g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip' = leastArea g γ hctr hlip := by
  have hmain := Geometry.leastSpanningArea_comp_homeomorphism g
    (toLipschitzContractible g γ hctr hlip)
    (toLipschitzContractible g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip') ψ rfl
  calc leastArea g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip'
      = Geometry.leastSpanningArea g
          (toLipschitzContractible g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip') :=
        leastArea_eq_leastSpanningArea g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip'
    _ = Geometry.leastSpanningArea g (toLipschitzContractible g γ hctr hlip) := hmain
    _ = leastArea g γ hctr hlip := (leastArea_eq_leastSpanningArea g γ hctr hlip).symm

omit [T3Space Q] in
theorem smoothTubularRetraction_exists_riemannian {N : ℕ}
    (e : SmoothLoopEmbedding (I := 𝓘(ℝ, E)) (Q := Q) N) :
    Nonempty (SmoothTubularRetraction e) := by
  obtain ⟨r, U, hU, hrange, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      (e := e.map) e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  exact ⟨⟨U, hU, hrange, r, hr, hleft⟩⟩

end Transport

section Composition

variable [T2Space Q] [CompactSpace Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {P : Type*} [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ, F) ∞ P]
  [T2Space P] [CompactSpace P]

theorem diskArea_lipschitz_comp_riemannian (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (h : SmoothRiemannianMetric 𝓘(ℝ, F) P) (f : C(Q, P)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y) (u : LipschitzDisk g) :
    diskArea h ((f : Q → P) ∘ u.map) ≤ (L : ℝ) ^ 2 * diskArea g u.map := by
  obtain ⟨C, hu⟩ := u.isLipschitz
  rw [diskArea_eq_riemannianDiskArea h ((f : Q → P) ∘ u.map),
    diskArea_eq_riemannianDiskArea g u.map]
  exact Geometry.riemannianDiskArea_comp_le g h hu hf

end Composition

def regularLoopEquiv : RegularLoop 𝓘(ℝ, E) Q ≃ DifferentialGeometry.Topology.regularLoop E Q where
  toFun γ := ⟨γ.toContinuousLoop, γ.contMDiff_lift⟩
  invFun γ := ⟨γ.1, γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def contractibleRegularLoopEquiv :
    ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q) ≃
      DifferentialGeometry.Topology.regularContractibleLoop E Q where
  toFun γ := ⟨regularLoopEquiv γ.1, γ.2⟩
  invFun γ := ⟨regularLoopEquiv.symm γ.1, γ.2⟩
  left_inv γ := by
    refine Subtype.ext ?_
    exact regularLoopEquiv.left_inv γ.1
  right_inv γ := by
    refine Subtype.ext ?_
    exact regularLoopEquiv.right_inv γ.1

section RegularContinuity

variable [CompactSpace Q] [T3Space Q] [ConnectedSpace Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem toLipschitzContractible_regularLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q)) :
    toLipschitzContractible g γ.1.toContinuousLoop γ.2 (γ.1.isLipschitz g) =
      DifferentialGeometry.Geometry.regularContractibleToLipschitz g
        (contractibleRegularLoopEquiv γ) := by
  refine Subtype.ext ?_
  exact Subtype.ext rfl

theorem regularLeastArea_eq_geometry (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q)) :
    regularLeastArea g γ =
      DifferentialGeometry.Geometry.regularLeastArea g (contractibleRegularLoopEquiv γ) := by
  rw [regularLeastArea, DifferentialGeometry.Geometry.regularLeastArea,
    leastArea_eq_leastSpanningArea, toLipschitzContractible_regularLoop]

theorem continuous_regularLeastArea_of_topology (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (e : Q → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (htop : (instTopologicalSpaceSubtype : TopologicalSpace (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q))) =
      TopologicalSpace.induced contractibleRegularLoopEquiv
        (DifferentialGeometry.Topology.regularContractibleLoopTopology e
          (he.of_le (by exact_mod_cast le_top)))) :
    Continuous (regularLeastArea g) := by
  have hgeo := DifferentialGeometry.Geometry.continuous_regularLeastArea g e he hemb hi
  have hcd : @Continuous (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q))
      (DifferentialGeometry.Topology.regularContractibleLoop E Q)
      (TopologicalSpace.induced (⇑contractibleRegularLoopEquiv)
        (DifferentialGeometry.Topology.regularContractibleLoopTopology e
          (he.of_le (by exact_mod_cast le_top))))
      (DifferentialGeometry.Topology.regularContractibleLoopTopology e
        (he.of_le (by exact_mod_cast le_top)))
      (⇑contractibleRegularLoopEquiv) :=
    continuous_induced_dom (f := ⇑contractibleRegularLoopEquiv)
      (t := DifferentialGeometry.Topology.regularContractibleLoopTopology e
        (he.of_le (by exact_mod_cast le_top)))
  have hcont : @Continuous (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q)) ℝ
      (TopologicalSpace.induced (⇑contractibleRegularLoopEquiv)
        (DifferentialGeometry.Topology.regularContractibleLoopTopology e
          (he.of_le (by exact_mod_cast le_top)))) inferInstance
      (fun γ => DifferentialGeometry.Geometry.regularLeastArea g
        (contractibleRegularLoopEquiv γ)) :=
    @Continuous.comp (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q))
      (DifferentialGeometry.Topology.regularContractibleLoop E Q) ℝ
      (TopologicalSpace.induced (⇑contractibleRegularLoopEquiv)
        (DifferentialGeometry.Topology.regularContractibleLoopTopology e
          (he.of_le (by exact_mod_cast le_top))))
      (DifferentialGeometry.Topology.regularContractibleLoopTopology e
        (he.of_le (by exact_mod_cast le_top))) inferInstance
      (⇑contractibleRegularLoopEquiv) (DifferentialGeometry.Geometry.regularLeastArea g)
      hgeo hcd
  have heq : regularLeastArea g =
      fun γ : ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q) =>
        DifferentialGeometry.Geometry.regularLeastArea g (contractibleRegularLoopEquiv γ) :=
    funext (regularLeastArea_eq_geometry g)
  rw [heq]
  rw [htop]
  exact hcont

end RegularContinuity

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
