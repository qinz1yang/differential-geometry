import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaBridge
import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaHomeomorphism
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaContinuity
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness

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

def toTopologyLoop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q]
    (γ : RegularLoop 𝓘(ℝ, E) Q) : DifferentialGeometry.Topology.regularLoop E Q :=
  ⟨γ.toContinuousLoop, γ.contMDiff_lift⟩

theorem regularLoopTopologicalSpace_eq_induced_regularLoopTopology
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
    [CompactSpace Q] [Nonempty Q]
    {N : ℕ} (e : SmoothLoopEmbedding (I := 𝓘(ℝ, E)) (Q := Q) N) :
    regularLoopTopologicalSpace (I := 𝓘(ℝ, E)) (Q := Q) =
      TopologicalSpace.induced (fun γ : RegularLoop 𝓘(ℝ, E) Q =>
        DifferentialGeometry.Topology.regularLoopJet e.map
          (e.smooth.of_le (by exact_mod_cast le_top)) (toTopologyLoop γ)) inferInstance := by
  refine le_antisymm ?_ ?_
  · rw [← continuous_iff_le_induced]
    have hval : Continuous (fun γ : RegularLoop 𝓘(ℝ, E) Q =>
        DifferentialGeometry.Topology.regularLoopValue e.map
          (e.smooth.of_le (by exact_mod_cast le_top)) (toTopologyLoop γ)) :=
      (ContinuousMap.continuous_postcomp (⟨e.map, e.smooth.continuous⟩ : C(Q, EuclideanSpace ℝ (Fin N)))).comp
        (continuous_fst.comp RegularLoop.continuous_value_jet)
    have hder : Continuous (fun γ : RegularLoop 𝓘(ℝ, E) Q =>
        DifferentialGeometry.Topology.regularLoopDerivative e.map
          (e.smooth.of_le (by exact_mod_cast le_top)) (toTopologyLoop γ)) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      have hgper : ∀ k : RegularLoop 𝓘(ℝ, E) Q,
          Periodic (fun t : ℝ => deriv (fun r : ℝ =>
            e.map (k.toContinuousLoop (r : Surgery.Topology.Circle))) t) 1 := by
        intro k
        have h1 : Periodic (fun r : ℝ =>
            e.map (k.toContinuousLoop (r : Surgery.Topology.Circle))) 1 := by
          intro r
          exact congrArg (fun x => e.map (k.toContinuousLoop x)) (AddCircle.coe_add_period (1 : ℝ) r)
        simpa only [iteratedDeriv_one] using
          DifferentialGeometry.Topology.periodic_iteratedDeriv h1 1
      have hg : Continuous (fun p : RegularLoop 𝓘(ℝ, E) Q × ℝ => deriv (fun r : ℝ =>
          e.map (p.1.toContinuousLoop (r : Surgery.Topology.Circle))) p.2) := by
        refine DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one ?_ ?_
        · have hjet : Continuous (fun γ : RegularLoop 𝓘(ℝ, E) Q => embeddingFirstJet e γ) :=
            continuous_embeddingFirstJet e
          have hJ : Continuous (fun q : RegularLoop 𝓘(ℝ, E) Q × Icc (0 : ℝ) 1 =>
              (embeddingFirstJet e q.1) q.2) :=
            continuous_eval.comp ((hjet.comp continuous_fst).prodMk continuous_snd)
          have hρ : Continuous (fun p :
              (univ ×ˢ Icc (0 : ℝ) 1 : Set (RegularLoop 𝓘(ℝ, E) Q × ℝ)) =>
              ((p.1.1, ⟨p.1.2, (Set.mem_prod.mp p.2).2⟩) :
                RegularLoop 𝓘(ℝ, E) Q × Icc (0 : ℝ) 1)) :=
            (continuous_subtype_val.fst).prodMk
              ((continuous_subtype_val.snd).subtype_mk fun p => (Set.mem_prod.mp p.2).2)
          have hdom : Continuous (fun p :
              (univ ×ˢ Icc (0 : ℝ) 1 : Set (RegularLoop 𝓘(ℝ, E) Q × ℝ)) =>
              ((embeddingFirstJet e p.1.1)
                ⟨p.1.2, (Set.mem_prod.mp p.2).2⟩).2) :=
            (continuous_snd.comp hJ).comp hρ
          refine continuousOn_iff_continuous_domRestrict.mpr (hdom.congr fun p => ?_)
          exact rfl
        · intro k t
          exact hgper k t
      refine (DifferentialGeometry.Topology.continuous_periodic_family hg hgper).congr fun p => ?_
      exact rfl
    exact (hval.prodMk hder).congr fun γ => rfl
  · rw [regularLoop_topology_eq_embedding e]
    let : TopologicalSpace (RegularLoop 𝓘(ℝ, E) Q) :=
      TopologicalSpace.induced (fun γ : RegularLoop 𝓘(ℝ, E) Q =>
        DifferentialGeometry.Topology.regularLoopJet e.map
          (e.smooth.of_le (by exact_mod_cast le_top)) (toTopologyLoop γ)) inferInstance
    rw [← continuous_iff_le_induced]
    have hc : Continuous (fun q : (DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N)) ×
        DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N))) × Icc (0 : ℝ) 1 =>
        (((q.2 : Icc (0 : ℝ) 1) : ℝ) : Surgery.Topology.Circle)) :=
      (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((continuous_subtype_val : Continuous fun q : Icc (0 : ℝ) 1 => (q : ℝ)).comp continuous_snd)
    let Res : C(DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N)) ×
        DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N)),
        C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))) :=
      ContinuousMap.curry ⟨fun q : (DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N)) ×
          DifferentialGeometry.Topology.freeLoop (EuclideanSpace ℝ (Fin N))) × Icc (0 : ℝ) 1 =>
          (q.1.1 (q.2 : Surgery.Topology.Circle), q.1.2 (q.2 : Surgery.Topology.Circle)),
        ((continuous_eval.comp (((continuous_fst.comp continuous_fst).prodMk hc))).prodMk
          (continuous_eval.comp (((continuous_snd.comp continuous_fst).prodMk hc))))⟩
    have hme : (fun γ : RegularLoop 𝓘(ℝ, E) Q =>
        Res (DifferentialGeometry.Topology.regularLoopJet e.map
          (e.smooth.of_le (by exact_mod_cast le_top)) (toTopologyLoop γ))) = embeddingFirstJet e := by
      funext γ
      exact rfl
    exact hme ▸ (Res.continuous.comp continuous_induced_dom)

theorem regularContractibleLoopTopologicalSpace_eq_induced
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
    [CompactSpace Q] [Nonempty Q]
    {N : ℕ} (e : SmoothLoopEmbedding (I := 𝓘(ℝ, E)) (Q := Q) N) :
    (instTopologicalSpaceSubtype :
        TopologicalSpace (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q))) =
      TopologicalSpace.induced (contractibleRegularLoopEquiv (E := E) (Q := Q))
        (DifferentialGeometry.Topology.regularContractibleLoopTopology e.map
          (e.smooth.of_le (by exact_mod_cast le_top))) := by
  have hsub : (instTopologicalSpaceSubtype :
      TopologicalSpace (ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q))) =
      TopologicalSpace.induced
        (Subtype.val : ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := Q) →
          RegularLoop 𝓘(ℝ, E) Q)
        (regularLoopTopologicalSpace (I := 𝓘(ℝ, E)) (Q := Q)) := rfl
  rw [hsub, regularLoopTopologicalSpace_eq_induced_regularLoopTopology e,
    DifferentialGeometry.Topology.regularContractibleLoopTopology,
    DifferentialGeometry.Topology.regularLoopTopology]
  rw [induced_compose, induced_compose, induced_compose]
  rfl


theorem continuous_regularLeastArea_stdModel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
    [CompactSpace Q] [T3Space Q] [ConnectedSpace Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) :
    Continuous (regularLeastArea g) := by
  obtain ⟨N, e, he, hs, hd⟩ :=
    _root_.exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := Q)
  exact continuous_regularLeastArea_of_topology g e he hs.isEmbedding hd
    (regularContractibleLoopTopologicalSpace_eq_induced ⟨e, he, hs, hd⟩)
private theorem areaDensity_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (U : ℂ → A) (z : ℂ) :
    Geometry.riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      Geometry.riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z =
        (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

private theorem riemannianDiskArea_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    Geometry.riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) u =
      Geometry.riemannianDiskArea g (fun z => Ψ (u z)) := by
  rw [Geometry.riemannianDiskArea, Geometry.riemannianDiskArea]
  refine integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  rw [areaDensity_pullbackDiffeo]
  refine Geometry.riemannianAreaDensity_congr g ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [Geometry.diskExtension, Function.comp_apply]

private theorem diskArea_pullbackDiffeoModel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    diskArea (Diffeomorph.pullbackMetricCross g Ψ) u = diskArea g (fun z => Ψ (u z)) := by
  rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea,
    riemannianDiskArea_pullbackDiffeo]




theorem competitorAreas_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (γ : ContinuousFreeLoop A) :
    competitorAreas (Diffeomorph.pullbackMetricCross g Ψ) γ =
      competitorAreas g ((⟨Ψ, Ψ.continuous⟩ : C(A, Q)).comp γ) := by
  classical
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨⟨⟨fun z => Ψ (u.1.map z), Ψ.continuous.comp u.1.map.continuous⟩,
      u.1.isLipschitz.choose, ?_⟩, ?_⟩, ?_⟩
    · intro z w
      have h := u.1.isLipschitz.choose_spec z w
      simp only [ContinuousMap.coe_mk] at h ⊢
      rw [← DifferentialGeometry.riemannianEDistOf_pullbackMetricCross]
      exact h
    · intro θ
      have h := u.2 θ
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at h ⊢
      rw [h]
    · exact (diskArea_pullbackDiffeoModel g Ψ u.1.map).symm
  · rintro ⟨v, rfl⟩
    refine ⟨⟨⟨⟨fun z => Ψ.symm (v.1.map z), Ψ.symm.continuous.comp v.1.map.continuous⟩,
      v.1.isLipschitz.choose, ?_⟩, ?_⟩, ?_⟩
    · intro z w
      have h := v.1.isLipschitz.choose_spec z w
      simp only [ContinuousMap.coe_mk] at h ⊢
      rw [DifferentialGeometry.riemannianEDistOf_pullbackMetricCross]
      simpa only [Diffeomorph.apply_symm_apply] using h
    · intro θ
      have h := v.2 θ
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at h ⊢
      rw [h, Ψ.symm_apply_apply]
    · simp only [ContinuousMap.coe_mk]
      rw [diskArea_pullbackDiffeoModel]
      exact congrArg (diskArea g) (funext fun z => Ψ.apply_symm_apply (v.1.map z))

theorem continuous_regularLeastArea
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [I.Boundaryless] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q]
    (g : SmoothRiemannianMetric I Q) : Continuous (regularLeastArea g) := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  let Ψ : c.Q ≃ₘ⟮𝓘(ℝ, E), I⟯ Q := c.equiv.symm
  let Φc : C(Q, c.Q) := ⟨c.equiv, c.equiv.continuous⟩
  let Ψc : C(c.Q, Q) := ⟨fun x => Ψ x, Ψ.continuous⟩
  let g' : SmoothRiemannianMetric 𝓘(ℝ, E) c.Q := Diffeomorph.pullbackMetricCross g Ψ
  have hcont' : Continuous (regularLeastArea g') := continuous_regularLeastArea_stdModel g'
  let T : ContractibleRegularLoop (I := I) (Q := Q) →
      ContractibleRegularLoop (I := 𝓘(ℝ, E)) (Q := c.Q) :=
    fun γ => ⟨RegularLoop.postcompose Φc c.equiv.contMDiff γ.1,
      γ.2.postcompose Φc⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact (continuous_regularLoop_postcompose Φc c.equiv.contMDiff).comp continuous_subtype_val
  have hcomp : ∀ γ' : ContinuousFreeLoop Q, Ψc.comp (Φc.comp γ') = γ' := by
    intro γ'
    exact ContinuousMap.ext fun θ => Ψ.apply_symm_apply (γ' θ)
  have hfun : regularLeastArea g = fun γ => regularLeastArea g' (T γ) := by
    funext γ
    simp only [regularLeastArea, leastArea]
    refine congrArg sInf ?_
    have h1 : competitorAreas g γ.1.toContinuousLoop =
        competitorAreas g' (Φc.comp γ.1.toContinuousLoop) := by
      rw [← hcomp γ.1.toContinuousLoop]
      exact (competitorAreas_pullbackDiffeo g Ψ (Φc.comp γ.1.toContinuousLoop)).symm
    exact h1
  rw [hfun]
  exact hcont'.comp hT

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
