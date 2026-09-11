import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.UniformDisjointStaticCaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCutCapEvent

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w z
private local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    CompleteSpace E := FiniteDimensional.complete ℝ E
private abbrev UniformE3 := EuclideanSpace ℝ (Fin 3)
private abbrev UniformIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace UniformE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private theorem actualNeck_local
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (U : Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : IsLocalDiffeomorph UniformIC I ∞ (neckAmbientMap U d) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_neckAmbientMap U d) _ (by simpa using (Fact.out : Module.finrank ℝ E = 3).symm)
  intro x
  rw [neckAmbientMap_mfderiv]
  exact d.immersion x

private abbrev UniformS2 := Metric.sphere (0 : UniformE3) 1
private abbrev UniformCap := {x : UniformE3 // ‖x‖ ≤ transitionEnd}

theorem exists_uniform_terminal_cut_cap_events :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [Nonempty M],
      ∀ (a s : ℝ) (has : a < s)
        (incoming : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a s has)),
        IsSolutionOn incoming → ∀ (o : SmoothOrientation I M)
        (g : SmoothRiemannianMetric I (terminalRegularRegion incoming.base.metric a s)),
        IsTerminalLimitMetric incoming.base.metric a s g →
      ∀ {ι : Type z} [Finite ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
        (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → (terminalRegularRegion incoming.base.metric a s))
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (m + 6)),
      let f := fun i => neckAmbientMap (terminalRegularRegion incoming.base.metric a s) (d₀ i)
      let hf := fun i => isOpenEmbedding_neckAmbientMap (terminalRegularRegion incoming.base.metric a s) (d₀ i)
      let hs := fun i => actualNeck_local (terminalRegularRegion incoming.base.metric a s) (d₀ i)
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) (terminalRegularRegion incoming.base.metric a s)),
      (Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)) →
      let B := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace UniformE3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      ∃ hrec : ∀ b : B, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
        ∃ d : ∀ b : B, normalizedDatum g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          (c * precision b.val.1) (m + 4),
        ∃ hmap : ∀ b : B, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
        ∃ hside : ∀ b : B, (d b).retainedSide = true,
        ∃ w : ∀ b : B, CanonicalStaticInsertionWitness (d b) A hA D m ε,
          (∀ b : B, |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
          (∀ b : B, StaticInsertionAdditionalProperties C (w b)) ∧
        ∃ gRet : SmoothRiemannianMetric (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R),
          (gRet = finiteFullPreparedMetric I hδ f hf hdisj hs (terminalRegularRegion incoming.base.metric a s) g R hRet c hc
            x₀ (fun _ => m + 6) d₀ (fun _ => rfl) hrec d hmap hside w ∧
          (∀ (b : B) (q : InsertionQuotient (inv_pos.mpr (d b).precision_pos))
            (v t : TangentSpace (𝓡 3) q),
            gRet.inner (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)
              (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q v)
              (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q t) =
                (w b).data.outMetric.inner q v t) ∧
          (∀ (p : coreInteriorDomain f)
            (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
            (v t : TangentSpace I p),
            gRet.inner (Opens.inclusion inf_le_left (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp))
              (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
              (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p t) =
                g.inner ⟨p.val, hRet hp⟩ v t) ∧
          (∀ b : B, Injective (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) ∧
            IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)) ∧
          Pairwise (fun b d : B => Disjoint
            (range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b))
            (range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc d)))) ∧
          OrientedFiniteCutCapGeometry I Fact.out transitionEnd_pos hδ f hf hdisj hs
            (fun i => (d₀ i).precision_lt_one) R o ∧
          FullMetricConclusions I hδ f hf hdisj hs (terminalRegularRegion incoming.base.metric a s) g R hRet c hc
            x₀ (fun _ => m + 6) d₀ d w C gRet ∧
          (∀ (b : B) (x : UniformCap),
            finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ((w b).data.capMap x) =
              (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj ⟨b.val, x⟩, b.property⟩ : finiteCapRetained transitionEnd_pos hδ f hf hdisj R)) ∧
          (∀ (b : B) (q : UniformS2 × Ico (0 : ℝ) (c * precision b.val.1)⁻¹),
            finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ((w b).data.retainedInclusion q) =
              finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
                (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b
                  (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q)) ∧
          MetricCutCapEventOn I a s has incoming g Fact.out transitionEnd_pos hδ f hf hdisj hs
            (fun i => (d₀ i).precision_lt_one) R hRet o gRet := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hmod⟩ := exists_uniform_disjoint_static_caps.{u, v, w, z}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hquarter, hprep⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ _ a s has incoming hIncoming o g hTerminal
    ι _ precision hδ hle x₀ d₀
  dsimp only
  intro hdisj R hRet hnontrivial
  let f := fun i => neckAmbientMap (terminalRegularRegion incoming.base.metric a s) (d₀ i)
  let hf := fun i => isOpenEmbedding_neckAmbientMap (terminalRegularRegion incoming.base.metric a s) (d₀ i)
  let hs := fun i => actualNeck_local (terminalRegularRegion incoming.base.metric a s) (d₀ i)
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace UniformE3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  have h := hprep o (terminalRegularRegion incoming.base.metric a s) g precision hδ hle x₀ d₀
    hdisj R hRet hnontrivial
  dsimp only at h
  obtain ⟨hrec, d, hmap, hside, w, hratio, hw, gRet, hOld, hG, hMetric, hCap, hCollar⟩ := h
  refine ⟨hrec, d, hmap, hside, w, hratio, hw, gRet, hOld, hG, hMetric, hCap, hCollar, ?_⟩
  exact metricCutCapEventOn_of_retained_identity I a s has incoming g Fact.out transitionEnd_pos
    hδ f hf hdisj hs (fun i => (d₀ i).precision_lt_one) R hRet o
    hIncoming hTerminal hG gRet (fun p v z => (hMetric.1 p v z).symm)
end DifferentialGeometry.PDE.RicciFlow.StandardCap
