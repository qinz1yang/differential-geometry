import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabChartBootstrap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabClosedMetricEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRm04Limit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

section ChartReconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance slabFlowBootstrapC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance slabFlowBootstrapC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem slabGram_model_to_manifold
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (p : M)
    (i j : Fin (Module.finrank ℝ E))
    (hmodel : ContDiffOn ℝ ∞
      (fun q : ℝ × E => chartGramOnE (I := I) (g q.1) p i j q.2)
      (J ×ˢ (extChartAt I p).target)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) p q.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) p).baseSet) := by
  let U := J ×ˢ (trivializationAt E (TangentSpace I) p).baseSet
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun q : ℝ × M => (q.1, extChartAt I p q.2)) U := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).comp
      contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    apply Set.mem_preimage.mpr
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
  have hmaps : MapsTo (fun q : ℝ × M => (q.1, extChartAt I p q.2)) U
      (J ×ˢ (extChartAt I p).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hxsrc : x ∈ (extChartAt I p).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
    exact ⟨ht, (extChartAt I p).map_source hxsrc⟩
  have hcomp := hmodel.contMDiffOn.comp hf hmaps
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ ⟨_, hx⟩
  have hxsrc : x ∈ (extChartAt I p).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
  change chartGramMatrix (I := I) (g t) p x i j =
    chartGramMatrix (I := I) (g t) p ((extChartAt I p).symm (extChartAt I p x)) i j
  rw [(extChartAt I p).left_inv hxsrc]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem slabMetricCLM_Ioo
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ Set.univ) := by
  set gsh : ℝ → SmoothRiemannianMetric I M := fun s => g (s + a) with hgsh
  have haddC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 + a, p.2)) :=
    (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
  have hsubC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 - a, p.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have hgram_sh : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (gsh p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1 + a, p.2))
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      rintro ⟨s, m⟩ ⟨hs, hm⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hm⟩
    exact (hgram x₀ i j).comp haddC.contMDiffOn hmaps
  have hsh := metricCLMSection_jointContMDiffOn_of_chartGram
    (I := I) gsh (b - a) hgram_sh
  have hmaps2 : Set.MapsTo (fun p : ℝ × M => (p.1 - a, p.2))
      (Set.Ioo a b ×ˢ (Set.univ : Set M))
      (Set.Ioo (0 : ℝ) (b - a) ×ˢ (Set.univ : Set M)) := by
    rintro ⟨t, m⟩ ⟨ht, _⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Set.mem_univ _⟩
  have hcomp := hsh.comp hsubC.contMDiffOn hmaps2
  refine hcomp.congr ?_
  rintro ⟨t, m⟩ _
  simp only [Function.comp_apply, hgsh, sub_add_cancel]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem slabMetricFrame_Ioo
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Idx : Type*}
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (Set.Ioo a b ×ˢ u) := by
  have hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ u) :=
    (slabMetricCLM_Ioo (I := I) g a b hgram).mono
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × M => p.2) (s := Set.Ioo a b ×ˢ u)
    (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    (v := fun p : ℝ × M => frame i p.2)
    (w := fun p : ℝ × M => frame j p.2) hψ hv hw
  intro p hp
  have hpx := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem slabMetricFamilySmooth_of_gram
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a ≤ b)
    (hgram : ∀ (p : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) p q.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) p).baseSet))
    (hcoeff : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t => (g t).inner x v w) (Icc a b))
    (htensor : tensor0SFamilyContinuousOnSet (I := I) 2 (Icc a b)
      (fun t x => metricTensorField (I := I) (g t) x)) :
    MetricFamilySmoothOn (RealTimeInterval.closed a b hab) g := by
  have hgramOpen : ∀ (p : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) p q.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) p).baseSet) :=
    fun p i j => (hgram p i j).mono fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩
  refine ⟨?_, hcoeff, htensor, ?_⟩
  · intro x v w
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun t : ℝ => (t, x)) (Ioo a b) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hψ : ContMDiffOn 𝓘(ℝ, ℝ)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun t : ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
          ((g t).inner x)) (Ioo a b) :=
      (slabMetricCLM_Ioo g a b hgramOpen).comp hcurve (fun t ht => ⟨ht, mem_univ _⟩)
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x v)
        (Ioo a b) := contMDiffOn_const
    have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x w)
        (Ioo a b) := contMDiffOn_const
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
      (E₃ := Bundle.Trivial M ℝ) (b := fun _ : ℝ => x)
      (ψ := fun t : ℝ => (g t).inner x)
      (v := fun _ : ℝ => v) (w := fun _ : ℝ => w) hψ hv hw
    have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (g t).inner x v w) (Ioo a b) := by
      intro t ht
      have hpt := happ t ht
      rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
      exact hpt.2
    exact hscalar.contDiffOn
  · intro Idx _ frame u hframe i j
    exact slabMetricFrame_Ioo g a b hgramOpen frame hframe i j

end ChartReconstruction

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

theorem IsSlabLimit.isSolutionOn_of_spatialJets
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g)
    (hjets : ∀ (p : L.space.M) (r : ℕ) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContinuousOn (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
        (chartGramOnE (I := I3) (g q.1) p i j) q.2)
        (Icc (-delta) 0 ×ˢ (extChartAt I3 p).target)) :
    IsSolutionOn (flowOn (N := L.space.M)
      (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  have hpde : ∀ t ∈ Ioo (-delta) 0, ∀ (x : L.space.M) (v w : TangentSpace I3 x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I3) (g t) x v w) t :=
    fun t ht => IsSlabLimit.metric_hasDerivAt L hle hlim ht
  have hgram : ∀ (p : L.space.M) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I3) 𝓘(ℝ) ∞
        (fun q : ℝ × L.space.M => chartGramMatrix (I := I3) (g q.1) p q.2 i j)
        (Icc (-delta) 0 ×ˢ (trivializationAt ThreeSpace (TangentSpace I3) p).baseSet) := by
    intro p i j
    have hmodel := chartGram_contDiffOn_of_spatialJets g p (by linarith : -delta < 0)
      (isOpen_extChartAt_target (I := I3) p) Subset.rfl (hjets p)
      hpde
    exact slabGram_model_to_manifold g (Icc (-delta) 0) p i j
      ((contDiffOn_pi.mp (contDiffOn_pi.mp hmodel i)) j)
  have hsmooth := slabMetricFamilySmooth_of_gram g (by linarith : -delta ≤ 0) hgram
    (IsSlabLimit.metricCoeff_continuousOn L hle hlim)
    (IsSlabLimit.metricTensor_cont L hle hlim)
  exact isSolutionOn_of_regularity g hsmooth hpde
    (IsSlabLimit.scalar_continuousOn L hle hlim)
    (fun t ht x => scalarTime_of_joint g (Icc (-delta) 0)
      (uniqueDiffOn_Icc (by linarith)) hgram t ht x)
    (IsSlabLimit.ricciTensor_cont L hle hlim)
    (IsSlabLimit.rm04Tensor_cont L hle hlim)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
