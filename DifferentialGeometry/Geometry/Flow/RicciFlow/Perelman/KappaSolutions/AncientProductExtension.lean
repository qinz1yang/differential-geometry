import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Topology.Manifold.ULift

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u v w uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{w, uE, uH} (I := I) ancientTimeInterval)

local instance productExtensionTopology : TopologicalSpace F.M := F.topology
local instance productExtensionCharted : ChartedSpace H F.M := F.charted
local instance productExtensionSmooth : IsManifold I ∞ F.M := F.smooth
local instance productExtensionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance productExtensionT2 : T2Space F.M := F.t2
local instance productExtensionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance productExtensionInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance productExtensionLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance productExtensionSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

set_option backward.isDefEq.respectTransparency false in
theorem ancient_fixed_universal_cover_product_of_surface_product
    (F : PointedFlowData.{max u v, uE, uH} (I := I) ancientTimeInterval)
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (N : Type v) [TopologicalSpace N]
    [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
    [IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (h : ℝ → SmoothRiemannianMetric
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
    (Phi : (N × ℝ) ≃ₘ⟮
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ), I⟯
        UniversalCover F.M)
    (hscalar : ∀ t < 0, ∀ y : N, 0 < metricScalarAt (h t) y)
    (hproduct : ∀ t < 0, Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi =
        (h t).prod (euclideanMetric (E := ℝ))) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G : PointedFlowData.{max u v, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G.M := G.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
      let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
      let _ : IsManifold (𝓡 2) 1 G.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
      let _ : T2Space G.M := G.t2
      let _ : SigmaCompactSpace G.M := G.sigmaCompact
      ConnectedSpace G.M ∧ SimplyConnectedSpace G.M ∧
      (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t)) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
      ∃ Psi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ t : ℝ, t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c := by
  let _ : ConnectedSpace F.M := hconnected
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) (ULift.{u} N) :=
    DifferentialGeometry.Topology.uliftChartedSpace
      (DifferentialGeometry.Topology.Morse.MorseModel 2) N
  let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞
      (ULift.{u} N) :=
    DifferentialGeometry.Topology.isManifold_ulift
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N
  let PsiU : (ULift.{u} N) ≃ₘ⟮
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ N :=
    (DifferentialGeometry.Topology.uliftDiffeomorph
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N).symm
  let e := (morseModelEuclideanModelEquiv 2).toHomeomorph
  let L := morseModelEuclideanModelEquiv 2
  have hcompat : ∀ y : DifferentialGeometry.Topology.Morse.MorseModel 2,
      (𝓡 2) (e y) = L (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y) :=
    fun _ => rfl
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (ULift.{u} N) :=
    DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := ULift.{u} N) e
  let _ : IsManifold (𝓡 2) ∞ (ULift.{u} N) :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := ULift.{u} N)
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) (𝓡 2) e L hcompat
  let PsiM : (ULift.{u} N) ≃ₘ⟮(𝓡 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ (ULift.{u} N) :=
    DifferentialGeometry.Manifold.diffeomorphChartedSpaceTransHomeomorph
      (M := ULift.{u} N) 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)
      (𝓡 2) e L hcompat
  let PsiN : (ULift.{u} N) ≃ₘ⟮(𝓡 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ N := PsiM.trans PsiU
  let Psi : ((ULift.{u} N) × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M :=
    (PsiN.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans Phi
  let U : SolutionOn (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
      (M := (ULift.{u} N) × ℝ) ancientTimeInterval := F.S.universalCover.pullback Psi
  have hU : IsSolutionOn U :=
    IsSolutionOn.pullback F.S.universalCover (F.isSolution.universalCover F.S) Psi
  let g : ℝ → SmoothRiemannianMetric (𝓡 2) (ULift.{u} N) :=
    fun t => (U.family.metric t).sliceFst (0 : ℝ)
  have hUprod (t : ℝ) (ht : t < 0) :
      U.family.metric t = (Diffeomorph.pullbackMetricCross (h t) PsiN).prod
        (euclideanMetric (E := ℝ)) := by
    change Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t))
      ((PsiN.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans Phi) = _
    rw [← Diffeomorph.pullbackMetricCross_trans, hproduct t ht,
      Diffeomorph.pullbackMetricCross_prodCongr, Diffeomorph.pullbackMetricCross_refl]
  have hslice (t : ℝ) (ht : t < 0) :
      g t = Diffeomorph.pullbackMetricCross (h t) PsiN := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    change ((U.family.metric t).sliceFst (0 : ℝ)).inner y v w = _
    rw [SmoothRiemannianMetric.sliceFst_inner, hUprod t ht,
      SmoothRiemannianMetric.prod_inner]
    simp
  have hUprod' (t : ℝ) (ht : t < 0) :
      U.family.metric t = (g t).prod (euclideanMetric (E := ℝ)) := by
    rw [hslice t ht]
    exact hUprod t ht
  have hUprod0 : U.family.metric 0 = (g 0).prod (euclideanMetric (E := ℝ)) :=
    hU.smoothMetric.eq_sliceFst_prod_at_terminal_of_lt
      (by intro t ht; simpa using ht) (euclideanMetric (E := ℝ)) (0 : ℝ) hUprod'
  have hUall : ∀ t ∈ ancientTimeInterval.carrier,
      U.family.metric t = (g t).prod (euclideanMetric (E := ℝ)) := by
    intro t ht
    have ht0 : t ≤ 0 := by simpa using ht
    rcases lt_or_eq_of_le ht0 with hlt | rfl
    · exact hUprod' t hlt
    · exact hUprod0
  have hg : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := 𝓡 2) (M := ULift.{u} N) ancientTimeInterval) :=
    isSolutionOn_sliceFst_of_prod_euclidean U hU hUall
  let xcover : UniversalCover F.M := ⟨F.basepoint, ⟦Path.refl F.basepoint⟧⟩
  let G : PointedFlowData.{max u v, 0, 0} (I := 𝓡 2) ancientTimeInterval := {
    M := ULift.{u} N
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := PsiN.symm (Phi.symm xcover).1
    S := { base := { metric := g } }
    isSolution := hg }
  have hpositive : ∀ t < 0, ∀ y : G.M, 0 < G.S.scalar t y := by
    intro t ht y
    change 0 < metricScalarAt (g t) y
    rw [hslice t ht, metricScalar_cross]
    exact hscalar t ht (PsiN y)
  have hinner : ∀ t < 0, ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c := by
    intro t ht y s v w a c
    have heq := congrArg
      (fun m => m.inner (y, s) (v, a) (w, c)) (hUprod' t ht)
    change (Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Psi).inner
        (y, s) (v, a) (w, c) = ((g t).prod (euclideanMetric (E := ℝ))).inner
          (y, s) (v, a) (w, c) at heq
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner] at heq
    have he : (euclideanMetric (E := ℝ)).inner s a c = a * c := by
      change inner ℝ a c = a * c
      rw [RCLike.inner_apply, conj_trivial, mul_comm]
    rw [he] at heq
    exact heq
  have hpositive0 := splitSurface_scalar_pos_at_zero_of_negative_product F hdim G Psi
    hcomplete hcurvature hbounded hpositive hinner
  exact ancient_fixed_universal_cover_product_of_negative_time_metric_product
    F G Psi hconnected hcomplete hpositive hpositive0 hinner

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
