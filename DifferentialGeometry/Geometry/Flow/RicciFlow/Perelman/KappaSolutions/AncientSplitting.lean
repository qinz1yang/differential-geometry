import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance upstreamAncientSplittingTopology : TopologicalSpace F.M := F.topology
local instance upstreamAncientSplittingCharted : ChartedSpace H F.M := F.charted
local instance upstreamAncientSplittingSmooth : IsManifold I ∞ F.M := F.smooth
local instance upstreamAncientSplittingC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance upstreamAncientSplittingT2 : T2Space F.M := F.t2
local instance upstreamAncientSplittingSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance upstreamAncientSplittingInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance upstreamAncientSplittingLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance upstreamAncientSplittingSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

omit [I.Boundaryless] in
theorem pointedFlow_metricAlgebraicCurvatureTensorAt_mem_nonnegativeCone
    (hop : ∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (t : ℝ) (ht : t ≤ 0) :
    ∀ x : F.M, metricAlgebraicCurvatureTensorAt (I := I) (M := F.M)
        (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  intro x
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  intro n c v w
  have h := hop t ht x n c v w
  simpa only [SolutionOn.family, SolutionFamily.rm04, metricRm04_apply,
    metricRm04StandardAt_apply] using h

theorem ancient_leastCurvatureOperatorEigenvalueAt_eq_zero_of_null_plane
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    leastCurvatureOperatorEigenvalueAt (I := I) (F.S.base.metric t₀) x₀
      (metricAlgebraicCurvatureTensorAt (I := I) (M := F.M)
        (F.S.base.metric t₀) x₀) = 0 := by
  have hcone := pointedFlow_metricAlgebraicCurvatureTensorAt_mem_nonnegativeCone
    F hcurvature t₀ ht₀ x₀
  have hvw : LinearIndependent ℝ ![v₀, w₀] :=
    Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := I) (F.S.base.metric t₀) x₀ v₀ w₀
      (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def,
          SolutionOn.family] using hplane)
  have hsec : Geometry.Riemannian.sectionalCurvature (I := I)
      (F.S.base.metric t₀) x₀ v₀ w₀ = 0 :=
    Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero
      (I := I) (F.S.base.metric t₀) x₀ v₀ w₀
      (by simpa only [SolutionFamily.rm04, metricRm04_apply] using hnull)
  have hdimTx : Module.finrank ℝ (TangentSpace I x₀) = 3 := by
    have hfin : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
    rw [hfin, hdim]
  exact Geometry.Curvature.DimensionThree.leastCurvatureOperatorEigenvalueAt_eq_zero_of_sectionalCurvature_eq_zero
    (I := I) (F.S.base.metric t₀) x₀ hdimTx hcone v₀ w₀ hvw hsec

theorem metricComplete_atTime_zero_of_universalCover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M)
    (hprod : ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric 0)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric 0).inner y v w + a * c)
    (hbase : MetricComplete (I := I) (F.atTime 0)) :
    MetricComplete (I := 𝓡 2) (G.atTime 0) := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  let _ : T2Space (TangentBundle (𝓡 2) G.M) := G.t2TangentBundle
  let _ : ConnectedSpace F.M := hconnected
  let _ : SigmaCompactSpace (UniversalCover F.M) :=
    Phi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have hliftBase : RiemannianMetricComplete (I := I) (F.S.family.metric 0) := ⟨hbase⟩
  have hlift : RiemannianMetricComplete (I := I)
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric 0)) :=
    UniversalCover.liftedMetric_complete (I := I) (F.S.family.metric 0) hliftBase
  have heq : Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric 0)) Phi =
      (G.S.family.metric 0).prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    obtain ⟨y, s⟩ := z
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
    change (UniversalCover.liftedMetric (I := I) (F.S.family.metric 0)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) v) =
      (G.S.family.metric 0).inner y u.1 v.1 + inner ℝ (u.2 : ℝ) (v.2 : ℝ)
    rw [RCLike.inner_apply, conj_trivial, mul_comm]
    exact hprod y s u.1 v.1 (u.2 : ℝ) (v.2 : ℝ)
  have hc : RiemannianMetricComplete
      ((G.S.family.metric 0).prod (euclideanMetric (E := ℝ))) := by
    rw [← heq]
    exact DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      (J := I) hlift Phi
  have hfac : RiemannianMetricComplete (I := 𝓡 2) (G.S.family.metric 0) :=
    (RiemannianMetricComplete.prod_iff.mp hc).1
  dsimp only [MetricComplete, PointedFlowData.atTime]
  exact hfac.complete

theorem universalCover_product_inner_at_zero_of_negative_times
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hprod : ∀ t : ℝ, t < 0 → ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric 0)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric 0).inner y v w + a * c := by
  intro y s v w a c
  let V : E := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I
    (fun z : G.M × ℝ => Phi z) (y, s) (v, a)
  let W : E := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I
    (fun z : G.M × ℝ => Phi z) (y, s) (w, c)
  have hcontA : ContinuousWithinAt (fun t : ℝ =>
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        V W) (Set.Iic 0) 0 := by
    have hc := DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn
      (F.S.family.metric) F.isSolution.smoothMetric
      (UniversalCover.proj (Phi (y, s))) V W
    simpa only [ancientTimeInterval_carrier, UniversalCover.liftedMetric_inner_eq] using
      hc.continuousWithinAt (by simp)
  have hcontB : ContinuousWithinAt (fun t : ℝ =>
      (G.S.family.metric t).inner y v w + a * c) (Set.Iic 0) 0 := by
    have hc := DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn
      (G.S.family.metric) G.isSolution.smoothMetric y v w
    have h1 : ContinuousWithinAt (fun t : ℝ => (G.S.family.metric t).inner y v w)
        (Set.Iic 0) 0 := by
      simpa only [ancientTimeInterval_carrier] using hc.continuousWithinAt (by simp)
    exact h1.add continuousWithinAt_const
  have hev : (fun t : ℝ =>
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        V W) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0] (fun t : ℝ =>
      (G.S.family.metric t).inner y v w + a * c) :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hprod t ht y s v w a c
  exact tendsto_nhds_unique
    (hcontA.mono_left (nhdsWithin_mono 0 Set.Iio_subset_Iic_self))
    ((hcontB.mono_left (nhdsWithin_mono 0 Set.Iio_subset_Iic_self)).congr' hev.symm)

theorem ancient_fixed_universal_cover_product_of_negative_splitting
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M)
    (hcompleteF : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hconnG : ConnectedSpace G.M) (hsimplyG : SimplyConnectedSpace G.M)
    (hcompleteG : ∀ t : ℝ, t < 0 → MetricComplete (I := 𝓡 2) (G.atTime t))
    (hscalarG : ∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y)
    (hprod : ∀ t : ℝ, t < 0 → ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c)
    (hscalar0 : ∀ y : G.M, 0 < G.S.scalar 0 y) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G' : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G'.M := G'.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G'.M := G'.charted
      let _ : IsManifold (𝓡 2) ∞ G'.M := G'.smooth
      let _ : IsManifold (𝓡 2) 1 G'.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G'.M) (n := ∞) (by decide)
      let _ : T2Space G'.M := G'.t2
      let _ : SigmaCompactSpace G'.M := G'.sigmaCompact
      ConnectedSpace G'.M ∧ SimplyConnectedSpace G'.M ∧
      (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G'.atTime t)) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y : G'.M, 0 < G'.S.scalar t y) ∧
      ∃ Phi' : (G'.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (y : G'.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi' (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (w, c)) =
            (G'.S.family.metric t).inner y v w + a * c := by
  have hprod0 := universalCover_product_inner_at_zero_of_negative_times F G Phi hprod
  refine ⟨G, hconnG, hsimplyG, ?_, ?_, ⟨Phi, ?_⟩⟩
  · intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hcompleteG t hlt
    · exact metricComplete_atTime_zero_of_universalCover_product F G Phi hconnected hprod0
        (hcompleteF 0 le_rfl)
  · intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hscalarG t hlt
    · exact hscalar0
  · intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hprod t hlt
    · exact hprod0

theorem ancient_fixed_universal_cover_product_of_null_plane
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
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
      ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
