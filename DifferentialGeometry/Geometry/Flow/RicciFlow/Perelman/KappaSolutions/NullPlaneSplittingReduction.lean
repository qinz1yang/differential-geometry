import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactnessFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNullPlane
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceShrinkerReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ForwardFlatness
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance nullPlaneSplittingReductionTopology : TopologicalSpace F.M := F.topology
local instance nullPlaneSplittingReductionCharted : ChartedSpace H F.M := F.charted
local instance nullPlaneSplittingReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance nullPlaneSplittingReductionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance nullPlaneSplittingReductionT2 : T2Space F.M := F.t2
local instance nullPlaneSplittingReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance nullPlaneSplittingReductionInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance nullPlaneSplittingReductionLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance nullPlaneSplittingReductionSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def NegativeTimeUniversalCoverMetricProduct : Prop :=
  ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
    let _ : TopologicalSpace G.M := G.topology
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
    let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
    let _ : IsManifold (𝓡 2) 1 G.M :=
      IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
    let _ : T2Space G.M := G.t2
    let _ : SigmaCompactSpace G.M := G.sigmaCompact
    ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
      (∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
      (∀ y : G.M, 0 < G.S.scalar 0 y) ∧
      ∀ (t : ℝ), t < 0 → ∀ (y : G.M) (s : ℝ)
        (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
        (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
          (G.S.family.metric t).inner y v w + a * c

def RankOnePastMetricProductSplitting : Prop :=
  Module.finrank ℝ E = 3 →
    (∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t) →
    (∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t)) →
    (∃ t₁ : ℝ, t₁ < 0 ∧ ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
        ⟨metricRm04At (I := I) (F.S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric t) x⟩) = 1) →
    NegativeTimeUniversalCoverMetricProduct (I := I) F

def AncientNullPlaneNegativeTimePropagation : Prop :=
  Module.finrank ℝ E = 3 →
    (∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t) →
    (∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t)) →
    (∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C) →
    PointedFlowNotFlat (I := I) F →
    ∀ (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀),
      0 <
        (F.S.family.metric 0).inner x₀ v₀ v₀ *
          (F.S.family.metric 0).inner x₀ w₀ w₀ -
            ((F.S.family.metric 0).inner x₀ v₀ w₀) ^ 2 →
      F.S.base.rm04 0 x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0 →
      ∃ t₁ : ℝ, t₁ < 0 ∧ ∃ x₁ : F.M, ∃ a b : TangentSpace I x₁,
        0 <
          (F.S.family.metric t₁).inner x₁ a a *
            (F.S.family.metric t₁).inner x₁ b b -
              ((F.S.family.metric t₁).inner x₁ a b) ^ 2 ∧
        F.S.base.rm04 t₁ x₁ (vec4 (I := I) a b b a) = 0

theorem rankOnePastMetricProductSplitting_of_metricProduct
    (h : NegativeTimeUniversalCoverMetricProduct (I := I) F) :
    RankOnePastMetricProductSplitting (I := I) F :=
  fun _ _ _ _ => h

theorem exists_negative_time_null_plane_of_metricProduct
    (h : NegativeTimeUniversalCoverMetricProduct (I := I) F)
    (t : ℝ) (ht : t < 0) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
            ((F.S.family.metric t).inner x a b) ^ 2 ∧
        F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0 := by
  obtain ⟨G, hG⟩ := h
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨Phi, -, -, hprod⟩ := hG
  exact exists_null_plane_of_universal_cover_product F G Phi t (fun y s v w a c =>
    hprod t ht y s v w a c)

theorem ancientNullPlaneNegativeTimePropagation_of_metricProduct
    (h : NegativeTimeUniversalCoverMetricProduct (I := I) F) :
    AncientNullPlaneNegativeTimePropagation (I := I) F :=
  fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨-1, by norm_num, exists_negative_time_null_plane_of_metricProduct F h (-1) (by norm_num)⟩

theorem negativeTimeUniversalCoverMetricProduct_of_splitting
    (h : NegativeTimeUniversalCoverSplitting (I := I) F) :
    NegativeTimeUniversalCoverMetricProduct (I := I) F := by
  obtain ⟨G, -, -, hcompleteG, hscalarG, hscalar0, Phi, hprod⟩ := h
  exact ⟨G, Phi, fun t ht => hscalarG t ht, hscalar0, fun t ht => hprod t ht⟩

theorem negativeTimeUniversalCoverSplitting_of_metricProduct
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (h : NegativeTimeUniversalCoverMetricProduct (I := I) F) :
    NegativeTimeUniversalCoverSplitting (I := I) F := by
  obtain ⟨G, hG⟩ := h
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨Phi, hscalarG, hscalar0, hprod⟩ := hG
  exact negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product F
    (ancient_fixed_universal_cover_product_of_negative_time_metric_product
      (I := I) F G Phi hconnected hcomplete hscalarG hscalar0 hprod)

theorem negativeTimeUniversalCoverSplitting_iff_metricProduct
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t)) :
    NegativeTimeUniversalCoverSplitting (I := I) F ↔
      NegativeTimeUniversalCoverMetricProduct (I := I) F :=
  ⟨negativeTimeUniversalCoverMetricProduct_of_splitting F,
    negativeTimeUniversalCoverSplitting_of_metricProduct F hconnected hcomplete⟩

theorem nullPlaneUniversalCoverSplittingAt_of_metricProduct
    (h : NegativeTimeUniversalCoverMetricProduct (I := I) F) (t₀ : ℝ) :
    NullPlaneUniversalCoverSplittingAt (I := I) F t₀ := by
  intro _ht₀ _hdim _hcomplete _hcurvature _hbounded _hnotFlat _x₀ _v₀ _w₀ _hplane _hnull
  exact h

theorem metricProduct_of_nullPlaneUniversalCoverSplittingAt
    (hdim : Module.finrank ℝ E = 3)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0)
    (hsplit : NullPlaneUniversalCoverSplittingAt (I := I) F t₀) :
    NegativeTimeUniversalCoverMetricProduct (I := I) F :=
  hsplit ht₀ hdim hcomplete hcurvature hbounded hnotFlat x₀ v₀ w₀ hplane hnull

theorem nullPlaneUniversalCoverSplittingAt_iff_metricProduct
    (hdim : Module.finrank ℝ E = 3)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    NullPlaneUniversalCoverSplittingAt (I := I) F t₀ ↔
      NegativeTimeUniversalCoverMetricProduct (I := I) F :=
  ⟨fun hsplit => metricProduct_of_nullPlaneUniversalCoverSplittingAt F hdim hcomplete
      hcurvature hbounded hnotFlat ht₀ x₀ v₀ w₀ hplane hnull hsplit,
    fun h => nullPlaneUniversalCoverSplittingAt_of_metricProduct F h t₀⟩

omit [I.Boundaryless] in
private theorem rmNormSq_eq_zero_of_image_finrank_eq_zero
    (hdim : Module.finrank ℝ E = 3) (t : ℝ) (x : F.M)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
      ⟨metricRm04At (I := I) (F.S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric t) x⟩) = 0) :
    F.rmNormSq (I := I) t x = 0 := by
  have hbot : curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
      ⟨metricRm04At (I := I) (F.S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric t) x⟩ = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hop : curvatureOperatorEndomorphismAt (I := I) (F.S.family.metric t) x
      ⟨metricRm04At (I := I) (F.S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric t) x⟩ = 0 := by
    refine ContinuousLinearMap.ext fun a => ?_
    have ha : curvatureOperatorEndomorphismAt (I := I) (F.S.family.metric t) x
        ⟨metricRm04At (I := I) (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.family.metric t) x⟩ a ∈
        (curvatureOperatorEndomorphismAt (I := I) (F.S.family.metric t) x
          ⟨metricRm04At (I := I) (F.S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.family.metric t) x⟩).range := ⟨a, rfl⟩
    rw [← curvatureOperatorImageAt_eq_range] at ha
    rw [hbot] at ha
    simpa using ha
  have hrm : metricRm04At (I := I) (F.S.family.metric t) x = 0 :=
    DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) (F.S.family.metric t) x hdim hop
  have hrm' : F.S.base.rm04 t x = 0 := by
    have h1 : F.S.base.rm04 t x =
        metricRm04At (I := I) (F.S.base.metric t) x := rfl
    rw [h1, ← SolutionOn.family_metric F.S]
    exact hrm
  rw [show F.rmNormSq (I := I) t x = Tensor0SBundle.normSq0S (I := I)
      (F.S.base.metric t) x 4 (F.S.base.rm04 t x) from by
    simp only [PointedFlowData.rmNormSq, SolutionOn.family_metric]]
  rw [hrm']
  simp only [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S,
    Tensor0SBundle.MetricFiberData.inner, map_zero]

theorem nullPlane_curvatureOperatorImageAt_finrank_eq_one_on_past
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    {t₀ : ℝ} (ht₀ : t₀ < 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∀ t : ℝ, t ≤ t₀ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
        ⟨metricRm04At (I := I) (F.S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric t) x⟩) = 1 := by
  obtain ⟨hscalar, hslice⟩ :=
    nullPlane_scalar_pos_and_rank_one_at_negative_time F hdim hconnected hcomplete
      hcurvature hbounded hnotFlat t₀ ht₀ x₀ v₀ w₀ hplane hnull
  have hsliceF : ∀ y : F.M, Module.finrank ℝ (curvatureOperatorImageAt (I := I)
      (F.S.family.metric t₀) y
      ⟨metricRm04At (I := I) (F.S.family.metric t₀) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric t₀) y⟩) = 1 := fun y => by
    rw [SolutionOn.family_metric F.S]
    exact hslice y
  have hconeOf : ∀ r : ℝ, r ≤ 0 → ∀ y : F.M,
      (⟨metricRm04At (I := I) (F.S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric r) y⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) y) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
    fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F hcurvature r hr
  intro t ht x
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have hreg : Set.Icc t t₀ ⊆ ancientTimeInterval.regular := by
      intro r hr
      simp only [ancientTimeInterval_regular, Set.mem_Iio]
      exact lt_of_le_of_lt hr.2 ht₀
    have hmono := curvatureOperatorImageAt_finrank_le_at_later_time (S := F.S)
      F.isSolution hdim hlt hreg (fun r hr => hconeOf r (le_of_lt (lt_of_le_of_lt hr.2 ht₀)))
      x x₀
    rw [hsliceF x₀] at hmono
    have hreg' : Set.Icc (t - 1) t ⊆ ancientTimeInterval.regular := by
      intro r hr
      simp only [ancientTimeInterval_regular, Set.mem_Iio]
      exact lt_of_le_of_lt hr.2 (lt_of_lt_of_le hlt ht₀.le)
    have hcone' : ∀ r ∈ Set.Icc (t - 1) t, ∀ y : F.M,
        (⟨metricRm04At (I := I) (F.S.family.metric r) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.family.metric r) y⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := F.M) y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
      fun r hr => hconeOf r (le_of_lt (lt_of_le_of_lt hr.2 (lt_of_lt_of_le hlt ht₀.le)))
    have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time (S := F.S)
      F.isSolution hdim (s := t - 1) (t := t) (by linarith) hreg' hcone' x
    have hconst := curvatureOperatorImageAt_finrank_eq_at_later_time (S := F.S)
      F.isSolution hdim (s := t - 1) (t := t) (by linarith) hreg' hcone'
    have hne : Module.finrank ℝ (curvatureOperatorImageAt (I := I)
        (F.S.family.metric t) x
        ⟨metricRm04At (I := I) (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.family.metric t) x⟩) ≠ 0 := by
      intro hzero
      have hflat : ∀ y : F.M, F.rmNormSq (I := I) t y = 0 := fun y =>
        rmNormSq_eq_zero_of_image_finrank_eq_zero F hdim t y
          (by rw [hconst y x]; exact hzero)
      obtain ⟨K, hK0, hK⟩ := hbounded t t₀ hlt ht₀.le
      have hflatAll := complete_forward_flatness F hlt
        (fun r hr => by
          simp only [ancientTimeInterval_carrier, Set.mem_Iic]
          exact le_of_lt (lt_of_le_of_lt hr.2 ht₀))
        (fun r hr => by
          simp only [ancientTimeInterval_regular, Set.mem_Iio]
          exact lt_of_lt_of_le hr.2 ht₀.le)
        (fun r hr => hcomplete r (le_of_lt (lt_of_le_of_lt hr.2 ht₀)))
        ⟨K, fun r hr y => hK r hr y⟩ hflat
      have hrm04 : metricRm04At (I := I) (F.S.base.metric t₀) x₀ = 0 := by
        have h1 : F.S.base.rm04 t₀ x₀ = 0 :=
          (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) (F.S.base.metric t₀) x₀ 4
            (F.S.base.rm04 t₀ x₀)).mp
            (by
              simpa only [PointedFlowData.rmNormSq, SolutionOn.family_metric] using
                hflatAll t₀ ⟨ht, le_rfl⟩ x₀)
        simpa only [SolutionFamily.rm04, metricRm04_apply] using h1
      have hsc : metricScalarAt (I := I) (F.S.base.metric t₀) x₀ = 0 :=
        metricScalarAt_eq_zero_of_metricRm04At_eq_zero (I := I) (F.S.base.metric t₀) x₀ hrm04
      rw [hsc] at hscalar
      exact lt_irrefl 0 hscalar
    have htri' : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
        ⟨metricRm04At (I := I) (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.family.metric t) x⟩) = 0 ∨
        Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
          ⟨metricRm04At (I := I) (F.S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.family.metric t) x⟩) = 1 ∨
        Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
          ⟨metricRm04At (I := I) (F.S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.family.metric t) x⟩) = 3 := htri
    rcases htri' with h0 | h1 | h3
    · exact absurd h0 hne
    · exact h1
    · omega
  · have h := hsliceF x
    rw [SolutionOn.family_metric F.S] at h
    exact h

theorem ancient_fixed_universal_cover_product_of_null_plane_of_metricProduct
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
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0)
    (hmetric : NegativeTimeUniversalCoverMetricProduct (I := I) F) :
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
  exact ancient_fixed_universal_cover_product_of_null_plane_of_nullPlaneSplittingAt
    (I := I) F hconnected hcomplete t₀ ht₀ hdim hcurvature hbounded hnotFlat x₀ v₀ w₀
    hplane hnull (nullPlaneUniversalCoverSplittingAt_of_metricProduct F hmetric t₀)

theorem ancient_fixed_universal_cover_product_of_null_plane_of_rankOnePastSplitting
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    {t₁ : ℝ} (ht₁ : t₁ < 0) (x₁ : F.M) (a b : TangentSpace I x₁)
    (hplane₁ : 0 <
      (F.S.family.metric t₁).inner x₁ a a *
        (F.S.family.metric t₁).inner x₁ b b -
          ((F.S.family.metric t₁).inner x₁ a b) ^ 2)
    (hnull₁ : F.S.base.rm04 t₁ x₁ (vec4 (I := I) a b b a) = 0)
    (hsplitting : RankOnePastMetricProductSplitting (I := I) F) :
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
            (G.S.family.metric t).inner y v w + a * c :=
  ancient_fixed_universal_cover_product_of_null_plane_of_metricProduct F hdim hconnected
    hcomplete hcurvature hbounded hnotFlat t₁ ht₁.le x₁ a b hplane₁ hnull₁
    (hsplitting hdim hcurvature hcomplete
      ⟨t₁, ht₁, nullPlane_curvatureOperatorImageAt_finrank_eq_one_on_past F hcomplete
        hcurvature hbounded hnotFlat hconnected hdim ht₁ x₁ a b hplane₁ hnull₁⟩)

theorem ancient_fixed_universal_cover_product_of_null_plane_of_terminalPropagation
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
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0)
    (hpropagation : AncientNullPlaneNegativeTimePropagation (I := I) F)
    (hsplitting : RankOnePastMetricProductSplitting (I := I) F) :
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
  rcases lt_or_eq_of_le ht₀ with hlt | rfl
  · exact ancient_fixed_universal_cover_product_of_null_plane_of_rankOnePastSplitting F
      hdim hconnected hcomplete hcurvature hbounded hnotFlat hlt x₀ v₀ w₀ hplane hnull
      hsplitting
  · obtain ⟨t₁, ht₁, x₁, a, b, hplane₁, hnull₁⟩ :=
      hpropagation hdim hcurvature hcomplete hbounded hnotFlat x₀ v₀ w₀ hplane hnull
    exact ancient_fixed_universal_cover_product_of_null_plane_of_rankOnePastSplitting F
      hdim hconnected hcomplete hcurvature hbounded hnotFlat ht₁ x₁ a b hplane₁ hnull₁
      hsplitting

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
