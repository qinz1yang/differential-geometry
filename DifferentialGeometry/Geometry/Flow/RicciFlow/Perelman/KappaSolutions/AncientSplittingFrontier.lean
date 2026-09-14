import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.DimensionThree
  (flow_time_slice_dichotomy_of_sectionalCurvature_eq_zero_at_later_time)
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplittingFrontierTopology : TopologicalSpace F.M := F.topology
local instance ancientSplittingFrontierCharted : ChartedSpace H F.M := F.charted
local instance ancientSplittingFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientSplittingFrontierC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientSplittingFrontierC2 : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
  change IsManifold I ∞ F.M
  infer_instance
local instance ancientSplittingFrontierT2 : T2Space F.M := F.t2
local instance ancientSplittingFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientSplittingFrontierT2TangentBundle :
    T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance ancientSplittingFrontierInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance ancientSplittingFrontierLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance ancientSplittingFrontierSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def NullPlaneUniversalCoverSplitting : Prop :=
  ∀ (t₀ : ℝ), t₀ ≤ 0 →
    Module.finrank ℝ E = 3 →
    (∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t)) →
    (∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t) →
    (∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C) →
    PointedFlowNotFlat (I := I) F →
    ∀ (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀),
      0 <
        (F.S.family.metric t₀).inner x₀ v₀ v₀ *
          (F.S.family.metric t₀).inner x₀ w₀ w₀ -
            ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2 →
      F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0 →
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

theorem ancient_fixed_universal_cover_product_of_null_plane_of_nullPlaneSplitting
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (hsplit : NullPlaneUniversalCoverSplitting (I := I) F) :
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
  obtain ⟨G, hG⟩ :=
    hsplit t₀ ht₀ hdim hcomplete hcurvature hbounded hnotFlat x₀ v₀ w₀ hplane hnull
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨Phi, hscalarG, hscalar0, hprod⟩ := hG
  exact ancient_fixed_universal_cover_product_of_negative_time_metric_product
    (I := I) F G Phi hconnected hcomplete hscalarG hscalar0 hprod

omit [I.Boundaryless] in
theorem nullPlane_curvatureOperatorImageAt_finrank_cone_membership
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (t : ℝ) (ht : t ≤ 0) :
    ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  intro x
  have h := pointedFlow_metricAlgebraicCurvatureTensorAt_mem_nonnegativeCone
    F hcurvature t ht x
  simpa only [metricAlgebraicCurvatureTensorAt] using h

theorem nullPlane_slice_dichotomy_at_t₀
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (t₀ : ℝ) (ht₀ : t₀ < 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    (metricScalarAt (I := I) (F.S.base.metric t₀) x₀ = 0 ∧
      ∀ x : F.M, curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric t₀) x
        ⟨metricRm04At (I := I) (F.S.base.metric t₀) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric t₀) x⟩ = 0) ∨
    (0 < metricScalarAt (I := I) (F.S.base.metric t₀) x₀ ∧
      ∀ x : F.M, Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) x
          ⟨metricRm04At (I := I) (F.S.base.metric t₀) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t₀) x⟩) = 1) := by
  let _ : ConnectedSpace F.M := hconnected
  have hreg : Set.Icc (t₀ - 1) t₀ ⊆ ancientTimeInterval.regular := by
    intro r hr
    simp only [ancientTimeInterval_regular, Set.mem_Iio]
    linarith [hr.2, ht₀]
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
  have h := flow_time_slice_dichotomy_of_sectionalCurvature_eq_zero_at_later_time
    (S := F.S) F.isSolution hdim (s := t₀ - 1) (t := t₀) (by linarith) hreg
    (fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F hcurvature r
      (hr.2.trans ht₀.le))
    (x₀ := x₀) v₀ w₀ hvw hsec
  exact h.1

theorem nullPlane_curvatureOperatorImageAt_finrank_le_one_on_past
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (t₀ : ℝ) (ht₀ : t₀ < 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∀ t : ℝ, t ≤ t₀ → ∀ x : F.M,
      Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩) ≤ 1 := by
  let _ : ConnectedSpace F.M := hconnected
  have hdich := nullPlane_slice_dichotomy_at_t₀ F hconnected hdim hcurvature t₀ ht₀
    x₀ v₀ w₀ hplane hnull
  have hslice : ∀ y : F.M, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) y
        ⟨metricRm04At (I := I) (F.S.base.metric t₀) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric t₀) y⟩) ≤ 1 := by
    intro y
    rcases hdich with ⟨_, hendo⟩ | ⟨_, hrank⟩
    · have hzero : Module.finrank ℝ
          (curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) y
            ⟨metricRm04At (I := I) (F.S.base.metric t₀) y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (F.S.base.metric t₀) y⟩) = 0 := by
        rw [curvatureOperatorImageAt_eq_range, hendo y]
        simp
      rw [hzero]
      exact Nat.zero_le 1
    · rw [hrank y]
  intro t ht x
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have hreg : Set.Icc t t₀ ⊆ ancientTimeInterval.regular := by
      intro r hr
      simp only [ancientTimeInterval_regular, Set.mem_Iio]
      linarith [hr.2, ht₀]
    have hmono := curvatureOperatorImageAt_finrank_le_at_later_time (S := F.S) F.isSolution hdim
      hlt hreg
      (fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F hcurvature r
        (hr.2.trans ht₀.le)) x x₀
    exact hmono.trans (hslice x₀)
  · exact hslice x

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
