import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientProductExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientProduct
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceShrinkerReduction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance rankProductTopology : TopologicalSpace F.M := F.topology
local instance rankProductCharted : ChartedSpace H F.M := F.charted
local instance rankProductSmooth : IsManifold I ∞ F.M := F.smooth
local instance rankProductC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance rankProductT2 : T2Space F.M := F.t2
local instance rankProductSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance rankProductInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance rankProductLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance rankProductSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

set_option backward.isDefEq.respectTransparency false in
theorem ancient_fixed_universal_cover_product_of_rank_one
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    {s : ℝ} (hs : s < 0) (x₀ : F.M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric s) x₀
      ⟨metricRm04At (F.S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (F.S.family.metric s) x₀⟩) = 1) :
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
      ∃ Psi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ t : ℝ, t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c := by
  let _ : ConnectedSpace F.M := hconnected
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology F.M := ChartedSpace.secondCountable_of_sigmaCompact H F.M
  let _ : PathConnectedSpace F.M := PathConnectedSpace.of_locallyPathConnectedSpace
  let x₀' : UniversalCover F.M := ⟨x₀, ⟦PathConnectedSpace.somePath default x₀⟧⟩
  let U := F.S.universalCover
  have hU : IsSolutionOn U := F.isSolution.universalCover F.S
  have hUc (t : ℝ) (ht : t < 0) : RiemannianMetricComplete (U.family.metric t) :=
    F.S.universalCover_complete t ⟨hcomplete t ht.le⟩
  have hUb (a b : ℝ) (hab : a < b) (hb : b < 0) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : UniversalCover F.M,
        DifferentialGeometry.Tensor0SBundle.normSq0S (U.family.metric t) x 4
          (metricRm04At (U.family.metric t) x) ≤ C := by
    obtain ⟨C, hC, hc⟩ := hbounded a b hab hb.le
    refine ⟨C, hC, ?_⟩
    intro t ht x
    change DifferentialGeometry.Tensor0SBundle.normSq0S
      (UniversalCover.liftedMetric (F.S.family.metric t)) x 4
      (metricRm04At (UniversalCover.liftedMetric (F.S.family.metric t)) x) ≤ C
    rw [UniversalCover.normSq0S_metricRm04At_liftedMetric]
    exact hc t ht (UniversalCover.proj x)
  have hrU : Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric s) x₀'
      ⟨metricRm04At (U.family.metric s) x₀',
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.family.metric s) x₀'⟩) = 1 :=
    (UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric
      (F.S.family.metric s) x₀' hdim).trans hrank
  obtain ⟨N, htop, hcs, hman, ht2, hσ, h, Phi, _, _, _, _, hprod, hscalar⟩ :=
    exists_positive_surface_product_of_rank_one_of_complete_ancient
      U hU hdim
      (by simpa only [ancientTimeInterval_regular] using Set.Subset.refl (Set.Iio (0 : ℝ)))
      hUc hUb hs x₀' hrU
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hσ
  exact ancient_fixed_universal_cover_product_of_surface_product
    F hdim hconnected hcomplete hcurvature hbounded N h Phi hscalar hprod

theorem ancient_fixed_universal_cover_product_of_negative_time_null_plane
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (t₀ : ℝ) (ht₀ : t₀ < 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
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
  have hrank := (nullPlane_scalar_pos_and_rank_one_at_negative_time
    F hdim hconnected hcomplete hcurvature hbounded hnotFlat t₀ ht₀ x₀ v₀ w₀
    hplane hnull).2 x₀
  exact ancient_fixed_universal_cover_product_of_rank_one
    F hdim hconnected hcomplete hcurvature hbounded ht₀ x₀ hrank

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
