import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRankProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientNullPlane

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

private local instance nullProductTopology : TopologicalSpace F.M := F.topology
private local instance nullProductCharted : ChartedSpace H F.M := F.charted
private local instance nullProductSmooth : IsManifold I ∞ F.M := F.smooth
private local instance nullProductC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
private local instance nullProductT2 : T2Space F.M := F.t2
private local instance nullProductSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance nullProductInhabited : Inhabited F.M := ⟨F.basepoint⟩
private local instance nullProductLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
private local instance nullProductSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

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
  rcases lt_or_eq_of_le ht₀ with hneg | rfl
  · exact ancient_fixed_universal_cover_product_of_negative_time_null_plane
      F hdim hconnected hcomplete hcurvature hbounded hnotFlat t₀ hneg x₀ v₀ w₀
      hplane hnull
  · have hzero := ancient_leastCurvatureOperatorEigenvalueAt_eq_zero_of_null_plane
      F hdim hcurvature 0 le_rfl x₀ v₀ w₀ hplane hnull
    obtain ⟨v, w, hgram, hnullneg⟩ :=
      exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero
        F.S F.isSolution hdim ancientTimeInterval_carrier ancientTimeInterval_regular
        (fun t ht => pointedFlow_metricAlgebraicCurvatureTensorAt_mem_nonnegativeCone
          F hcurvature t ht) x₀ hzero (s := -1) (by norm_num)
    exact ancient_fixed_universal_cover_product_of_negative_time_null_plane
      F hdim hconnected hcomplete hcurvature hbounded hnotFlat (-1) (by norm_num)
      x₀ v w hgram hnullneg

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
