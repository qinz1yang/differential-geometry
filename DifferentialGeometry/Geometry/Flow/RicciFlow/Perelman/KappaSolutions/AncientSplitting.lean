import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRankProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientNullPlane
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientCurvatureRank

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

theorem ancient_fixed_universal_cover_product_of_curvatureOperatorImage_rank_eq_one
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hrank : ∀ t ≤ (0 : ℝ), ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (F.S.family.metric t) x)) = 1) :
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
  let _ : ConnectedSpace F.M := hconnected
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology F.M := ChartedSpace.secondCountable_of_sigmaCompact H F.M
  let U := F.S.universalCover
  have hU : IsSolutionOn U := F.isSolution.universalCover F.S
  have hcomp (t : ℝ) (ht : t ≤ 0) : RiemannianMetricComplete (U.family.metric t) :=
    F.S.universalCover_complete t ⟨hcomplete t ht⟩
  have hr (t : ℝ) (ht : t ≤ 0) (x : UniversalCover F.M) :
      Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (U.family.metric t) x)) = 1 :=
    (UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric
      (F.S.family.metric t) x hdim).trans (hrank t ht (UniversalCover.proj x))
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, S, Phi, hconn, hsimply, hS, hc, hs, hp⟩ :=
    exists_positive_surface_global_product_on_closed_past_of_curvatureOperatorImage_rank_eq_one
      (show (0 : ℝ) ≤ 0 from le_rfl) U hU hdim hcomp hr
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  let _ := hconn
  let G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval :=
    { M := N
      topology := htop
      charted := hcs
      smooth := hmanifold
      t2 := ht2
      sigmaCompact := hσ
      t2TangentBundle := inferInstance
      basepoint := (Phi.symm (⟨F.basepoint, ⟦Path.refl F.basepoint⟧⟩ : UniversalCover F.M)).1
      S := S
      isSolution := hS }
  refine ⟨G, hconn, hsimply, fun t ht => (hc t ht).complete, hs, Phi, ?_⟩
  intro t ht y s v w a c
  have hmetric := congrArg (fun g => g.inner (y, s) (v, a) (w, c)) (hp t ht)
  have hpb := Diffeomorph.pullbackMetricCross_inner
    (U.family.metric t) Phi (y, s) (v, a) (w, c)
  have hprod := SmoothRiemannianMetric.prod_inner (S.family.metric t)
    (euclideanMetric (E := ℝ)) (y, s) (v, a) (w, c)
  have heuc : (euclideanMetric (E := ℝ)).inner s a c = a * c := by
    change inner ℝ a c = a * c
    rw [RCLike.inner_apply]
    simp only [conj_trivial]
    ring
  exact hpb.symm.trans (hmetric.trans (hprod.trans
    (congrArg (fun z : ℝ => (S.family.metric t).inner y v w + z) heuc)))

theorem ancient_fixed_universal_cover_product_of_terminal_null_plane
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (x₀ : F.M) (v w : TangentSpace I x₀)
    (hplane : 0 < (F.S.base.metric 0).inner x₀ v v * (F.S.base.metric 0).inner x₀ w w -
      ((F.S.base.metric 0).inner x₀ v w) ^ 2)
    (hnull : metricRm04StandardAt (F.S.base.metric 0) x₀ v w w v = 0) :
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
  let _ : ConnectedSpace F.M := hconnected
  have hnonflat : ∃ t ≤ (0 : ℝ), ∃ x : F.M, metricRm04At (F.S.base.metric t) x ≠ 0 := by
    obtain ⟨t, ht, x, hx⟩ := hnotFlat
    refine ⟨t, ht, x, ?_⟩
    intro hz
    apply hx
    exact (DifferentialGeometry.Tensor0SBundle.normSq0S_eq_zero_iff _ x 4 _).mpr hz
  apply ancient_fixed_universal_cover_product_of_curvatureOperatorImage_rank_eq_one
    F hdim hconnected hcomplete
  intro t ht x
  exact curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_nonflat_null_plane
    F.S F.isSolution hdim (fun _ hr => hr) (fun _ hr => hr)
    (fun r hr => ⟨hcomplete r hr⟩) hbounded hnonflat le_rfl x₀ v w hplane hnull ht x


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
