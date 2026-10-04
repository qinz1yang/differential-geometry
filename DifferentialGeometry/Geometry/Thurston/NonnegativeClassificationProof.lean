import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Classification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Curvature.PositiveSectionalRicci
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.NonnegativeCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureScalar
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Geometry.Thurston.SphericalProductDevelopingMap
import DifferentialGeometry.Geometry.Thurston.FoldDescent
import DifferentialGeometry.Geometry.Thurston.ModelAtlas.Descent
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckProductAction
import DifferentialGeometry.Geometry.Metric.ProductIsometry
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductCompactness
import DifferentialGeometry.Geometry.Thurston.NonnegativeGeometrizes
import DifferentialGeometry.Geometry.Thurston.FlatPrime
import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedral
import DifferentialGeometry.Geometry.Thurston.SphericalProductUniversalCover
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Closure

/-!
# Closed nonnegatively curved `3`-manifolds carry a spherical, `S² × ℝ` or flat structure

Chapter 7, packet P8 (Hamilton 1986). `closed_nonnegative_sectional_classification_proved` has the
statement of the admitted `closed_nonnegative_sectional_classification`; it is assembled from the
Ricci flow results of the tree. `closedNonnegativeClassification` discharges the named input
`ClosedNonnegativeClassification` and `geometrizes_of_sectional_nonneg_proved` feeds it, with
`flatStructurePrime` and the `S² × ℝ` packets, to `geometrizes_of_nonnegative_of_classification`.

* Assembly `exists_geometricStructure_of_sectional_nonneg` (model `𝓡 3`): run the flow from `g`
  (`flow_to_seed`), keep the curvature operator nonnegative
  (`metric_curvature_operator_nonnegative_preserved`), and at time `T / 2` use the constant rank
  trichotomy `0, 1, 3` with a parallel kernel (strong maximum principle).
* Rank `0`: the metric is flat and P4 gives a Euclidean atlas
  (`exists_euclideanStructure_of_metricRm04At_eq_zero`).
* Rank `3`: sectional curvature is positive, so Ricci is positive; Hamilton 1982
  (`hamilton_admits_constant_positive_sectional_curvature`) and rescaling give a spherical atlas
  (`exists_sphericalStructure_of_hasPositiveSectionalCurvature`).
* Rank `1`: the flow is transported to the model `morseModelThree`, the image line is parallel and
  the universal cover splits as `N × ℝ` with `N` compact of positive curvature
  (`exists_sphericalProductStructure_of_parallelLine`). Deck transformations act by isometries
  `φ × (affine)`; the local lemma `exists_isometryInvariant_roundMetric` (proved by
  `exists_isometryInvariant_roundMetric_proved`, `EquivariantRoundMetricA5Closure`) gives a
  round metric on `N` invariant under every isometry; it descends along the universal cover
  (`GeometricStructure.ofFold`, `metricFiberCompatible_proj_of_deck_invariant`).
* `exists_isometryInvariant_roundMetric` is equivariant uniformization of `S²`: by Hamilton 1988
  the normalized Ricci flow of a positively curved surface converges to constant curvature, and by
  uniqueness every isometry of the initial metric is an isometry of the limit (alternatively:
  uniformization, and compact subgroups of the Möbius group are conjugate into `O(3)`).
* A carrier with empty boundary is treated through its interior atlas on the type synonym
  `InteriorCopy` (`exists_geometricStructure_of_boundaryless`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open GC.Geometry.SphericalProduct
open scoped Manifold ContDiff

namespace GC.Geometry

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CI" => SpatialNeckCylinderModel
local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2
local notation "MM3" => DifferentialGeometry.Topology.Morse.MorseModel 3

theorem exists_isometryInvariant_roundMetric {N : Type*} [TopologicalSpace N]
    [ChartedSpace MM2 N] [IsManifold 𝓘(ℝ, MM2) ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]
    (h : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (hscal : ∀ y, 0 < metricScalarAt h y) :
    ∃ h₁ : SmoothRiemannianMetric 𝓘(ℝ, MM2) N,
      (∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
        metricRm04StandardAt h₁ y X Y Y X =
          1 * (h₁.inner y X X * h₁.inner y Y Y - h₁.inner y X Y * h₁.inner y X Y)) ∧
      ∀ φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N,
        Diffeomorph.pullbackMetric h φ = h → Diffeomorph.pullbackMetric h₁ φ = h₁ :=
  exists_isometryInvariant_roundMetric_proved h hscal

theorem metricFiberCompatible_proj_of_deck_invariant {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M] [Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [Inhabited M] (g : SmoothRiemannianMetric I (UniversalCover M))
    (hinv : ∀ a : FundamentalGroup M (default : M),
      Diffeomorph.pullbackMetric g (deckDiffeo (I := I) a) = g) :
    metricFiberCompatible g proj (proj_localDiffeo (I := I)) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (proj_eq_iff_smul y x).mp hxy.symm
  exact localPushInner_eq_of_fiber_preserving_isometry g proj (proj_localDiffeo (I := I))
    (deckDiffeo (I := I) a) (funext fun _ => rfl) (hinv a) y

theorem proj_surjective_of_pathConnected {X : Type*} [TopologicalSpace X] [Inhabited X]
    [PathConnectedSpace X] : Function.Surjective (proj : UniversalCover X → X) :=
  fun x => ⟨⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath default x)⟩, rfl⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
theorem exists_euclideanStructure_of_metricRm04At_eq_zero (g : SmoothRiemannianMetric (𝓡 3) M)
    (h0 : ∀ x, metricRm04At g x = 0) :
    ∃ G : GeometricStructure (𝓡 3) M, G.model = .euclidean := by
  have hc : HasConstantSectionalCurvature g 0 := by
    rw [hasConstantSectionalCurvature_iff]
    intro x X Y
    simp [metricRm04StandardAt_apply, h0 x]
  have hg := DifferentialGeometry.RiemannianMetricComplete.of_compact g
  exact ⟨⟨.euclidean, g, hg, hasThurstonAtlas_euclidean_of_hasConstantSectionalCurvature g hg hc,
    fun h => by cases h⟩, rfl⟩

theorem exists_sphericalStructure_of_hasPositiveSectionalCurvature
    (g : SmoothRiemannianMetric (𝓡 3) M) (hpos : hasPositiveSectionalCurvature g) :
    ∃ G : GeometricStructure (𝓡 3) M, G.model = .spherical := by
  have hric : positiveRicciMetric g :=
    HasPositiveSectionalCurvature.positive_ricci_metric hpos (by simp)
  have hM : DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold (I := 𝓡 3)
      (M := M) := ⟨inferInstance, inferInstance, inferInstance, by simp⟩
  obtain ⟨g₁, c, hc, hg₁⟩ :=
    HamiltonPositiveRicci.hamilton_admits_constant_positive_sectional_curvature
      hM ⟨g, hric⟩
  let g₂ := scaleMetric c hc g₁
  have hcs : HasConstantSectionalCurvature g₂ 1 := by
    rw [hasConstantSectionalCurvature_iff]
    intro x X Y
    rw [DifferentialGeometry.PDE.RicciFlow.metricRm04StandardAt_scaleMetric, hg₁ x X Y]
    simp only [g₂, scaleMetric, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hg := DifferentialGeometry.RiemannianMetricComplete.of_compact g₂
  exact ⟨⟨.spherical, g₂, hg, hasThurstonAtlas_spherical_of_hasConstantSectionalCurvature g₂ hg hcs,
    fun h => by cases h⟩, rfl⟩


theorem exists_sphericalProductStructure_of_parallelLine
    (g : SmoothRiemannianMetric morseModelThree M)
    (S : ContMDiffVectorSubbundle (I := morseModelThree) (F := MM3)
      (V := TangentSpace morseModelThree) (n := (∞ : WithTop ℕ∞)))
    (hS : S.rank = 1) (hpar : Connection.IsParallelSubmoduleFamily g S.fiber)
    (hscal : ∀ x, 0 < metricScalarAt g x) :
    ∃ G : GeometricStructure (𝓡 3) M, G.model = .sphericalProduct := by
  let J := morseModelThree
  let idJ : M ≃ₘ⟮𝓡 3, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 3) M
    morseEquivThree
  have hg : DifferentialGeometry.RiemannianMetricComplete g :=
    DifferentialGeometry.RiemannianMetricComplete.of_compact g
  let : LocallyPathConnectedSpace E3 := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E3 M
  let : Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := J)
  let : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨N, topN, csN, mfdN, t2N, σN, h, hconn, hsc, hcompl, F, -, hiso⟩ :=
    exists_global_product_diffeomorph_of_parallel_line (I := J) (M := M) (m := 2) g hg S hS
      hpar
  let : TopologicalSpace N := topN
  let : ChartedSpace MM2 N := csN
  let : IsManifold 𝓘(ℝ, MM2) ∞ N := mfdN
  let : T2Space N := t2N
  let : SigmaCompactSpace N := σN
  let : ConnectedSpace N := hconn
  let : SimplyConnectedSpace N := hsc
  have hprod : Diffeomorph.pullbackMetricCross (liftedMetric (I := J) g) F =
      h.prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
    have hflat : (euclideanMetric (E := ℝ)).inner z.2 u.2 v.2 = u.2 * v.2 := by
      change inner ℝ u.2 v.2 = _
      rw [RCLike.inner_apply]
      simp only [conj_trivial]
      ring
    rw [hflat]
    exact hiso z.1 z.2 u.1 v.1 u.2 v.2
  have hdim2 : Module.finrank ℝ MM2 = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  let : CompleteSpace MM3 := FiniteDimensional.complete ℝ _
  let : CompleteSpace MM2 := FiniteDimensional.complete ℝ _
  have hfactor : ∀ y : N, metricScalarAt h y = metricScalarAt g (proj (F (y, 0))) := by
    intro y
    have hprod' : metricScalarAt (h.prod (euclideanMetric (E := ℝ))) (y, (0 : ℝ)) =
        metricScalarAt h y := by
      rw [metricScalarAt_productMetric,
        metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp), add_zero]
    have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
      (I := (𝓘(ℝ, MM2)).prod 𝓘(ℝ, ℝ)) (J := J) (g := liftedMetric g) (Phi := F) (x := (y, 0))
    have hs := congrArg
      (fun q : SmoothRiemannianMetric ((𝓘(ℝ, MM2)).prod 𝓘(ℝ, ℝ)) (N × ℝ) =>
        metricScalarAt q (y, 0)) hprod
    rw [hprod'] at hs
    exact hs.symm.trans (hpull.trans (metricScalarAt_lifted g (F (y, 0))))
  have hposN : ∀ y, 0 < metricScalarAt h y := fun y => (hfactor y).symm ▸ hscal _
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  obtain ⟨x₁, -, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set M).Nonempty) hcont.continuousOn
  have hRic : Riemannian.BonnetMyers.RicciBoundedBelow h
      (((Module.finrank ℝ MM2 : ℝ) - 1) * (metricScalarAt g x₁ / 2)) := by
    intro y v
    rw [hdim2]
    norm_num
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two h hdim2]
    have hlower : metricScalarAt g x₁ ≤ metricScalarAt h y := by
      rw [hfactor y]
      exact hmin (Set.mem_univ _)
    have hinner : 0 ≤ h.inner y v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact (h.pos y v hv).le
    exact mul_le_mul_of_nonneg_right (by linarith) hinner
  let : NeZero (Module.finrank ℝ MM2) := ⟨by rw [hdim2]; norm_num⟩
  let : CompactSpace N := Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_complete_metric h
    hcompl (by rw [hdim2]) (by linarith [hscal x₁]) hRic
  obtain ⟨h₁, hsec₁, hinv₁⟩ := exists_isometryInvariant_roundMetric h hposN
  obtain ⟨Φ, hΦ⟩ := exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    (I := 𝓘(ℝ, MM2)) (M := N) (n := 2) (by norm_num) hdim2 h₁ 1 one_pos hsec₁
  let Φ' : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓡 2⟯ SpatialNeckSphere := Φ
  have hΦ' : Diffeomorph.pullbackMetricCross (roundMetric (E := E3) (n := 2)) Φ' = h₁ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    have hx := hΦ x v w
    rw [one_mul] at hx
    exact hx
  have hround : Diffeomorph.pullbackMetricCross h₁ Φ'.symm = roundMetric (E := E3) (n := 2) :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hΦ'
  let P := h₁.prod (euclideanMetric (E := ℝ))
  let gU : SmoothRiemannianMetric J (UniversalCover M) := Diffeomorph.pullbackMetricCross P F.symm
  have hgUF : Diffeomorph.pullbackMetricCross gU F = P := by
    exact (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp rfl :
      Diffeomorph.pullbackMetricCross gU F.symm.symm = P)
  let A : SpatialNeckCylinder ≃ₘ⟮CI, 𝓘(ℝ, MM2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ) :=
    Φ'.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let Ψ := A.trans F
  have hΨ : Diffeomorph.pullbackMetricCross gU Ψ = sphericalProductModelMetric := by
    rw [← Diffeomorph.pullbackMetricCross_trans, hgUF, Diffeomorph.pullbackMetricCross_prodCongr,
      hround, Diffeomorph.pullbackMetricCross_refl, sphericalProductModelMetric_eq_prod]
  have hatlas : HasThurstonAtlas gU .sphericalProduct :=
    ModelAtlas.of_surjective_localDiffeomorph sphericalProductModelMetric gU
      Ψ.isLocalDiffeomorph Ψ.surjective fun x v w => by
        have hx := congrArg (fun q => q.inner x v w) hΨ
        simpa only [Diffeomorph.pullbackMetricCross_inner] using hx
  have hdeck : ∀ a : FundamentalGroup M (default : M),
      Diffeomorph.pullbackMetric gU (deckDiffeo (I := J) a) = gU := by
    intro a
    let D := deckDiffeo (I := J) a
    have hD : Diffeomorph.pullbackMetricCross (liftedMetric (I := J) g) D =
        liftedMetric (I := J) g := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [Diffeomorph.pullbackMetricCross_inner]
      exact deck_inner g a x v w
    let Θ := F.trans (D.trans F.symm)
    have hFsym : Diffeomorph.pullbackMetricCross (h.prod (euclideanMetric (E := ℝ))) F.symm =
        liftedMetric (I := J) g :=
      Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hprod
    have hΘ : Diffeomorph.pullbackMetricCross (h.prod (euclideanMetric (E := ℝ))) Θ =
        h.prod (euclideanMetric (E := ℝ)) := by
      rw [← Diffeomorph.pullbackMetricCross_trans, ← Diffeomorph.pullbackMetricCross_trans, hFsym,
        hD, hprod]
    obtain ⟨φ, ψ, hΘeq, hφ, hψ⟩ :=
      exists_prod_isometries_of_scalar_ne_zero h hdim2 (fun y => (hposN y).ne') Θ hΘ
    have hPΘ : Diffeomorph.pullbackMetricCross P Θ = P := by
      rw [hΘeq, Diffeomorph.pullbackMetricCross_prodCongr,
        Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
        Diffeomorph.pullbackMetricCross_eq_pullbackMetric, hinv₁ φ hφ, hψ]
    have hrel : D.trans F.symm = F.symm.trans Θ := by
      apply Diffeomorph.ext
      intro z
      simp [Θ]
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    change Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross P F.symm) D = gU
    rw [Diffeomorph.pullbackMetricCross_trans, hrel, ← Diffeomorph.pullbackMetricCross_trans, hPΘ]
  have hcompat := metricFiberCompatible_proj_of_deck_invariant (I := J) gU hdeck
  let : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let G₀ := GeometricStructure.ofFold gU hatlas (by decide) proj (proj_localDiffeo (I := J))
    proj_surjective_of_pathConnected hcompat (foldMetric_complete_of_compact _ _ _ _ _)
  exact ⟨G₀.pullback idJ, rfl⟩

theorem exists_geometricStructure_of_sectional_nonneg (g : SmoothRiemannianMetric (𝓡 3) M)
    (hsec : ∀ x (v w : TangentSpace (𝓡 3) x), 0 ≤ metricRm04StandardAt g x v w w v) :
    ∃ G : GeometricStructure (𝓡 3) M,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  obtain ⟨T, ⟨P⟩⟩ := flow_to_seed (I := 𝓡 3) (M := M) g
  have hT := P.time_pos
  have hinit : ∀ x, metricAlgebraicCurvatureTensorAt (P.S.base.metric 0) x ∈
      algebraicCurvatureOperatorNonnegativeCone := by
    intro x
    have h0 : P.S.base.metric 0 = g := P.start
    rw [h0]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      g x hdim).mpr (hsec x)
  have hpres := metric_curvature_operator_nonnegative_preserved
    (smoothOfSolution P.S P.isSolution) (fun _ => hdim) (T := T / 2) (by linarith)
    (fun r hr => ⟨hr.1, by linarith [hr.2]⟩) (fun r hr => ⟨hr.1, by linarith [hr.2]⟩) hinit
  have hR : ∀ r ∈ Set.Icc (T / 4) (T / 2), ∀ x,
      (⟨metricRm04At (P.S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (P.S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := 𝓡 3) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3) (M := M) :=
    fun r hr x => hpres r ⟨by linarith [hr.1], hr.2⟩ x
  have hst : T / 4 < T / 2 := by linarith
  have hreg : Set.Icc (T / 4) (T / 2) ⊆
      (RealTimeInterval.closedOpen 0 T P.time_pos).regular :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  let gt := P.S.family.metric (T / 2)
  have hcone : ∀ x, metricAlgebraicCurvatureTensorAt gt x ∈
      algebraicCurvatureOperatorNonnegativeCone := fun x => hR (T / 2) ⟨hst.le, le_rfl⟩ x
  have heq := curvatureOperatorImageAt_finrank_eq_at_later_time P.S P.isSolution hdim hst hreg hR
  rcases curvatureOperatorImageAt_finrank_trichotomy_at_later_time P.S P.isSolution hdim hst hreg
    hR x₀ with h0 | h1 | h3
  · obtain ⟨G, hG⟩ := exists_euclideanStructure_of_metricRm04At_eq_zero gt fun x => by
      apply DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero gt x hdim
      have hx := (heq x x₀).trans h0
      exact ContinuousLinearMap.coe_injective
        (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hx))
    exact ⟨G, Or.inr (Or.inr hG)⟩
  · let idJ : M ≃ₘ⟮𝓡 3, morseModelThree⟯ M :=
      ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 3) M morseEquivThree
    let : CompleteSpace MM3 := FiniteDimensional.complete ℝ _
    have hdimJ : Module.finrank ℝ MM3 = 3 := by
      simp [DifferentialGeometry.Topology.Morse.MorseModel]
    let : NeZero (Module.finrank ℝ MM3) := ⟨by rw [hdimJ]; norm_num⟩
    let S' := P.S.pullback idJ.symm
    have hS' : IsSolutionOn S' := IsSolutionOn.pullback P.S P.isSolution idJ.symm
    have hR' : ∀ r ∈ Set.Icc (T / 4) (T / 2), ∀ x,
        (⟨metricRm04At (S'.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S'.family.metric r) x⟩ :
            algebraicCurvatureTensorSubmodule (I := morseModelThree) (M := M) x) ∈
              algebraicCurvatureOperatorNonnegativeCone (I := morseModelThree) (M := M) := by
      intro r hr x
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        _ x hdimJ).mpr
      intro v w
      change 0 ≤ metricRm04StandardAt
        (Diffeomorph.pullbackMetricCross (P.S.family.metric r) idJ.symm) x v w w v
      rw [metricRm04Standard_pullbackCross]
      exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        _ _ hdim).mp (hR r hr _) _ _
    have h1' : Module.finrank ℝ (curvatureOperatorImageAt (S'.family.metric (T / 2)) x₀
        ⟨metricRm04At (S'.family.metric (T / 2)) x₀,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S'.family.metric (T / 2)) x₀⟩) =
        1 := by
      have hnat := DimensionThree.metricCurvatureOperatorRankAt_localPull
        (P.S.family.metric (T / 2)) idJ.symm idJ.symm.isLocalDiffeomorph x₀ hdimJ hdim
      have e1 := metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
        (S'.family.metric (T / 2)) x₀ hdimJ
      have e2 := metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
        (P.S.family.metric (T / 2)) x₀ hdim
      have e3 : S'.family.metric (T / 2) = localPullMetric (P.S.family.metric (T / 2))
          idJ.symm idJ.symm.isLocalDiffeomorph :=
        Diffeomorph.pullbackMetricCross_eq_localPullMetric _ _
      rw [← e1, e3]
      exact hnat.trans (e2.trans h1)
    obtain ⟨L, hLrank, -, hLpar⟩ :=
      exists_parallel_curvatureOperatorImageLine_at_later_time S' hS' hdimJ hst hreg hR' h1'
    obtain ⟨G, hG⟩ := exists_sphericalProductStructure_of_parallelLine (S'.family.metric (T / 2))
      L hLrank hLpar
      (metricScalarAt_pos_of_curvatureOperatorImage_rank_eq_one_at_later_time S' hS' hdimJ hst
        hreg hR' h1')
    exact ⟨G, Or.inr (Or.inl hG)⟩
  · obtain ⟨G, hG⟩ := exists_sphericalStructure_of_hasPositiveSectionalCurvature gt
      fun x v w hvw => by
        have hrank : DimensionThree.metricCurvatureOperatorRankAt gt x hdim = 3 :=
          (metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank gt x hdim).trans
            ((heq x x₀).trans h3)
        exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative gt x
          hdim hrank (hcone x) v w (by
            have hv : vec2 v w = ![v, w] := by
              funext i
              fin_cases i <;> rfl
            rwa [hv])
    exact ⟨G, Or.inl hG⟩


def InteriorCopy (X : Type u) : Type u := X

theorem exists_geometricStructure_of_boundaryless {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E3 H} {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [BoundarylessManifold I X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] (g : SmoothRiemannianMetric I X)
    (hsec : Riemannian.SectionalBoundedBelow g 0) :
    ∃ G : GeometricStructure I X,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  let : TopologicalSpace (InteriorCopy X) := ‹TopologicalSpace X›
  let : ChartedSpace E3 (InteriorCopy X) := Manifold.interiorChartedSpace I ∞ (M := X)
  let : IsManifold (𝓡 3) ∞ (InteriorCopy X) := Manifold.interiorIsManifold I ∞ (M := X)
  let : T2Space (InteriorCopy X) := ‹T2Space X›
  let : CompactSpace (InteriorCopy X) := ‹CompactSpace X›
  let : ConnectedSpace (InteriorCopy X) := ‹ConnectedSpace X›
  let Φ : X ≃ₘ⟮I, 𝓡 3⟯ InteriorCopy X := Manifold.interiorAtlasDiffeomorph I ∞ (M := X)
  obtain ⟨G', hG'⟩ := exists_geometricStructure_of_sectional_nonneg
    (Diffeomorph.pullbackMetricCross g Φ.symm) fun x v w => by
      rw [metricRm04Standard_pullbackCross]
      simpa using hsec (Φ.symm x) (mfderiv (𝓡 3) I Φ.symm x v) (mfderiv (𝓡 3) I Φ.symm x w)
  refine ⟨⟨G'.model, Diffeomorph.pullbackMetricCross G'.metric Φ,
    Metric.riemannianMetricComplete_pullbackMetricCross G'.complete Φ, G'.atlas.pullback Φ,
    fun h => ?_⟩, hG'⟩
  rcases hG' with h' | h' | h' <;> rw [h'] at h <;> cases h

open GC.Endpoint in
theorem closed_nonnegative_sectional_classification_proved
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hboundary : W.model.boundary W.Carrier = ∅)
    (hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :
    ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  have := ModelWithCorners.Boundaryless.of_boundary_eq_empty hboundary
  exact exists_geometricStructure_of_boundaryless g hsec

theorem closedNonnegativeClassification : GC.Endpoint.ClosedNonnegativeClassification.{u} :=
  fun W _ g hboundary hsec => closed_nonnegative_sectional_classification_proved W g hboundary hsec

theorem geometrizes_of_sectional_nonneg_proved
    (P : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier) (hsec : Riemannian.SectionalBoundedBelow g 0) :
    GC.Endpoint.Geometrizes P :=
  GC.Endpoint.geometrizes_of_nonnegative_of_classification closedNonnegativeClassification
    GC.Endpoint.flatStructurePrime
    (sphericalProductStandardConnectedSum_of_universalCover_only sphericalProductUniversalCover)
    P g hsec

end GC.Geometry
