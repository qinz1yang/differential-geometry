import DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

variable {N : Type} [TopologicalSpace N]
  [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

theorem compactSpace_of_compact_of_base_scalar_pos_of_pullback_eq_prod
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) N)
    (hcomplete : RiemannianMetricComplete h)
    (F : Diffeomorph
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      I (N × ℝ) (UniversalCover M) ∞)
    (hprod : Diffeomorph.pullbackMetricCross (liftedMetric g) F =
      h.prod (euclideanMetric (E := ℝ)))
    (hscalar : ∀ x, 0 < metricScalarAt g x) : CompactSpace N := by
  let _ : CompleteSpace (DifferentialGeometry.Topology.Morse.MorseModel 3) :=
    FiniteDimensional.complete ℝ _
  let _ : CompleteSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) :=
    FiniteDimensional.complete ℝ _
  have hcont : Continuous (metricScalarAt g) :=
    (metricScalar_smooth g).continuous
  obtain ⟨x, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set M).Nonempty) hcont.continuousOn
  let _ : NeZero (Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2)) :=
    ⟨by simp [DifferentialGeometry.Topology.Morse.MorseModel]⟩
  have hfactor : ∀ y : N,
      metricScalarAt h y = metricScalarAt g (proj (F (y, 0))) := by
    intro y
    have hprod' : metricScalarAt (h.prod (euclideanMetric (E := ℝ))) (y, (0 : ℝ)) =
        metricScalarAt h y := by
      rw [metricScalarAt_productMetric,
        metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp), add_zero]
    have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
      (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      (J := I) (g := liftedMetric g) (Phi := F) (x := (y, 0))
    have hs := congrArg
      (fun q : SmoothRiemannianMetric
        ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
        (N × ℝ) => metricScalarAt q (y, 0)) hprod
    rw [hprod'] at hs
    exact hs.symm.trans (hpull.trans (metricScalarAt_lifted g (F (y, 0))))
  have hRic : BonnetMyers.RicciBoundedBelow h
      (((Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2) : ℝ) - 1) *
        (metricScalarAt g x / 2)) := by
    intro y v
    have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
      simp [DifferentialGeometry.Topology.Morse.MorseModel]
    rw [hdim]
    norm_num
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two h hdim]
    have hlower : metricScalarAt g x ≤ metricScalarAt h y := by
      rw [hfactor y]
      exact hmin (Set.mem_univ _)
    have hinner : 0 ≤ h.inner y v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact (h.pos y v hv).le
    exact mul_le_mul_of_nonneg_right (by linarith) hinner
  exact BonnetMyers.bonnet_myers_compactSpace_of_complete_metric h hcomplete
    (by simp [DifferentialGeometry.Topology.Morse.MorseModel])
    (by linarith [hscalar x]) hRic

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

variable (g : SmoothRiemannianMetric I M)
  (P : GlobalSurfaceProductSplitting (I := I) (M := M) g)

theorem metricScalarAt_eq_base (y : P.N) (t : ℝ) :
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    metricScalarAt P.metricN y = metricScalarAt g (proj (P.F (y, t))) := by
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  have hprod := metricScalarAt_prod_flat P.metricN y t
  have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
    (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
    (J := I) (g := liftedMetric g) (Phi := P.F) (x := (y, t))
  have heq := P.pullbackMetric_eq_prod g
  have heqscalar := congrArg
    (fun q : SmoothRiemannianMetric
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      (P.N × ℝ) => metricScalarAt q (y, t)) heq
  rw [hprod] at heqscalar
  exact (heqscalar.symm.trans hpull).trans (metricScalarAt_lifted g (P.F (y, t)))

theorem compactSpace_of_compact_of_base_scalar_pos [CompactSpace M]
    (hscalar : ∀ x, 0 < metricScalarAt g x) :
    let _ : TopologicalSpace P.N := P.topologyN
    CompactSpace P.N := by
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : ConnectedSpace P.N := P.connectedN
  exact compactSpace_of_compact_of_base_scalar_pos_of_pullback_eq_prod
    g P.metricN P.completeN P.F (by simpa only [flatModelMetric] using P.pullbackMetric_eq_prod g)
    hscalar

theorem compactSpace_of_compact_of_nonnegative_of_rank_one [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (P : GlobalSurfaceProductSplitting (I := I) (M := M) g)
    (hcone : ∀ x,
      (⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x, Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 1) :
    let _ : TopologicalSpace P.N := P.topologyN
    CompactSpace P.N := by
  exact compactSpace_of_compact_of_base_scalar_pos g P fun x =>
    metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      (by simp [DifferentialGeometry.Topology.Morse.MorseModel]) g x (hcone x) (hrank x)

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting
