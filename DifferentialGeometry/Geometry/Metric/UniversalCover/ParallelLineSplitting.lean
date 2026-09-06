import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelSubbundle
import DifferentialGeometry.Geometry.Connection.GlobalParallelLineSplitting

open Bundle
open scoped Manifold ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

structure GlobalSurfaceProductSplitting
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [Inhabited M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) where
  N : Type
  [topologyN : TopologicalSpace N]
  [chartedN : ChartedSpace
    (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [manifoldN : IsManifold
    (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
  [t2N : T2Space N]
  [sigmaN : SigmaCompactSpace N]
  metricN : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
    (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) N
  connectedN : ConnectedSpace N
  simplyConnectedN : SimplyConnectedSpace N
  completeN : DifferentialGeometry.RiemannianMetricComplete
    (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) metricN
  F : Diffeomorph
    ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
      𝓘(ℝ, ℝ)) I (N × ℝ) (UniversalCover M)
    (↑(⊤ : ℕ∞) : WithTop ℕ∞)
  line : ContMDiffVectorSubbundle
    (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel 3)
    (V := (TangentSpace I : UniversalCover M → Type _))
    (n := (∞ : WithTop ℕ∞))
  line_rank : line.rank = 1
  line_parallel : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily
    (liftedMetric (I := I) g) line.fiber
  line_compatibility : ∀ (y : N) (t : ℝ),
      line.fiber (F (y, t)) =
        ℝ ∙
          ((mfderiv
            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
              𝓘(ℝ, ℝ)) I (fun z : N × ℝ => F z) (y, t))
            (show TangentSpace
              ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                𝓘(ℝ, ℝ)) (y, t) from (0, 1)))
  isometry : ∀ (y : N) (t : ℝ)
      (u v : TangentSpace
        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) y)
      (r q : ℝ),
    (liftedMetric (I := I) g).inner (F (y, t))
        ((mfderiv
          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(ℝ, ℝ)) I (fun z : N × ℝ => F z) (y, t))
          (show TangentSpace
            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
              𝓘(ℝ, ℝ)) (y, t) from (u, r)))
        ((mfderiv
          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
            𝓘(ℝ, ℝ)) I (fun z : N × ℝ => F z) (y, t))
          (show TangentSpace
            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
              𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
      metricN.inner y u v + r * q

def HasGlobalSurfaceProductSplitting
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) : Prop :=
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  Nonempty (GlobalSurfaceProductSplitting (I := I) (M := M) g)

theorem exists_global_product_diffeomorph_of_parallel_line
    {m : ℕ}
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel (m + 1))
      (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily g S.fiber) :
  let _ : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel m) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ h : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
                (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) N,
              And (ConnectedSpace N)
              (And (SimplyConnectedSpace N)
              (And (DifferentialGeometry.RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) h)
              (∃ F : Diffeomorph
                  ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                    𝓘(ℝ, ℝ)) I (N × ℝ) (UniversalCover M)
                  (↑(⊤ : ℕ∞) : WithTop ℕ∞),
                And
                  (∀ (y : N) (t : ℝ),
                    (liftTangentSubbundle (I := I) (M := M) S).fiber (F (y, t)) =
                      ℝ ∙
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (0, 1))))
                  (∀ (y : N) (t : ℝ)
                      (u v : TangentSpace
                        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) y)
                      (r q : ℝ),
                    (liftedMetric (I := I) g).inner (F (y, t))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (u, r)))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
                      h.inner y u v + r * q)))) := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  let _ : SecondCountableTopology H :=
    ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  have hg' : DifferentialGeometry.RiemannianMetricComplete
      (I := I) (liftedMetric (I := I) g) :=
    liftedMetric_complete (I := I) (M := M) g hg
  have hS' := liftTangentSubbundle_isParallel_of_rank_eq_one
    (I := I) (M := M) g S hSrank hS
  exact
    DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_global_product_diffeomorph_of_rank_eq_one
      (liftedMetric (I := I) g) hg'
      (liftTangentSubbundle (I := I) (M := M) S)
      (by simpa using hSrank) hS'

theorem hasGlobalSurfaceProductSplitting_of_parallel_line
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel 3)
      (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily g S.fiber) :
    HasGlobalSurfaceProductSplitting (I := I) (M := M) g := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  have hS' := liftTangentSubbundle_isParallel_of_rank_eq_one
    (I := I) (M := M) g S hSrank hS
  obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσ, h,
      hconnected, hsimplyConnected, hhcomplete, F, hF, hmetric⟩ :=
    exists_global_product_diffeomorph_of_parallel_line
      (I := I) (M := M) (m := 2) g hg S hSrank hS
  let _ : TopologicalSpace N := topologyN
  let _ : ChartedSpace
      (DifferentialGeometry.Topology.Morse.MorseModel 2) N := hcs
  let _ : IsManifold
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) N := hmanifold
  let _ : T2Space N := ht2
  let _ : SigmaCompactSpace N := hσ
  exact ⟨{
    N := N
    metricN := h
    connectedN := hconnected
    simplyConnectedN := hsimplyConnected
    completeN := hhcomplete
    F := F
    line := liftTangentSubbundle (I := I) (M := M) S
    line_rank := by simpa using hSrank
    line_parallel := hS'
    line_compatibility := hF
    isometry := hmetric
  }⟩

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
