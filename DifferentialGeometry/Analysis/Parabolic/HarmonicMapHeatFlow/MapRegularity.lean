import DifferentialGeometry.Analysis.Parabolic.HarmonicMapHeatFlow.Energy
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M]

noncomputable irreducible_def harmonicMapFlowSpectralMap
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} → M :=
  fun z =>
    harmonicMapFlowAdd (I := I) (M := M) q
      (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMap_eq
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (x : M) :
    harmonicMapFlowSpectralMap (I := I) (M := M) q S x =
      fun z : EuclideanSpace ℝ {i // i ∈ S} =>
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x := by
  funext z
  rw [harmonicMapFlowSpectralMap_def]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpectralMap_apply
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (x : M) (z : EuclideanSpace ℝ {i // i ∈ S}) :
    harmonicMapFlowSpectralMap (I := I) (M := M) q S x z =
      harmonicMapFlowAdd (I := I) (M := M) q
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x := by
  rw [harmonicMapFlowSpectralMap_eq]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMap_contMDiff
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I
        (n : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          harmonicMapFlowSpectralMap (I := I) (M := M) q S p.2 p.1)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hjoint⟩ :=
    harmonicMapFlowSpectralAdd_contMDiff (I := I) (M := M) q S n
  refine ⟨R, hR, ?_⟩
  intro p hp
  simpa only [harmonicMapFlowSpectralMap_def, harmonicMapFlowAdd, harmonicMapFlowSpectralLaunch] using (hjoint p hp).snd

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMap_mdifferentiableAt
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ∀ x : M,
          MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
            (harmonicMapFlowSpectralMap (I := I) (M := M) q S x) u := by
  obtain ⟨R, hR, hjoint⟩ :=
    harmonicMapFlowSpectralMap_contMDiff (I := I) (M := M) q S 1
  refine ⟨R, hR, ?_⟩
  intro u hu x
  have hp : (u, x) ∈
      Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) R ×ˢ
        (Set.univ : Set M) :=
    ⟨hu, Set.mem_univ _⟩
  have hopen : IsOpen
      (Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) R ×ˢ
        (Set.univ : Set M)) :=
    Metric.isOpen_ball.prod isOpen_univ
  have hjointAt := (hjoint (u, x) hp).contMDiffAt (hopen.mem_nhds hp)
  have hincl : ContMDiffAt
      𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S})
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (1 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦ (z, x)) u :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact (hjointAt.comp u hincl).mdifferentiableAt (by norm_num)

omit [BoundarylessManifold I M]
  [ConnectedSpace M] in
theorem harmonicMapFlowSpectralSlice_contMDiff
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ContMDiff I I (n : ℕ∞)
          (harmonicMapFlowAdd (I := I) (M := M) q
            (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u)) := by
  obtain ⟨R, hR, hjoint⟩ :=
    harmonicMapFlowSpectralMap_contMDiff (I := I) (M := M) q S n
  refine ⟨R, hR, ?_⟩
  intro u hu x
  have hp :
      (u, x) ∈ Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) R ×ˢ
        (Set.univ : Set M) := ⟨hu, Set.mem_univ x⟩
  have hP := (hjoint (u, x) hp).contMDiffAt
    ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds hp)
  have hin : ContMDiffAt I
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (n : ℕ∞)
      (fun y : M ↦ (u, y)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have hc := hP.comp x hin
  have hfun :
      ((fun p => harmonicMapFlowSpectralMap (I := I) (M := M) q S p.2 p.1) ∘
        Prod.mk u) =
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u) := by
    funext y
    exact harmonicMapFlowSpectralMap_apply (I := I) (M := M) q S y u
  rw [hfun] at hc
  exact hc

omit [BoundarylessManifold I M]
  [ConnectedSpace M] in
theorem harmonicMapFlowSpectralTangent_contMDiff
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ContMDiff I.tangent I.tangent (1 : ℕ∞)
          (tangentMap I I
            (harmonicMapFlowAdd (I := I) (M := M) q
              (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u))) := by
  obtain ⟨R, hR, hslice⟩ :=
    harmonicMapFlowSpectralSlice_contMDiff (I := I) (M := M) q S 2
  refine ⟨R, hR, ?_⟩
  intro u hu
  exact (hslice u hu).contMDiff_tangentMap (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
