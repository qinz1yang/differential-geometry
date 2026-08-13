import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicEnergy
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M]

noncomputable irreducible_def hmfSpecMap
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} → M :=
  fun z =>
    hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S z) x

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem hmfSpecMap_eq
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (x : M) :
    hmfSpecMap (I := I) (M := M) q S x =
      fun z : EuclideanSpace ℝ {i // i ∈ S} =>
        hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S z) x := by
  funext z
  rw [hmfSpecMap_def]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem hmfSpecMap_apply
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (x : M) (z : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfSpecMap (I := I) (M := M) q S x z =
      hmfAdd (I := I) (M := M) q
        (hmfSpecIncl (I := I) (M := M) q S z) x := by
  rw [hmfSpecMap_eq]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem hmfSpecMap_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I
        (n : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          hmfSpecMap (I := I) (M := M) q S p.2 p.1)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hjoint⟩ :=
    hmfSpecAdd_cd (I := I) (M := M) q S n hn
  refine ⟨R, hR, ?_⟩
  intro p hp
  simpa only [hmfSpecMap_def, hmfAdd, hmfSpecLaunch] using (hjoint p hp).snd

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem hmfSpecMap_md
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ∀ x : M,
          MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
            (hmfSpecMap (I := I) (M := M) q S x) u := by
  obtain ⟨R, hR, hjoint⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S 1 (by norm_num)
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
theorem hmfSpecSlice_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ContMDiff I I (n : ℕ∞)
          (hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S u)) := by
  obtain ⟨R, hR, hjoint⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S n hn
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
  simpa only [hmfSpecMap_apply] using hP.comp x hin

omit [BoundarylessManifold I M]
  [ConnectedSpace M] in
theorem hmfSpecTan_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ContMDiff I.tangent I.tangent (1 : ℕ∞)
          (tangentMap I I
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S u))) := by
  obtain ⟨R, hR, hslice⟩ :=
    hmfSpecSlice_cd (I := I) (M := M) q S 2 (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro u hu
  exact (hslice u hu).contMDiff_tangentMap (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
