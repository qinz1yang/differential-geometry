import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicEnergy

/-!
# Finite-spectral local-addition slice regularity

The moving-mass harmonic-map Galerkin construction differentiates the
Dirichlet density in the spatial variable.  This file extracts the first
consumer-shaped consequence of the joint local-addition chart: on one
coefficient ball, every finite-spectral slice is a genuine smooth self-map,
and its bundled tangent map has the expected one-lower regularity.
-/

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

/-- The target component of the finite-spectral diagonal exponential is
jointly `C^n` in the coefficient and spatial variables on the uniform
pointwise local-addition ball. -/
theorem hmfSpecMap_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I
        (n : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hjoint⟩ :=
    hmfSpecAdd_cd (I := I) (M := M) q S n hn
  refine ⟨R, hR, ?_⟩
  simpa only [hmfAdd, hmfSpecLaunch] using hjoint.snd

/-- A single finite-spectral coefficient slice of the intrinsic local
addition is genuinely `C^n` on the whole manifold.  The coefficient radius
is uniform in the spatial point (but, correctly, may depend on the finite
mode set). -/
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
      (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (n : ℕ∞)
      (fun y : M ↦ (u, y)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  exact hP.comp x hin

/-- On the same kind of finite-spectral ball, the bundled spatial derivative
of every local-addition slice is `C¹`.  This is the regularity object used by
the pointwise Dirichlet density; it is derived from the actual slice map and
does not treat `mfderiv` as an independent field. -/
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
