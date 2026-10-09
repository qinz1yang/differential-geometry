import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointOutwardNormalFlow

/-!
# Consumer of LC54

On a complete connected noncompact manifold with `sec ≥ 0`, the soul's normal bundle is
diffeomorphic to the manifold by a map `e` fixing the zero section whose rays beyond the radius `ℓ`
are flow lines of ONE smooth field `V`, and `V` pairs at most `-1/4` with every inward unit
minimizing direction to the base point far out. This is the blueprint's form of LC54,
`e (q, t v) = ϕ_{t - ℓ} (e (q, ℓ v))`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **Consumer of LC54.** The soul normal bundle carries an actual diffeomorphism onto the
manifold, fixing the zero section, whose rays beyond `ℓ` are flow lines of one bounded field that
is outward for the base point far out. -/
theorem soul_normal_diffeomorph_point_outward_rays
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧
      ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ϕ : Flow ℝ M, ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A₂ : ℝ, 0 < A₂ ∧
        (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
        (∀ q, A₂ ≤ dist p q → ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
          g.inner q (V q) w ≤ -(1 / 4)) ∧
        let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
        let _ := embeddedSliceChartedSpace hS
        let a := normalBundlePrebundle g hEnorm hconv hB
        let _ := a.totalSpaceTopology
        let _ := a.toFiberBundle
        let _ := a.toVectorBundle
        ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) ≃ₘ⟮
              (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
          (∀ q : S, e ⟨q, 0⟩ = q.1) ∧
          ∀ (q : S) (v : normalBundleFiber (I := I) g S q), g.inner q.1 v.1 v.1 = 1 →
            ∀ t : ℝ, ℓ < t → e ⟨q, t • v⟩ = ϕ (t - ℓ) (e ⟨q, ℓ • v⟩) := by
  obtain ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A₂, hA₂, -, -, hIntegral, hpoint, e, he,
    hezero⟩ := exists_point_outward_normalFlow_data (I := I) g hEnorm hsec p
  refine ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A₂, hA₂, hIntegral, hpoint, e, hezero, ?_⟩
  intro q v hv t ht
  rw [he, he]
  exact normalFlowMap_ray (I := I) g hEnorm S ϕ hℓ.le ht q v hv

end DifferentialGeometry.Geometry.Collapse
