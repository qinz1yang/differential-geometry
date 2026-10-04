import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle
import DifferentialGeometry.Geometry.Comparison.Soul.SoulDiffeomorph

/-!
# Consumer of the LC61 kernel

On a complete connected noncompact manifold with `sec ≥ 0`, compose the open-disk-bundle
diffeomorphism with the PC soul diffeomorphism `exists_soul_normal_diffeomorph`: the open unit
normal disk bundle of the soul is smoothly identified with the whole manifold, fixing the soul.
This is the last step of the LC61 proof (open disk bundle → `νS` → `N` by the retained `Θ`).
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

/-- **Consumer of the LC61 kernel.** The open unit normal disk bundle of the PC soul is mapped
onto the whole normal bundle by `Ψ`, and then onto the manifold by the soul diffeomorphism `Θ`;
the composite fixes the soul pointwise. -/
theorem soul_openDisk_bundle_onto_manifold
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧
      let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
      let _ := embeddedSliceChartedSpace hS
      let a := normalBundlePrebundle g hEnorm hconv hB
      let _ := a.totalSpaceTopology
      let _ := a.toFiberBundle
      let _ := a.toVectorBundle
      ∃ Ψ : PartialDiffeomorph
          ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
          ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
          (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) (normalBundleFiber g S))
          (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) (normalBundleFiber g S)) ∞,
        ∃ Θ : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) ≃ₘ⟮
              (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
          Ψ.source = {z | g.inner z.proj.1 z.snd.1 z.snd.1 < 1} ∧ Ψ.target = univ ∧
          ∀ q : S, Θ (Ψ ⟨q, 0⟩) = q.1 := by
  obtain ⟨S, hconv, hB, hSne, hScomp, -, -, -, -, Θ, hΘ⟩ :=
    exists_soul_normal_diffeomorph (I := I) g hEnorm hsec p
  refine ⟨S, hconv, hB, hSne, hScomp, ?_⟩
  obtain ⟨Ψ, hs, ht, hΨ⟩ := exists_soul_normal_openDisk_partialDiffeomorph (I := I) g hEnorm hconv hB
  refine ⟨Ψ, Θ, hs, ht, fun q => ?_⟩
  rw [hΨ]
  simp only [smul_zero]
  exact hΘ q

end DifferentialGeometry.Geometry.Collapse
