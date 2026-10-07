import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapScalarLower_S53

/-!
# CH12-S53, group 1b: `q/4 ≤ R` on the flowed cap, abstract form

`cap_scalar_lower_S53` is the conclusion of step (b) of hZC v2 on any smooth Ricci-flow solution
`S` on `[0, T]` over a charted 3-manifold `M` which (i) starts with `R ≥ 1/2` at `z`, (ii) has
order-2 jets `≤ B` at `z` along `[0, T]`, (iii) has final-time metric the `q`-scaled pullback of
`L` under an injective local diffeomorphism `f` (this is the kernel's last-time identification with
`f = backwardSurvivorIncomingMap ∘ Ξ`), (iv) `c √B T ≤ 1/4`, where `c` is the Laplacian constant
of the Laplacian estimate (`lapR_le_jet_S52`, S52: `hlap` below is its shape, no inline assumption).  Conclusion: `q / 4 ≤ R_L (f z)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

theorem cap_scalar_lower_S53 {M N : Type} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (c : ℝ) (hc : 0 < c)
    (hlap : ∀ (N : Type) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
      [IsManifold ThreeModel ∞ N] [T2Space N]
      {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := N) D),
      IsSolutionOn (I := ThreeModel) S →
      ∀ (t : ℝ) (x : N), t ∈ D.carrier →
        |laplacianAt (I := ThreeModel) (flowG (I := ThreeModel) S) t (S.scalar t) x| ≤
          c * Real.sqrt (DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq
            (I := ThreeModel) 2 (S.base.metric t) x))
    (B T q : ℝ) (hT : 0 ≤ T) (hq : 0 < q)
    (S : SolutionOn (I := ThreeModel) (M := M) (RealTimeInterval.closed 0 T hT))
    (hS : IsSolutionOn (I := ThreeModel) S) (z : M)
    (hinit : 1 / 2 ≤ S.scalar 0 z)
    (hB : ∀ t ∈ Icc 0 T, CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) 2
        (S.base.metric t) z ≤ B)
    (L : SmoothRiemannianMetric ThreeModel N) (f : M → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (hinj : Function.Injective f)
    (hfinal : ∀ y (v w : TangentSpace ThreeModel y), (S.base.metric T).inner y v w =
      q * L.inner (f y) (mfderiv ThreeModel ThreeModel f y v) (mfderiv ThreeModel ThreeModel f y w)) :
    c * Real.sqrt B * T ≤ 1 / 4 → q / 4 ≤ metricScalarAt L (f z) := by
  intro hsmall
  have hode := scalar_ge_of_lapR_S53 c B T hT S hS z
    (fun t ht => hlap M S hS t z ht) hB hc.le
  have hscal : S.scalar T z = metricScalarAt L (f z) / q := by
    change metricScalarAt (S.base.metric T) z = _
    exact scalar_eq_of_scaled_inner_local_S53 _ L f hf hinj hq hfinal z
  have h4 : 1 / 4 ≤ metricScalarAt L (f z) / q := by linarith
  have := (le_div_iff₀ hq).mp h4
  linarith

end GC.LongTime.Ch12
