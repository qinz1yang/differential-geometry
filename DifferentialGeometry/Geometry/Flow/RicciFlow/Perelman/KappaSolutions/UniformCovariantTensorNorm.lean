import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTensorNorm

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformCovTensorC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem uniform_tensor02_covariant_norm_on_compact_closedWindow {D : RealTimeInterval}
    (L : SolutionOn (I := I) (M := M) D) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Icc c b)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hcoord : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E,
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (fun z => A n t ((extChartAt I p).symm z)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      tensor02CovDerivNormWith (I := I) r (A n t) (L.base.metric t) (L.base.metric t)
        ((extChartAt I p).symm y) ≤ ε := by
  exact uniform_tensor02_covariant_norm_on_compact_time_of_closed_interval
    L hL hac hcb hslab hregular hJ hJb A p hU hUt hcoord hK hKU r

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
