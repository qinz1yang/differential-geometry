import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

structure TensorChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (_P₀ : TensorCompIdx (E := E) r s) where
  toChartData : ChartBilinearH1ComplData (I := I) (M := M) g α

namespace TensorChartBilinearH1ComplData

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def uChart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.uChart

def fChart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.fChart

def weakPartial {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    Fin (Module.finrank ℝ E) → EuclN → ℝ :=
  D.toChartData.weakPartial

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma u_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.uChart = D.toChartData.uChart := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma f_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.fChart = D.toChartData.fChart := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma weak_partial_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.weakPartial = D.toChartData.weakPartial := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma u_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    MemLp D.uChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.u_chart_memLp_weighted

omit [NeZero (Module.finrank ℝ E)] in
lemma f_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    MemLp D.fChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.f_chart_memLp_weighted

omit [NeZero (Module.finrank ℝ E)] in
lemma weak_partial_locally_memLp {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weakPartial i) 2 ((volume : Measure EuclN).restrict K) :=
  D.toChartData.weak_partial_locally_memLp i K hK hK_in

omit [NeZero (Module.finrank ℝ E)] in
lemma weak_partial_isWeakPartial {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (D.weakPartial i) D.uChart
      (chartTargetEuclid (I := I) (M := M) α) :=
  D.toChartData.weak_partial_isWeakPartial i

omit [NeZero (Module.finrank ℝ E)] in
lemma variational_identity {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (ψ : EuclN → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.toChartData.variational_identity ψ hψ hψ_cs hψ_supp

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_u_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.uChart 2 ((volume : Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted hK_compact hK_meas hK_in

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_f_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.fChart 2 ((volume : Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.f_chart_memLp_weighted hK_compact hK_meas hK_in

end TensorChartBilinearH1ComplData

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor_chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_supp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
