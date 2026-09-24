import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.RicciSoliton

noncomputable section

open Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedCGHMaps (I := I) X P subseq}
  {R : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M}
  {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ}
  {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)

theorem gradientRicciSoliton_and_hamiltonNormalized_time_sub_of_hamilton_jacobi
    (hreg : Iio 0 ⊆ X.D.regular) (a : ℝ) (D : RealTimeInterval)
    (f : ℝ → P.M → ℝ) {t : ℝ} (ht : t ∈ D.regular) (htpos : 0 < t) (hat : a < t) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    let G : MetricConnectionFamily (I := I) (M := P.M) ℝ :=
      { metric := fun r => co.gInf (a - r)
        connection := fun r => leviCivitaConnectionOfMetric (I := I) (co.gInf (a - r))
        metricCompatible := fun r =>
          leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (co.gInf (a - r)) }
    IsHeatPotOn D G (fun r x => -metricScalarAt (co.gInf (a - r)) x)
      (fun r => perelmanDensity (Module.finrank ℝ E) r (f r)) →
    (∀ r, r ∈ D.regular → 0 < r → ∀ x : P.M,
      2 * deriv (fun q => f q x) r +
        (co.gInf (a - r)).inner x
          (gradientFun (I := I) (co.gInf (a - r)) (f r) x)
          (gradientFun (I := I) (co.gInf (a - r)) (f r) x) -
        metricScalarAt (co.gInf (a - r)) x + f r x / r = 0) →
    ∃ hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t),
      gradientRicciSoliton (I := I) (co.gInf (a - t)) ⟨f t, hf⟩ (1 / t) ∧
        hamiltonNormalized (I := I) (co.gInf (a - t)) ⟨f t, hf⟩ (1 / t) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro G hu hHJ
  let D₀ : RealTimeInterval := RealTimeInterval.infiniteOpen 0 (-1) (by norm_num)
  let S : SolutionOn (I := I) (M := P.M) D₀ := { base := { metric := co.gInf } }
  have hS : IsSolutionOn S :=
    co.isSolutionOn_of_carrier_subset (Φ := Φ) hreg (D := D₀) Subset.rfl
  have htime : a - t ∈ D₀.regular := by
    change a - t < 0
    exact sub_neg.mpr hat
  exact gradientRicciSoliton_and_hamiltonNormalized_of_conjugate_density_and_hamilton_jacobi
    S hS a f hu ht htpos htime hHJ

end DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData
