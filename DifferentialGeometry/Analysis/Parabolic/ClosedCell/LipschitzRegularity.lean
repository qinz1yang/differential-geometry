import DifferentialGeometry.Analysis.Parabolic.ClosedCell.SmoothRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.SpatialLp

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Analysis.Sobolev.Euclidean
  (exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn)

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

private local instance : MeasurableSpace W :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ V)) → ℝ)

theorem contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω)) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (u : ℝ × W → ℝ), LocallyLipschitzOn (Icc a b ×ˢ closure Ω) u →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
            fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) u
          (Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀)) := by
  intro z Ψ Q Ωh hΩhc hΩhs u hu hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
  obtain ⟨U, K, hU, hK, hspatial⟩ :=
    exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn hΩ hΩc hu 2
  have hucont : ContinuousOn u (Ioo a b ×ˢ Ω) := hu.continuousOn.mono <|
    fun _ hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, subset_closure hq.2⟩
  have hweakLp (φ : ℝ × W → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0) ∂ν) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
    calc
      _ = ∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hU] with q hq
        rw [hq]
      _ = ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := hweak φ hφ hφc hφs
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hK] with q hq
        simp only [hq]
  exact contDiffOn_affineImage_of_continuousOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K u hU hucont
    hspatial hweakLp haa hbb hΩ₀ hΩ₀Ω

end DifferentialGeometry.Analysis.Parabolic
