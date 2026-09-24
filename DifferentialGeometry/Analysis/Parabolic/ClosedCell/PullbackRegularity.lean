import DifferentialGeometry.Analysis.Parabolic.ClosedCell.LipschitzRegularity
import DifferentialGeometry.Topology.Handle.ClosedCell.ChartNeighborhood

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

theorem contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩball : closure Ω ⊆ (toEuclidean (E := V)) '' Metric.ball c r) :
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
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
        IsOpen Ω₀ → closure Ω₀ ⊆ Ω →
        ContDiffOn ℝ (⊤ : ℕ∞) u (Ioo a' b' ×ˢ Ω₀) := by
  intro Ψ Q u hu hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let α : ClosedCell (m + 1) := ⟨0, by simp⟩
  have hα : ‖α.val‖ < 1 := by simp [α]
  let z : W := (toEuclidean (E := V)) c -
    r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
  let A : W ≃ₜ W := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft z)
  have hcl (S : Set W) : closure (A ⁻¹' S) = A ⁻¹' closure S :=
    (A.preimage_closure S).symm
  have hcompact : IsCompact (closure (A ⁻¹' Ω)) := by
    rw [hcl]
    exact A.isCompact_preimage.mpr hΩc
  have htarget : closure (A ⁻¹' Ω) ⊆
      toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target := by
    intro y hy
    rw [hcl] at hy
    have hy' := hΩball hy
    have himage := affine_image_closedCell_extChartAt_target
      (toEuclidean (E := V)) α hα c hr
    change (fun y : W => A y) ''
      (toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) = _ at himage
    rw [← himage] at hy'
    rcases hy' with ⟨x, hx, hxy⟩
    rwa [A.injective hxy] at hx
  have hΩ₀A : IsOpen (A ⁻¹' Ω₀) := hΩ₀.preimage A.continuous
  have hΩ₀sub : closure (A ⁻¹' Ω₀) ⊆ A ⁻¹' Ω := by
    rw [hcl]
    exact preimage_mono hΩ₀Ω
  have hs := contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩc hcompact htarget u hu hweak
    haa hbb hΩ₀A hΩ₀sub
  have himage : (fun y : W => z + r • y) '' (A ⁻¹' Ω₀) = Ω₀ := by
    change A '' (A ⁻¹' Ω₀) = Ω₀
    exact A.surjective.image_preimage Ω₀
  change ContDiffOn ℝ (⊤ : ℕ∞) u
    (Ioo a' b' ×ˢ ((fun y : W => z + r • y) '' (A ⁻¹' Ω₀))) at hs
  rwa [himage] at hs

end DifferentialGeometry.Analysis.Parabolic
