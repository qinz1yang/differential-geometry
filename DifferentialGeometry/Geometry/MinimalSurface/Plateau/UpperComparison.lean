import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExactAttainment
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskFirstVariation
import DifferentialGeometry.Analysis.Calculus.Derivative.UpperContact









noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]




theorem SmoothDiskExtension.leastSpanningArea_le
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : lipschitzContractibleLoop g}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ.val.val (t : loopCircle)))
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U) (hσ : IsSmoothPositiveCircleMap σ)
    (htrace : diskTrace u = γ.val.val.comp σ) :
    leastSpanningArea g γ ≤ riemannianDiskArea g u := by
  obtain ⟨v, hv, harea⟩ :=
    exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace
      g hγ hσ htrace (hu.lipschitz g)
  exact (leastSpanningArea_le_competitor g γ hv).trans_eq harea




theorem IsConformalMinimizingDisk.isotopy_upper_comparison
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {γ : ∀ t, lipschitzContractibleLoop (G t)}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r : ℝ => (γ t₀).val.val (r : loopCircle)))
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (hu : IsConformalMinimizingDisk (G t₀) (γ t₀).val.val u σ U)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (htrace : ∀ᶠ t in 𝓝 t₀, (γ t).val.val =
      (⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp (γ t₀).val.val) :
    let F := fun t => riemannianDiskArea (G t)
      ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)
    let W := fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t₀ 1
    let d := (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      ∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))
    (∀ᶠ t in 𝓝 t₀, leastSpanningArea (G t) (γ t) ≤ F t) ∧
      F t₀ = leastSpanningArea (G t₀) (γ t₀) ∧ HasDerivAt F d t₀ ∧
      limsup (fun t => (slope (fun r => leastSpanningArea (G r) (γ r)) t₀ t : EReal))
        (𝓝[>] t₀) ≤ (d : EReal) := by
  dsimp only
  let F := fun t => riemannianDiskArea (G t)
    ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)
  have hupper : ∀ᶠ t in 𝓝 t₀, leastSpanningArea (G t) (γ t) ≤ F t := by
    filter_upwards [htrace] with t ht
    let f : C(M, M) := ⟨Φ t, (Φ t).contMDiff.continuous⟩
    have hγt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun r : ℝ => (γ t).val.val (r : loopCircle)) := by
      rw [ht]
      exact (Φ t).contMDiff.comp hγ
    apply (hu.extension.comp f (Φ t).contMDiff).leastSpanningArea_le hγt hu.positiveTrace
    change f.comp (diskTrace u) = _
    rw [hu.trace, ht]
    rfl
  have heq : F t₀ = leastSpanningArea (G t₀) (γ t₀) := by
    have hf : (⟨Φ t₀, (Φ t₀).contMDiff.continuous⟩ : C(M, M)).comp u = u := by
      ext z
      simp [hΦ₀]
    dsimp only [F]
    rw [hf]
    exact hu.area_eq_leastSpanningArea hγ
  have hd := (hu.extension.hasDerivAt_area_isotopy_flux hG ht₀ hT hT₀ hΦ hΦ₀ hu.conformal
    (fun z hz => hu.harmonic z (Metric.ball_subset_closedBall hz))).2.2
  exact ⟨hupper, heq, hd, DifferentialGeometry.Analysis.limsup_right_slope_le_of_upper_contact hd
    (hupper.filter_mono nhdsWithin_le_nhds) heq.symm⟩

end DifferentialGeometry.Geometry
