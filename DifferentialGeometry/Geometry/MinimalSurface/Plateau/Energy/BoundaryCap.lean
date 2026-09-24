import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalComparison
import DifferentialGeometry.Topology.MetricSpace.LipschitzExtension
import DifferentialGeometry.Analysis.Integration.BallBoundary
import DifferentialGeometry.Analysis.Sobolev.Interpolation.BoundaryCap
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.BoundaryCap
import DifferentialGeometry.Analysis.Integration.Integral.CompactPlaneEnergy
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.Crosscut

noncomputable section

open Manifold Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem integrable_pullback_energy_and_inf_le_of_lipschitzOn
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} {τ : C(loopCircle, loopCircle)} (hτ : IsWeaklyMonotoneOnce τ)
    {z : ℂ → F} {L : ℝ≥0} (hz : LipschitzOnWith L z (Metric.closedBall (0 : ℂ) 1))
    (hzΦ : MapsTo z (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (htrace : ∀ θ, z (diskBoundary θ) = Φ (γ (τ θ))) :
    let e : ℂ → ℝ := fun x =>
      (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
        pullbackMetricCoefficients g r (z x)
          (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2
    IntegrableOn e (Metric.closedBall (0 : ℂ) 1) ∧
      sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ) ≤ ∫ x in Metric.closedBall (0 : ℂ) 1, e x := by
  obtain ⟨w, C, hw, hzw⟩ := hz.exists_lipschitz_extension
  have hwΦ : MapsTo w (Metric.closedBall (0 : ℂ) 1) (range Φ) := by
    intro x hx
    rw [← hzw hx]
    exact hzΦ hx
  have hwtrace (θ : loopCircle) : w (diskBoundary θ) = Φ (γ (τ θ)) := by
    rw [← hzw (diskBoundary θ).property]
    exact htrace θ
  obtain ⟨D, hD⟩ := exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    g hΦ hU hr hΦU hleft
  obtain ⟨_, _, _, _, _, _, hwi, _⟩ := hD w C hw hwΦ γ τ hwtrace
  have hinf := disk_energy_inf_le_pullback_integral_of_lipschitz g hΦ hU hr
    hΦU hleft hτ hw hwΦ hwtrace
  have heq : (fun x =>
      (pullbackMetricCoefficients g r (w x) (fderiv ℝ w x 1) (fderiv ℝ w x 1) +
        pullbackMetricCoefficients g r (w x)
          (fderiv ℝ w x Complex.I) (fderiv ℝ w x Complex.I)) / 2) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)]
      (fun x => (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
        pullbackMetricCoefficients g r (z x)
          (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2) := by
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere volume (0 : ℂ) 1)] with x hx
    have hgerm : z =ᶠ[𝓝 x] w := by
      filter_upwards [Metric.closedBall_mem_nhds_of_mem hx] with y hy
      exact hzw hy
    rw [hgerm.eq_of_nhds, hgerm.fderiv_eq]
  exact ⟨hwi.congr heq, hinf.trans_eq (integral_congr_ae heq)⟩

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem pullback_energy_boundaryLens_le_of_attachBoundaryCap
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} {σ τ : C(loopCircle, loopCircle)}
    (hσ : IsWeaklyMonotoneOnce σ) (hτ : IsWeaklyMonotoneOnce τ)
    (u q : ℂ → F) (ρ : ℝ) {Lu Lq : ℝ≥0}
    (hu : LipschitzOnWith Lu u (Metric.closedBall (0 : ℂ) 1))
    (hq : LipschitzOnWith Lq q (Metric.closedBall (0 : ℂ) 1))
    (huK : MapsTo u (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (hqK : MapsTo q (boundaryLens ρ) (range Φ))
    (hglue : EqOn q u (Metric.closedBall (0 : ℂ) 1 ∩ Metric.sphere (-1) ρ))
    (hutrace : ∀ θ, u (diskBoundary θ) = Φ (γ (σ θ)))
    (htrace : ∀ θ, attachBoundaryCap u q ρ (diskBoundary θ) = Φ (γ (τ θ))) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    (∫ z in boundaryLens ρ, e u z) ≤
      (∫ z in boundaryLens ρ, e q z) +
        ((∫ z in Metric.closedBall (0 : ℂ) 1, e u z) -
          sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  let w := attachBoundaryCap u q ρ
  have hw := attachBoundaryCap_lipschitzOn hu hq hglue
  have hwK : MapsTo w (Metric.closedBall (0 : ℂ) 1) (range Φ) := by
    intro z hz
    by_cases hi : ‖z + 1‖ ≤ ρ
    · rw [show w z = q z from attachBoundaryCap_inner u q ρ hi]
      exact hqK ⟨by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hi, hz⟩
    · rw [show w z = u z from attachBoundaryCap_outside u q ρ (lt_of_not_ge hi)]
      exact huK hz
  obtain ⟨hwi, hInf⟩ := integrable_pullback_energy_and_inf_le_of_lipschitzOn
    g hΦ hU hr hΦU hleft hτ hw hwK htrace
  have hui := (integrable_pullback_energy_and_inf_le_of_lipschitzOn
    g hΦ hU hr hΦU hleft hσ hu huK hutrace).1
  have hwdecomp := integral_quadratic_fderiv_attachBoundaryCap A u q ρ hwi
  have hudecomp := integral_inter_add_sdiff (t := Metric.closedBall (-1 : ℂ) ρ)
    measurableSet_closedBall hui
  rw [inter_comm] at hudecomp
  change (∫ z in boundaryLens ρ, e u z) +
    (∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (-1) ρ, e u z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, e u z at hudecomp
  change (∫ z in Metric.closedBall (0 : ℂ) 1, e w z) =
    (∫ z in boundaryLens ρ, e q z) +
      ∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (-1) ρ, e u z at hwdecomp
  change sInf _ ≤ ∫ z in Metric.closedBall (0 : ℂ) 1, e w z at hInf
  change (∫ z in boundaryLens ρ, e u z) ≤
    (∫ z in boundaryLens ρ, e q z) +
      ((∫ z in Metric.closedBall (0 : ℂ) 1, e u z) - _)
  linarith

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_uniform_metric_boundary_cap_comparison
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ))) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    ∃ Λ : ℝ, 0 ≤ Λ ∧ (∀ y ∈ range Φ, ‖A y‖ ≤ Λ) ∧
      ∀ (f : ℂ → F) (Kf : ℝ≥0), LipschitzWith Kf f →
      MapsTo f (closedBall (0 : ℂ) 1) (range Φ) →
      ∀ (ψ : CircleDeg1Lift), Continuous ψ →
      (∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Φ (γ ((ψ t : ℝ) : loopCircle))) →
      ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 →
      ∀ (U : Set F) (η : ℝ),
      closedBall (f (circleMap (-1) ρ (-Real.arccos (ρ / 2)))) η ⊆ U →
      (1 + 2 * (KΓ : ℝ) * (J : ℝ)) * Real.sqrt
        (∫ s in Icc (0 : ℝ) 1, ‖deriv (fun s => f (circleMap (-1) ρ
          (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))) s‖ ^ 2) ≤ η →
      ∀ (T : F → F) (LT : ℝ≥0), Differentiable ℝ T →
      (∀ y, ‖fderiv ℝ T y‖ ≤ LT) → MapsTo T U (range Φ) →
      (∀ y ∈ range Φ, T y = y) →
      ∃ (ψbar : CircleDeg1Lift) (q : ℂ → F),
        Continuous ψbar ∧
        EqOn ψbar ψ (⋃ k : ℤ, Ioo (Real.arccos (ρ / 2) / Real.pi + k)
          (1 - Real.arccos (ρ / 2) / Real.pi + k))ᶜ ∧
        (∃ Cq : ℝ≥0, LipschitzWith Cq q) ∧
        MapsTo q (boundaryLens ρ) (range Φ) ∧
        EqOn q f (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ) ∧
        (∀ t : ℝ, attachBoundaryCap f q ρ (circleMap 0 1 (2 * Real.pi * t)) =
          Φ (γ ((ψbar t : ℝ) : loopCircle))) ∧
        (∫ z in boundaryLens ρ, e f z) ≤
          Λ * (2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 *
            (LT : ℝ) ^ 2 * ((Real.pi / 2) * (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 +
              (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi))) *
            (∫ s in Icc (0 : ℝ) 1, ‖deriv (fun s => f (circleMap (-1) ρ
              (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))) s‖ ^ 2) +
            ((∫ z in closedBall (0 : ℂ) 1, e f z) -
              sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
                weaklyMonotoneDiskCompetitors g γ)) := by
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  have hAc : ContinuousOn A (range Φ) :=
    (contDiffOn_pullback_metric_coefficients g hN hr).continuousOn.mono hΦN
  obtain ⟨Λ, hΛ, hΛA, hΛbound⟩ :=
    exists_uniform_integral_plane_quadratic_bound_of_isCompact (isCompact_range hΦ) A hAc
  refine ⟨Λ, hΛ, hΛA, ?_⟩
  intro f Kf hf hfK ψ hψ htrace ρ hρ hρ1 hshort U η hηU hsmall T LT hT hLT hmap hfix
  let Γ : ℝ → F := fun t => Φ (γ (t : loopCircle))
  have hperiod : Function.Periodic Γ 1 := by
    intro t
    simp only [Γ, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hInv' : AntilipschitzWith J (hperiod.lift : loopCircle → F) := by
    intro x y
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    simpa only [Function.Periodic.lift_coe, Γ] using hInv (s : loopCircle) (t : loopCircle)
  have hΓK : range Γ ⊆ range Φ := by
    rintro _ ⟨t, rfl⟩
    exact mem_range_self (γ (t : loopCircle))
  obtain ⟨ψbar, h, q, hψbar, hsame, _, _, _, _, hqLip, hqK, hseam, hcapTrace, hqEnergy⟩ :=
    exists_boundary_cap_of_short_lift_increment Γ hΓ hperiod hInv' hΓK f hf hfK ψ hψ
      htrace hρ hρ1 hshort hηU hsmall T hT hLT hmap hfix
  obtain ⟨Cq, hCq⟩ := hqLip
  let σ := affineCircleMap ψ hψ ψ.map_add_one
  let τ := affineCircleMap ψbar hψbar ψbar.map_add_one
  have hσ : IsWeaklyMonotoneOnce σ :=
    ⟨ψ, hψ, fun _ => rfl, Or.inl ⟨ψ.monotone, ψ.map_add_one⟩⟩
  have hτ : IsWeaklyMonotoneOnce τ :=
    ⟨ψbar, hψbar, fun _ => rfl, Or.inl ⟨ψbar.monotone, ψbar.map_add_one⟩⟩
  have htraceσ (θ : loopCircle) : f (diskBoundary θ) = Φ (γ (σ θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [σ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul] using htrace t
  have htraceτ (θ : loopCircle) : attachBoundaryCap f q ρ (diskBoundary θ) = Φ (γ (τ θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [τ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul, Γ] using hcapTrace t
  have hcomparison := pullback_energy_boundaryLens_le_of_attachBoundaryCap
    g hΦ hN (hr.of_le (by simp)) hΦN hleft hσ hτ f q ρ hf.lipschitzOnWith hCq.lipschitzOnWith
      hfK hqK hseam htraceσ htraceτ
  have hLens : IsCompact (boundaryLens ρ) :=
    (isCompact_closedBall (-1 : ℂ) ρ).inter_right isClosed_closedBall
  have hmetric := (hΛbound q Cq hCq (boundaryLens ρ) hLens hqK).2.2
  have hqle := (le_abs_self _).trans (hmetric.trans
    (mul_le_mul_of_nonneg_left hqEnergy hΛ))
  refine ⟨ψbar, q, hψbar, hsame, ⟨Cq, hCq⟩, hqK, hseam, hcapTrace, ?_⟩
  dsimp only [A, e] at hcomparison hqle ⊢
  calc
    _ ≤ _ := hcomparison
    _ ≤ _ := by nlinarith only [hqle]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_uniform_boundary_cap_energy_estimate
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ (f : ℂ → F) (Kf : ℝ≥0), LipschitzWith Kf f →
      MapsTo f (closedBall (0 : ℂ) 1) (range Φ) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Φ (γ ((ψ t : ℝ) : loopCircle))) →
      ∀ a b B : ℝ, 0 < a → a < b → b < 1 →
      (∀ ρ ∈ Ioo a b, ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      (∫ z in {z : ℂ | dist z (-1) ∈ Icc a b} ∩ closedBall (0 : ℂ) 1,
        ‖fderiv ℝ f z‖ ^ 2) ≤ B →
      B / Real.log (b / a) ≤ ε →
      (∫ z in boundaryLens a, e f z) ≤ C * B / Real.log (b / a) +
        ((∫ z in closedBall (0 : ℂ) 1, e f z) -
          sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  obtain ⟨Λ, hΛ, _, hcomp⟩ := exists_uniform_metric_boundary_cap_comparison
    g hΦ hN hr hΦN hleft γ hΓ hInv
  let D : ℝ := 1 + 2 * (KΓ : ℝ) * J
  have hD : 0 < D := by dsimp only [D]; positivity
  let ε := (η / D) ^ 2 / Real.pi
  have hε : 0 < ε := div_pos (sq_pos_of_pos (div_pos hη hD)) Real.pi_pos
  let Q : ℝ := 2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 *
    (LT : ℝ) ^ 2 * ((Real.pi / 2) * D ^ 2 +
      (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨ε, Λ * Q * Real.pi, hε, by positivity, ?_⟩
  intro f Kf hf hfK ψ hψ htrace a b B ha hab hb1 hshort henergy hsmall
  obtain ⟨ρ, hρ, hE⟩ := exists_radius_normalized_crosscut_energy_le hf ha hab
    (hb1.trans (by norm_num)) henergy
  let Ea := ∫ s in Icc (0 : ℝ) 1, ‖deriv (fun s => f (circleMap (-1) ρ
    (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))) s‖ ^ 2
  have hEa : Ea ≤ (η / D) ^ 2 := by
    calc
      Ea ≤ Real.pi * B / Real.log (b / a) := hE
      _ = Real.pi * (B / Real.log (b / a)) := by ring
      _ ≤ Real.pi * ε := mul_le_mul_of_nonneg_left hsmall Real.pi_pos.le
      _ = (η / D) ^ 2 := by dsimp only [ε]; field_simp
  have hsmall' : D * Real.sqrt Ea ≤ η := by
    have hs := Real.sqrt_le_sqrt hEa
    rw [Real.sqrt_sq (div_nonneg hη.le hD.le)] at hs
    exact (mul_le_mul_of_nonneg_left hs hD.le).trans_eq (mul_div_cancel₀ η hD.ne')
  have hρ0 := ha.trans hρ.1
  have hρ1 := hρ.2.trans hb1
  have hpoint : f (circleMap (-1) ρ (-Real.arccos (ρ / 2))) ∈ range Φ :=
    hfK (Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le (by linarith)
      ⟨le_rfl, neg_le_self (Real.arccos_nonneg _)⟩)
  obtain ⟨_, _, _, _, _, _, _, _, hlocal⟩ := hcomp f Kf hf hfK ψ hψ htrace ρ hρ0 hρ1
    (hshort ρ hρ) U η (hηU _ hpoint) hsmall' T LT hT hLT hmap hfix
  let σ := affineCircleMap ψ hψ ψ.map_add_one
  have hσ : IsWeaklyMonotoneOnce σ :=
    ⟨ψ, hψ, fun _ => rfl, Or.inl ⟨ψ.monotone, ψ.map_add_one⟩⟩
  have htraceσ (θ : loopCircle) : f (diskBoundary θ) = Φ (γ (σ θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [σ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul] using htrace t
  have hi := (integrable_pullback_energy_and_inf_le_of_lipschitzOn g hΦ hN
    (hr.of_le (by simp)) hΦN hleft hσ hf.lipschitzOnWith hfK htraceσ).1
  have hnonneg (z : ℂ) : 0 ≤ e f z := by
    dsimp only [e, A]
    simp only [pullbackMetricCoefficients_apply]
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hsub : boundaryLens a ⊆ boundaryLens ρ := by
    intro z hz
    exact ⟨(closedBall_subset_closedBall hρ.1.le) hz.1, hz.2⟩
  have hmono : (∫ z in boundaryLens a, e f z) ≤ ∫ z in boundaryLens ρ, e f z :=
    setIntegral_mono_set (hi.mono_set inter_subset_right)
      (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hsub)
  have hbnd := mul_le_mul_of_nonneg_left hE (mul_nonneg hΛ hQ)
  change (∫ z in boundaryLens ρ, e f z) ≤ Λ * Q * Ea + _ at hlocal
  change (∫ z in boundaryLens a, e f z) ≤ Λ * Q * Real.pi * B / Real.log (b / a) + _
  apply hmono.trans
  apply hlocal.trans
  have hmul : Λ * Q * Ea ≤ Λ * Q * Real.pi * B / Real.log (b / a) := by
    change Λ * Q * Ea ≤ Λ * Q * (Real.pi * B / Real.log (b / a)) at hbnd
    exact hbnd.trans_eq (by ring)
  exact add_le_add hmul le_rfl

end DifferentialGeometry.Geometry

end
