import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskAreaMetricVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [hBoundary : I.Boundaryless]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] hBoundary in
private theorem SmoothDisk.differential_eq_mfderiv_extension
    (u : SmoothDisk (I := I) (Q := Q)) {U : ℂ → Q} {N : Set ℂ}
    (hN : IsOpen N) (hDN : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hUN : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U N) (heq : ∀ z : Disk, U z = u.map z)
    (z : Disk) (v : ℂ) :
    (u.differential z v : E) = (mfderiv 𝓘(ℝ, ℂ) I U (z : ℂ) v : E) := by
  have hcongr : EqOn (diskExtension (⇑u.map)) U (Metric.closedBall (0 : ℂ) 1) := by
    intro y hy
    rw [diskExtension_coe u.map ⟨y, hy⟩]
    exact (heq ⟨y, hy⟩).symm
  have h1 : mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension (⇑u.map))
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) =
      mfderivWithin 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    mfderivWithin_congr_of_mem hcongr z.property
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) I U (z : ℂ) :=
    (hUN.contMDiffAt (hN.mem_nhds (hDN z.property))).mdifferentiableAt (by simp)
  have h2 : mfderivWithin 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) (z : ℂ) =
      mfderiv 𝓘(ℝ, ℂ) I U (z : ℂ) :=
    hmd.hasMFDerivAt.hasMFDerivWithinAt.mfderivWithin
      (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension (⇑u.map))
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) v = mfderiv 𝓘(ℝ, ℂ) I U (z : ℂ) v
  exact congrArg (fun (L : ℂ →L[ℝ] E) => L v) (h1.trans h2)

omit [FiniteDimensional ℝ E] [T2Space Q] hBoundary in
private theorem diskArea_eq_integral_riemannianAreaDensity_extension
    (g : SmoothRiemannianMetric I Q) (u : Disk → Q) :
    diskArea g u = ∫ z in Metric.closedBall (0 : ℂ) 1,
      DifferentialGeometry.Geometry.riemannianAreaDensity g (diskExtension u) z := by
  simp only [diskArea, diskJacobian]
  refine integral_congr_ae ?_
  filter_upwards [DifferentialGeometry.Geometry.ae_disk_interior] with z hz
  exact parametricJacobian_eq_riemannianAreaDensity_of_mem_nhds g (diskExtension u)
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)

theorem SmoothDisk.hasDerivAt_diskArea_metricFamily
    [CompactSpace Q] [SigmaCompactSpace Q]
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    (u : SmoothDisk (I := I) (Q := Q)) (g : ℝ → SmoothRiemannianMetric I Q)
    (J : Set ℝ) {D : RealTimeInterval} {t₀ : ℝ}
    {hG : MetricFamilySmoothOn D g} (ht₀ : D.regular ∈ 𝓝 t₀)
    (hJ : J ∈ 𝓝 t₀) (hconf : u.IsConformal (g t₀)) :
    IntegrableOn (diskExtension (u.metricVariationDensity g J t₀)) (Metric.closedBall (0 : ℂ) 1) ∧
      HasDerivAt (fun t : ℝ => diskArea (g t) u.map)
        ((1 / 2) * ∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity g J t₀) z) t₀ := by
  obtain ⟨U, heq, N, hN, hDN, hUN⟩ :=
    SmoothDisk.exists_smoothExtension (I := I) (Q := Q) (hne := ⟨u.map diskCenter⟩) u
  let K : ℂ → ℝ := fun z =>
    ((deriv (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))) t₀) +
      (deriv (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
        (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)) t₀)) / 2
  have hconfU : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0 ∧
        (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
          (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
            (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) := by
    intro z hz
    have hd (v : ℂ) : u.differential ⟨z, hz⟩ v = mfderiv 𝓘(ℝ, ℂ) I U z v :=
      SmoothDisk.differential_eq_mfderiv_extension u hN hDN hUN heq ⟨z, hz⟩ v
    obtain ⟨h1, h2⟩ := hconf ⟨z, hz⟩
    have key (v w : ℂ) : (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v)
        (mfderiv 𝓘(ℝ, ℂ) I U z w) =
        (g t₀).inner (u.map ⟨z, hz⟩) (u.differential ⟨z, hz⟩ v)
          (u.differential ⟨z, hz⟩ w) := by
      rw [heq ⟨z, hz⟩]
      exact congrArg₂ (fun p q => (g t₀).inner (u.map ⟨z, hz⟩) p q) (hd v).symm (hd w).symm
    exact ⟨(key 1 Complex.I).trans h1, (key 1 1).trans (h2.trans (key Complex.I Complex.I).symm)⟩
  obtain ⟨hKint, hKderiv⟩ :=
    DifferentialGeometry.Geometry.hasDerivAt_integral_riemannianAreaDensity_metricFamily
      (I := I) (Q := Q) (D := D) (t₀ := t₀) (g := g) (hG := hG) c ht₀ hN hUN hDN hconfU
  have hKint' : IntegrableOn K (Metric.closedBall (0 : ℂ) 1) := by
    simpa only [K] using hKint
  have hKderiv' : HasDerivAt (fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) 1,
      DifferentialGeometry.Geometry.riemannianAreaDensity (g t) U z)
      (∫ z in Metric.closedBall (0 : ℂ) 1, K z) t₀ := by
    simpa only [K] using hKderiv
  have hdens : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
      diskExtension (u.metricVariationDensity g J t₀) z = 2 * K z := by
    filter_upwards [DifferentialGeometry.Geometry.ae_disk_interior] with z hz
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    have hzdiff (v : ℂ) : u.differential ⟨z, hzcb⟩ v = mfderiv 𝓘(ℝ, ℂ) I U z v :=
      SmoothDisk.differential_eq_mfderiv_extension u hN hDN hUN heq ⟨z, hzcb⟩ v
    have hpt : U z = u.map ⟨z, hzcb⟩ := heq ⟨z, hzcb⟩
    have hD (v : ℂ) : deriv (fun r : ℝ => (g r).inner (u.map ⟨z, hzcb⟩)
          (u.differential ⟨z, hzcb⟩ v) (u.differential ⟨z, hzcb⟩ v)) t₀ =
        deriv (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v)
          (mfderiv 𝓘(ℝ, ℂ) I U z v)) t₀ := by
      refine congrArg (fun f : ℝ → ℝ => deriv f t₀) (funext fun r => ?_)
      rw [hzdiff v, ← hpt]
    rw [show diskExtension (u.metricVariationDensity g J t₀) z =
        u.metricVariationDensity g J t₀ ⟨z, hzcb⟩ from dif_pos hzcb,
      SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds hJ, derivWithin_of_mem_nhds hJ, hD 1, hD Complex.I]
      simp only [K]
      ring
    · have hzero1 : u.differential ⟨z, hzcb⟩ 1 = 0 := by
        by_contra hne
        exact absurd ((g t₀).pos (u.map ⟨z, hzcb⟩) (u.differential ⟨z, hzcb⟩ 1) hne)
          (not_lt.mpr (not_lt.mp hpos))
      have hzeroI : u.differential ⟨z, hzcb⟩ Complex.I = 0 := by
        by_contra hne
        have hp := (g t₀).pos (u.map ⟨z, hzcb⟩) (u.differential ⟨z, hzcb⟩ Complex.I) hne
        rw [← (hconf ⟨z, hzcb⟩).2] at hp
        exact absurd hp (not_lt.mpr (not_lt.mp hpos))
      have hz1 : mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ) = 0 := by rw [← hzdiff 1]; exact hzero1
      have hzI : mfderiv 𝓘(ℝ, ℂ) I U z Complex.I = 0 := by
        rw [← hzdiff Complex.I]; exact hzeroI
      have hf1 : (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))) = fun _ : ℝ => 0 := by
        funext r
        rw [hz1]
        simp
      have hfI : (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
          (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)) = fun _ : ℝ => 0 := by
        funext r
        rw [hzI]
        simp
      simp only [K]
      rw [hf1, hfI]
      simp
  have hdensEq : (fun z : ℂ => diskExtension (u.metricVariationDensity g J t₀) z) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)] fun z => 2 * K z := hdens
  have hInt : IntegrableOn (diskExtension (u.metricVariationDensity g J t₀))
      (Metric.closedBall (0 : ℂ) 1) :=
    (hKint'.const_mul 2).congr hdensEq.symm
  have hArea : ∀ t : ℝ, diskArea (g t) u.map = ∫ z in Metric.closedBall (0 : ℂ) 1,
      DifferentialGeometry.Geometry.riemannianAreaDensity (g t) U z := by
    intro t
    rw [diskArea_eq_integral_riemannianAreaDensity_extension (g t) u.map]
    refine integral_congr_ae ?_
    filter_upwards [DifferentialGeometry.Geometry.ae_disk_interior] with z hz
    refine DifferentialGeometry.Geometry.riemannianAreaDensity_congr (g t) ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    rw [diskExtension_coe u.map ⟨w, Metric.ball_subset_closedBall hw⟩]
    exact (heq ⟨w, Metric.ball_subset_closedBall hw⟩).symm
  have hIntEq : (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskExtension (u.metricVariationDensity g J t₀) z) = 2 * ∫ z in Metric.closedBall (0 : ℂ) 1, K z := by
    rw [integral_congr_ae hdensEq, integral_const_mul]
  have hV : (∫ z in Metric.closedBall (0 : ℂ) 1, K z) =
      (1 / 2) * ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity g J t₀) z := by
    rw [hIntEq]
    ring
  refine ⟨hInt, ?_⟩
  rw [show (fun t : ℝ => diskArea (g t) u.map) = fun t : ℝ =>
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        DifferentialGeometry.Geometry.riemannianAreaDensity (g t) U z from funext hArea, ← hV]
  exact hKderiv'

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
