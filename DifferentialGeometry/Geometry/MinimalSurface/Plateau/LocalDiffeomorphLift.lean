import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIsoDifferentiable
import DifferentialGeometry.Geometry.Connection.SectionAlongRegularity
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem diskMapPartial_comp_of_mdifferentiableAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    {U : ℂ → M} {z : ℂ} (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (v : ℂ) :
    diskMapPartial (p ∘ U) z v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z) (diskMapPartial U z v) := by
  exact congrArg (fun L : ℂ →L[ℝ] F => L v)
    (mfderiv_comp z (hp.mdifferentiableAt (by simp)) hU)

private theorem diskSmoothInterior_of_localDiffeomorph_lift
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    {u : C(closedDisk, N)} (hu : DiskSmoothInterior (E := F) u)
    (p : M → N) (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (uLift : C(closedDisk, M)) (hmap : ∀ z, p (uLift z) = u z) :
    DiskSmoothInterior (E := E) uLift := by
  have hproj (z : ℂ) : p (diskExtension uLift z) = diskExtension u z :=
    hmap (diskRetraction z)
  have hc : Continuous (diskExtension uLift) :=
    uLift.continuous.comp diskRetraction_lipschitz.continuous
  intro z hz
  obtain ⟨φ, hx, hφ⟩ := hps (diskExtension uLift z)
  have htarget : diskExtension u z ∈ φ.target := by
    rw [← hproj z, hφ hx]
    exact φ.map_source hx
  have hs := (φ.contMDiffOn_invFun.contMDiffAt
    (φ.open_target.mem_nhds htarget)).comp z
      (hu.contMDiffAt (Metric.isOpen_ball.mem_nhds hz))
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hc.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hx)] with w hw
  change diskExtension uLift w = φ.symm (diskExtension u w)
  rw [← hproj w, hφ hw]
  exact (φ.left_inv hw).symm

private theorem diskMapCovariantPartial_map_localIso
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s)
    (v w : ℂ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z)
      (diskMapCovariantPartial (g.pullback p hp himm) U z v w) =
        diskMapCovariantPartial g (p ∘ U) z v w := by
  let curve : ℝ → M := fun t => U (z + t • v)
  let field : ∀ t, TangentSpace 𝓘(ℝ, E) (curve t) :=
    fun t => diskMapPartial U (z + t • v) w
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => z + t • v) 0 := by
    have hc : ContDiff ℝ ∞ (fun t : ℝ => z + t • v) := by fun_prop
    exact hc.contDiffAt.contMDiffAt
  have hz0 : (fun t : ℝ => z + t • v) 0 ∈ s := by simpa using hz
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) curve 0 := by
    exact ((hU.contMDiffAt (hs.mem_nhds hz0)).comp 0 hline).mdifferentiableAt (by simp)
  have hsection : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (curve t) (field t)) 0 :=
    ((contMDiffOn_source_partial hs hU le_rfl w).contMDiffAt
      (hs.mem_nhds hz0)).comp 0 hline
  have hfield : DifferentiableAt ℝ (chartRepAt curve field 0) 0 :=
    (contDiffAt_chartRepAt_of_section hsection).differentiableAt (by simp)
  have hnat := covDerivAlong_map_localIso_of_mdifferentiableAt
    (g.pullback p hp himm) g hps
    (fun x a b => SmoothRiemannianMetric.pullback_inner g p hp himm x a b)
    curve field 0 hcurve hfield
  have hreplace :
      covDerivAlong g (fun t => p (curve t))
        (fun t => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (curve t) (field t)) 0 =
      diskMapCovariantPartial g (p ∘ U) z v w := by
    apply DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    · exact Eventually.of_forall fun _ => rfl
    · filter_upwards [hline.continuousAt.preimage_mem_nhds (hs.mem_nhds hz0)] with t ht
      exact (diskMapPartial_comp_of_mdifferentiableAt p hp
        ((hU.contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by simp)) w).symm
  have hpush :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z)
        (diskMapCovariantPartial (g.pullback p hp himm) U z v w) =
      covDerivAlong g (fun t => p (curve t))
        (fun t => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (curve t) (field t)) 0 := by
    have hbase : curve 0 = U z := by simp only [curve, zero_smul, add_zero]
    have hdp :
        (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (curve 0)) =
        (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z)) :=
      congrArg (fun x : M => (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x)) hbase
    change (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z))
      (covDerivAlong (g.pullback p hp himm) curve field 0) = _
    rw [← hdp]
    exact hnat
  exact hpush.trans hreplace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]

/-- The supplied lift of the same Morrey disk is a Morrey disk for the literal
pullback metric. The boundary compatibility and metric-Lipschitz bound belong
to that same lift; interior smoothness and harmonicity are derived. -/
theorem IsMorreyDisk.of_localDiffeomorph_lift
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N} {γ : freeLoop N} {u : C(closedDisk, N)}
    (hu : IsMorreyDisk g γ u) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (uLift : C(closedDisk, M)) (γLift : freeLoop M)
    (hmap : ∀ z, p (uLift z) = u z) (hloop : ∀ θ, p (γLift θ) = γ θ)
    (htrace : DiskWeakJordanTrace γLift uLift) {C : ℝ≥0}
    (hLift : ∀ z w, riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
      (C : ℝ≥0∞) * edist z w) :
    IsMorreyDisk (g.pullback p hp himm) γLift uLift := by
  have hproj : p ∘ diskExtension uLift = diskExtension u := funext fun z => hmap (diskRetraction z)
  have hsmooth : DiskSmoothInterior (E := E) uLift :=
    diskSmoothInterior_of_localDiffeomorph_lift hu.smoothInterior p hps uLift hmap
  have hinner (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) (v w : ℂ) :
      (g.pullback p hp himm).inner (diskExtension uLift z)
        (diskMapPartial (diskExtension uLift) z v) (diskMapPartial (diskExtension uLift) z w) =
      g.inner (diskExtension u z)
        (diskMapPartial (diskExtension u) z v) (diskMapPartial (diskExtension u) z w) := by
    have hd := (hsmooth.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp)
    rw [SmoothRiemannianMetric.pullback_inner,
      ← diskMapPartial_comp_of_mdifferentiableAt p hp hd v,
      ← diskMapPartial_comp_of_mdifferentiableAt p hp hd w]
    change g.inner ((p ∘ diskExtension uLift) z) _ _ = _
    rw [hproj]
  have henergy : diskMapEnergyDensity (g.pullback p hp himm) (diskExtension uLift) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)] diskMapEnergyDensity g (diskExtension u) := by
    filter_upwards [ae_disk_interior] with z hz
    simp only [diskMapEnergyDensity, hinner z hz]
  apply isMorreyDisk_of_minimizesLipschitz (g.pullback p hp himm) hsmooth
  · intro z hz
    simpa only [DiskMapConformalAt, hinner z hz] using hu.conformal z hz
  · intro z hz
    apply himm (diskExtension uLift z)
    rw [map_zero]
    have hnat : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (diskExtension uLift z)
        (diskMapTension (g.pullback p hp himm) (diskExtension uLift) z) =
        diskMapTension g (p ∘ diskExtension uLift) z := by
      unfold diskMapTension
      rw [map_add,
        diskMapCovariantPartial_map_localIso g p hp himm hps Metric.isOpen_ball hsmooth hz,
        diskMapCovariantPartial_map_localIso g p hp himm hps Metric.isOpen_ball hsmooth hz]
    rw [hnat, hproj]
    exact hu.harmonic z hz
  · exact hu.finiteEnergy.congr henergy.symm
  · exact htrace
  · exact hu.minimizesLipschitz_of_immersion_lift p hp himm uLift γLift hmap hloop hLift

end DifferentialGeometry.Geometry
