import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ClosedNoncompactLimit
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Conformality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Component

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_disk_energy_minimizer_of_homogeneously_regular
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ (q : C(closedDisk, M)) (τ : C(loopCircle, loopCircle)),
      IsWeaklyMonotoneOnce τ ∧ τ 0 = 0 ∧
      τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
      τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) ∧
      diskTrace q = γ.comp τ ∧ DiskSmoothInterior (E := E) q ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension q) z = 0) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z) ∧
      IntegrableOn (diskMapEnergyDensity g (diskExtension q)) (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskEnergy g q = sInf
        ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
          weaklyMonotoneDiskCompetitors g γ) := by
  have hnonzero : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    apply hγ.immersed 0
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => γ (t : loopCircle)) 0 1 : E) = 0
    exact @Subsingleton.elim E (Module.finrank_zero_iff.mp hzero) _ _
  let : NeZero (Module.finrank ℝ E) := ⟨hnonzero⟩
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨_, _, q, τ, _, _, _, _, hτ, hτ0, hτ1, hτ2, htrace, hq, hharm, hE, hle⟩ :=
    exists_closed_disk_harmonic_minimizing_limit_energy_le_inf g hg hregular L γ hγ hfinite
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let γC : freeLoop C := loopInComponent γ
  let ι : C(C, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let Q : C(closedDisk, M) := ι.comp q
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  have hγC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => γC (t : loopCircle)) :=
    (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff C _).mp
      (hγ.smooth.of_le (by simp))
  have hdensity (z : ℂ) : diskMapEnergyDensity gC (diskExtension q) z =
      diskMapEnergyDensity g (diskExtension Q) z :=
    diskMapEnergyDensity_restrictOpen g C _ z
  have hEC : IntegrableOn (diskMapEnergyDensity gC (diskExtension q))
      (Metric.closedBall (0 : ℂ) 1) := by
    exact hE.congr (Eventually.of_forall fun z => (hdensity z).symm)
  have hharmC (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      diskMapTension gC (diskExtension q) z = 0 :=
    (diskMapTension_restrictOpen g C _ z
      (q.continuous.comp diskRetraction_lipschitz.continuous).continuousAt).trans (hharm z hz)
  have hleC : riemannianDiskEnergy gC q ≤ sInf
      ((fun w : C(closedDisk, C) => riemannianDiskEnergy gC w) ''
        weaklyMonotoneDiskCompetitors gC γC) := by
    rw [disk_energy_inf_eq_component g γ, riemannianDiskEnergy_restrictOpen g C q]
    exact hle
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hgeC⟩ :=
    exists_weakly_monotone_disks_tendsto_energy_of_contMDiffOn gC γC hγC q
      (hq.of_le (by simp)) hEC τ hτ hτ0 hτ1 hτ2 htrace
  have heqC := le_antisymm hleC hgeC
  have hconfC := diskMapConformalAt_of_harmonic_energy_minimizer
    gC γC hγC q hq hharmC hEC τ hτ hτ0 hτ1 hτ2 htrace heqC
  have hconf (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      DiskMapConformalAt g (diskExtension Q) z :=
    (diskMapConformalAt_restrictOpen g C _ z).mp (hconfC z hz)
  have htraceQ : diskTrace Q = γ.comp τ := by
    ext θ
    exact congrArg Subtype.val (congrArg (fun w => w θ) htrace)
  have heqQ : riemannianDiskEnergy g Q = sInf
      ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ) := by
    change riemannianDiskEnergy g (Subtype.val ∘ q) = _
    rw [← riemannianDiskEnergy_restrictOpen g C q, heqC]
    exact disk_energy_inf_eq_component g γ
  exact ⟨Q, τ, hτ, hτ0, hτ1, hτ2, htraceQ,
    (diskSmoothInterior_open_inclusion_iff C q).mpr hq, hharm, hconf, hE, heqQ⟩

end DifferentialGeometry.Geometry
