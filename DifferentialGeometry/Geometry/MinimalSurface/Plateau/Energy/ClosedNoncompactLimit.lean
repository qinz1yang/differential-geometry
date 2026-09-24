import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.NoncompactLimit
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Boundary.Compactness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.NoncompactHarmonicMap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.NoncompactClosedDiskExtension
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality

noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_closed_disk_harmonic_minimizing_limit_energy_le_inf
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    let b := sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
    let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
    ∃ (u : ℕ → C(closedDisk, M)) (v : ℂ → C)
      (q : C(closedDisk, C)) (τ : C(loopCircle, loopCircle)),
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop (𝓝 b) ∧
      (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
        Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z : M))) ∧
      v =ᵐ[volume.restrict (ball (0 : ℂ) 1)] diskExtension q ∧
      IsWeaklyMonotoneOnce τ ∧ τ 0 = 0 ∧
      τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
      τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) ∧
      diskTrace q = (loopInComponent γ).comp τ ∧ DiskSmoothInterior (E := E) q ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        diskMapTension g (diskExtension (Subtype.val ∘ q)) z = 0) ∧
      IntegrableOn (diskMapEnergyDensity g (diskExtension (Subtype.val ∘ q)))
        (closedBall (0 : ℂ) 1) ∧ riemannianDiskEnergy g (Subtype.val ∘ q) ≤ b := by
  classical
  obtain ⟨u₀, hu₀, hanti₀, hmin₀, σ₀, htrace₀, hσ₀, h00, h01, h02,
      φ, v, hφ, _, _, _, _, _, hae, henergy⟩ :=
    exists_normalized_minimizing_component_ae_limit_energy_bound g hg L γ hfinite
  let u₁ := u₀ ∘ φ
  let σ₁ := σ₀ ∘ φ
  have hu₁ (n : ℕ) : u₁ n ∈ weaklyMonotoneDiskCompetitors g γ := hu₀ (φ n)
  have hmin₁ := hmin₀.comp hφ.tendsto_atTop
  obtain ⟨τ, ψ, hψ, hτ, hτ0, hτ1, hτ2, _, hboundary⟩ :=
    exists_subseq_tendsto_diskTrace_of_normalized_energy_bound g γ hγ.embedding u₁
      (fun n => (hu₁ n).2) (fun n => hanti₀ (Nat.zero_le (φ n))) σ₁
      (fun n => hσ₀ (φ n)) (fun n => htrace₀ (φ n))
      (fun n => h00 (φ n)) (fun n => h01 (φ n)) (fun n => h02 (φ n))
  let u := u₁ ∘ ψ
  let σ := σ₁ ∘ ψ
  have hu (n : ℕ) : u n ∈ weaklyMonotoneDiskCompetitors g γ := hu₁ (ψ n)
  have hmin := hmin₁.comp hψ.tendsto_atTop
  have hae' : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z : M)) :=
    hae.mono fun z hz => hz.comp hψ.tendsto_atTop
  obtain ⟨V, hVae, hVs, hVharm⟩ :=
    exists_smooth_harmonic_component_limit_of_minimizing_sequence
      g hg hregular γ u hu hmin v hae'
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  have hVsC : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ V (ball (0 : ℂ) 1) :=
    (DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff C V _).mp hVs
  have haeV : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (V z : M)) := by
    filter_upwards [hae', hVae] with z hz hVz
    rwa [hVz]
  have hσ (n : ℕ) : IsWeaklyMonotoneOnce (σ n) := hσ₀ (φ (ψ n))
  have ht (n : ℕ) : diskTrace (u n) = γ.comp (σ n) := htrace₀ (φ (ψ n))
  have hlift (n : ℕ) := (hσ n).exists_monotone_lift_of_three_fixed_points
    (a := 1 / 3) (b := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
    (h00 (φ (ψ n))) (h01 (φ (ψ n))) (h02 (φ (ψ n)))
  choose ζ₀ hζ₀ hζlift hζmono hζinc hζ0 hζ1 hζ2 using hlift
  let ζ (n : ℕ) : CircleDeg1Lift := ⟨⟨ζ₀ n, hζmono n⟩, hζinc n⟩
  have hζ (n : ℕ) : Continuous (ζ n) := hζ₀ n
  have hζtrace (n : ℕ) (t : ℝ) :
      u n (diskBoundary (t : loopCircle)) = γ ((ζ n t : ℝ) : loopCircle) := by
    have hh := congrArg (fun w : freeLoop M => w (t : loopCircle)) (ht n)
    change u n (diskBoundary (t : loopCircle)) = γ (σ n (t : loopCircle)) at hh
    exact hh.trans (congrArg γ (hζlift n t).symm)
  have hthird (n : ℕ) : ζ n (1 / 3 : ℝ) = ζ n 0 + 1 / 3 := by
    change ζ₀ n (1 / 3) = ζ₀ n 0 + 1 / 3
    rw [hζ0 n, hζ1 n, zero_add]
  have htwothird (n : ℕ) : ζ n (2 / 3 : ℝ) = ζ n 0 + 2 / 3 := by
    change ζ₀ n (2 / 3) = ζ₀ n 0 + 2 / 3
    rw [hζ0 n, hζ2 n, zero_add]
  let η : C(loopCircle, C) := (loopInComponent γ).comp τ
  have hboundary' (θ : loopCircle) :
      Tendsto (fun n => u n (diskBoundary θ)) atTop (𝓝 (η θ : M)) :=
    ((continuous_eval_const θ).tendsto _).comp hboundary
  obtain ⟨q, hq, hqtrace, _, _⟩ :=
    exists_closed_disk_component_limit_with_trace_of_minimizing_sequence
      g hg hregular γ hγ u hu hmin ζ hζ hζtrace hthird htwothird V
      hVsC.continuousOn haeV η hboundary'
  have hqV (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : diskExtension q z = V z :=
    (diskExtension_coe q ⟨z, ball_subset_closedBall hz⟩).trans (hq z hz)
  have hqsm : DiskSmoothInterior (E := E) q :=
    hVsC.congr (fun z hz => hqV z hz)
  have hvq : v =ᵐ[volume.restrict (ball (0 : ℂ) 1)] diskExtension q := by
    filter_upwards [hVae, ae_restrict_mem measurableSet_ball] with z hz hzB
    exact hz.symm.trans (hqV z hzB).symm
  obtain ⟨hfiniteq, hle⟩ := henergy q (hqsm.of_le (by simp)) hvq
  have hqh (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      diskMapTension g (diskExtension (Subtype.val ∘ q)) z = 0 := by
    have hgerm : diskExtension (Subtype.val ∘ q) =ᶠ[𝓝 z] (fun z => (V z : M)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact congrArg Subtype.val (hqV y hy)
    exact (diskMapTension_congr_of_eventuallyEq g hgerm).trans (hVharm z hz)
  exact ⟨u, v, q, τ, hu, hmin, hae', hvq, hτ, hτ0, hτ1, hτ2, hqtrace,
    hqsm, hqh, hfiniteq, hle⟩

end DifferentialGeometry.Geometry
