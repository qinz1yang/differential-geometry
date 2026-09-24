import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundedDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Boundary.EmbeddedLoop
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Normalization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakCompactness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Boundary.Compactness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ClosedDiskExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.SmoothHarmonicMap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Attainment
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Conformality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_disk_energy_minimizer_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (weaklyMonotoneDiskCompetitors g γ).Nonempty) :
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
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨u₀, σ₀, hu₀, hσ₀, ht₀, h00, h01, h02, hanti₀, hmin₀⟩ :=
    exists_three_point_normalized_disk_energy_minimizing_sequence g γ hfinite
      (p := 1 / 3) (q := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨τ, φ₁, hφ₁, hτ, hτ0, hτ1, hτ2, _, htr₁⟩ :=
    exists_subseq_tendsto_diskTrace_of_normalized_energy_bound g γ hγ.embedding u₀
      (fun n => (hu₀ n).2) (fun n => hanti₀ (Nat.zero_le n))
      σ₀ hσ₀ ht₀ h00 h01 h02
  let u₁ := u₀ ∘ φ₁
  have hu₁ (n : ℕ) : u₁ n ∈ weaklyMonotoneDiskCompetitors g γ := hu₀ (φ₁ n)
  have hmin₁ := hmin₀.comp hφ₁.tendsto_atTop
  obtain ⟨m, Φ, hΦ, hΦemb, hΦimm, hs₀, φ₂, w, hw, _, hφ₂, hrep₀,
      _, hL2, hae, _, _, _, _, hweak⟩ :=
    exists_embedded_disk_weak_memW1p_subseq g u₁ (fun n => (hu₁ n).2)
      (fun n => hanti₀ (Nat.zero_le (φ₁ n)))
  let u := u₁ ∘ φ₂
  let σ := σ₀ ∘ φ₁ ∘ φ₂
  let hs (n : ℕ) (i : Fin m) := hs₀ (φ₂ n) i
  have hu (n : ℕ) : u n ∈ weaklyMonotoneDiskCompetitors g γ := hu₁ (φ₂ n)
  have hmin := hmin₁.comp hφ₂.tendsto_atTop
  have htraceLimit := htr₁.comp hφ₂.tendsto_atTop
  have hσ (n : ℕ) : IsWeaklyMonotoneOnce (σ n) := hσ₀ (φ₁ (φ₂ n))
  have ht (n : ℕ) : diskTrace (u n) = γ.comp (σ n) := ht₀ (φ₁ (φ₂ n))
  have hmarks (n : ℕ) : σ n 0 = 0 ∧
      σ n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
      σ n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) :=
    ⟨h00 _, h01 _, h02 _⟩
  have hlift (n : ℕ) := (hσ n).exists_monotone_lift_of_three_fixed_points
    (a := 1 / 3) (b := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
    (hmarks n).1 (hmarks n).2.1 (hmarks n).2.2
  choose ψ₀ hψ₀ hψlift hψmono hψinc hψ0 hψ1 hψ2 using hlift
  let ψ (n : ℕ) : CircleDeg1Lift := ⟨⟨ψ₀ n, hψmono n⟩, hψinc n⟩
  have hψ (n : ℕ) : Continuous (ψ n) := hψ₀ n
  have hψtrace (n : ℕ) (t : ℝ) :
      u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle) := by
    have heq := congrArg (fun v : freeLoop M => v (t : loopCircle)) (ht n)
    change u n (diskBoundary (t : loopCircle)) = γ (σ n (t : loopCircle)) at heq
    exact heq.trans (congrArg γ (hψlift n t).symm)
  have hthird (n : ℕ) : ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3 := by
    change ψ₀ n (1 / 3) = ψ₀ n 0 + 1 / 3
    rw [hψ0 n, hψ1 n, zero_add]
  have htwothird (n : ℕ) : ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3 := by
    change ψ₀ n (2 / 3) = ψ₀ n 0 + 2 / 3
    rw [hψ0 n, hψ2 n, zero_add]
  have hrep (n : ℕ) (i : Fin m) (j : Fin 2) :
      (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)) :=
    Eventually.of_forall fun x => hrep₀ (φ₂ n) i x j
  obtain ⟨r, N, hN, hΦN, hr, hleft⟩ :=
    exists_smooth_neighborhood_retraction hΦ hΦemb.isEmbedding hΦimm
  obtain ⟨KΓ, J, hΓ, hInv⟩ := exists_lipschitz_antilipschitz_embedded_loop
    hΦ hΦemb.isEmbedding hΦimm hγ
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hR : ContDiffOn ℝ ∞ (Φ ∘ r) N := (hΦ.comp_contMDiffOn hr).contDiffOn
  have hRmap : MapsTo (Φ ∘ r) N (range Φ) := fun _ _ => mem_range_self _
  have hRfix : ∀ y ∈ range Φ, (Φ ∘ r) y = y := by
    rintro _ ⟨p, rfl⟩
    exact congrArg Φ (hleft p)
  obtain ⟨U, T, C, hU, hKU, _, _, hT, _, hC, hCT, hmap, hfix⟩ :=
    Analysis.exists_contDiff_retraction_extension_fderiv_bound hK hN hΦN (Φ ∘ r) hR hRmap hRfix
  obtain ⟨η, hη, hηU⟩ := hK.exists_cthickening_subset_open hU hKU
  have htube (p) (hp : p ∈ range Φ) : Metric.closedBall p η ⊆ U := by
    intro y hy
    exact hηU (Metric.mem_cthickening_of_dist_le y p η (range Φ) hp hy)
  let LT : ℝ≥0 := ⟨C, hC⟩
  obtain ⟨v, hv, hvs, hrvs, hvw, hvK, _, hharm⟩ :=
    exists_smooth_harmonic_weak_representative_of_disk_energy_minimizing_sequence
      g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak
  obtain ⟨q, qF, hqF, hqint, hqtrace⟩ :=
    exists_closed_disk_extension_of_disk_energy_minimizing_sequence
      g hΦ hN hr hΦN hleft γ hΓ hInv hη htube T LT (hT.differentiable (by simp)) hCT hmap hfix
      u hu hmin ψ hψ hψtrace hthird htwothird w hs hw hrep hL2 hae hweak
      v hvs.continuousOn hvw τ htraceLimit
  have hq (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)) :=
    (diskExtension_coe q ⟨z, Metric.ball_subset_closedBall hz⟩).trans (hqint z hz).2
  have hgerm (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      diskExtension q =ᶠ[𝓝 z] (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact hq y hy
  have hqsm : DiskSmoothInterior (E := E) q := by
    have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
        (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) (Metric.ball (0 : ℂ) 1) :=
      hrvs.comp
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn
      (by
        intro z hz
        change Complex.orthonormalBasisOneI.repr z ∈ Metric.ball (0 : V) 1
        rw [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
        simpa only [Metric.mem_ball, dist_zero_right] using hz)
    exact hcomp.congr (fun z hz => hq z hz)
  have hqh (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      diskMapTension g (diskExtension q) z = 0 := by
    exact (diskMapTension_congr_of_eventuallyEq g (hgerm z hz)).trans (hharm z hz)
  have hfiniteq := (integrable_diskMapEnergyDensity_and_energy_eq_of_contDiffOn_representative
    g hN (hr.of_le (by simp)) hK hΦN q w hw v (hvs.of_le (by simp)) hvw hvK hq).1
  have heq := riemannianDiskEnergy_eq_inf_of_minimizing_sequence g hΦ hN hr hΦN hleft
    u hu hmin w hs hw hrep hweak hae v (hvs.of_le (by simp)) hvw hvK q hq
    hΓ τ hτ hτ0 hτ1 hτ2 hqtrace
  have hconf := diskMapConformalAt_of_minimizing_sequence g hΦ hN hr hΦN hleft
    u hu hmin w hs hw hrep hL2 hweak hae v hvs.continuousOn hvw hvK q hq
    hΓ τ hτ hτ0 hτ1 hτ2 hqtrace
  exact ⟨q, τ, hτ, hτ0, hτ1, hτ2, hqtrace, hqsm, hqh, hconf, hfiniteq, heq⟩

end DifferentialGeometry.Geometry

end
