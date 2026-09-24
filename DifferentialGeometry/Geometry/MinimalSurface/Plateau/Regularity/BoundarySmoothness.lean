import DifferentialGeometry.Geometry.HarmonicMap.DiskBoundaryRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Conformality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.SmoothHarmonicMap
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import DifferentialGeometry.Analysis.Calculus.Periodic.Derivative

noncomputable section

open Manifold Set Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smooth_extension_of_conformal_harmonic_disk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (q : C(closedDisk, M))
    (hqi : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension q) z = 0)
    (τ : C(loopCircle, loopCircle)) (htrace : diskTrace q = γ.comp τ) :
    ∃ Q : ℂ → M, SmoothDiskExtension (E := E) q Q := by
  have hboundary : ∀ z : ℂ, ‖z‖ = 1 → diskExtension q z ∈ range γ := by
    intro z hz
    let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hb : (diskBoundary θ : ℂ) = z := by
      have hc := congrArg (fun x : Circle => (x : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    refine ⟨τ θ, ?_⟩
    have he := congrArg (fun f : freeLoop M => f θ) htrace
    change q (diskBoundary θ) = γ (τ θ) at he
    rw [← hb, diskExtension_coe]
    exact he.symm
  have hclosed : DiskSmoothUpToBoundary (E := E) q :=
    contMDiffOn_closedDisk_of_embedded_loop g (by norm_num : (0 : ℝ) < 1)
      hγ.embedding hγ.smooth hγ.immersed
      (q.continuous.comp diskRetraction_lipschitz.continuous).continuousOn hqi hboundary
      (fun z hz => (hconf z hz).1) (fun z hz => (hconf z hz).2) hharm
  exact exists_smoothDiskExtension_of_diskSmoothUpToBoundary hclosed

theorem contDiff_lift_of_conformal_harmonic_disk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (q : C(closedDisk, M))
    (hqi : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension q) z = 0)
    (τ : C(loopCircle, loopCircle)) (htrace : diskTrace q = γ.comp τ)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hlift : ∀ t : ℝ, (ψ t : loopCircle) = τ (t : loopCircle)) :
    ContDiff ℝ ∞ ψ := by
  obtain ⟨Q, hQ⟩ :=
    exists_smooth_extension_of_conformal_harmonic_disk g hγ q hqi hconf hharm τ htrace
  exact hγ.contDiff_weakTraceLift hQ.smoothUpToBoundary htrace hψ hlift

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem exists_smooth_extension_and_normalized_lift_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 μ) atTop (𝓝 0))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    : ∃ Q : ℂ → M, SmoothDiskExtension (E := E) q Q ∧
      ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
        (∀ t, ψ (t + 1) = ψ t + 1) ∧
        (∀ t : ℝ, (ψ t : loopCircle) = τ (t : loopCircle)) ∧
        ψ 0 = 0 ∧ ψ (1 / 3) = 1 / 3 ∧ ψ (2 / 3) = 2 / 3 := by
  let hv (i : Fin n) := (hw i).congr
    (hvw.symm.mono fun x hx => congrArg (fun y : F => y i) hx)
  have hsm := contMDiffOn_representative_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK
  let e := Complex.orthonormalBasisOneI.repr
  have hemap : MapsTo e (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : V) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz
  have hqi : DiskSmoothInterior (E := E) q := by
    have h := hsm.1.comp e.contDiff.contMDiff.contMDiffOn hemap
    exact h.congr (fun z hz => hq z hz)
  let Γ : ℝ → F := fun t => Φ (γ (t : loopCircle))
  have hΓc : ContDiff ℝ ∞ Γ := (hΦ.comp hγ.smooth).contDiff
  have hΓp : Function.Periodic Γ 1 := by
    intro t
    simp only [Γ, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).image
    (hΓc.continuous_fderiv (by simp))).isBounded.exists_norm_le
  let KΓ : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hΓ : LipschitzWith KΓ Γ :=
    hΓp.lipschitzWith_of_norm_fderiv_le_Icc (by norm_num) (hΓc.differentiable (by simp))
      (fun t ht => (hB _ (mem_image_of_mem _ ht)).trans (le_max_left _ _))
  have hconf := diskMapConformalAt_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin w hs hw hrep hL2 hweak hae
    v hvc hvw hvK q hq hΓ τ hτ hτ0 hτ1 hτ2 htrace
  have hharm := diskMapTension_diskExtension_eq_zero_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK q hq
  obtain ⟨Q, hQ⟩ :=
    exists_smooth_extension_of_conformal_harmonic_disk g hγ q hqi hconf hharm τ htrace
  obtain ⟨ψ, hψc, hlift, hmono, hinc, h0, h1, h2⟩ :=
    hτ.exists_monotone_lift_of_three_fixed_points (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1) hτ0 hτ1 hτ2
  have hψ : ContDiff ℝ ∞ ψ := hγ.contDiff_weakTraceLift hQ.smoothUpToBoundary htrace hψc hlift
  exact ⟨Q, hQ, ψ, hψ, hmono, hinc, hlift, h0, h1, h2⟩

end DifferentialGeometry.Geometry

end
