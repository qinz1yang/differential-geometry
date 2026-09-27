import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundarySmoothness

noncomputable section

open Manifold Set Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smoothDisk_and_circleMap_of_smooth_extension_and_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) (Q : ℂ → M) (hQ : Geometry.SmoothDiskExtension (E := E) q Q)
    (γ : freeLoop M) (τ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hmono : Monotone ψ)
    (hinc : ∀ t, ψ (t + 1) = ψ t + 1)
    (hlift : ∀ t : ℝ, τ (t : loopCircle) = (ψ t : loopCircle))
    (htrace : DifferentialGeometry.Topology.diskTrace q = γ.comp τ)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Geometry.DiskMapConformalAt g (Geometry.diskExtension q) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      (Geometry.diskMapTension g (Geometry.diskExtension q) z : E) = 0) :
    ∃ (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M)) (σ : SmoothWeaklyMonotoneCircleMap),
      u.map = q ∧ σ.map = τ ∧ σ.lift = ψ ∧
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧
      u.IsConformal g ∧ u.IsHarmonic g := by
  let u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M) := smoothDisk_of_smoothDiskExtension hQ
  let σ : SmoothWeaklyMonotoneCircleMap :=
    { map := τ
      lift := ψ
      smooth_lift := hψ
      monotone_lift := hmono
      increment := hinc
      lift_eq := hlift }
  have hU : Geometry.SmoothDiskExtension (E := E) u.map Q := hQ
  have hQc : ∀ z ∈ Metric.ball (0 : ℂ) 1, Geometry.DiskMapConformalAt g Q z := by
    intro z hz
    exact (Geometry.diskMapConformalAt_congr_of_eventuallyEq g
      (hQ.eventuallyEq_diskExtension hz)).mpr (hconf z hz)
  have hQh : ∀ z ∈ Metric.ball (0 : ℂ) 1, (Geometry.diskMapTension g Q z : E) = 0 := by
    intro z hz
    exact (Geometry.diskMapTension_congr_of_eventuallyEq g
      (hQ.eventuallyEq_diskExtension hz)).trans (hharm z hz)
  refine ⟨u, σ, rfl, rfl, rfl, ?_,
    u.isConformal_of_diskMapConformalAt_on_ball g hU hQc,
    u.isHarmonic_of_diskMapTension_eq_zero_on_ball g hU hQh⟩
  intro θ
  have h := congrArg (fun v : freeLoop M => v θ) htrace
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem exists_smooth_disk_with_normalized_trace_of_minimizing_sequence
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
      (fun x => Φ (Geometry.diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (Geometry.diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (Geometry.diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 μ) atTop (𝓝 0))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (Geometry.diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Geometry.diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    : ∃ (d : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M)) (σ : SmoothWeaklyMonotoneCircleMap),
      d.map = q ∧ σ.map = τ ∧
      (∀ θ, d.map (diskBoundary θ) = γ (σ.map θ)) ∧
      d.IsConformal g ∧ d.IsHarmonic g ∧
      σ.lift 0 = 0 ∧ σ.lift (1 / 3) = 1 / 3 ∧ σ.lift (2 / 3) = 2 / 3 := by
  obtain ⟨Q, hQ, ψ, hψ, hmono, hinc, hlift, h0, h1, h2⟩ :=
    Geometry.exists_smooth_extension_and_normalized_lift_of_minimizing_sequence
      g hΦ hN hr hΦN hleft hγ u hu hmin w hs hw hrep hL2 hweak hae
      v hvc hvw hvK q hq τ hτ hτ0 hτ1 hτ2 htrace
  let hv (i : Fin n) := (hw i).congr
    (hvw.symm.mono fun x hx => congrArg (fun y : F => y i) hx)
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
  have hconf := Geometry.diskMapConformalAt_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin w hs hw hrep hL2 hweak hae
    v hvc hvw hvK q hq hΓ τ hτ hτ0 hτ1 hτ2 htrace
  have hharm := Geometry.diskMapTension_diskExtension_eq_zero_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK q hq
  obtain ⟨d, σ, hd, hσ, hσψ, htr, hc, hh⟩ :=
    exists_smoothDisk_and_circleMap_of_smooth_extension_and_lift
      g q Q hQ γ τ ψ hψ hmono hinc (fun t => (hlift t).symm) htrace hconf hharm
  exact ⟨d, σ, hd, hσ, htr, hc, hh, hσψ ▸ h0, hσψ ▸ h1, hσψ ▸ h2⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end
