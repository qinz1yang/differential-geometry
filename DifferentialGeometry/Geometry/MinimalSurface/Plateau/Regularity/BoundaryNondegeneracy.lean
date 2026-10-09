import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryHopf
import DifferentialGeometry.Geometry.HarmonicMap.ConvexBarrier
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FixedTraceBoundaryRank
import DifferentialGeometry.Analysis.Calculus.Periodic.CircleLift

set_option autoImplicit false
noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff


open Manifold DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold

namespace DifferentialGeometry.Geometry

/-- A smooth conformal harmonic disk has injective boundary differential when a
scalar function has nonnegative target Hessian on an annular collar, is negative
on its inner circle, and vanishes on its outer circle. -/
theorem SmoothDiskExtension.boundary_immersion_of_convex_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : ∀ z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ),
      planarTension g U z = 0)
    (hH : ∀ z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ),
      ∀ v : TangentSpace 𝓘(ℝ, E) (U z), 0 ≤ hessFun g ρ (U z) v v)
    (hinner : ∀ z ∈ sphere (0 : ℂ) r, ρ (U z) < 0)
    (houter : ∀ z ∈ sphere (0 : ℂ) 1, ρ (U z) = 0)
    (hconf : ∀ z ∈ sphere (0 : ℂ) 1, DiskMapConformalAt g U z) :
    ∀ p ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p) := by
  obtain ⟨_, N, hN, hDN, hUs⟩ := hU
  have hUsm (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z :=
    hUs.contMDiffAt (hN.mem_nhds (hDN hz))
  have hq (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ) :
      ContDiffAt ℝ 2 (ρ ∘ U) z :=
    (((hρ.contMDiffAt.comp z (hUsm z hz.1)).of_le (by simp)).contDiffAt)
  have hΔ (z : ℂ)
      (hz : z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ)) :
      0 ≤ Laplacian.laplacian (ρ ∘ U) z := by
    rw [laplacian_comp_of_planarTension_eq_zero g hρ
      ((hUsm z (interior_subset hz).1).of_le (by simp)) (hτ z hz)]
    exact add_nonneg (hH z hz _) (hH z hz _)
  intro p hp
  have hpD : p ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hdq : 0 < fderiv ℝ (ρ ∘ U) p p :=
    Analysis.annulus_hopf_radial hr hr1 hq hΔ hinner
      (fun z hz => (houter z hz).le) hp (houter p hp)
  have hne : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p ≠ 0 := by
    intro hzero
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, ℝ)) p (hρ.mdifferentiable (by simp) (U p))
        ((hUsm p hpD).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, hzero] at hchain
    have he : fderiv ℝ (ρ ∘ U) p p = 0 := by
      have hvalue := congrArg
        (fun D : TangentSpace 𝓘(ℝ, ℂ) p →L[ℝ]
            TangentSpace 𝓘(ℝ, ℝ) ((ρ ∘ U) p) =>
          NormedSpace.fromTangentSpace ((ρ ∘ U) p)
            (D ((NormedSpace.fromTangentSpace p).symm p))) hchain
      simpa using hvalue
    exact (ne_of_gt hdq) he
  have hc : diskMapConformalCoefficient g U p ≠ 0 :=
    fun h => hne ((hconf p hp).coefficient_eq_zero_iff.mp h)
  let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p
  change Function.Injective L
  intro v w hvw
  have hzero : diskMapPartial (E := E) U p (v - w) = 0 := by
    change L (v - w) = 0
    exact (map_sub L v w).trans (sub_eq_zero.mpr hvw)
  have hinner := (hconf p hp).inner_partials (v - w) (v - w)
  rw [hzero] at hinner
  have hmul : diskMapConformalCoefficient g U p * inner ℝ (v - w) (v - w) = 0 := by
    simpa using hinner.symm
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hc))


/-- The convex-collar boundary rank criterion for a smooth extension of the same
Morrey disk. Harmonicity and boundary conformality come from that disk. -/
theorem IsMorreyDisk.boundary_immersion_of_convex_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : IsMorreyDisk g γ u) (hU : SmoothDiskExtension (E := E) u U)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hH : ∀ z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ),
      ∀ v : TangentSpace 𝓘(ℝ, E) (U z), 0 ≤ hessFun g ρ (U z) v v)
    (hinner : ∀ z ∈ sphere (0 : ℂ) r, ρ (U z) < 0)
    (houter : ∀ z ∈ sphere (0 : ℂ) 1, ρ (U z) = 0) :
    ∀ p ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p) := by
  have hτ (z : ℂ)
      (hz : z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ)) :
      planarTension g U z = 0 := by
    change diskMapTension g U z = 0
    exact hu.tension_eq_zero_of_extension_closedBall hU z (interior_subset hz).1
  exact hU.boundary_immersion_of_convex_collar g ρ hρ hr hr1 hτ hH hinner houter
    (fun z hz => hu.conformal_of_extension_closedBall hU z (sphere_subset_closedBall hz))

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

private theorem exists_annulus_mapsTo_of_boundary
    {M : Type*} [TopologicalSpace M] (u : C(closedDisk, M))
    {V : Set M} (hV : IsOpen V)
    (hboundary : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → u z ∈ V) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z : closedDisk, r ≤ ‖(z : ℂ)‖ → u z ∈ V := by
  let K : Set closedDisk := (u ⁻¹' V)ᶜ
  have hK : IsCompact K := (hV.preimage u.continuous).isClosed_compl.isCompact
  by_cases hnonempty : K.Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hnonempty
      (continuous_norm.comp continuous_subtype_val).continuousOn
    have hnorm : ‖(z₀ : ℂ)‖ < 1 := by
      apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp z₀.property)
      intro heq
      exact hz₀ (hboundary z₀ heq)
    refine ⟨(‖(z₀ : ℂ)‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro z hz
    by_contra hnot
    have hle : ‖(z : ℂ)‖ ≤ ‖(z₀ : ℂ)‖ := hmax hnot
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, fun z _ => ?_⟩
    by_contra hnot
    exact hnonempty ⟨z, hnot⟩


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An open target neighborhood of the boundary image contains the image of one
closed annulus of the same disk extension. -/
private theorem SmoothDiskExtension.exists_annulus_mapsTo
    {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U)
    {V : Set M} (hV : IsOpen V)
    (hboundary : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → u z ∈ V) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      MapsTo U (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ) V := by
  obtain ⟨r, hr, hr1, hrV⟩ := exists_annulus_mapsTo_of_boundary u hV hboundary
  refine ⟨r, hr, hr1, fun z hz => ?_⟩
  rw [hU.1 ⟨z, hz.1⟩]
  apply hrV ⟨z, hz.1⟩
  exact not_lt.mp (fun hlt => hz.2 (mem_ball_zero_iff.mpr hlt))

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Strict confinement and a nonnegative original-metric Hessian in an open
neighborhood of the boundary image give boundary rank for the same Morrey disk
and its same smooth extension. The required annulus is derived by compactness. -/
theorem IsMorreyDisk.boundary_immersion_of_hessian_nonneg_near_boundary
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {V : Set M} (hV : IsOpen V)
    (hboundaryV : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → u z ∈ V)
    (hH : ∀ x ∈ V, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      0 ≤ hessFun g ρ x v v)
    (hstrict : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ (u z) < 0)
    (hboundary : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ρ (u z) = 0) :
    ∀ p ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p) := by
  obtain ⟨r, hr, hr1, hrV⟩ := hU.exists_annulus_mapsTo hV hboundaryV
  apply hu.boundary_immersion_of_convex_collar hU ρ hρ hr hr1
  · intro z hz v
    exact hH (U z) (hrV (interior_subset hz)) v
  · intro z hz
    have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hzD : z ∈ closedBall (0 : ℂ) 1 :=
      mem_closedBall_zero_iff.mpr (hzn.trans_le hr1.le)
    rw [hU.1 ⟨z, hzD⟩]
    exact hstrict ⟨z, hzD⟩ (hzn.trans_lt hr1)
  · intro z hz
    rw [hU.1 ⟨z, sphere_subset_closedBall hz⟩]
    exact hboundary ⟨z, sphere_subset_closedBall hz⟩ (mem_sphere_zero_iff_norm.mp hz)

end DifferentialGeometry.Geometry

set_option autoImplicit false

noncomputable section

open Manifold Set Metric
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Boundary rank makes the supplied signed trace lift regular. The real lift is
retained, as are the disk, its smooth extension and its circle phase. -/
theorem SmoothDiskExtension.regular_signed_trace_lift
    {γ : freeLoop M} {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ}
    (hψc : Continuous ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))
    (htrace : diskTrace u = γ.comp σ)
    (hsign : (Monotone ψ ∧ ∀ t : ℝ, ψ (t + 1) = ψ t + 1) ∨
      (Antitone ψ ∧ ∀ t : ℝ, ψ (t + 1) = ψ t - 1))
    (hrank : ∀ z ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ContDiff ℝ ∞ ψ ∧
      ((Monotone ψ ∧ (∀ t, ψ (t + 1) = ψ t + 1) ∧ ∀ t, 0 < deriv ψ t) ∨
       (Antitone ψ ∧ (∀ t, ψ (t + 1) = ψ t - 1) ∧ ∀ t, deriv ψ t < 0)) := by
  have hσ : IsWeaklyMonotoneOnce σ := ⟨ψ, hψc, hlift, hsign⟩
  obtain ⟨η, hη, hηlift, hηsign⟩ :=
    hU.exists_regular_signed_trace_lift hγ hσ htrace hrank
  have hderiv (t : ℝ) : deriv ψ t = deriv η t :=
    deriv_eq_of_addCircle_coe_eventuallyEq hψc.continuousAt hη.continuous.continuousAt
      (Filter.Eventually.of_forall fun s => (hlift s).trans (hηlift s).symm)
  have hne (t : ℝ) : deriv ψ t ≠ 0 := by
    rw [hderiv t]
    rcases hηsign with ⟨_, _, hpos⟩ | ⟨_, _, hneg⟩
    · exact ne_of_gt (hpos t)
    · exact ne_of_lt (hneg t)
  refine ⟨hγ.contDiff_weakTraceLift hU.smoothUpToBoundary htrace hψc hlift, ?_⟩
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · exact Or.inl ⟨hm, hp, fun t => lt_of_le_of_ne hm.deriv_nonneg (hne t).symm⟩
  · exact Or.inr ⟨hm, hp, fun t => lt_of_le_of_ne hm.deriv_nonpos (hne t)⟩

end DifferentialGeometry.Geometry
