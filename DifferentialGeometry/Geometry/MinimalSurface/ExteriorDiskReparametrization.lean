import DifferentialGeometry.Topology.Circle.Extension
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Geometry.MinimalSurface

theorem exists_smooth_disk_reparametrization
    (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞) :
    ∃ Φ : ℂ ≃ₘ[ℝ] ℂ,
      (∀ θ : loopCircle, Φ (diskBoundary θ) = (diskBoundary (ψ θ) : ℂ)) ∧
      Φ '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
  let A := AddCircle.diffeomorphCircle
  obtain ⟨Φ, hΦ, _, hball⟩ := Circle.exists_diffeomorph_extension ((A.symm.trans ψ).trans A)
  refine ⟨Φ, ?_, hball⟩
  intro θ
  have hA (x : loopCircle) : (A x : ℂ) = (diskBoundary x : ℂ) := by
    congr 1
    exact AddCircle.homeomorphCircle_apply one_ne_zero x
  rw [← hA θ, hΦ]
  change (A (ψ (A.symm (A θ))) : ℂ) = (diskBoundary (ψ θ) : ℂ)
  rw [A.symm_apply_apply]
  exact hA (ψ θ)


theorem isExteriorSpanningDisk.comp_smooth_disk_reparametrization
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) (φ : closedDisk ≃ₜ closedDisk)
    (ψ : loopCircle ≃ₜ loopCircle) (Φ : ℂ ≃ₘ[ℝ] ℂ)
    (hΦ : ∀ z : closedDisk, Φ z = (φ z : ℂ))
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (ψ θ)) :
    isExteriorSpanningDisk W (γ.comp ⟨ψ, ψ.continuous⟩) (u.comp ⟨φ, φ.continuous⟩) := by
  rcases hu with ⟨htrace, hfrontier, hemb, hrange, hint, U, hU, himm⟩
  have himage : Φ '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hΦ ⟨x, hx⟩]
      exact (φ ⟨x, hx⟩).property
    · intro hz
      exact ⟨φ.symm ⟨z, hz⟩, (φ.symm ⟨z, hz⟩).property,
        (hΦ (φ.symm ⟨z, hz⟩)).trans (congrArg Subtype.val (φ.apply_symm_apply ⟨z, hz⟩))⟩
  refine ⟨?_, ?_, hemb.comp φ.isEmbedding, ?_, ?_, U ∘ Φ, ?_, ?_⟩
  · ext θ
    change u (φ (diskBoundary θ)) = γ (ψ θ)
    rw [hboundary]
    exact congrArg (fun f : freeLoop M => f (ψ θ)) htrace
  · rintro _ ⟨θ, rfl⟩
    exact hfrontier (mem_range_self (ψ θ))
  · rintro _ ⟨z, rfl⟩
    exact hrange (mem_range_self (φ z))
  · intro z hz
    apply hint
    change ‖(φ z : ℂ)‖ < 1
    have himage' := Φ.toHomeomorph.image_interior (Metric.closedBall (0 : ℂ) 1)
    change Φ '' interior (Metric.closedBall (0 : ℂ) 1) = interior (Φ '' Metric.closedBall (0 : ℂ) 1) at himage'
    rw [himage, interior_closedBall _ one_ne_zero] at himage'
    have hm : Φ z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [← himage']
      exact mem_image_of_mem Φ (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
    simpa only [hΦ, Metric.mem_ball, dist_zero_right] using hm
  · obtain ⟨hUeq, N, hN, hDN, hUs⟩ := hU
    refine ⟨fun z => ?_, Φ ⁻¹' N, hN.preimage Φ.continuous, ?_, ?_⟩
    · change U (Φ z) = u (φ z)
      rw [hΦ, hUeq]
    · intro z hz
      exact hDN (himage ▸ mem_image_of_mem Φ hz)
    · exact hUs.comp Φ.contMDiff.contMDiffOn (fun _ hx => hx)
  · intro z hz
    rw [mfderiv_comp (I' := 𝓘(ℝ, ℂ))]
    · change Function.Injective ((mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U (Φ z)) ∘ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Φ z))
      exact (himm (Φ z) (himage ▸ mem_image_of_mem Φ hz)).comp
        (Φ.mfderivToContinuousLinearEquiv (by simp) z).injective
    · obtain ⟨_, N, hN, hDN, hUs⟩ := hU
      exact (hUs.contMDiffAt (hN.mem_nhds (hDN (himage ▸ mem_image_of_mem Φ hz)))).mdifferentiableAt (by simp)
    · exact Φ.mdifferentiable (by simp) z

theorem isExteriorSpanningDisk.area_comp_reparametrization
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M] {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) (g : SmoothRiemannianMetric (𝓡 3) M)
    (φ : closedDisk ≃ₜ closedDisk) {K L : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ' : LipschitzWith L φ.symm) :
    Geometry.riemannianDiskArea g (u.comp ⟨φ, φ.continuous⟩) = Geometry.riemannianDiskArea g u := by
  obtain ⟨U, hU, _⟩ := hu.2.2.2.2.2
  obtain ⟨C, hC⟩ := hU.lipschitz g
  exact Geometry.riemannianDiskArea_reparametrize g hC φ hφ hφ'

end DifferentialGeometry.Geometry.MinimalSurface
