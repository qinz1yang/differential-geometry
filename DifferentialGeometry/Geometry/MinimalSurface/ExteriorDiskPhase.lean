import DifferentialGeometry.Topology.Manifold.AddCircle.RegularLiftExtension
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskReparametrization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FixedTraceBoundaryRank
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Geometry.MinimalSurface

private theorem exists_diffeomorph_extension_of_regular_signed_lift
    {σ : C(loopCircle, loopCircle)} {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a)
    (hlift : ∀ t : ℝ, (a t : loopCircle) = σ (t : loopCircle))
    (hsign : ((∀ t, a (t + 1) = a t + 1) ∧ ∀ t, 0 < deriv a t) ∨
      ((∀ t, a (t + 1) = a t - 1) ∧ ∀ t, deriv a t < 0)) :
    ∃ (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞)
      (P : ℂ ≃ₘ[ℝ] ℂ),
      (∀ θ : loopCircle, ψ θ = σ θ) ∧
      (∀ θ : loopCircle, P (diskBoundary θ) = (diskBoundary (σ θ) : ℂ)) ∧
      P '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
  rcases hsign with ⟨hperiod, hder⟩ | ⟨hperiod, hder⟩
  · obtain ⟨ψ, hψ, P, hP, _, hPball⟩ :=
      AddCircle.exists_diffeomorph_extension_of_regular_degree_one_lift
        ha hperiod hder hlift
    exact ⟨ψ, P, hψ, hP, hPball⟩
  · let τ : C(loopCircle, loopCircle) := ⟨fun θ => -σ θ, σ.continuous.neg⟩
    have hperiod' (t : ℝ) : -a (t + 1) = -a t + 1 := by
      rw [hperiod]
      ring
    have hder' (t : ℝ) : 0 < deriv (fun s => -a s) t := by
      change 0 < deriv (-a) t
      rw [deriv.neg]
      exact neg_pos.mpr (hder t)
    have hlift' (t : ℝ) : ((-a t : ℝ) : loopCircle) = τ (t : loopCircle) := by
      change ((-a t : ℝ) : loopCircle) = -σ (t : loopCircle)
      rw [QuotientAddGroup.mk_neg, hlift]
    obtain ⟨ψPos, hψPos, PPos, hPPos, _, hPball⟩ :=
      AddCircle.exists_diffeomorph_extension_of_regular_degree_one_lift
        ha.neg hperiod' hder' hlift'
    have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun θ : loopCircle => -θ) := by
      apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
        QuotientAddGroup.mk_surjective
      exact (AddCircle.contMDiff_coe.comp contDiff_neg.contMDiff).congr
        (fun t => (QuotientAddGroup.mk_neg (AddSubgroup.zmultiples (1 : ℝ)) t).symm)
    let N : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞ :=
      { toEquiv := Equiv.neg loopCircle
        contMDiff_toFun := hneg
        contMDiff_invFun := hneg }
    have hconjBoundary (θ : loopCircle) :
        starRingEnd ℂ (diskBoundary θ : ℂ) = (diskBoundary (-θ) : ℂ) := by
      change starRingEnd ℂ (AddCircle.toCircle θ : ℂ) =
        (AddCircle.toCircle (-θ) : ℂ)
      rw [AddCircle.toCircle_neg]
      exact (Circle.coe_inv_eq_conj _).symm
    refine ⟨ψPos.trans N, PPos.trans Complex.conjCLE.toDiffeomorph, ?_, ?_, ?_⟩
    · intro θ
      change -ψPos θ = σ θ
      rw [hψPos]
      exact neg_neg (σ θ)
    · intro θ
      change starRingEnd ℂ (PPos (diskBoundary θ)) = (diskBoundary (σ θ) : ℂ)
      rw [hPPos, hconjBoundary]
      change (diskBoundary (-(-σ θ)) : ℂ) = (diskBoundary (σ θ) : ℂ)
      rw [neg_neg]
    · change (fun z => starRingEnd ℂ (PPos z)) '' Metric.closedBall (0 : ℂ) 1 = _
      rw [← Set.image_image, hPball]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hx
      · intro hz
        refine ⟨starRingEnd ℂ z, ?_, ?_⟩
        · simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
        · simp

theorem isExteriorSpanningDisk.exists_exact_trace_of_weakly_monotone_phase
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    {σ : C(loopCircle, loopCircle)}
    (hu : isExteriorSpanningDisk W (γ.comp σ) u)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (hσ : IsWeaklyMonotoneOnce σ) :
    ∃ (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞)
      (Φ : ℂ ≃ₘ[ℝ] ℂ) (φ : closedDisk ≃ₜ closedDisk),
      (∀ θ : loopCircle, ψ θ = σ θ) ∧
      (∀ z : closedDisk, Φ z = (φ z : ℂ)) ∧
      (∀ θ : loopCircle, φ (diskBoundary θ) = diskBoundary (ψ.symm θ)) ∧
      (∃ K L : ℝ≥0, LipschitzWith K φ ∧ LipschitzWith L φ.symm) ∧
      isExteriorSpanningDisk W γ (u.comp ⟨φ, φ.continuous⟩) ∧
      Set.range (u.comp ⟨φ, φ.continuous⟩) = Set.range u ∧
      ∀ g : SmoothRiemannianMetric (𝓡 3) M,
        riemannianDiskArea g (u.comp ⟨φ, φ.continuous⟩) = riemannianDiskArea g u := by
  have htrace := hu.1
  obtain ⟨U, hU, hrank⟩ := hu.2.2.2.2.2
  obtain ⟨a, ha, halift, hsign⟩ := hU.exists_regular_signed_trace_lift hγ
    hσ htrace (fun z hz => hrank z (Metric.sphere_subset_closedBall hz))
  have hregular : ((∀ t, a (t + 1) = a t + 1) ∧ ∀ t, 0 < deriv a t) ∨
      ((∀ t, a (t + 1) = a t - 1) ∧ ∀ t, deriv a t < 0) :=
    hsign.imp (fun h => h.2) (fun h => h.2)
  obtain ⟨ψ, P, hψ, hPboundary, hPball⟩ :=
    exists_diffeomorph_extension_of_regular_signed_lift ha halift hregular
  let Φ : ℂ ≃ₘ[ℝ] ℂ := P.symm
  have hΦboundary (θ : loopCircle) :
      Φ (diskBoundary θ) = (diskBoundary (ψ.symm θ) : ℂ) := by
    apply P.injective
    change P (P.symm (diskBoundary θ : ℂ)) = P (diskBoundary (ψ.symm θ) : ℂ)
    rw [P.apply_symm_apply, hPboundary, ← hψ, ψ.apply_symm_apply]
  have hΦball : Φ '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
    change P.symm '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1
    calc
      P.symm '' Metric.closedBall (0 : ℂ) 1 =
          P.symm '' (P '' Metric.closedBall (0 : ℂ) 1) :=
        congrArg (fun S : Set ℂ => P.symm '' S) hPball.symm
      _ = Metric.closedBall (0 : ℂ) 1 := by
        rw [Set.image_image]
        simp only [P.symm_apply_apply, Set.image_id']
  have hpre : Metric.closedBall (0 : ℂ) 1 = Φ ⁻¹' Metric.closedBall (0 : ℂ) 1 :=
    (Φ.toHomeomorph.preimage_image (Metric.closedBall (0 : ℂ) 1)).symm.trans
      (congrArg (fun S : Set ℂ => Φ ⁻¹' S) hΦball)
  let φ : closedDisk ≃ₜ closedDisk := Φ.toHomeomorph.sets hpre
  have hcompat (z : closedDisk) : Φ z = (φ z : ℂ) := rfl
  have hinvcompat (z : closedDisk) : Φ.symm z = (φ.symm z : ℂ) := by
    apply Φ.injective
    change Φ (Φ.symm (z : ℂ)) = Φ (φ.symm z : ℂ)
    rw [Φ.apply_symm_apply, hcompat, φ.apply_symm_apply]
  have hboundary (θ : loopCircle) : φ (diskBoundary θ) = diskBoundary (ψ.symm θ) := by
    apply Subtype.ext
    exact (hcompat (diskBoundary θ)).symm.trans (hΦboundary θ)
  have hΦsmooth : ContDiff ℝ ∞ (fun z : ℂ => Φ z) := Φ.contMDiff.contDiff
  have hΦinvsmooth : ContDiff ℝ ∞ (fun z : ℂ => Φ.symm z) := Φ.symm.contMDiff.contDiff
  obtain ⟨K, hK⟩ := hΦsmooth.contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_closedBall (0 : ℂ) 1) (isCompact_closedBall (0 : ℂ) 1)
  obtain ⟨L, hL⟩ := hΦinvsmooth.contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_closedBall (0 : ℂ) 1) (isCompact_closedBall (0 : ℂ) 1)
  have hφ : LipschitzWith K φ := by
    intro x y
    change edist (φ x : ℂ) (φ y : ℂ) ≤ (K : ENNReal) * edist (x : ℂ) (y : ℂ)
    simpa only [hcompat] using hK x.property y.property
  have hφinv : LipschitzWith L φ.symm := by
    intro x y
    change edist (φ.symm x : ℂ) (φ.symm y : ℂ) ≤ (L : ENNReal) * edist (x : ℂ) (y : ℂ)
    simpa only [hinvcompat] using hL x.property y.property
  have hcancel : (γ.comp σ).comp ⟨ψ.symm, ψ.symm.continuous⟩ = γ := by
    ext θ
    change γ (σ (ψ.symm θ)) = γ θ
    rw [← hψ, ψ.apply_symm_apply]
  have hexact : isExteriorSpanningDisk W γ (u.comp ⟨φ, φ.continuous⟩) := by
    have hc := hu.comp_smooth_disk_reparametrization φ ψ.symm.toHomeomorph Φ hcompat hboundary
    change isExteriorSpanningDisk W
      ((γ.comp σ).comp ⟨ψ.symm, ψ.symm.continuous⟩)
      (u.comp ⟨φ, φ.continuous⟩) at hc
    simpa only [hcancel] using hc
  have hrange : Set.range (u.comp ⟨φ, φ.continuous⟩) = Set.range u := by
    change Set.range (u ∘ φ) = Set.range u
    rw [Set.range_comp, φ.surjective.range_eq, Set.image_univ]
  refine ⟨ψ, Φ, φ, hψ, hcompat, hboundary, ⟨K, L, hφ, hφinv⟩, hexact, hrange, ?_⟩
  intro g
  exact hu.area_comp_reparametrization g φ hφ hφinv

theorem isExteriorSpanningDisk.exists_exact_trace_of_smooth_positive_phase
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    {σ : C(loopCircle, loopCircle)}
    (hu : isExteriorSpanningDisk W (γ.comp σ) u)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (hσ : IsSmoothPositiveCircleMap σ) :
    ∃ (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞)
      (Φ : ℂ ≃ₘ[ℝ] ℂ) (φ : closedDisk ≃ₜ closedDisk),
      (∀ θ : loopCircle, ψ θ = σ θ) ∧
      (∀ z : closedDisk, Φ z = (φ z : ℂ)) ∧
      (∀ θ : loopCircle, φ (diskBoundary θ) = diskBoundary (ψ.symm θ)) ∧
      (∃ K L : ℝ≥0, LipschitzWith K φ ∧ LipschitzWith L φ.symm) ∧
      isExteriorSpanningDisk W γ (u.comp ⟨φ, φ.continuous⟩) ∧
      ∀ g : SmoothRiemannianMetric (𝓡 3) M,
        riemannianDiskArea g (u.comp ⟨φ, φ.continuous⟩) = riemannianDiskArea g u := by
  obtain ⟨ψ, Φ, φ, hψ, hΦ, hboundary, hLip, hexact, _, harea⟩ :=
    hu.exists_exact_trace_of_weakly_monotone_phase hγ hσ.weaklyMonotoneOnce
  exact ⟨ψ, Φ, φ, hψ, hΦ, hboundary, hLip, hexact, harea⟩

end DifferentialGeometry.Geometry.MinimalSurface
