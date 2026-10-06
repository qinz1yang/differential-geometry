import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileBoundaryRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.BoundaryCollar
import DifferentialGeometry.Geometry.HarmonicMap.ConformalRank

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DiskRegularity.ConsumerAudit

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The original completed-profile disk has finitely many critical points, and
all fibers over their values lie in one compact interior subdisk. Boundary
rank, separation and singleton fibers are derived for the supplied disk and
smooth extension. No interior rank or finite-fiber hypothesis is assumed. -/
theorem profile_boundary_singletons_and_finite_critical_set
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
      let B : Set closedDisk := {z | ¬ Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γU θ) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z) ∧
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < 1 ∧
        (∀ z : closedDisk, r₀ < ‖(z : ℂ)‖ →
          (∀ w, q w = q z → w = z) ∧
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) ∧
        (∀ z ∈ B, ‖(z : ℂ)‖ ≤ r₀) ∧ B.Finite ∧
        ∀ z ∈ q ⁻¹' (q '' B), ‖(z : ℂ)‖ ≤ r₀ := by
  let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
  dsimp only
  intro γU q hγ hq hγzero Q hQ
  let ρU : U → ℝ := fun x => ρ (x : M)
  have hρU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρU :=
    hρ.comp contMDiff_subtype_val
  have hρUa : ∀ x : U, ρU x < a := fun x => x.property
  have hbaseU (x : U) (hx : 0 < ρU x) (v : TangentSpace 𝓘(ℝ, E) x) :
      0 ≤ hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    exact hbase (x : M) hx x.property
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v)
  have hcontactU (x : U) (hx : ρU x = 0) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ≠ 0) : 0 < hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    simpa only [mfderiv_subtype_val_apply] using hcontact (x : M) hx v hv
  have hqProfile : IsMorreyDisk
      (profileMetric (g.restrictOpen U) a ha ρU hρU hρUa) γU q := hq
  obtain ⟨_, hstrict, _⟩ :=
    IsMorreyDisk.profile_confinement (g.restrictOpen U) a ha ρU hρU hρUa
      hbaseU hcontactU hqProfile hγ (fun θ => (hγzero θ).le)
  have hseparate (z : closedDisk) (hz : ‖(z : ℂ)‖ < 1) (θ : loopCircle) :
      q z ≠ γU θ := by
    intro heq
    have hneg := hstrict z hz
    change ρ (q z : M) < 0 at hneg
    rw [heq, hγzero θ] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  obtain ⟨_, hrank⟩ :=
    boundary_immersion_of_profile_metric g a ha ρ hρ hbase hcontact
      γU q hγ hq hγzero Q hQ
  have hrankQ (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
    have h := hrank z hz
    rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
      (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U Q z] at h
    exact h
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace hrankQ hseparate
  have hsingle (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1)
      (w : closedDisk) (hw : q w = q z) : w = z := by
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hz
    have hθz : diskBoundary θ = z := Subtype.ext hθ
    exact (hboundary θ w (hw.trans (congrArg q hθz).symm)).trans hθz
  obtain ⟨r₀, hr₀, hr₀1, hcollar⟩ := hQ.exists_singleton_regular_collar hsingle hrankQ
  let B : Set closedDisk := {z | ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
  have hBinner (z : closedDisk) (hz : z ∈ B) : ‖(z : ℂ)‖ ≤ r₀ := by
    apply le_of_not_gt
    intro hlt
    exact hz (hcollar z hlt).2
  have hcompact := hq.finite_not_injective_mfderiv_of_isCompact hγ
    (isCompact_closedBall (0 : ℂ) r₀) (closedBall_subset_ball hr₀1)
  have hBfinite : B.Finite := by
    have hpre := Set.Finite.preimage
      (f := (Subtype.val : closedDisk → ℂ)) Subtype.val_injective.injOn hcompact
    apply hpre.subset
    intro z hz
    have hzK : (z : ℂ) ∈ closedBall (0 : ℂ) r₀ :=
      mem_closedBall_zero_iff.mpr (hBinner z hz)
    have hzD : (z : ℂ) ∈ ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.mpr ((hBinner z hz).trans_lt hr₀1)
    refine ⟨hzK, ?_⟩
    have heq : (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) =
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
      ext v
      exact congrArg (fun L => L v)
        ((hQ.eventuallyEq_diskExtension hzD).mfderiv_eq
          (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
    intro hinj
    apply hz
    change Function.Injective
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)
    intro v w hvw
    apply hinj
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) heq).symm.trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) heq))
  refine ⟨hseparate, hsingle, r₀, hr₀, hr₀1, hcollar, hBinner, hBfinite, ?_⟩
  intro z hz
  obtain ⟨b, hb, hbz⟩ := hz
  apply le_of_not_gt
  intro hlt
  have hbEq : b = z := (hcollar z hlt).1 b hbz
  exact (not_lt_of_ge (hbEq ▸ hBinner b hb)) hlt

end DiskRegularity.ConsumerAudit
