import DifferentialGeometry.Geometry.HarmonicMap.CountableCriticalValues
import DifferentialGeometry.Geometry.EuclideanDisk.CountablePunctures
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FiniteFibers

set_option autoImplicit false
noncomputable section

open Set Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold

/-- For the literal original affine restriction with the supplied SAME selected
trace-fiber law, deleting both actual disks' critical VALUES leaves a connected
full source preimage. The alternate disk needs no boundary singleton law. -/
theorem IMS03Embeddedness.ConsumerAudit.actual_proper_restriction_regular_value_source_connected
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (QOriginal : ℂ → M) (hQOriginal : SmoothDiskExtension (E := E) u QOriginal)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hinside : ‖a‖ + r < 1)
    (hloop : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk u a r)))
    (htraceFiber : ∀ (θ : loopCircle) (w : closedDisk),
      u w = diskTrace (affineSubdisk u a r) θ →
        (w : ℂ) = a + r • (diskBoundary θ : ℂ))
    (qAlt : C(closedDisk, M))
    (hqAlt : IsMorreyDisk g (diskTrace (affineSubdisk u a r)) qAlt) :
    let qRest := affineSubdisk u a r
    let V := (Set.range (diskTrace qRest) ∪
      (diskInteriorCriticalValues (E := E) qRest ∪
        diskInteriorCriticalValues (E := E) qAlt))ᶜ
    IsConnected (qRest ⁻¹' V) := by
  classical
  let qRest := affineSubdisk u a r
  let Γ := Set.range (diskTrace qRest)
  let K := diskInteriorCriticalValues (E := E) qRest ∪
    diskInteriorCriticalValues (E := E) qAlt
  let V := (Γ ∪ K)ᶜ
  change IsConnected (qRest ⁻¹' V)
  obtain ⟨L, huLip⟩ := hQOriginal.lipschitz g
  have hqRest := hu.affineSubdisk huLip a r hr hinside hloop.immersed
  have hφ (z : closedDisk) : a + r • (z : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    apply mem_closedBall_zero_iff.mpr
    have hz : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    calc
      ‖a + r • (z : ℂ)‖ ≤ ‖a‖ + ‖r • (z : ℂ)‖ := norm_add_le _ _
      _ = ‖a‖ + r * ‖(z : ℂ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ ‖a‖ + r := by nlinarith
      _ ≤ 1 := hinside.le
  let φ : closedDisk → closedDisk := fun z => ⟨a + r • (z : ℂ), hφ z⟩
  have hqval (z : closedDisk) : qRest z = u (φ z) := diskExtension_coe u (φ z)
  have hsingle (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1)
      (w : closedDisk) (hw : qRest w = qRest z) : w = z := by
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hz
    have hθz : diskBoundary θ = z := Subtype.ext hθ
    have hvalue : u (φ w) = diskTrace qRest θ :=
      (hqval w).symm.trans (hw.trans (congrArg qRest hθz).symm)
    have heq := htraceFiber θ (φ w) hvalue
    change a + r • (w : ℂ) = a + r • (diskBoundary θ : ℂ) at heq
    have hcoord : (w : ℂ) = (diskBoundary θ : ℂ) := by
      have hh := congrArg (fun v : ℂ => r⁻¹ • v) (add_left_cancel heq)
      simpa only [inv_smul_smul₀ hr.ne'] using hh
    exact (Subtype.ext hcoord).trans hθz
  have hfiber :=
    DiskRegularity.ConsumerAudit.morrey_finite_fibers_of_boundary_fibers_singleton
      hqRest hloop hsingle
  have hK : K.Countable :=
    (hqRest.countable_interior_critical_values hloop).union
      (hqAlt.countable_interior_critical_values hloop)
  let B : Set closedDisk := qRest ⁻¹' K
  have hB : B.Countable := by
    apply (hK.biUnion fun y _ => (hfiber y).countable).mono
    intro z hz
    exact mem_iUnion₂.mpr ⟨qRest z, hz, rfl⟩
  let S : Set ℂ := Subtype.val '' B
  have hS : S.Countable := hB.image Subtype.val
  have himage : (Subtype.val : closedDisk → ℂ) '' (qRest ⁻¹' V) =
      ball (0 : ℂ) 1 \ S := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have haway : qRest z ∉ Γ := fun h => hz (Or.inl h)
      have hnorm : ‖(z : ℂ)‖ < 1 := by
        by_contra hnot
        have heq : ‖(z : ℂ)‖ = 1 :=
          le_antisymm (mem_closedBall_zero_iff.mp z.property) (le_of_not_gt hnot)
        obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one heq
        exact haway ⟨θ, congrArg qRest (Subtype.ext hθ)⟩
      refine ⟨mem_ball_zero_iff.mpr hnorm, ?_⟩
      rintro ⟨w, hw, heq⟩
      have hwz : w = z := Subtype.ext heq
      exact hz (Or.inr (hwz ▸ hw))
    · rintro ⟨hx, hnot⟩
      let z : closedDisk := ⟨x, ball_subset_closedBall hx⟩
      refine ⟨z, ?_, rfl⟩
      intro hbad
      rcases hbad with hΓ | hKz
      · obtain ⟨θ, hθ⟩ := hΓ
        have hnormθ : ‖(diskBoundary θ : ℂ)‖ = 1 := Circle.norm_coe _
        have hzθ : z = diskBoundary θ := hsingle _ hnormθ z hθ.symm
        have hxnorm : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.mp hx
        rw [hzθ, hnormθ] at hxnorm
        exact (lt_irrefl 1) hxnorm
      · exact hnot ⟨z, hKz, rfl⟩
  have hconnected := isConnected_openDisk_diff_countable hS
  have hpre : IsPreconnected (qRest ⁻¹' V) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [himage]
    exact hconnected.isPreconnected
  have hnonempty : (qRest ⁻¹' V).Nonempty := by
    apply Set.image_nonempty.mp
    rw [himage]
    exact hconnected.nonempty
  exact ⟨hnonempty, hpre⟩
