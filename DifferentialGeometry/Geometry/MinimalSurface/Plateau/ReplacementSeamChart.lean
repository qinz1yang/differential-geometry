import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence
import DifferentialGeometry.Analysis.Complex.DiskBoundaryChart
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

/-- A real-angular inward sector contains an ambient neighborhood of its marked
circle point, after intersecting with the closed disk. The angle is centered at
that same point, so there is no branch-cut or changed-phase choice. -/
private theorem exists_neighborhood_in_radial_sector (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ V : Set ℂ, IsOpen V ∧ (diskBoundary (s₀ : loopCircle) : ℂ) ∈ V ∧
      ∀ z ∈ V ∩ Metric.closedBall (0 : ℂ) 1,
        ∃ t : ℝ, |t - s₀| < η ∧ ∃ r ∈ Icc (1 / 2 : ℝ) 1,
          z = r • (diskBoundary (t : loopCircle) : ℂ) := by
  let p : ℂ := diskBoundary (s₀ : loopCircle)
  have hp : ‖p‖ = 1 := Circle.norm_coe _
  have hpne : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
  let θ : ℂ → ℝ := fun z => s₀ + Complex.arg (z / p) / (2 * Real.pi)
  have hθp : θ p = s₀ := by simp only [θ, div_self hpne, Complex.arg_one, zero_div, add_zero]
  have hquot : ContinuousAt (fun z : ℂ => z / p) p := continuousAt_id.div_const p
  have harg : ContinuousAt (fun z : ℂ => Complex.arg (z / p)) p := by
    have hslit : p / p ∈ Complex.slitPlane := by
      rw [div_self hpne]
      simp [Complex.mem_slitPlane_iff]
    exact (Complex.continuousAt_arg hslit).comp (f := fun z : ℂ => z / p) hquot
  have hθ : ContinuousAt θ p := continuousAt_const.add (harg.div_const _)
  have hnearθ : ∀ᶠ z in 𝓝 p, |θ z - s₀| < η := by
    have hb : Metric.ball s₀ η ∈ 𝓝 (θ p) := hθp.symm ▸ Metric.ball_mem_nhds s₀ hη
    have h : ∀ᶠ z in 𝓝 p, θ z ∈ Metric.ball s₀ η := hθ.preimage_mem_nhds hb
    filter_upwards [h] with z hz
    simpa only [Metric.mem_ball, Real.dist_eq] using hz
  have hnearNorm : ∀ᶠ z in 𝓝 p, (1 / 2 : ℝ) < ‖z‖ :=
    continuous_norm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [hp]; norm_num))
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (hnearθ.and hnearNorm)
  refine ⟨V, hV, hpV, ?_⟩
  intro z hz
  refine ⟨θ z, (hVsub hz.1).1, ‖z‖,
    ⟨(hVsub hz.1).2.le, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2⟩, ?_⟩
  have hangle : 2 * Real.pi * θ z = 2 * Real.pi * s₀ + Complex.arg (z / p) := by
    dsimp only [θ]
    field_simp [Real.pi_ne_zero]
  have hquotNorm : ‖z / p‖ = ‖z‖ := by rw [norm_div, hp, div_one]
  rw [diskBoundary_coe, hangle, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hpexp : Complex.exp ((2 * Real.pi * s₀ : ℝ) * Complex.I) = p :=
    (diskBoundary_coe s₀).symm
  rw [hpexp, Complex.real_smul]
  calc
    z = p * (z / p) := by field_simp [hpne]
    _ = p * ((‖z / p‖ : ℂ) * Complex.exp ((Complex.arg (z / p) : ℂ) * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖z‖ : ℂ) * (p * Complex.exp ((Complex.arg (z / p) : ℂ) * Complex.I)) := by
      rw [hquotNorm]
      ring

private theorem seam_chart_image_ball_eq_interior
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) :
    e '' Metric.ball (0 : ℂ) 1 = interior (e '' Metric.closedBall (0 : ℂ) 1) := by
  let K := e '' Metric.closedBall (0 : ℂ) 1
  have htarget : K ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source' (hsrc hz)
  have himage : e.toOpenPartialHomeomorph.IsImage (Metric.closedBall (0 : ℂ) 1) K := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change e '' (e.source ∩ Metric.closedBall (0 : ℂ) 1) = e.target ∩ K
    rw [inter_eq_right.mpr hsrc, inter_eq_right.mpr htarget]
  have h := himage.interior.image_eq
  change e '' (e.source ∩ interior (Metric.closedBall (0 : ℂ) 1)) =
    e.target ∩ interior K at h
  rw [inter_eq_right.mpr (interior_subset.trans hsrc),
    inter_eq_right.mpr (interior_subset.trans htarget),
    interior_closedBall (0 : ℂ) one_ne_zero] at h
  exact h

private theorem seam_uniqueMDiff : UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 (1 / 4)) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) (1 / 4)))
  have hinside : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ interior (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 (1 / 4)).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(1 / 8 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((1 / 8 : ℂ) * Complex.I).im
    norm_num
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    norm_num [norm_mul, norm_div]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Rank at the original seam point gives an open regular neighborhood, also
on the outside of the selected patch. -/
private theorem exists_open_original_rank_neighborhood
    {Q : ℂ → M} (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (Metric.ball 0 1))
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ N : Set ℂ, IsOpen N ∧ a ∈ N ∧ N ⊆ Metric.ball (0 : ℂ) 1 ∧
      ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let F : S → M := fun z => Q z
  let aS : S := ⟨a, ha⟩
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQ.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F aS) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) aS : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF aS hDF
  let T : Set S := {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hT : IsOpen T := IsOpen.isImmersionAt
  refine ⟨Subtype.val '' T, Metric.isOpen_ball.isOpenMap_subtype_val T hT,
    ⟨aS, hImm, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩
    have hd := hz.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
    rw [DifferentialGeometry.mfderiv_restrict_open] at hd
    exact hd

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem seam_mfderivWithin_congr {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

/-- One scaled Cayley chart places the literal corrected inner sheet and the
unchanged original outer sheet in a common regular half-disk. The same selected
phase point and disk diffeomorphism are retained. Only a genuine preserved
radial sector is used; the correction annulus is never asserted to be minimal.
-/
theorem exists_regular_replacement_seam_chart
    (u d qAlt : C(closedDisk, M))
    (hU : DiskSmoothInterior (E := E) u)
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (s₀ t₀ : ℝ)
    (hiU : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (diskExtension u) (e (diskBoundary (s₀ : loopCircle)))))
    (D : ℂ ≃ₘ[ℝ] ℂ)
    (hDclosed : D '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall (0 : ℂ) 1)
    (hDopen : D '' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1)
    (hDpoint : D (diskBoundary (s₀ : loopCircle) : ℂ) =
      (diskBoundary (t₀ : loopCircle) : ℂ))
    (Q : ℂ → M) (hQ : SmoothDiskExtension (E := E) qAlt Q)
    {VAlt : Set ℂ} (hVAlt : IsOpen VAlt)
    (hpAlt : (diskBoundary (t₀ : loopCircle) : ℂ) ∈ VAlt)
    (hQV : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q VAlt)
    (hiQ : ∀ z ∈ VAlt ∩ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {η : ℝ} (hη : 0 < η)
    (hsector : ∀ t : ℝ, |t - s₀| < η → ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      diskExtension d (r • (diskBoundary (t : loopCircle) : ℂ)) =
        diskExtension qAlt (D (r • (diskBoundary (t : loopCircle) : ℂ)))) :
    ∃ α : ℝ, 0 < α ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        (∀ z : ℂ, χ z = e (Complex.diskBoundaryChart
          (diskBoundary (s₀ : loopCircle) : ℂ) (by simp [diskBoundary]) (α • z))) ∧
        χ 0 = e (diskBoundary (s₀ : loopCircle)) ∧
        Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
        χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
        let ψAlt : ℂ → ℂ := D ∘ e.symm ∘ χ
        ψAlt 0 = (diskBoundary (t₀ : loopCircle) : ℂ) ∧
        MapsTo χ (closedHalfDisk 0 (1 / 4)) (e '' Metric.closedBall (0 : ℂ) 1) ∧
        (∀ z ∈ closedHalfDisk 0 (1 / 4),
          χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1)) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
          (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 (1 / 4)) ∧
        (∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
            (closedHalfDisk 0 (1 / 4)) z)) ∧
        (∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
            (closedHalfDisk 0 (1 / 4)) z)) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψAlt (openHalfDisk 0 (1 / 4)) ∧
        MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Function.Bijective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψAlt z)) ∧
        EqOn (diskExtension d ∘ e.symm ∘ χ)
          (diskExtension qAlt ∘ ψAlt) (openHalfDisk 0 (1 / 4)) ∧
        EqOn (diskExtension d ∘ e.symm ∘ χ) (Q ∘ ψAlt) (closedHalfDisk 0 (1 / 4)) ∧
        MapsTo ψAlt (closedHalfDisk 0 (1 / 4)) (VAlt ∩ Metric.closedBall (0 : ℂ) 1) := by
  let p : ℂ := diskBoundary (s₀ : loopCircle)
  have hp : ‖p‖ = 1 := Circle.norm_coe _
  have hpD : p ∈ Metric.closedBall (0 : ℂ) 1 := (diskBoundary (s₀ : loopCircle)).property
  obtain ⟨N, hN, hepN, hNin, hNrank⟩ := exists_open_original_rank_neighborhood hU
    (hinside ⟨p, hpD, rfl⟩) hiU
  obtain ⟨V, hV, hpV, hpolar⟩ := exists_neighborhood_in_radial_sector s₀ hη
  have hkeep : EqOn (diskExtension d) (diskExtension qAlt ∘ D)
      (V ∩ Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    obtain ⟨t, ht, r, hr, rfl⟩ := hpolar z hz
    exact hsector t ht r hr
  let c := Complex.diskBoundaryChart p hp
  let κ := c.trans e
  have hc0 : (0 : ℂ) ∈ c.source := by
    change (0 : ℂ) ≠ -Complex.I
    exact (neg_ne_zero.mpr Complex.I_ne_zero).symm
  have hκ0 : (0 : ℂ) ∈ κ.source := by
    refine ⟨hc0, ?_⟩
    change c 0 ∈ e.source
    rw [Complex.diskBoundaryChart_zero]
    exact hsrc hpD
  have hcc : ContinuousAt c 0 :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hκc : ContinuousAt κ 0 :=
    κ.contMDiffOn_toFun.continuousOn.continuousAt (κ.open_source.mem_nhds hκ0)
  have hDc : ContinuousAt (D ∘ c) 0 := D.continuous.continuousAt.comp hcc
  have hκN : κ 0 ∈ N := by
    change e (c 0) ∈ N
    rw [Complex.diskBoundaryChart_zero]
    exact hepN
  have hcV : c 0 ∈ V := by rw [Complex.diskBoundaryChart_zero]; exact hpV
  have hDcV : (D ∘ c) 0 ∈ VAlt := by
    change D (c 0) ∈ VAlt
    rw [Complex.diskBoundaryChart_zero, hDpoint]
    exact hpAlt
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ κ.source ∧ κ z ∈ N ∧
      c z ∈ V ∧ D (c z) ∈ VAlt := by
    filter_upwards [κ.open_source.mem_nhds hκ0, hκc (hN.mem_nhds hκN),
      hcc (hV.mem_nhds hcV), hDc (hVAlt.mem_nhds hDcV)] with z hz hNz hVz hAltz
    exact ⟨hz, hNz, hVz, hAltz⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let α : ℝ := ε / 4
  have hα : 0 < α := by dsimp only [α]; positivity
  let A : ℂ ≃ₘ[ℝ] ℂ :=
    (LinearEquiv.smulOfNeZero ℝ ℂ α hα.ne').toContinuousLinearEquiv.toDiffeomorph
  let χ := (A.toPartialDiffeomorph.trans c).trans e
  let ψ := (χ.trans e.symm).trans D.toPartialDiffeomorph
  let χr := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  have hbuffer {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      α • z ∈ κ.source ∧ e (c (α • z)) ∈ N ∧
      c (α • z) ∈ V ∧ D (c (α • z)) ∈ VAlt := by
    apply hεsub
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hα.le]
    have hzNorm : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [α]
    nlinarith
  have hbar {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      conj z ∈ Metric.closedBall (0 : ℂ) 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
  have hχsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ χ.source :=
    ⟨⟨mem_univ _, (hbuffer hz).1.1⟩, (hbuffer hz).1.2⟩
  have hχrsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ χr.source :=
    ⟨mem_univ _, hχsource (hbar hz)⟩
  have hψsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ ψ.source :=
    ⟨⟨hχsource hz, e.map_source' (hbuffer hz).1.2⟩, mem_univ _⟩
  have hinverse {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      e.symm (χ z) = c (α • z) := e.toPartialEquiv.left_inv (hbuffer hz).1.2
  have hψvalue {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      ψ z = D (c (α • z)) := congrArg D (hinverse hz)
  have hHtwo : closedHalfDisk 0 (1 / 4) ⊆ Metric.closedBall (0 : ℂ) 2 :=
    fun _ hz => Metric.closedBall_subset_closedBall (by norm_num) hz.2
  have hHO : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hcDisk {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
      c (α • z) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (Complex.norm_diskBoundaryChart_le_one_iff p hp (hbuffer (hHtwo hz)).1.1).mpr
    simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using mul_nonneg hα.le (show 0 ≤ z.im from hz.1)
  have hcOpen {z : ℂ} (hz : z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ)) :
      c (α • z) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    apply (Complex.norm_diskBoundaryChart_lt_one_iff p hp (hbuffer (hHtwo (hHO hz))).1.1).mpr
    simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using mul_pos hα (show 0 < z.im from hz.1)
  have hψmaps : MapsTo ψ (closedHalfDisk 0 (1 / 4))
      (VAlt ∩ Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [hψvalue (hHtwo hz)]
    exact ⟨(hbuffer (hHtwo hz)).2.2.2, hDclosed ▸ ⟨c (α • z), hcDisk hz, rfl⟩⟩
  have hinner : MapsTo χ (closedHalfDisk 0 (1 / 4))
      (e '' Metric.closedBall (0 : ℂ) 1) := fun z hz => ⟨c (α • z), hcDisk hz, rfl⟩
  have houter : ∀ z ∈ closedHalfDisk 0 (1 / 4),
      χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1) := by
    intro z hz hzinside
    rw [← seam_chart_image_ball_eq_interior e hsrc] at hzinside
    obtain ⟨w, hw, hweq⟩ := hzinside
    have hcw : w = c (α • conj z) :=
      e.injOn (hsrc (Metric.ball_subset_closedBall hw))
        (hbuffer (hbar (hHtwo hz))).1.2 hweq
    have hcnorm : ‖c (α • conj z)‖ < 1 := by
      rw [← hcw]
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    have him := (Complex.norm_diskBoundaryChart_lt_one_iff p hp
      (hbuffer (hbar (hHtwo hz))).1.1).mp hcnorm
    change 0 < (α • conj z).im at him
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.conj_im] at him
    have hzpos : 0 ≤ z.im := hz.1
    nlinarith
  have heqAltClosed : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (diskExtension qAlt ∘ ψ) (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    change diskExtension d (e.symm (χ z)) = diskExtension qAlt (ψ z)
    rw [hinverse (hHtwo hz), hψvalue (hHtwo hz)]
    exact hkeep ⟨(hbuffer (hHtwo hz)).2.2.1, hcDisk hz⟩
  have heqQ : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (Q ∘ ψ) (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    refine (heqAltClosed hz).trans ?_
    exact (diskExtension_coe qAlt ⟨ψ z, (hψmaps hz).2⟩).trans (hQ.1 _).symm
  have hψsmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ (closedHalfDisk 0 (1 / 4)) :=
    ψ.contMDiffOn_toFun.mono (fun _ hz => hψsource (hHtwo hz))
  have hinnerSmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 (1 / 4)) :=
    (hQV.comp hψsmooth (fun _ hz => (hψmaps hz).1)).congr heqQ
  have hinnerRank : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    have hD := seam_mfderivWithin_congr (E := E) heqQ hz
    have hdQ := (hQV.contMDiffAt (hVAlt.mem_nhds (hψmaps hz).1)).mdifferentiableAt (by simp)
    have hdψ := ψ.mdifferentiableAt (by simp) (hψsource (hHtwo hz))
    have hiComp : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (Q ∘ ψ) (closedHalfDisk 0 (1 / 4)) z) := by
      rw [mfderivWithin_eq_mfderiv (seam_uniqueMDiff z hz) (hdQ.comp z hdψ),
        mfderiv_comp z hdQ hdψ]
      exact (hiQ _ (hψmaps hz)).comp
        ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsource (hHtwo hz))).mfderivToContinuousLinearEquiv
          (by simp)).injective
    intro v w hvw
    apply hiComp
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hD).symm.trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hD))
  have houterRank : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    change Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (diskExtension u ∘ χr) (closedHalfDisk 0 (1 / 4)) z)
    have hχrN : χr z ∈ N := (hbuffer (hbar (hHtwo hz))).2.1
    have hdU := (hU.contMDiffAt (Metric.isOpen_ball.mem_nhds (hNin hχrN))).mdifferentiableAt
      (by simp)
    have hdχr := χr.mdifferentiableAt (by simp) (hχrsource (hHtwo hz))
    rw [mfderivWithin_eq_mfderiv (seam_uniqueMDiff z hz) (hdU.comp z hdχr),
      mfderiv_comp z hdU hdχr]
    exact (hNrank _ hχrN).comp
      ((χr.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hχrsource (hHtwo hz))).mfderivToContinuousLinearEquiv
        (by simp)).injective
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 2 := by simp
  refine ⟨α, hα, χ, fun _ => rfl, ?_, ?_, ?_, ?_, hinner, houter,
    hinnerSmooth.of_le (by simp), hinnerRank, houterRank, hψsmooth.mono hHO,
    ?_, ?_, heqAltClosed.mono hHO, heqQ, hψmaps⟩
  · change e (c (α • (0 : ℂ))) = e p
    rw [smul_zero, Complex.diskBoundaryChart_zero]
  · intro z hz
    exact hχsource (Metric.closedBall_subset_closedBall (by norm_num) hz)
  · rintro _ ⟨z, hz, rfl⟩
    exact hNin (hbuffer (Metric.closedBall_subset_closedBall (by norm_num) hz)).2.1
  · change ψ 0 = (diskBoundary (t₀ : loopCircle) : ℂ)
    rw [hψvalue hzero, smul_zero, Complex.diskBoundaryChart_zero]
    exact hDpoint
  · intro z hz
    change ψ z ∈ Metric.ball (0 : ℂ) 1
    rw [hψvalue (hHtwo (hHO hz))]
    exact hDopen ▸ ⟨c (α • z), hcOpen hz, rfl⟩
  · intro z hz
    exact ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsource (hHtwo (hHO hz)))).mfderivToContinuousLinearEquiv
      (by simp)).bijective

end DifferentialGeometry.Geometry
