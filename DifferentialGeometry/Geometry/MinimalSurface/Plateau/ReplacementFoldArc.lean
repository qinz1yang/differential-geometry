import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ReplacementFold
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

private def arcSourceDiffeomorph (x : ℝ) : ℂ ≃ₘ[ℝ] ℂ where
  toEquiv :=
    { toFun := fun z => (x : ℂ) + (1 / 8 : ℝ) • z
      invFun := fun z => (8 : ℝ) • (z - (x : ℂ))
      left_inv := fun z => by
        change (8 : ℝ) • ((x : ℂ) + (1 / 8 : ℝ) • z - (x : ℂ)) = z
        rw [add_sub_cancel_left, smul_smul]
        norm_num
      right_inv := fun z => by
        change (x : ℂ) + (1 / 8 : ℝ) • ((8 : ℝ) • (z - (x : ℂ))) = z
        rw [smul_smul, show (1 / 8 : ℝ) * 8 = 1 by norm_num, one_smul,
          add_comm (x : ℂ), sub_add_cancel] }
  contMDiff_toFun := (contDiff_const.add (contDiff_const_smul (1 / 8 : ℝ))).contMDiff
  contMDiff_invFun := (contDiff_const_smul (8 : ℝ)).contMDiff.comp
    (contMDiff_id.sub contMDiff_const)

private theorem arc_uniqueMDiff : UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 (1 / 4)) := by
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

private theorem arcSource_maps_closed (x : ℝ) (hx : |x| < 1 / 16) :
    MapsTo (arcSourceDiffeomorph x) (closedHalfDisk 0 (1 / 4))
      (closedHalfDisk 0 (1 / 4)) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change 0 ≤ ((x : ℂ) + (1 / 8 : ℝ) • z).im
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg (by norm_num) (show 0 ≤ z.im from hz.1)
  · rw [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right]
    change ‖(x : ℂ) + (1 / 8 : ℝ) • z‖ ≤ 1 / 4
    have hnorm := norm_add_le (x : ℂ) ((1 / 8 : ℝ) • z)
    have hzNorm : ‖z‖ ≤ (1 / 4 : ℝ) := by
      simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right] using hz.2
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at hnorm
    linarith

private theorem arcSource_maps_open (x : ℝ) (hx : |x| < 1 / 16) :
    MapsTo (arcSourceDiffeomorph x) (openHalfDisk 0 (1 / 4))
      (openHalfDisk 0 (1 / 4)) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change 0 < ((x : ℂ) + (1 / 8 : ℝ) • z).im
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (by norm_num) (show 0 < z.im from hz.1)
  · rw [Metric.mem_ball, Complex.ofReal_zero, dist_zero_right]
    change ‖(x : ℂ) + (1 / 8 : ℝ) • z‖ < 1 / 4
    have hnorm := norm_add_le (x : ℂ) ((1 / 8 : ℝ) • z)
    have hzNorm : ‖z‖ < (1 / 4 : ℝ) := by
      simpa only [Metric.mem_ball, Complex.ofReal_zero, dist_zero_right] using hz.2
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at hnorm
    linarith

private theorem arcSource_maps_unit (x : ℝ) (hx : |x| < 1 / 16) :
    MapsTo (arcSourceDiffeomorph x) (Metric.closedBall (0 : ℂ) 1)
      (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖(x : ℂ) + (1 / 8 : ℝ) • z‖ ≤ 1
  have hnorm := norm_add_le (x : ℂ) ((1 / 8 : ℝ) • z)
  have hzNorm : ‖z‖ ≤ (1 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at hnorm
  linarith

private theorem arcSource_conj (x : ℝ) (z : ℂ) :
    arcSourceDiffeomorph x (conj z) = conj (arcSourceDiffeomorph x z) := by
  change (x : ℂ) + (1 / 8 : ℝ) • conj z = conj ((x : ℂ) + (1 / 8 : ℝ) • z)
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
private def linearConormal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : M) (L : ℂ →L[ℝ] E) : E :=
  (Real.sqrt (g.inner q (L 1) (L 1)) * tangentTwoJacobian g (x := q) (L 1) (L Complex.I))⁻¹ •
    (g.inner q (L 1) (L 1) • L Complex.I - g.inner q (L 1) (L Complex.I) • L 1)

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem linearConormal_smul_pos (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : M) (L : ℂ →L[ℝ] E) {c : ℝ} (hc : 0 < c) :
    linearConormal g q (c • L) = linearConormal g q L := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner q
  let J (v w : E) : ℝ := Real.sqrt (B v v * B w w - B v w ^ 2)
  have hg (v w : E) : B (c • v) (c • w) = c ^ 2 * B v w := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hJ : J (c • L 1) (c • L Complex.I) =
      c ^ 2 * J (L 1) (L Complex.I) := by
    change Real.sqrt (B (c • L 1) (c • L 1) *
        B (c • L Complex.I) (c • L Complex.I) - B (c • L 1) (c • L Complex.I) ^ 2) =
      c ^ 2 * Real.sqrt (B (L 1) (L 1) * B (L Complex.I) (L Complex.I) -
        B (L 1) (L Complex.I) ^ 2)
    rw [hg, hg, hg]
    have hscale : (c ^ 2 * B (L 1) (L 1)) *
        (c ^ 2 * B (L Complex.I) (L Complex.I)) -
        (c ^ 2 * B (L 1) (L Complex.I)) ^ 2 =
        (c ^ 2) ^ 2 * (B (L 1) (L 1) * B (L Complex.I) (L Complex.I) -
          B (L 1) (L Complex.I) ^ 2) := by ring
    rw [hscale, Real.sqrt_mul (sq_nonneg (c ^ 2)), Real.sqrt_sq (sq_nonneg c)]
  have hnum : (c ^ 2 * B (L 1) (L 1)) • (c • L Complex.I) -
      (c ^ 2 * B (L 1) (L Complex.I)) • (c • L 1) =
      c ^ 3 • (B (L 1) (L 1) • L Complex.I -
        B (L 1) (L Complex.I) • L 1) := by
    simp only [smul_smul, smul_sub]
    congr 1 <;> congr 1 <;> ring
  change (Real.sqrt (B ((c • L) 1) ((c • L) 1)) *
      J ((c • L) 1) ((c • L) Complex.I))⁻¹ •
      (B ((c • L) 1) ((c • L) 1) • (c • L) Complex.I -
        B ((c • L) 1) ((c • L) Complex.I) • (c • L) 1) =
    (Real.sqrt (B (L 1) (L 1)) * J (L 1) (L Complex.I))⁻¹ •
      (B (L 1) (L 1) • L Complex.I - B (L 1) (L Complex.I) • L 1)
  simp only [smul_apply]
  rw [hg, hg, hJ, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, hnum]
  have hden : (c * Real.sqrt (B (L 1) (L 1))) *
      (c ^ 2 * J (L 1) (L Complex.I)) =
      c ^ 3 * (Real.sqrt (B (L 1) (L 1)) *
        J (L 1) (L Complex.I)) := by ring
  rw [hden, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 3 hc.ne'), mul_one]

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem arcSource_mfderiv_apply (x : ℝ) (z v : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (arcSourceDiffeomorph x) z v : ℂ) = (1 / 8 : ℝ) • v := by
  have hd : HasFDerivAt (arcSourceDiffeomorph x)
      ((1 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).const_smul (1 / 8 : ℝ)).const_add (x : ℂ)
  rw [mfderiv_eq_fderiv, hd.fderiv]
  rfl

omit [FiniteDimensional ℝ E] [T3Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem arc_mfderivWithin_comp {F : ℂ → M}
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk 0 (1 / 4)))
    {x : ℝ} (hx : |x| < 1 / 16) {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (F ∘ arcSourceDiffeomorph x) (closedHalfDisk 0 (1 / 4)) z) =
    (1 / 8 : ℝ) • (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      F (closedHalfDisk 0 (1 / 4)) (arcSourceDiffeomorph x z)) := by
  have hdF := hF.mdifferentiableOn (by simp) _ (arcSource_maps_closed x hx hz)
  have hdT := (arcSourceDiffeomorph x).contMDiff.mdifferentiableAt (by simp) (x := z)
  rw [mfderivWithin_comp z hdF hdT.mdifferentiableWithinAt (arcSource_maps_closed x hx)
    (arc_uniqueMDiff z hz), mfderivWithin_eq_mfderiv (arc_uniqueMDiff z hz) hdT]
  ext v
  let A : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F
    (closedHalfDisk 0 (1 / 4)) (arcSourceDiffeomorph x z)
  change A (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (arcSourceDiffeomorph x) z v) =
    (1 / 8 : ℝ) • A v
  rw [arcSource_mfderiv_apply]
  exact A.map_smul (1 / 8 : ℝ) v

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem arc_inwardConormal_comp (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {F : ℂ → M}
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk 0 (1 / 4)))
    {x : ℝ} (hx : |x| < 1 / 16) {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
    (inwardConormalWithin g (F ∘ arcSourceDiffeomorph x) (closedHalfDisk 0 (1 / 4)) z : E) =
      (inwardConormalWithin g F (closedHalfDisk 0 (1 / 4)) (arcSourceDiffeomorph x z) : E) := by
  change linearConormal g (F (arcSourceDiffeomorph x z))
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (F ∘ arcSourceDiffeomorph x) (closedHalfDisk 0 (1 / 4)) z) =
    linearConormal g (F (arcSourceDiffeomorph x z))
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        F (closedHalfDisk 0 (1 / 4)) (arcSourceDiffeomorph x z))
  rw [arc_mfderivWithin_comp hF hx hz]
  exact linearConormal_smul_pos g _ _ (by norm_num)

omit [FiniteDimensional ℝ E] [T3Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem arc_rank_comp {F : ℂ → M}
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk 0 (1 / 4)))
    (hiF : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk 0 (1 / 4)) z))
    {x : ℝ} (hx : |x| < 1 / 16) {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
    Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (F ∘ arcSourceDiffeomorph x) (closedHalfDisk 0 (1 / 4)) z) := by
  have hD := arc_mfderivWithin_comp hF hx hz
  intro v w hvw
  apply hiF _ (arcSource_maps_closed x hx hz)
  have heq := (congrArg (fun A : ℂ →L[ℝ] E => A v) hD).symm.trans
    (hvw.trans (congrArg (fun A : ℂ →L[ℝ] E => A w) hD))
  let A : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F
    (closedHalfDisk 0 (1 / 4)) (arcSourceDiffeomorph x z)
  change (1 / 8 : ℝ) • A v = (1 / 8 : ℝ) • A w at heq
  change A v = A w
  have h := congrArg (fun y : E => (8 : ℝ) • y) heq
  simpa only [smul_smul,
    show (8 : ℝ) * (1 / 8) = 1 by norm_num, one_smul] using h

private theorem arc_real_mem_half {x : ℝ} (hx : |x| < 1 / 16) :
    (x : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
  refine ⟨(show 0 ≤ (x : ℂ).im from le_rfl), ?_⟩
  rw [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right,
    Complex.norm_real, Real.norm_eq_abs]
  linarith

private theorem arc_chart_image_ball_eq_interior
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
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

/-- Recenter the same regular replacement fold at every real point in a
smaller fixed interval. No new filling, phase, disk diffeomorphism, or minimizing
disk is chosen. Positive source dilation leaves the actual unit conormal
unchanged, so the center-only shortening obstruction gives cancellation along
this entire arc in the original chart. -/
theorem IsMorreyDisk.sourceChart_replacement_conormal_sum_eq_zero_on_arc
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (d qAlt : C(closedDisk, M)) {L C : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hdLip : ∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w)
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (e z))
    (harea : riemannianDiskArea g d =
      riemannianArea g (diskExtension u) (e '' Metric.closedBall (0 : ℂ) 1))
    {W : Set M} (huW : Set.range u ⊆ W) (hdW : Set.range d ⊆ W)
    (hInterior : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskExtension u z ∈ interior W)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinner : MapsTo χ (closedHalfDisk 0 (1 / 4)) (e '' Metric.closedBall (0 : ℂ) 1))
    (houter : ∀ z ∈ closedHalfDisk 0 (1 / 4),
      χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1))
    (hFinner : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 (1 / 4)))
    (hiInner : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 (1 / 4)) z))
    (hiOuter : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 (1 / 4)) z))
    (hAltSmooth : DiskSmoothInterior (E := E) qAlt)
    (hAltConf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension qAlt) z)
    (hAltHarm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension qAlt) z = 0)
    (ψAlt : ℂ → ℂ)
    (hψAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψAlt (openHalfDisk 0 (1 / 4)))
    (hmapsAlt : MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1))
    (hbijAlt : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψAlt z))
    (heqAlt : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (diskExtension qAlt ∘ ψAlt) (openHalfDisk 0 (1 / 4))) :
    ∀ x : ℝ, |x| < 1 / 16 →
      diskExtension d (e.symm (χ (x : ℂ))) = diskExtension u (χ (conj (x : ℂ))) ∧
      inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 (1 / 4)) (x : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) (x : ℂ))
          ((diskExtension d ∘ e.symm ∘ χ) (x : ℂ))
          (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj)
            (closedHalfDisk 0 (1 / 4)) (x : ℂ)) = 0 := by
  let χr := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  have hHunit : closedHalfDisk 0 (1 / 4) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun _ hz => Metric.closedBall_subset_closedBall (by norm_num) hz.2
  have hbarunit {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
      conj z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hHunit hz
  have hχrsource : closedHalfDisk 0 (1 / 4) ⊆ χr.source :=
    fun _ hz => ⟨mem_univ _, hχsrc (hbarunit hz)⟩
  have hχrmaps : MapsTo χr (closedHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => hχinside ⟨conj z, hbarunit hz, rfl⟩
  have hFouter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension u ∘ χ ∘ conj) (closedHalfDisk 0 (1 / 4)) :=
    (hu.smoothInterior.comp (χr.contMDiffOn_toFun.mono hχrsource) hχrmaps).of_le (by simp)
  intro x hx
  let T := arcSourceDiffeomorph x
  let χx := T.toPartialDiffeomorph.trans χ
  have hTclosed : MapsTo T (closedHalfDisk 0 (1 / 4)) (closedHalfDisk 0 (1 / 4)) :=
    arcSource_maps_closed x hx
  have hTopen : MapsTo T (openHalfDisk 0 (1 / 4)) (openHalfDisk 0 (1 / 4)) :=
    arcSource_maps_open x hx
  have hχxsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χx.source :=
    fun _ hz => ⟨mem_univ _, hχsrc (arcSource_maps_unit x hx hz)⟩
  have hχxinside : χx '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hχinside ⟨T z, arcSource_maps_unit x hx hz, rfl⟩
  have hinnerx : MapsTo χx (closedHalfDisk 0 (1 / 4)) (e '' Metric.closedBall (0 : ℂ) 1) :=
    fun _ hz => hinner (hTclosed hz)
  have houterx : ∀ z ∈ closedHalfDisk 0 (1 / 4),
      χx (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    change χ (T (conj z)) ∉ _
    rw [arcSource_conj]
    exact houter _ (hTclosed hz)
  have hFinnerx : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension d ∘ e.symm ∘ χx) (closedHalfDisk 0 (1 / 4)) :=
    hFinner.comp (T.contMDiff.contMDiffOn.of_le (by simp)) hTclosed
  have hFoutereq : (diskExtension u ∘ χx ∘ conj) = (diskExtension u ∘ χ ∘ conj) ∘ T := by
    funext z
    change diskExtension u (χ (T (conj z))) = diskExtension u (χ (conj (T z)))
    rw [arcSource_conj]
  have hiInnerx : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χx)
        (closedHalfDisk 0 (1 / 4)) z) :=
    fun _ hz => arc_rank_comp hFinner hiInner hx hz
  have hiOuterx : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χx ∘ conj)
        (closedHalfDisk 0 (1 / 4)) z) := by
    rw [hFoutereq]
    exact fun _ hz => arc_rank_comp hFouter hiOuter hx hz
  have hψx : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ψAlt ∘ T) (openHalfDisk 0 (1 / 4)) :=
    hψAlt.comp T.contMDiff.contMDiffOn hTopen
  have hmapsx : MapsTo (ψAlt ∘ T) (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) :=
    fun _ hz => hmapsAlt (hTopen hz)
  have hbijx : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (ψAlt ∘ T) z) := by
    intro z hz
    have hdψ := (hψAlt.contMDiffAt ((openHalfDisk 0 (1 / 4)).isOpen.mem_nhds
      (hTopen hz))).mdifferentiableAt (by simp)
    have hdT := T.contMDiff.mdifferentiableAt (by simp) (x := z)
    rw [mfderiv_comp z hdψ hdT]
    exact (hbijAlt _ (hTopen hz)).comp (T.mfderivToContinuousLinearEquiv (by simp) z).bijective
  have heqx : EqOn (diskExtension d ∘ e.symm ∘ χx)
      (diskExtension qAlt ∘ (ψAlt ∘ T)) (openHalfDisk 0 (1 / 4)) :=
    fun _ hz => heqAlt (hTopen hz)
  have hpoint : (x : ℂ) ∈ closedHalfDisk 0 (1 / 4) := arc_real_mem_half hx
  obtain ⟨w, hw, hweq⟩ := hinner hpoint
  have hwnorm : ‖w‖ = 1 := by
    have hwNorm : ‖w‖ ≤ (1 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    apply le_antisymm hwNorm
    apply le_of_not_gt
    intro hlt
    have hc : χ (x : ℂ) ∈ interior (e '' Metric.closedBall (0 : ℂ) 1) := by
      rw [← arc_chart_image_ball_eq_interior e hsrc]
      exact ⟨w, by simpa only [Metric.mem_ball, dist_zero_right] using hlt, hweq⟩
    have hnot := houter (x : ℂ) hpoint
    rw [Complex.conj_ofReal] at hnot
    exact hnot hc
  have hcenterEq : diskExtension d (e.symm (χ (x : ℂ))) = diskExtension u (χ (x : ℂ)) := by
    rw [← hweq]
    exact (congrArg (diskExtension d) (e.toPartialEquiv.left_inv (hsrc hw))).trans
      (hboundary w (by simpa only [Metric.mem_sphere, dist_zero_right] using hwnorm))
  have hpWx : diskExtension d (e.symm (χx 0)) ∈ interior W := by
    change diskExtension d (e.symm (χ ((x : ℂ) + (1 / 8 : ℝ) • (0 : ℂ)))) ∈ interior W
    rw [smul_zero, add_zero, hcenterEq]
    exact hInterior _ (hχinside ⟨(x : ℂ), hHunit hpoint, rfl⟩)
  have hcancel := hu.sourceChart_replacement_conormal_sum_eq_zero d qAlt huLip hdLip e
    hsrc hinside hboundary harea huW hdW χx hχxsrc hχxinside
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    hinnerx houterx hFinnerx hiInnerx hiOuterx hAltSmooth hAltConf hAltHarm
    (ψAlt ∘ T) hψx hmapsx hbijx heqx hpWx
  change (fun a b : E => a + b)
    (inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χx)
      (closedHalfDisk 0 (1 / 4)) 0)
    (inwardConormalWithin g (diskExtension u ∘ χx ∘ conj)
      (closedHalfDisk 0 (1 / 4)) 0) = 0 at hcancel
  rw [hFoutereq] at hcancel
  have hzero : (0 : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    refine ⟨(show 0 ≤ (0 : ℂ).im from le_rfl), ?_⟩
    norm_num [Metric.mem_closedBall]
  change (fun a b : E => a + b)
    (inwardConormalWithin g ((diskExtension d ∘ e.symm ∘ χ) ∘ T)
      (closedHalfDisk 0 (1 / 4)) 0) _ = 0 at hcancel
  rw [arc_inwardConormal_comp g hFinner hx hzero,
    arc_inwardConormal_comp g hFouter hx hzero] at hcancel
  refine ⟨?_, ?_⟩
  · simpa only [Complex.conj_ofReal] using hcenterEq
  · change (fun a b : E => a + b)
      (inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 (1 / 4)) (x : ℂ))
      (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 (1 / 4)) (x : ℂ)) = 0
    have hTzero : T 0 = (x : ℂ) := by
      change (x : ℂ) + (1 / 8 : ℝ) • (0 : ℂ) = (x : ℂ)
      rw [smul_zero, add_zero]
    change (fun a b : E => a + b)
      (inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 (1 / 4)) (T 0))
      (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 (1 / 4)) (T 0)) = 0 at hcancel
    rw [hTzero] at hcancel
    exact hcancel

end DifferentialGeometry.Geometry
