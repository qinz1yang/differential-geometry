import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitArea
import DifferentialGeometry.Topology.Planar.BranchSlitChart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitRegularBuffer
import DifferentialGeometry.Topology.Planar.SlitSeamCharts
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ChartFoldShortening
import DifferentialGeometry.Geometry.MinimalSurface.Variation.TransverseConormal
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Planar.SlitRegluing
open DifferentialGeometry.Topology.Planar.SlitSeamCharts
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [T3Space M] in
/-- Algebraic identification of the actual pasted disk on its original source
patch. The filling and replacement identities are exactly the conclusions of
`exists_actual_branch_slit_filling`; no continuity of the raw slit map is used. -/
private theorem slit_pasted_value
    (u d v : C(closedDisk, M)) (e S : OpenPartialHomeomorph ℂ ℂ)
    {R : ℝ} (hR : 0 < R)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (heBall : Metric.closedBall (0 : ℂ) R ⊆ e.target)
    (hSnorm : ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      ‖S w‖ = ‖w‖ ∧ ‖S.symm w‖ = ‖w‖ ∧
      S.symm (S w) = w ∧ S (S.symm w) = w)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hχ : ∀ z, χ z = e.symm ((R : ℂ) * z))
    (hχinv : ∀ z, χ.symm z = e z / (R : ℂ))
    (hd : ∀ z : closedDisk, d z = diskExtension u
      (e.symm (S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z))))))
    (hv : ∀ z : closedDisk, (z : ℂ) ∈ χ '' Metric.closedBall (0 : ℂ) 1 →
      v z = diskExtension d (χ.symm z)) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      diskExtension v (e.symm (S w)) =
        diskExtension u (e.symm (S (scaledSlitMap (R / 4) w))) := by
  intro w hw
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hSw : S w ∈ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, (hSnorm w hw).1] using hw
  have hSwTarget := heBall hSw
  have hzInside := heSource (e.map_target hSwTarget)
  let z : closedDisk := ⟨e.symm (S w), Metric.ball_subset_closedBall hzInside⟩
  have hs : S w / (R : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_div, hnormR]
    rw [div_le_iff₀ hR, one_mul]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hSw
  have hscale : (R : ℂ) * (S w / (R : ℂ)) = S w := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hRc]
  have hzPatch : (z : ℂ) ∈ χ '' Metric.closedBall (0 : ℂ) 1 := by
    refine ⟨S w / (R : ℂ), hs, ?_⟩
    rw [hχ, hscale]
  have hχiz : χ.symm z = S w / (R : ℂ) := by
    rw [hχinv]
    change e (e.symm (S w)) / (R : ℂ) = S w / (R : ℂ)
    rw [e.right_inv hSwTarget]
  calc
    diskExtension v (e.symm (S w)) = v z := diskExtension_coe v z
    _ = diskExtension d (χ.symm z) := hv z hzPatch
    _ = diskExtension d (S w / (R : ℂ)) := congrArg (diskExtension d) hχiz
    _ = d ⟨S w / (R : ℂ), hs⟩ := diskExtension_coe d ⟨_, hs⟩
    _ = diskExtension u (e.symm (S (scaledSlitMap (R / 4)
        (S.symm ((R : ℂ) * (S w / (R : ℂ))))))) := hd _
    _ = diskExtension u (e.symm (S (scaledSlitMap (R / 4) w))) := by
      rw [hscale, (hSnorm w hw).2.2.1]

omit [T3Space M] in
/-- Transport the finite-map closed-cell equations to the actual disk cut out
of the globally pasted replacement. The affine equations will be supplied by
the single literal `SlitSeamCharts` construction. -/
private theorem slit_pasted_halfdisk_identities
    (u v : C(closedDisk, M)) (e S : OpenPartialHomeomorph ℂ ℂ)
    {R : ℝ} (T Bplus Bminus : ℂ → ℂ)
    (hT : MapsTo T (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) R))
    (hV : ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      diskExtension v (e.symm (S w)) =
        diskExtension u (e.symm (S (scaledSlitMap (R / 4) w))))
    (hplus : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ w.im →
      diskExtension u (e.symm (S (scaledSlitMap (R / 4) (T w)))) =
        diskExtension u (e.symm (S (Bplus w))))
    (hminus : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ w.im →
      diskExtension u (e.symm (S (scaledSlitMap (R / 4) (T (conj w))))) =
        diskExtension u (e.symm (S (Bminus w))))
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχ : ∀ w, χ w = e.symm (S (T w))) :
    let d := diskThroughSourceChart v χ hχsrc
    EqOn (diskExtension d) (fun w => diskExtension u (e.symm (S (Bplus w))))
      (closedHalfDisk 0 (1 / 4)) ∧
    EqOn (diskExtension d ∘ conj) (fun w => diskExtension u (e.symm (S (Bminus w))))
      (closedHalfDisk 0 (1 / 4)) := by
  let d := diskThroughSourceChart v χ hχsrc
  have hball {w : ℂ} (hw : w ∈ closedHalfDisk 0 (1 / 4)) :
      w ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.closedBall_subset_closedBall (by norm_num) hw.2
  have hbar {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
      conj w ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hw
  have hd (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
      diskExtension d w = diskExtension v (e.symm (S (T w))) := by
    rw [diskExtension_coe d ⟨w, hw⟩]
    change diskExtension v (χ w) = _
    rw [hχ]
  constructor
  · intro w hw
    rw [hd w (hball hw), hV (T w) (hT (hball hw))]
    exact hplus w (hball hw) hw.1
  · intro w hw
    change diskExtension d (conj w) = _
    rw [hd (conj w) (hbar (hball hw)), hV (T (conj w)) (hT (hbar (hball hw)))]
    exact hminus w (hball hw) hw.1

private theorem slit_fold_uniqueMDiff {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) r))
  have hinside : (openHalfDisk 0 r : Set ℂ) ⊆ interior (closedHalfDisk 0 r) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 r).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(r / 2 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((r / 2 : ℂ) * Complex.I).im
    simp only [Complex.mul_I_im, Complex.div_ofNat_re, Complex.ofReal_re]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    simp only [norm_mul, Complex.norm_I, mul_one, norm_div,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem slit_fold_mfderivWithin_congr {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem slit_fold_conormal_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (inwardConormalWithin g F H z : E) = (inwardConormalWithin g G H z : E) := by
  let Q : M → (ℂ →L[ℝ] E) → E := fun q D =>
    (Real.sqrt (g.inner q (D 1) (D 1)) *
      tangentTwoJacobian g (x := q) (D 1) (D Complex.I))⁻¹ •
      (g.inner q (D 1) (D 1) • D Complex.I - g.inner q (D 1) (D Complex.I) • D 1)
  have h := congrArg₂ Q (heq hz) (slit_fold_mfderivWithin_congr heq hz)
  simpa only [Q, inwardConormalWithin, gramWithin, densityWithin, partialWithin] using! h

private theorem slit_fold_chart_fderiv_bijective
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    {z : ℂ} (hz : z ∈ ψ.source) : Function.Bijective (fderiv ℝ ψ z) := by
  have h := ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ hz).mfderivToContinuousLinearEquiv (by simp)).bijective
  change Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z) at h
  rw [mfderiv_eq_fderiv] at h
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using!
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ z)).bijective.comp
      (h.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.bijective)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem slit_fold_sheet_regular
    {U : ℂ → M} (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hiU : ∀ z ∈ ψ.target,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {r : ℝ} (hr : 0 < r) (hsource : closedHalfDisk 0 r ⊆ ψ.source)
    (htarget : ψ.target ⊆ Metric.ball (0 : ℂ) 1) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U ∘ ψ) (closedHalfDisk 0 r) ∧
      ∀ z ∈ closedHalfDisk 0 r, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ ψ) (closedHalfDisk 0 r) z) := by
  refine ⟨hU.comp (ψ.contMDiffOn_toFun.mono hsource)
    (fun z hz => htarget (ψ.map_source' (hsource hz))), ?_⟩
  intro z hz
  have hdψ := ψ.mdifferentiableAt (by simp) (hsource hz)
  have hdU := (hU.contMDiffAt
    (Metric.isOpen_ball.mem_nhds (htarget (ψ.map_source' (hsource hz))))).mdifferentiableAt
      (by simp)
  rw [mfderivWithin_eq_mfderiv (slit_fold_uniqueMDiff hr z hz) (hdU.comp z hdψ),
    mfderiv_comp z hdU hdψ]
  exact (hiU (ψ z) (ψ.map_source' (hsource hz))).comp
    ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hsource hz)).mfderivToContinuousLinearEquiv (by simp)).injective


omit [T3Space M] in
/-- Construct the three actual source charts from the one supplied punctured
chart and the one regular-buffer parameter. Their total functions stay literal
after the two sheet charts are restricted to a unit parameter ball. -/
private theorem slit_regular_charts
    {u : C(closedDisk, M)}
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.ball 0 1))
    (κ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    {ell : ℝ} (hell : 0 < ell)
    (hp : (ell / 4 : ℂ) ∈ κ.source) (hm : (-(ell / 4 : ℂ)) ∈ κ.source)
    (ht : Complex.I * (ell / 4 : ℂ) ∈ κ.source)
    (hκ : MapsTo κ κ.source (Metric.ball (0 : ℂ) 1))
    (hrankp : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (κ (ell / 4 : ℂ))))
    (hrankm : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (κ (-(ell / 4 : ℂ))))) :
    ∃ η : ℝ, 0 < η ∧ η < ell / 16 ∧
      ∃ χ ψ₁ ψ₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        (∀ w, χ w = κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.T ell η w)) ∧
        (∀ w, ψ₁ w = κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.Bplus ell η w)) ∧
        (∀ w, ψ₂ w = κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.Bminus ell η w)) ∧
        ψ₁ 0 = κ (ell / 4 : ℂ) ∧ ψ₂ 0 = κ (-(ell / 4 : ℂ)) ∧
        Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
        χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
        Metric.closedBall (0 : ℂ) (2 * (1 / 4 : ℝ)) ⊆ ψ₁.source ∩ ψ₂.source ∧
        ψ₁.target ⊆ Metric.ball (0 : ℂ) 1 ∧ ψ₂.target ⊆ Metric.ball (0 : ℂ) 1 ∧
        (∀ z ∈ ψ₁.target, Function.Injective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)) ∧
        (∀ z ∈ ψ₂.target, Function.Injective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)) := by
  obtain ⟨Np, Nm, _hNpOpen, _hNmOpen, _hpNp, _hmNm, hNpBall, hNmBall,
    hiNp, hiNm, η, hη, hηsmall, hbuffer⟩ :=
    exists_branch_slit_regular_buffer hU κ hell hp hm ht hκ hrankp hrankm
  let χ := (DifferentialGeometry.Topology.Planar.SlitSeamCharts.TChart ell η hη.ne').trans κ
  let k₁ := (DifferentialGeometry.Topology.Planar.SlitSeamCharts.BplusChart ell η hη.ne').trans κ
  let k₂ := (DifferentialGeometry.Topology.Planar.SlitSeamCharts.BminusChart ell η hη.ne').trans κ
  let ψ₁ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict k₁ (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
  let ψ₂ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict k₂ (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
  have hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source := by
    intro w hw
    exact ⟨mem_univ _, (hbuffer w hw).2.2.2.2.1⟩
  have hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hbuffer w hw).2.2.2.2.2
  have hψsrc : Metric.closedBall (0 : ℂ) (2 * (1 / 4 : ℝ)) ⊆ ψ₁.source ∩ ψ₂.source := by
    intro w hw
    have hw1 : w ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (by norm_num) hw
    have hwopen : w ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.closedBall_subset_ball (by norm_num) hw
    exact ⟨⟨⟨mem_univ _, (hbuffer w hw1).1⟩, hwopen⟩,
      ⟨⟨mem_univ _, (hbuffer w hw1).2.2.1⟩, hwopen⟩⟩
  have ht₁ : ψ₁.target ⊆ Np := by
    rintro z ⟨hz, hzinv⟩
    have h := (hbuffer (k₁.symm z) (Metric.ball_subset_closedBall hzinv)).2.1
    change k₁ (k₁.symm z) ∈ Np at h
    have hinv : k₁ (k₁.symm z) = z := k₁.toPartialEquiv.right_inv hz
    rw [hinv] at h
    exact h
  have ht₂ : ψ₂.target ⊆ Nm := by
    rintro z ⟨hz, hzinv⟩
    have h := (hbuffer (k₂.symm z) (Metric.ball_subset_closedBall hzinv)).2.2.2.1
    change k₂ (k₂.symm z) ∈ Nm at h
    have hinv : k₂ (k₂.symm z) = z := k₂.toPartialEquiv.right_inv hz
    rw [hinv] at h
    exact h
  refine ⟨η, hη, hηsmall, χ, ψ₁, ψ₂, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    ?_, ?_, hχsrc, hχinside, hψsrc, ht₁.trans hNpBall, ht₂.trans hNmBall,
    (fun _ hz => hiNp _ (ht₁ hz)), (fun _ hz => hiNm _ (ht₂ hz))⟩
  · change κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.Bplus ell η 0) = _
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      congrArg κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.centers ell η).2.1
  · change κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.Bminus ell η 0) = _
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, neg_div] using
      congrArg κ (DifferentialGeometry.Topology.Planar.SlitSeamCharts.centers ell η).2.2

/-- The existing local fold variation applied to the exact replacement. This
private receiving step is called only after the literal filling and its area
identity have been constructed. `univ` is the same Morrey target, not a change
of metric or an assertion of ambient original-metric minimality. -/
private theorem slit_fold_contradiction
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hdim : Module.finrank ℝ E = 3) (v : C(closedDisk, M))
    {A : ℝ≥0} (hvLip : ∀ z w, riemannianEDistOf g (v z) (v w) ≤
      (A : ℝ≥0∞) * edist z w)
    (hvTrace : diskTrace v = diskTrace u)
    (hvArea : riemannianDiskArea g v = riemannianDiskArea g u)
    (χ ψ₁ ψ₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hbuffer : Metric.closedBall (0 : ℂ) (2 * (1 / 4 : ℝ)) ⊆ ψ₁.source ∩ ψ₂.source)
    (htarget₁ : ψ₁.target ⊆ Metric.ball (0 : ℂ) 1)
    (htarget₂ : ψ₂.target ⊆ Metric.ball (0 : ℂ) 1)
    (hrank₁ : ∀ z ∈ ψ₁.target, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hrank₂ : ∀ z ∈ ψ₂.target, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hseam : ∀ t ∈ Icc (-2 * (1 / 4 : ℝ)) (2 * (1 / 4 : ℝ)),
      diskExtension u (ψ₁ (t : ℂ)) = diskExtension u (ψ₂ (t : ℂ)))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (ψ₁ 0)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (ψ₂ 0))))) :
    let d := diskThroughSourceChart v χ hχsrc
    EqOn (diskExtension d) (diskExtension u ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) →
    EqOn (diskExtension d ∘ conj) (diskExtension u ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) →
    False := by
  let d := diskThroughSourceChart v χ hχsrc
  change EqOn (diskExtension d) (diskExtension u ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) →
    EqOn (diskExtension d ∘ conj) (diskExtension u ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) → False
  intro hF₁ hF₂
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hzbuffer : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (2 * (1 / 4 : ℝ)) := by
    simp only [Metric.mem_closedBall, dist_self]
    norm_num
  have hz₁ := (hbuffer hzbuffer).1
  have hz₂ := (hbuffer hzbuffer).2
  have hpair : diskExtension u (ψ₁ 0) = diskExtension u (ψ₂ 0) :=
    hseam 0 (by constructor <;> norm_num)
  obtain ⟨_, _, _, _, _, _, hnonzero, _⟩ :=
    paired_halfdisk_inward_conormals_ne_zero_of_transverse g Metric.isOpen_ball hu.smoothInterior
      hpair (hrank₁ _ (ψ₁.map_source' hz₁)) (hrank₂ _ (ψ₂.map_source' hz₂))
      htrans hdim hquarter ψ₁.toOpenPartialHomeomorph ψ₂.toOpenPartialHomeomorph
      rfl rfl hbuffer htarget₁ htarget₂
      (contMDiffOn_iff_contDiffOn.mp ψ₁.contMDiffOn_toFun)
      (contMDiffOn_iff_contDiffOn.mp ψ₂.contMDiffOn_toFun)
      (fun _ hz => slit_fold_chart_fderiv_bijective ψ₁ hz)
      (fun _ hz => slit_fold_chart_fderiv_bijective ψ₂ hz) hseam
  have hHsrc : closedHalfDisk 0 (1 / 4) ⊆ ψ₁.source ∩ ψ₂.source := by
    intro z hz
    exact hbuffer (Metric.closedBall_subset_closedBall (by norm_num) hz.2)
  obtain ⟨hreg₁, hi₁⟩ := slit_fold_sheet_regular hu.smoothInterior ψ₁ hrank₁ hquarter
    (fun _ hz => (hHsrc hz).1) htarget₁
  obtain ⟨hreg₂, hi₂⟩ := slit_fold_sheet_regular hu.smoothInterior ψ₂ hrank₂ hquarter
    (fun _ hz => (hHsrc hz).2) htarget₂
  have hd₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d)
      (closedHalfDisk 0 (1 / 4)) := hreg₁.congr hF₁
  have hd₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d ∘ conj)
      (closedHalfDisk 0 (1 / 4)) := hreg₂.congr hF₂
  have hdi₁ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    have hD := slit_fold_mfderivWithin_congr (E := E) hF₁ hz
    intro x y hxy
    apply hi₁ z hz
    exact (congrArg (fun L : ℂ →L[ℝ] E => L x) hD).symm.trans
      (hxy.trans (congrArg (fun L : ℂ →L[ℝ] E => L y) hD))
  have hdi₂ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj)
        (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    have hD := slit_fold_mfderivWithin_congr (E := E) hF₂ hz
    intro x y hxy
    apply hi₂ z hz
    exact (congrArg (fun L : ℂ →L[ℝ] E => L x) hD).symm.trans
      (hxy.trans (congrArg (fun L : ℂ →L[ℝ] E => L y) hD))
  have hzero : (0 : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    refine ⟨(show 0 ≤ (0 : ℂ).im from le_rfl), ?_⟩
    simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_self] using hquarter.le
  have hfold : (inwardConormalWithin g (diskExtension d) (closedHalfDisk 0 (1 / 4)) 0 : E) +
      (tangentSpaceCast 𝓘(ℝ, E) ((diskExtension d ∘ conj) 0) (diskExtension d 0)
        (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk 0 (1 / 4)) 0) : E) ≠ 0 := by
    change (fun x y : E => x + y)
      (inwardConormalWithin g (diskExtension d) (closedHalfDisk 0 (1 / 4)) 0)
      (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk 0 (1 / 4)) 0) ≠ 0
    rw [slit_fold_conormal_congr g hF₁ hzero, slit_fold_conormal_congr g hF₂ hzero]
    exact hnonzero
  have hdcenter : diskExtension d 0 ∈ interior (Set.univ : Set M) := by simp
  have hopenClosed : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hψsrc : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ ψ₁.source ∩ ψ₂.source :=
    hopenClosed.trans hHsrc
  obtain ⟨r, Y, Φ, _, hrsmall, hY, _, _, hΦ, hΦzero, hvelocity, hfix, hΦW, hnegative⟩ :=
    exists_supported_flow_of_reparametrized_nonzero_fold g d (diskExtension u) ψ₁ ψ₂
      hu.smoothInterior hu.conformal hu.harmonic hquarter
      (hd₁.of_le (by simp)) (hd₂.of_le (by simp)) hdi₁ hdi₂
      (ψ₁.contMDiffOn_toFun.mono (fun _ hz => (hψsrc hz).1))
      (ψ₂.contMDiffOn_toFun.mono (fun _ hz => (hψsrc hz).2))
      (fun _ hz => htarget₁ (ψ₁.map_source' (hψsrc hz).1))
      (fun _ hz => htarget₂ (ψ₂.map_source' (hψsrc hz).2))
      (fun _ hz => ((ψ₁.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsrc hz).1).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
      (fun _ hz => ((ψ₂.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsrc hz).2).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
      (hF₁.mono hopenClosed) (hF₂.mono hopenClosed) hdcenter hfold
  have hopen : Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆
      (openHalfDisk 0 (1 / 4) : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrsmall⟩
  have hclosedNhds (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk 0 (1 / 4) ∈ 𝓝 z :=
    mem_of_superset ((openHalfDisk 0 (1 / 4)).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hrankd₁ : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₁ z (mem_of_mem_nhds (hclosedNhds z hz))
  have hrankd₂ : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₂ z (mem_of_mem_nhds (hclosedNhds z hz))
  obtain ⟨w, K, hwLip, hwtrace, _, hwarea⟩ :=
    exists_disk_area_lt_of_chart_fold_divergence_neg g v hvLip χ (by simp) hχsrc hχinside
      (Set.subset_univ _) Φ hΦ hΦzero Y hY hvelocity 0 r
      (by simp only [Complex.ofReal_zero, norm_zero, zero_add]; linarith)
      hfix hΦW (hd₁.mono (hopen.trans hopenClosed)) (hd₂.mono (hopen.trans hopenClosed))
      hrankd₁ hrankd₂ hnegative
  have hwJordan : DiskWeakJordanTrace γ w := by
    obtain ⟨σ, hσ, hσtrace⟩ := hu.trace
    exact ⟨σ, hσ, hwtrace.trans (hvTrace.trans hσtrace)⟩
  have hmin := hu.minimizesLipschitz w hwJordan ⟨K, hwLip⟩
  exact (not_lt_of_ge hmin) (hwarea.trans_eq hvArea)

/-- A finite slit replacement of the same disk rules out a transverse regular
pair on its retained nodal arc. The replacement and its area equality are
constructed in the original metric. The straightening is required to be smooth
only away from the center; its total maps stay those of the supplied witness. -/
theorem IsMorreyDisk.not_transverse_of_actual_slit_straightening
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hdim : Module.finrank ℝ E = 3)
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (e S : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hea : e a = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (heBall : Metric.closedBall (0 : ℂ) R ⊆ e.target)
    (heForward : ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}))
    (heInverse : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}))
    (hSsource : S.source = Metric.ball 0 R)
    (hStarget : S.target = Metric.ball 0 R)
    (hSnorm : ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      ‖S w‖ = ‖w‖ ∧ ‖S.symm w‖ = ‖w‖ ∧
      S.symm (S w) = w ∧ S (S.symm w) = w)
    {K J : ℝ≥0}
    (hSLip : LipschitzOnWith K (S : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hSiLip : LipschitzOnWith J (S.symm : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hSsmooth : ContDiffOn ℝ ∞ (S : ℂ → ℂ) (Metric.ball 0 R \ {0}))
    (hSismooth : ContDiffOn ℝ ∞ (S.symm : ℂ → ℂ) (Metric.ball 0 R \ {0}))
    (hpair : ∀ t ∈ Icc (0 : ℝ) R,
      diskExtension u (e.symm (S (t : ℂ))) =
        diskExtension u (e.symm (S (-(t : ℂ)))))
    (hrankp : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (diskExtension u) (e.symm (S (R / 16 : ℂ)))))
    (hrankm : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (diskExtension u) (e.symm (S (-(R / 16 : ℂ)))))) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
          (e.symm (S (R / 16 : ℂ)))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
          (e.symm (S (-(R / 16 : ℂ))))))) := by
  intro htrans
  classical
  obtain ⟨χ₀, d₀, v, _C, A, hχ₀, hχ₀inv, _hχ₀src, _hχ₀inside,
    _hphysical, hd₀, _hd₀Lip, _hd₀boundary, _hd₀range, hvLip, hvTrace, _hvRange,
    hvPatch, _hvOutside, _hvSubtraction, _hd₀Area, hvArea⟩ :=
    exists_actual_branch_slit_filling_same_area g u huLip e S hR he hei heSource heBall
      hSnorm hSLip hSiLip hpair
  have hvValue := slit_pasted_value u d₀ v e S hR heSource heBall hSnorm
    χ₀ hχ₀ hχ₀inv hd₀ hvPatch
  obtain ⟨κ, _hκsource, _hκtarget, hκfun, _hκinv, _hκinside, hκmap, hmodel⟩ :=
    DifferentialGeometry.Topology.Planar.exists_branch_slit_chart e S hea heSource heBall
      heForward heInverse hSsource hStarget
      (fun w hw => ⟨(hSnorm w hw).1, (hSnorm w hw).2.1⟩) hSsmooth hSismooth
  let ell : ℝ := R / 4
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hellR : ell < 4 * R := by dsimp [ell]; linarith
  have hq : (ell / 4 : ℂ) = (R / 16 : ℂ) := by
    dsimp [ell]
    push_cast
    ring
  have hmodel' : (ell / 4 : ℂ) ∈ κ.source ∧ (-(ell / 4 : ℂ)) ∈ κ.source ∧
      Complex.I * (ell / 4 : ℂ) ∈ κ.source := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hmodel ell hell hellR
  have hκpPoint : κ (ell / 4 : ℂ) = e.symm (S (R / 16 : ℂ)) := by
    rw [hκfun, hq]
  have hκmPoint : κ (-(ell / 4 : ℂ)) = e.symm (S (-(R / 16 : ℂ))) := by
    rw [hκfun, hq]
  have hiκp : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (κ (ell / 4 : ℂ))) := by
    exact (congrArg (fun z : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)) hκpPoint).mpr hrankp
  have hiκm : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (κ (-(ell / 4 : ℂ)))) := by
    exact (congrArg (fun z : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)) hκmPoint).mpr hrankm
  obtain ⟨η, hη, hηsmall, χ, ψ₁, ψ₂, hχfun, hψ₁fun, hψ₂fun,
    hψ₁zero, hψ₂zero, hχsrc, hχinside, hbuffer, htarget₁, htarget₂, hi₁, hi₂⟩ :=
    slit_regular_charts hu.smoothInterior κ hell hmodel'.1 hmodel'.2.1 hmodel'.2.2
      hκmap hiκp hiκm
  let f : ℂ → M := fun w => diskExtension u (e.symm (S w))
  have hpairSmall : ∀ t ∈ Icc (0 : ℝ) (ell / 2), f (t : ℂ) = f (-t : ℂ) := by
    intro t ht
    exact hpair t ⟨ht.1, by dsimp [ell] at ht; linarith [ht.2]⟩
  have hplus (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (him : 0 ≤ w.im) :
      f (scaledSlitMap ell (T ell η w)) = f (Bplus ell η w) :=
    comp_scaledSlitMap_T hell hη hηsmall hpairSmall hw him
  have hminus (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (him : 0 ≤ w.im) :
      f (scaledSlitMap ell (T ell η (conj w))) = f (Bminus ell η w) :=
    comp_scaledSlitMap_T_conj hell hη hηsmall hpairSmall hw him
  have hT : MapsTo (T ell η) (Metric.closedBall (0 : ℂ) 1)
      (Metric.closedBall (0 : ℂ) R) := by
    intro w hw
    have hn := (T_norm_bounds hell hη hηsmall hw).2
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [ell] at hn
    linarith
  have hχliteral (w : ℂ) : χ w = e.symm (S (T ell η w)) := by
    rw [hχfun, hκfun]
  obtain ⟨hF₁, hF₂⟩ := slit_pasted_halfdisk_identities u v e S
    (T ell η) (Bplus ell η) (Bminus ell η) hT hvValue hplus hminus χ hχsrc hχliteral
  have hseam : ∀ t ∈ Icc (-2 * (1 / 4 : ℝ)) (2 * (1 / 4 : ℝ)),
      diskExtension u (ψ₁ (t : ℂ)) = diskExtension u (ψ₂ (t : ℂ)) := by
    intro t ht
    have htBall : (t : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have him : 0 ≤ (t : ℂ).im := by simp only [Complex.ofReal_im, le_refl]
    calc
      diskExtension u (ψ₁ (t : ℂ)) = f (Bplus ell η (t : ℂ)) := by rw [hψ₁fun, hκfun]
      _ = f (scaledSlitMap ell (T ell η (t : ℂ))) := (hplus _ htBall him).symm
      _ = f (scaledSlitMap ell (T ell η (conj (t : ℂ)))) := by rw [Complex.conj_ofReal]
      _ = f (Bminus ell η (t : ℂ)) := hminus _ htBall him
      _ = diskExtension u (ψ₂ (t : ℂ)) := by rw [hψ₂fun, hκfun]
  have htransψ : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (ψ₁ 0)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (ψ₂ 0)))) := by
    have hpPoint : ψ₁ 0 = e.symm (S (R / 16 : ℂ)) := hψ₁zero.trans hκpPoint
    have hmPoint : ψ₂ 0 = e.symm (S (-(R / 16 : ℂ))) := hψ₂zero.trans hκmPoint
    exact (congrArg₂ (fun p q : ℂ => Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) p).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) q))))
      hpPoint hmPoint).mpr htrans
  apply slit_fold_contradiction hu hdim v hvLip hvTrace hvArea χ ψ₁ ψ₂ hχsrc hχinside
    hbuffer htarget₁ htarget₂ hi₁ hi₂ hseam htransψ
  · simpa only [Function.comp_def, hψ₁fun, hκfun] using hF₁
  · simpa only [Function.comp_def, hψ₂fun, hκfun] using hF₂

end DifferentialGeometry.Geometry
