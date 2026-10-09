import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ChartFoldShortening
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem replacement_fold_mfderivWithin_congr {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem replacement_fold_conormal_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (inwardConormalWithin g F H z : E) = (inwardConormalWithin g G H z : E) := by
  let Q : M → (ℂ →L[ℝ] E) → E := fun q D =>
    (Real.sqrt (g.inner q (D 1) (D 1)) *
      tangentTwoJacobian g (x := q) (D 1) (D Complex.I))⁻¹ •
      (g.inner q (D 1) (D 1) • D Complex.I - g.inner q (D 1) (D Complex.I) • D 1)
  have h := congrArg₂ Q (heq hz) (replacement_fold_mfderivWithin_congr heq hz)
  simpa only [Q, inwardConormalWithin, gramWithin, densityWithin, partialWithin] using! h

/-- An equal-area replacement filling cannot form a regular nonzero seam fold
with the unchanged part of the original Morrey disk. The synchronized filling
may differ from the harmonic conformal alternative disk: its actual interior
sheet must agree locally with a smooth invertible reparameterization of that
alternative. The pasted disk and its fixed-trace strict competitor are
constructed, and only the original disk's minimum is used. -/
theorem IsMorreyDisk.sourceChart_replacement_conormal_sum_eq_zero
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
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    {R : ℝ} (hR : 0 < R) (hRunit : R < 1)
    (hinner : MapsTo χ (closedHalfDisk 0 R) (e '' Metric.closedBall (0 : ℂ) 1))
    (houter : ∀ z ∈ closedHalfDisk 0 R,
      χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1))
    (hFinner : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R))
    (hiInner : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 R) z))
    (hiOuter : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 R) z))
    (hAltSmooth : DiskSmoothInterior (E := E) qAlt)
    (hAltConf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension qAlt) z)
    (hAltHarm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension qAlt) z = 0)
    (ψAlt : ℂ → ℂ)
    (hψAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψAlt (openHalfDisk 0 R))
    (hmapsAlt : MapsTo ψAlt (openHalfDisk 0 R) (Metric.ball (0 : ℂ) 1))
    (hbijAlt : ∀ z ∈ (openHalfDisk 0 R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψAlt z))
    (heqAlt : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (diskExtension qAlt ∘ ψAlt) (openHalfDisk 0 R))
    (hpW : diskExtension d (e.symm (χ 0)) ∈ interior W) :
    inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R) 0 +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) 0)
        ((diskExtension d ∘ e.symm ∘ χ) 0)
        (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj) (closedHalfDisk 0 R) 0) = 0 := by
  by_contra hnonzero
  obtain ⟨v, A, hvLip, hvtrace, hvW, hvinner, hvouter, hvarea⟩ :=
    exists_sourceChart_disk_replacement g u d huLip hdLip e le_rfl hsrc hinside hboundary huW hdW
  have hvareaeq : riemannianDiskArea g v = riemannianDiskArea g u := by
    rw [harea] at hvarea
    linarith
  let vχ := diskThroughSourceChart v χ hχsrc
  let F₁ := diskExtension d ∘ e.symm ∘ χ
  let χr := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  let F₂ := diskExtension u ∘ χr
  have hHunit : closedHalfDisk 0 R ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun _ hz => Metric.closedBall_subset_closedBall hRunit.le hz.2
  have hbarunit {z : ℂ} (hz : z ∈ closedHalfDisk 0 R) :
      conj z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hHunit hz
  have hχrsource : closedHalfDisk 0 R ⊆ χr.source :=
    fun _ hz => ⟨mem_univ _, hχsrc (hbarunit hz)⟩
  have hχrmaps : MapsTo χr (closedHalfDisk 0 R) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => hχinside ⟨conj z, hbarunit hz, rfl⟩
  have hFouter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F₂ (closedHalfDisk 0 R) :=
    hu.smoothInterior.comp (χr.contMDiffOn_toFun.mono hχrsource) hχrmaps
  have hvχvalue {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      diskExtension vχ z = v ⟨χ z, Metric.ball_subset_closedBall (hχinside ⟨z, hz, rfl⟩)⟩ :=
    calc
      diskExtension vχ z = diskExtension v (χ z) := diskExtension_coe vχ ⟨z, hz⟩
      _ = v ⟨χ z, Metric.ball_subset_closedBall (hχinside ⟨z, hz, rfl⟩)⟩ :=
        diskExtension_coe v ⟨χ z, Metric.ball_subset_closedBall (hχinside ⟨z, hz, rfl⟩)⟩
  have heq₁ : EqOn (diskExtension vχ) F₁ (closedHalfDisk 0 R) := by
    intro z hz
    exact (hvχvalue (hHunit hz)).trans (hvinner _ (hinner hz))
  have heq₂ : EqOn (diskExtension vχ ∘ conj) F₂ (closedHalfDisk 0 R) := by
    intro z hz
    exact (hvχvalue (hbarunit hz)).trans
      ((hvouter _ (houter z hz)).trans (diskExtension_coe u _).symm)
  have hi₁ : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension vχ) (closedHalfDisk 0 R) z) := by
    intro z hz
    have hD := replacement_fold_mfderivWithin_congr (E := E) heq₁ hz
    intro a b hab
    apply hiInner z hz
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) hD).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) hD))
  have hi₂ : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension vχ ∘ conj)
        (closedHalfDisk 0 R) z) := by
    intro z hz
    have hD := replacement_fold_mfderivWithin_congr (E := E) heq₂ hz
    intro a b hab
    apply hiOuter z hz
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) hD).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) hD))
  have hzero : (0 : ℂ) ∈ closedHalfDisk 0 R := by
    refine ⟨(show 0 ≤ (0 : ℂ).im from le_rfl), ?_⟩
    simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_self] using hR.le
  have hfold : inwardConormalWithin g (diskExtension vχ) (closedHalfDisk 0 R) 0 +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension vχ ∘ conj) 0) (diskExtension vχ 0)
        (inwardConormalWithin g (diskExtension vχ ∘ conj) (closedHalfDisk 0 R) 0) ≠ 0 := by
    change (fun a b : E => a + b)
      (inwardConormalWithin g (diskExtension vχ) (closedHalfDisk 0 R) 0)
      (inwardConormalWithin g (diskExtension vχ ∘ conj) (closedHalfDisk 0 R) 0) ≠ 0
    rw [replacement_fold_conormal_congr g heq₁ hzero,
      replacement_fold_conormal_congr g heq₂ hzero]
    exact hnonzero
  have hvχW : diskExtension vχ 0 ∈ interior W := by
    rw [heq₁ hzero]
    exact hpW
  have hopenClosed : (openHalfDisk 0 R : Set ℂ) ⊆ closedHalfDisk 0 R :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension vχ) (openHalfDisk 0 R) :=
    (hAltSmooth.comp hψAlt hmapsAlt).congr ((heq₁.mono hopenClosed).trans heqAlt)
  have hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension vχ ∘ conj) (openHalfDisk 0 R) :=
    (hFouter.congr heq₂).mono hopenClosed
  obtain ⟨r, Y, Φ, _, hrR, hY, _, _, hΦ, hΦzero, hvelocity, hfix, hΦW, hnegative⟩ :=
    exists_supported_flow_of_nonzero_fold_of_two_reparametrizations g vχ
      (diskExtension qAlt) (diskExtension u) ψAlt χr
      hAltSmooth hAltConf hAltHarm hu.smoothInterior hu.conformal hu.harmonic hR
      (hFinner.congr heq₁) ((hFouter.congr heq₂).of_le (by simp)) hi₁ hi₂
      hψAlt (χr.contMDiffOn_toFun.mono (hopenClosed.trans hχrsource))
      hmapsAlt (fun _ hz => hχrmaps (hopenClosed hz))
      hbijAlt (fun _ hz => ((χr.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hχrsource (hopenClosed hz))).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
      ((heq₁.mono hopenClosed).trans heqAlt) (heq₂.mono hopenClosed) hvχW hfold
  have hopen : Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆ (openHalfDisk 0 R : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrR⟩
  have hclosedNhds (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk 0 R ∈ 𝓝 z :=
    mem_of_superset ((openHalfDisk 0 R).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hi₁' : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension vχ) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hi₁ z (mem_of_mem_nhds (hclosedNhds z hz))
  have hi₂' : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension vχ ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hi₂ z (mem_of_mem_nhds (hclosedNhds z hz))
  obtain ⟨w, K, hwLip, hwtrace, _, hwarea⟩ :=
    exists_disk_area_lt_of_chart_fold_divergence_neg g v hvLip χ (by simp) hχsrc hχinside
      hvW Φ hΦ hΦzero Y hY hvelocity 0 r
      (by simp only [Complex.ofReal_zero, norm_zero, zero_add]; exact hrR.trans_lt hRunit)
      hfix hΦW (hUi.mono hopen) (hUri.mono hopen) hi₁' hi₂' hnegative
  have hwJordan : DiskWeakJordanTrace γ w := by
    obtain ⟨σ, hσ, hσtrace⟩ := hu.trace
    exact ⟨σ, hσ, hwtrace.trans (hvtrace.trans hσtrace)⟩
  exact (not_lt_of_ge (hu.minimizesLipschitz w hwJordan ⟨K, hwLip⟩))
    (hwarea.trans_eq hvareaeq)

end DifferentialGeometry.Geometry
