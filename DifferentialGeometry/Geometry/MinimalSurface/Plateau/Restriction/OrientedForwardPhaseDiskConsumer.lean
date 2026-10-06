/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.ForwardPhaseDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.StrictSignedTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ForwardTracePhase

noncomputable section

open Set Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Orient the once-chosen strict signed lift of the actual alternate Morrey
filling, then perform the literal forward-phase splice. The original two
minima give equal areas, including in the reflected branch; no Morrey record
for the reflected filling or rank conclusion is assumed. -/
theorem IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {Lq La : ℝ≥0}
    (hqLip : ∀ z w : closedDisk, riemannianEDistOf G (q z) (q w) ≤
      (Lq : ℝ≥0∞) * edist z w)
    (haOrigLip : ∀ z w : closedDisk, riemannianEDistOf G (aOrig z) (aOrig w) ≤
      (La : ℝ≥0∞) * edist z w)
    {r2 b : ℝ} (hr2 : 0 < r2) (hr2b : r2 < b) (hb : b < 1)
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r2)) aOrig)
    (hΓ : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r2)))
    {A : ℂ → M} (hA : SmoothDiskExtension (E := E) aOrig A)
    {W : Set M} (hqW : Set.range q ⊆ W) (haOrigW : Set.range aOrig ⊆ W) :
    ∃ (σ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ),
      ContDiff ℝ ∞ ψ ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      diskTrace aOrig = (diskTrace (affineSubdisk q 0 r2)).comp σ ∧
      ((StrictMono ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
        (StrictAnti ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) ∧
      ∃ (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ)
        (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
        (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1),
        ((aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
          (aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
            ∀ t : ℝ, φ t = ψ (-t))) ∧
        StrictMono φ ∧
        (∀ t : ℝ, diskTrace aForward (t : loopCircle) =
          diskTrace (affineSubdisk q 0 r2) (φ t : loopCircle)) ∧
        riemannianDiskArea G aForward = riemannianDiskArea G aOrig ∧
        Set.range aForward = Set.range aOrig ∧
        (∀ z w : closedDisk, riemannianEDistOf G (aForward z) (aForward w) ≤
          (La : ℝ≥0∞) * edist z w) ∧
        let H := ForwardPhaseAnnulus.map r2 b hφ hp
        ∃ (F : C(closedDisk, M)) (KF : ℝ≥0),
          (∀ z : closedDisk, F z =
            if ‖(z : ℂ)‖ ≤ r2 then diskExtension aForward (r2⁻¹ • (z : ℂ))
            else if ‖(z : ℂ)‖ ≤ b then diskExtension q (H z)
            else diskExtension q z) ∧
          (∀ z w : closedDisk, riemannianEDistOf G (F z) (F w) ≤
            (KF : ℝ≥0∞) * edist z w) ∧
          (∀ z : ℂ, ‖z‖ ≤ r2 →
            diskExtension F z = diskExtension aForward (r2⁻¹ • z)) ∧
          (∀ z : ℂ, r2 ≤ ‖z‖ → ‖z‖ ≤ b →
            diskExtension F z = diskExtension q (H z)) ∧
          (∀ z : ℂ, (r2 + b) / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
            diskExtension F z = diskExtension q z) ∧
          diskTrace F = diskTrace q ∧
          Set.range F = Set.range aForward ∪
            diskExtension q '' {z : ℂ | r2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} ∧
          riemannianDiskArea G F =
            riemannianArea G (diskExtension q)
              (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) r2) +
            riemannianDiskArea G aForward ∧
          riemannianDiskArea G F = riemannianDiskArea G q -
            riemannianArea G (diskExtension q) (Metric.closedBall (0 : ℂ) r2) +
            riemannianDiskArea G aForward ∧
          Set.range F ⊆ W ∧ DiskWeakJordanTrace γ F ∧
          riemannianDiskArea G aOrig = riemannianDiskArea G (affineSubdisk q 0 r2) ∧
          riemannianDiskArea G aForward = riemannianDiskArea G (affineSubdisk q 0 r2) ∧
          riemannianDiskArea G aOrig =
            riemannianArea G (diskExtension q) (Metric.closedBall (0 : ℂ) r2) ∧
          riemannianDiskArea G F = riemannianDiskArea G q := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U := diskExtension q
  let qr := affineSubdisk q 0 r2
  let T : ℂ →L[ℝ] ℂ := r2 • ContinuousLinearMap.id ℝ ℂ
  let S : ℂ →L[ℝ] ℂ := r2⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hST (z : ℂ) : S (T z) = z := by
    change r2⁻¹ • (r2 • z) = z
    exact inv_smul_smul₀ hr2.ne' z
  have hTS (z : ℂ) : T (S z) = z := by
    change r2 • (r2⁻¹ • z) = z
    exact smul_inv_smul₀ hr2.ne' z
  have hU : LipschitzWith Lq U := diskExtension_riemannian_lipschitz G hqLip
  have hqr (z : closedDisk) : qr z = U (T z) := by
    change U (0 + r2 • (z : ℂ)) = U (T z)
    rw [zero_add]
    rfl
  have hqrLip : ∀ z w : closedDisk, riemannianEDistOf G (qr z) (qr w) ≤
      ((Lq * ‖T‖₊ : ℝ≥0) : ℝ≥0∞) * edist z w := by
    intro z w
    rw [hqr z, hqr w]
    exact (hU.comp T.lipschitzWith) z w
  have hTimage : T '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall (0 : ℂ) r2 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖r2 • z‖ ≤ r2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr2]
      nlinarith
    · intro z hz
      have hz' : ‖z‖ ≤ r2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      refine ⟨S z, ?_, hTS z⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖r2⁻¹ • z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr2)]
      calc
        r2⁻¹ * ‖z‖ ≤ r2⁻¹ * r2 := mul_le_mul_of_nonneg_left hz' (inv_nonneg.mpr hr2.le)
        _ = 1 := inv_mul_cancel₀ hr2.ne'
  have hqrArea : riemannianDiskArea G qr =
      riemannianArea G U (Metric.closedBall (0 : ℂ) r2) := by
    calc
      _ = riemannianArea G (U ∘ T) (Metric.closedBall (0 : ℂ) 1) :=
        riemannianDiskArea_eq_of_extension G qr (U ∘ T) (fun z => (hqr z).symm)
      _ = riemannianArea G U (T '' Metric.closedBall (0 : ℂ) 1) :=
        riemannianArea_precomp G hU T.lipschitzWith S.lipschitzWith
          measurableSet_closedBall (fun z _ => hST z)
      _ = _ := by rw [hTimage]
  obtain ⟨σ, ψ, hψ, hlift, htraceOrig, hsign⟩ :=
    haOrig.exists_smooth_strict_signed_lift hΓ hA
  obtain ⟨aForward, φ, hbranch, hφ, hm, hp, htraceForward, hForwardArea,
    hForwardRange, haForwardLip⟩ :=
    exists_forward_phase_of_smooth_strict_signed_trace G aOrig σ ψ hψ hlift
      htraceOrig hsign hA haOrigLip
  have htraceNumeric : ∀ t : ℝ, diskTrace aForward (t : loopCircle) =
      diskExtension q (r2 • (AddCircle.toCircle (φ t : loopCircle) : ℂ)) := by
    intro t
    rw [htraceForward t]
    change diskExtension q (0 + r2 • (AddCircle.toCircle (φ t : loopCircle) : ℂ)) = _
    rw [zero_add]
  have hAltLe : riemannianDiskArea G aOrig ≤ riemannianDiskArea G qr :=
    haOrig.minimizesLipschitz qr (DiskWeakJordanTrace.of_diskTrace_eq rfl)
      ⟨Lq * ‖T‖₊, hqrLip⟩
  obtain ⟨F, KF, hFraw, hFLip, hFinner, hFmiddle, hFouter, hFtrace,
    hFrange, hFareaAnnulus, hFarea⟩ :=
    exists_forwardPhase_pastedDisk G q aForward hqLip haForwardLip
      hq.smoothInterior hr2 hr2b hb φ hφ hm hp htraceNumeric
  change riemannianDiskArea G F = riemannianDiskArea G q -
    riemannianArea G U (Metric.closedBall (0 : ℂ) r2) +
    riemannianDiskArea G aForward at hFarea
  have hFW : Set.range F ⊆ W := by
    intro y hy
    rw [hFrange] at hy
    rcases hy with hay | ⟨z, _, rfl⟩
    · exact haOrigW (hForwardRange ▸ hay)
    · exact hqW ⟨diskRetraction z, rfl⟩
  obtain ⟨σq, hσq, hqtrace⟩ := hq.trace
  have hFweak : DiskWeakJordanTrace γ F := ⟨σq, hσq, hFtrace.trans hqtrace⟩
  have hOriginalLe : riemannianDiskArea G q ≤ riemannianDiskArea G F :=
    hq.minimizesLipschitz F hFweak ⟨KF, hFLip⟩
  have hAltArea : riemannianDiskArea G aOrig = riemannianDiskArea G qr := by
    linarith only [hAltLe, hOriginalLe, hFarea, hqrArea, hForwardArea]
  have hForwardAltArea : riemannianDiskArea G aForward = riemannianDiskArea G qr :=
    hForwardArea.trans hAltArea
  have hFsameArea : riemannianDiskArea G F = riemannianDiskArea G q := by
    linarith only [hFarea, hqrArea, hForwardAltArea]
  exact ⟨σ, ψ, hψ, hlift, htraceOrig, hsign, aForward, φ, hφ, hp,
    hbranch, hm, htraceForward, hForwardArea, hForwardRange, haForwardLip,
    F, KF, hFraw, hFLip, hFinner, hFmiddle, hFouter, hFtrace, hFrange,
    hFareaAnnulus, hFarea, hFW, hFweak, hAltArea, hForwardAltArea,
    hAltArea.trans hqrArea, hFsameArea⟩
