import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryNoShortcutBufferC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric

/-!
# O-CH11-SPINE-A2 G6：(D4′) 的 `hpush` ⇐ 不同 cap window 不相交（`_C11SP`）

G5 `oldTerminal_edist_le_mul_of_buffer_C11SP` 的 `hpush`（buffer 端点 → 受保护点）由 cap window 的
**径向推出**付清，`Cp = 22`：模型径向路径 `ρ(t)·e`（`ρ = a + (1 − cos πt)/2 · (R* − a)`，
`R* = transitionEnd + 10 + min 1 ((D − transitionEnd − 10)/2)`），长度用 `actual_window_quad_bounds`
（`scale·g_out ≤ (3/2)·g_cap`）+ `StandardCap.metric_inner_unit_radial`（模型径向单位长）；
路径落在 `interior (range oldOutput)` 由 `exceptional_mem_inner_window` + window 单射 + `hdisj`。
剩下的 binder 只有 `hdisj`：不同 cap 的 window 像不与他 cap 的内窗 `‖z‖ ≤ transitionEnd + 10` 相交
（树内未找到；repair target = StandardCap / EventCap 线的 cap 间分离）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private exceptional_mem_inner_window actual_window_quad_bounds from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- 径向参数的导数。 -/
theorem hasDerivAt_radialParam_C11SP (A R t : ℝ) :
    HasDerivAt (fun t : ℝ => A + (1 - Real.cos (Real.pi * t)) / 2 * (R - A))
      (Real.pi * Real.sin (Real.pi * t) / 2 * (R - A)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos (Real.pi * t))
      (-Real.sin (Real.pi * t) * (Real.pi * 1)) t :=
    (Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
  have h2 := (((h1.const_sub 1).div_const 2).mul_const (R - A)).const_add A
  convert h2 using 1
  ring

/-- **G6（PROVISIONAL[hdisj]）**：G5 的 `hpush`（`Cp = 22`）由 cap window 径向推出给出。 -/
theorem hpush_of_disjoint_windows_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (hdisj : ∀ b b' : E.RetainedBoundaryIndex, b ≠ b' → ∀ y z : standardCapWindow D,
      ‖z.val‖ ≤ StandardCap.transitionEnd + 10 → (S b).window y ≠ (S b').window z) :
    ∀ (u : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      ∃ u' : E.old, (∀ b, E.oldOutput u' ∉ (S b).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
          γ 0 = E.oldOutput u ∧ γ 1 = E.oldOutput u' ∧
          MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
          riemannianCurveELength E.outputMetric γ 0 1 ≤
            ENNReal.ofReal (22 / Real.sqrt (S b₀).neck.scale) := by
  intro u b₀ x hx1 hx2 hxu
  have hTE := StandardCap.transitionEnd_pos
  set A : ℝ := ‖x.val‖ with hA
  have hA0 : 0 < A := hTE.trans hx1
  set μ : ℝ := min 1 ((D - (StandardCap.transitionEnd + 10)) / 2) with hμ
  have hμ0 : 0 < μ := lt_min one_pos (by linarith)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  have hμ2 : μ ≤ (D - (StandardCap.transitionEnd + 10)) / 2 := min_le_right _ _
  set Rs : ℝ := StandardCap.transitionEnd + 10 + μ with hRs
  have hRsA : A < Rs := by linarith
  have hRsD : Rs < D := by linarith
  have hRsA11 : Rs - A ≤ 11 := by linarith
  set e : ThreeSpace := A⁻¹ • x.val with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, Real.norm_of_nonneg hA0.le, ← hA,
      inv_mul_cancel₀ hA0.ne']
  let ρ : ℝ → ℝ := fun t => A + (1 - Real.cos (Real.pi * t)) / 2 * (Rs - A)
  have hσ0 (t : ℝ) : 0 ≤ (1 - Real.cos (Real.pi * t)) / 2 := by
    have := Real.cos_le_one (Real.pi * t)
    linarith
  have hσ1 (t : ℝ) : (1 - Real.cos (Real.pi * t)) / 2 ≤ 1 := by
    have := Real.neg_one_le_cos (Real.pi * t)
    linarith
  have hρA (t : ℝ) : A ≤ ρ t := by
    have := mul_nonneg (hσ0 t) (sub_nonneg.mpr hRsA.le)
    change A ≤ A + (1 - Real.cos (Real.pi * t)) / 2 * (Rs - A)
    linarith
  have hρR (t : ℝ) : ρ t ≤ Rs := by
    have := mul_le_mul_of_nonneg_right (hσ1 t) (sub_nonneg.mpr hRsA.le)
    change A + (1 - Real.cos (Real.pi * t)) / 2 * (Rs - A) ≤ Rs
    linarith
  let p : ℝ → ThreeSpace := fun t => ρ t • e
  have hpnorm (t : ℝ) : ‖p t‖ = ρ t := by
    change ‖ρ t • e‖ = ρ t
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (hA0.le.trans (hρA t))]
  have hpmem (t : ℝ) : p t ∈ standardCapWindow D := by
    change ‖p t‖ < D + 1
    rw [hpnorm]
    linarith [hρR t]
  let η : ℝ → standardCapWindow D := fun t => ⟨p t, hpmem t⟩
  have hpderiv (t : ℝ) : HasDerivAt p
      ((Real.pi * Real.sin (Real.pi * t) / 2 * (Rs - A)) • e) t :=
    (hasDerivAt_radialParam_C11SP A Rs t).smul_const e
  have hpsmooth : ContDiff ℝ ∞ p := by
    have hc : ContDiff ℝ ∞ (fun t : ℝ => Real.cos (Real.pi * t)) :=
      Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
    exact ((contDiff_const.add (((contDiff_const.sub hc).div_const 2).mul contDiff_const)).smul
      contDiff_const)
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ η :=
    (ContMDiff.subtypeVal_comp_iff (standardCapWindow D) η).mp hpsmooth.contMDiff
  let γ : ℝ → Q.Carrier := (S b₀).window ∘ η
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ := (S b₀).window_smooth.contMDiff.comp hη
  have hinj := (S b₀).window_smooth.isEmbedding.injective
  have hηnorm (t : ℝ) : ‖(η t).val‖ = ρ t := hpnorm t
  have hη0 : η 0 = x := by
    apply Subtype.ext
    change ρ 0 • e = x.val
    have hρ0 : ρ 0 = A := by
      change A + (1 - Real.cos (Real.pi * 0)) / 2 * (Rs - A) = A
      simp
    rw [hρ0, he_def, smul_smul, mul_inv_cancel₀ hA0.ne', one_smul]
  have hρ1 : ρ 1 = Rs := by
    change A + (1 - Real.cos (Real.pi * 1)) / 2 * (Rs - A) = Rs
    rw [mul_one, Real.cos_pi]
    ring
  have hint (t : ℝ) : γ t ∈ interior (range E.oldOutput) := by
    by_contra hnot
    obtain ⟨b, z, hz, hzt⟩ := exceptional_mem_inner_window E S hOld hcanonical hnot
    by_cases hb : b = b₀
    · subst hb
      have hzη : z = η t := hinj hzt
      have h1 : ‖z.val‖ = ρ t := by rw [hzη]; exact hηnorm t
      linarith [hρA t]
    · exact hdisj b₀ b (Ne.symm hb) (η t) z (by linarith) hzt.symm
  obtain ⟨u', hu'⟩ := interior_subset (hint 1)
  refine ⟨u', ?_, γ, hγ, ?_, hu'.symm, fun t _ => hint t, ?_⟩
  · rintro b ⟨z, hz, hzeq⟩
    by_cases hb : b = b₀
    · subst hb
      have hzη : z = η 1 := hinj (hzeq.trans hu')
      have h1 : ‖z.val‖ = Rs := by rw [hzη, hηnorm, hρ1]
      change ‖z.val‖ ≤ StandardCap.transitionEnd + 10 at hz
      linarith
    · exact hdisj b₀ b (Ne.symm hb) (η 1) z hz (hzeq.trans hu').symm
  · change (S b₀).window (η 0) = E.oldOutput u
    rw [hη0, hxu]
  · -- 长度
    have hscale := (S b₀).neck.scale_pos
    have hspeed (t : ℝ) : riemannianCurveSpeed E.outputMetric γ t ≤
        22 / Real.sqrt (S b₀).neck.scale := by
      have hD' := mfderiv_comp t ((S b₀).window_smooth.contMDiff.mdifferentiableAt (by simp))
        (hη.mdifferentiableAt (by simp) (x := t))
      have hvalD := mfderiv_comp t
        ((contMDiff_subtype_val (U := standardCapWindow D) (n := ∞)).mdifferentiableAt
          (by simp)) (hη.mdifferentiableAt (by simp) (x := t))
      rw [DifferentialGeometry.mfderiv_subtype_val] at hvalD
      let v : ThreeSpace := mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1
      let c : ℝ := Real.pi * Real.sin (Real.pi * t) / 2 * (Rs - A)
      have hpD : mfderiv 𝓘(ℝ, ℝ) ThreeModel (Subtype.val ∘ η) t 1 = c • e := by
        change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ThreeSpace) p t 1 = c • e
        rw [mfderiv_eq_fderiv]
        exact (hpderiv t).deriv
      have hv : v = c • e := by
        have := congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L 1) hvalD
        exact this.symm.trans hpD
      have hγD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ t 1 : ThreeSpace) =
          mfderiv ThreeModel ThreeModel (S b₀).window (η t) v :=
        congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L 1) hD'
      have hnorm_e : NormedSpace.normalize (V := ThreeSpace) (η t).val = e := by
        change NormedSpace.normalize (V := ThreeSpace) (ρ t • e) = e
        rw [NormedSpace.normalize, norm_smul, he, mul_one,
          Real.norm_of_nonneg (hA0.le.trans (hρA t)), smul_smul,
          inv_mul_cancel₀ (hA0.trans_le (hρA t)).ne', one_smul]
      have hne : (η t).val ≠ 0 := by
        intro h0
        have h1 := hηnorm t
        rw [h0, norm_zero] at h1
        linarith only [hρA t, h1, hA0]
      have hunit := StandardCap.metric_inner_unit_radial hne
      rw [hnorm_e] at hunit
      have hX : StandardCap.metric.inner (η t).val v v = c * c := by
        have h1 : ∀ w : TangentSpace (𝓡 3) (η t).val,
            StandardCap.metric.inner (η t).val (c • w) (c • w) =
              c * c * StandardCap.metric.inner (η t).val w w := by
          intro w
          rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
            FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
          ring
        rw [hv]
        exact (h1 e).trans (by rw [hunit, mul_one])
      have hlt : ‖(η t).val‖ < D := by rw [hηnorm]; linarith only [hρR t, hRsD]
      have hquad := (actual_window_quad_bounds (S b₀) (hcanonical b₀) hε (η t) hlt v).2
      rw [hX] at hquad
      have hR0 : 0 ≤ Rs - A := sub_nonneg.mpr hRsA.le
      have hR2 : (Rs - A) ^ 2 ≤ 121 := by
        have := pow_le_pow_left₀ hR0 hRsA11 2
        norm_num at this ⊢
        exact this
      have hsin := Real.sin_sq_le_one (Real.pi * t)
      have hprod : Real.sin (Real.pi * t) ^ 2 * (Rs - A) ^ 2 ≤ 121 := by
        calc Real.sin (Real.pi * t) ^ 2 * (Rs - A) ^ 2 ≤ 1 * 121 :=
              mul_le_mul hsin hR2 (sq_nonneg _) zero_le_one
          _ = 121 := by norm_num
      have hcc : c * c = Real.pi ^ 2 / 4 * (Real.sin (Real.pi * t) ^ 2 * (Rs - A) ^ 2) := by
        change Real.pi * Real.sin (Real.pi * t) / 2 * (Rs - A) *
          (Real.pi * Real.sin (Real.pi * t) / 2 * (Rs - A)) = _
        ring
      have hc2 : c * c ≤ Real.pi ^ 2 / 4 * 121 := by
        rw [hcc]
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
      have hpi2 : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
        pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
      have hsp : riemannianCurveSpeed E.outputMetric γ t =
          Real.sqrt (E.outputMetric.inner ((S b₀).window (η t))
            (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)
            (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)) :=
        congrArg Real.sqrt (congrArg (fun w : ThreeSpace =>
          E.outputMetric.inner ((S b₀).window (η t)) w w) hγD)
      rw [hsp]
      generalize E.outputMetric.inner ((S b₀).window (η t))
        (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)
        (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v) = Y at hquad ⊢
      have hYle : Y ≤ 484 / (S b₀).neck.scale := by
        rw [le_div_iff₀ hscale]
        have hk : (3 : ℝ) / 2 * (Real.pi ^ 2 / 4 * 121) ≤ 484 := by
          have : (3 : ℝ) / 2 * ((3.15 : ℝ) ^ 2 / 4 * 121) ≤ 484 := by norm_num
          linarith only [this, hpi2]
        have h3 : (S b₀).neck.scale * Y ≤ 484 := by
          linarith only [hquad, hc2, hk]
        linarith only [h3, mul_comm Y (S b₀).neck.scale]
      calc Real.sqrt Y ≤ Real.sqrt (484 / (S b₀).neck.scale) := Real.sqrt_le_sqrt hYle
        _ = 22 / Real.sqrt (S b₀).neck.scale := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 484)]
          congr 1
          rw [show (484 : ℝ) = 22 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hle : riemannianCurveELength E.outputMetric γ 0 1 ≤
        ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (22 / Real.sqrt (S b₀).neck.scale) := by
      unfold riemannianCurveELength
      exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hspeed t)
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hle
    exact hle

end MetricCutCapEvent

namespace ObservedHistory

/-- **G6 history 层（PROVISIONAL[hdisj, hshort]）**：G5 `surgery_no_shortcut_buffer_C11SP` 的 `hpush`
由 `hpush_of_disjoint_windows_C11SP`（`Cp = 22`）付清。 -/
theorem surgery_no_shortcut_buffer_disjoint_C11SP (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {c Cs : ℝ} (hc : 0 < c)
    (hdisj : ∀ b b' : (H.event e).RetainedBoundaryIndex, b ≠ b' →
      ∀ y z : standardCapWindow Dc, ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        (S b).window y ≠ (S b').window z)
    (hshort : ∀ (u w : (H.event e).old) (b₀ : (H.event e).RetainedBoundaryIndex)
      (x : standardCapWindow Dc),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = (H.event e).oldOutput u →
      riemannianEDistOf (H.event e).outputMetric ((H.event e).oldOutput u)
          ((H.event e).oldOutput w) <
        ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale) →
      ∃ γ : ℝ → (H.stage e.succ).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        γ 0 = (H.event e).oldOutput u ∧ γ 1 = (H.event e).oldOutput w ∧
        MapsTo γ (Icc (0 : ℝ) 1) (interior (range (H.event e).oldOutput)) ∧
        riemannianCurveELength (H.event e).outputMetric γ 0 1 ≤
          ENNReal.ofReal Cs * riemannianEDistOf (H.event e).outputMetric
            ((H.event e).oldOutput u) ((H.event e).oldOutput w))
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpb : (∀ b, pp ∉ (S b).window ''
        {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow Dc),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = pp)
    (hqb : (∀ b, qp ∉ (S b).window ''
        {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow Dc),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = qp)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc t) pm qm ≤
        ENNReal.ofReal (max (1 + 4 * (22 / c)) Cs) *
          riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp + ENNReal.ofReal δ :=
  surgery_no_shortcut_buffer_C11SP H e S hOld hcanonical hε hD (by norm_num) hc
    ((H.event e).hpush_of_disjoint_windows_C11SP S hOld hcanonical hε hD hdisj) hshort hp hq
    hpb hqb hδ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
