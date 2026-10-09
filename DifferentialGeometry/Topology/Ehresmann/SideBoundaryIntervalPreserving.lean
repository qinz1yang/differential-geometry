import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval
import DifferentialGeometry.Analysis.Calculus.Cutoff.SymmetricCutoff

/-!
# Side-boundary transport and trivialization preserving the side function

Additions to `SideBoundaryInterval.lean` (frozen, untouched) for the LFR28 rim-product clause
(lane ASM-L1b): the flow of `exists_sideBoundary_transport` lifts the base field
`(ζ(P) κ(χ_r ∘ B), 0)` through `Q = (P, χ_r ∘ B)`, so it preserves `χ_r ∘ B` everywhere; `χ_r` is
strictly monotone on `[-r/2, r/2]`, hence the flow preserves `B` itself on `{|B| < r/2}`.

* `sideProfile_monotone`, `sideProfile_strictMonoOn`, `eq_of_sideProfile_eq`: `χ_r` is monotone,
  and strictly monotone on `[-r/2, r/2]` (from the existing
  `DifferentialGeometry.Analysis.smoothTransition_strictMonoOn`).
* `exists_sideBoundary_transport_preserving`: the transport, exporting the invariance of `χ_r ∘ B`
  and translating `P` already on `{B ≥ -r/4}` (profile plateau `[χ_r(-r/4), 1/2]`).
* `exists_sideBoundary_interval_trivialization_preserving`: the interval trivialization `Θ`, with
  moreover `B (Θ (x, t)) = B x` for `B x < r'` (some `r' > 0`), and its underlying flow `D` on an
  open `U` containing the fibre exported: `Θ (x, t) = D t x`, `P (D t z) = t` for `P z = 0`,
  `B z ≥ -r'` (also on the far side of `{B = 0}`), `B (D t z) = B z` for `|B z| < r'`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

section Profile

theorem sideProfile_monotone {r : ℝ} (hr : 0 < r) {u v : ℝ} (huv : u ≤ v) :
    sideProfile r u ≤ sideProfile r v := by
  unfold sideProfile
  have h := Real.smoothTransition.monotone
    (show u / r + 1 / 2 ≤ v / r + 1 / 2 by
      have := div_le_div_of_nonneg_right huv hr.le
      linarith)
  linarith

theorem sideProfile_strictMonoOn {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (sideProfile r) (Icc (-(r / 2)) (r / 2)) := by
  intro u hu v hv huv
  unfold sideProfile
  have hmem : ∀ w ∈ Icc (-(r / 2)) (r / 2), w / r + 1 / 2 ∈ Icc (0 : ℝ) 1 := by
    intro w hw
    have h1 : -(r / 2) / r ≤ w / r := div_le_div_of_nonneg_right hw.1 hr.le
    have h2 : w / r ≤ (r / 2) / r := div_le_div_of_nonneg_right hw.2 hr.le
    rw [neg_div, div_div_cancel_left' hr.ne'] at h1
    rw [div_div_cancel_left' hr.ne'] at h2
    constructor <;> linarith
  have h := DifferentialGeometry.Analysis.smoothTransition_strictMonoOn (hmem u hu) (hmem v hv)
    (show u / r + 1 / 2 < v / r + 1 / 2 by
      have := div_lt_div_of_pos_right huv hr
      linarith)
  linarith

/-- Equal profiles at two points, one of them in the band `|u| < r/2`, force equality. -/
theorem eq_of_sideProfile_eq {r : ℝ} (hr : 0 < r) {u v : ℝ} (hu : |u| < r / 2)
    (h : sideProfile r v = sideProfile r u) : v = u := by
  have hlt : sideProfile r u < 1 / 2 := by
    have hu' := abs_lt.mp hu
    have := sideProfile_strictMonoOn hr ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ hu'.2
    rwa [sideProfile_of_ge hr le_rfl] at this
  have hgt : -(1 / 2) < sideProfile r u := by
    have hu' := abs_lt.mp hu
    have := sideProfile_strictMonoOn hr ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ hu'.1
    rwa [sideProfile_of_le hr le_rfl] at this
  have hv : |v| < r / 2 := by
    rw [abs_lt]
    constructor
    · by_contra hc
      rw [sideProfile_of_le hr (not_lt.mp hc)] at h
      linarith
    · by_contra hc
      rw [sideProfile_of_ge hr (not_lt.mp hc)] at h
      linarith
  have hv' := abs_lt.mp hv
  have hu' := abs_lt.mp hu
  exact (sideProfile_strictMonoOn hr).injOn ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ h

end Profile

section Core

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **Side-boundary transport preserving the side function.** The hypotheses of
`exists_sideBoundary_transport`; the flow `D` (built in the same way, with the profile plateau
`[χ_r(-r/4), 1/2]` instead of `[0, 1/2]`) moreover preserves `χ_r ∘ B` everywhere and translates
`P` on `{B ≥ -r/4} ∩ P⁻¹[a₀, b₀]`. -/
theorem exists_sideBoundary_transport_preserving {P B : M → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    {a₁ a₀ b₀ b₁ r : ℝ} (ha : a₁ < a₀) (hab : a₀ ≤ b₀) (hb : b₀ < b₁) (hr : 0 < r)
    (hC : IsCompact {x | P x ∈ Icc a₁ b₁ ∧ -r ≤ B x})
    (hsP : ∀ x, P x ∈ Icc a₁ b₁ → -r ≤ B x → Surjective (mfderiv I 𝓘(ℝ, ℝ) P x))
    (hsPB : ∀ x, P x ∈ Icc a₁ b₁ → |B x| < r →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) x)) :
    ∃ D : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M ↦ D p.1 p.2) ∧
      D 0 = Diffeomorph.refl I M ∞ ∧
      (∀ s t, (D s).trans (D t) = D (s + t)) ∧
      (∀ s, (D s).symm = D (-s)) ∧
      (∀ t x, 0 ≤ B (D t x) ↔ 0 ≤ B x) ∧
      (∀ t x, sideProfile r (B (D t x)) = sideProfile r (B x)) ∧
      ∀ x, -(r / 4) ≤ B x → P x ∈ Icc a₀ b₀ → ∀ t ∈ Icc a₀ b₀, P (D (t - P x) x) = t := by
  classical
  set c₀ : ℝ := sideProfile r (-(r / 4)) with hc₀def
  have hc₀lo : -(1 / 2) < c₀ := by
    have h1 : 0 < Real.smoothTransition (-(r / 4) / r + 1 / 2) :=
      Real.smoothTransition.pos_of_pos (by
        rw [neg_div, div_div_cancel_left' hr.ne']
        norm_num)
    rw [hc₀def]
    unfold sideProfile
    linarith
  have hc₀hi : c₀ < 1 / 2 := by
    have h1 : Real.smoothTransition (-(r / 4) / r + 1 / 2) < 1 :=
      Real.smoothTransition.lt_one_of_lt_one (by
        rw [neg_div, div_div_cancel_left' hr.ne']
        norm_num)
    rw [hc₀def]
    unfold sideProfile
    linarith
  set η : ℝ := min (a₀ - a₁) (b₁ - b₀) / 3 with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hη1 : 3 * η ≤ a₀ - a₁ := by
    rw [hηdef]
    linarith [min_le_left (a₀ - a₁) (b₁ - b₀)]
  have hη2 : 3 * η ≤ b₁ - b₀ := by
    rw [hηdef]
    linarith [min_le_right (a₀ - a₁) (b₁ - b₀)]
  let ζb : ContDiffBump ((a₀ + b₀) / 2) :=
    ⟨(b₀ - a₀) / 2 + η, (b₀ - a₀) / 2 + 2 * η, by linarith, by linarith⟩
  let κb : ContDiffBump ((c₀ + 1 / 2) / 2) :=
    ⟨(1 / 2 - c₀) / 2, 1 / 2, by linarith, by linarith⟩
  let ζ : ℝ → ℝ := ζb
  let κ : ℝ → ℝ := κb
  let χ : ℝ → ℝ := sideProfile r
  have hζ : ContDiff ℝ ∞ ζ := ζb.contDiff
  have hκ : ContDiff ℝ ∞ κ := κb.contDiff
  have hχ : ContDiff ℝ ∞ χ := contDiff_sideProfile r
  have hζone : ∀ s ∈ Ioo (a₀ - η) (b₀ + η), ζ s = 1 := by
    intro s hs
    apply ζb.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -((b₀ - a₀) / 2 + η) ≤ s - (a₀ + b₀) / 2 ∧ s - (a₀ + b₀) / 2 ≤ (b₀ - a₀) / 2 + η
    constructor <;> linarith [hs.1, hs.2]
  have hκone : ∀ w ∈ Icc c₀ (1 / 2), κ w = 1 := by
    intro w hw
    apply κb.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -((1 / 2 - c₀) / 2) ≤ w - (c₀ + 1 / 2) / 2 ∧ w - (c₀ + 1 / 2) / 2 ≤ (1 / 2 - c₀) / 2
    constructor <;> linarith [hw.1, hw.2]
  have hζsupp : tsupport ζ ⊆ Icc a₁ b₁ := by
    intro s hs
    have h : s ∈ Metric.closedBall ((a₀ + b₀) / 2) ((b₀ - a₀) / 2 + 2 * η) := by
      have := ζb.tsupport_eq
      change s ∈ tsupport ζ at hs
      rw [show tsupport ζ = tsupport ζb from rfl, this] at hs
      exact hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hκsupp : tsupport κ ⊆ Icc ((c₀ - 1 / 2) / 2) ((c₀ + 3 / 2) / 2) := by
    intro w hw
    have h : w ∈ Metric.closedBall ((c₀ + 1 / 2) / 2 : ℝ) (1 / 2) := by
      have := κb.tsupport_eq
      rw [show tsupport κ = tsupport κb from rfl, this] at hw
      exact hw
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  -- the base field on `ℝ × ℝ`
  let Z : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y := fun y => (ζ y.1 * κ y.2, (0 : ℝ))
  have hZs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr
      (((hζ.comp contDiff_fst).mul (hκ.comp contDiff_snd)).prodMk contDiff_const)
  have hZsupp : tsupport Z ⊆ tsupport ζ ×ˢ tsupport κ := by
    apply closure_minimal _ ((isClosed_tsupport ζ).prod (isClosed_tsupport κ))
    intro y hy
    have hne : ζ y.1 * κ y.2 ≠ 0 := by
      intro h0
      apply hy
      change ((ζ y.1 * κ y.2, (0 : ℝ)) : ℝ × ℝ) = 0
      rw [h0]
      rfl
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
      subset_tsupport _ (right_ne_zero_of_mul hne)⟩
  have hZc : IsCompact (tsupport Z) :=
    (ζb.hasCompactSupport.isCompact.prod κb.hasCompactSupport.isCompact).of_isClosed_subset
      (isClosed_tsupport Z) hZsupp
  -- the map `Q = (P, χ ∘ B)`
  let Q : M → ℝ × ℝ := fun x => (P x, χ (B x))
  have hχB : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => χ (B x)) := hχ.contMDiff.comp hB
  have hQ : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ Q := hP.prodMk_space hχB
  have hQd : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) Q x := fun x =>
    (hQ x).mdifferentiableAt (by simp)
  have hPd : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) P x := fun x => (hP x).mdifferentiableAt (by simp)
  have hBd : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) B x := fun x => (hB x).mdifferentiableAt (by simp)
  have hQ1 : ∀ x v, (mfderiv I 𝓘(ℝ, ℝ × ℝ) Q x v).1 = mfderiv I 𝓘(ℝ, ℝ) P x v := fun x v =>
    mfderiv_apply_fst_of_prodSpace (hQd x) v
  have hQ2 : ∀ x v, (mfderiv I 𝓘(ℝ, ℝ × ℝ) Q x v).2 =
      deriv χ (B x) * mvfderiv I B x v := by
    intro x v
    rw [mfderiv_apply_snd_of_prodSpace (hQd x) v]
    exact mvfderiv_comp_real (hBd x) ((hχ.differentiable (by simp)) (B x)) v
  -- where the base field can be nonzero
  have hfar : ∀ x, Q x ∈ tsupport Z → P x ∈ Icc a₁ b₁ ∧ -(r / 2) < B x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hZsupp hx
    refine ⟨hζsupp h1, ?_⟩
    by_contra hcon
    have h3 := (hκsupp h2).1
    change (c₀ - 1 / 2) / 2 ≤ sideProfile r (B x) at h3
    rw [sideProfile_of_le hr (not_lt.mp hcon)] at h3
    linarith
  -- local lifts
  have Hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ Xloc : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x : M ↦ (⟨x, Xloc x⟩ : TangentBundle I M)) U ∧
      (∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ × ℝ) Q x (Xloc x) = Z (Q x)) ∧
      (∀ x ∈ U, Z (Q x) = 0 → Xloc x = 0) := by
    intro x₀
    by_cases hx₀ : Q x₀ ∈ tsupport Z
    · obtain ⟨hPx₀, hBx₀⟩ := hfar x₀ hx₀
      by_cases hsmall : |B x₀| < r
      · let G : M → ℝ × ℝ := fun y => (P y, B y)
        have hG : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ G := hP.prodMk_space hB
        let W : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y :=
          fun y => (ζ y.1 * κ (χ y.2), (0 : ℝ))
        have hW : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
            (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
          contMDiff_vectorSpace_iff_contDiff.mpr
            (((hζ.comp contDiff_fst).mul (hκ.comp (hχ.comp contDiff_snd))).prodMk contDiff_const)
        obtain ⟨U, hU, Xl, hXl, hrelG, hzeroG⟩ := exists_local_smoothDerivativeLift_of_surjective
          G hG W hW x₀ (hsPB x₀ hPx₀ hsmall)
        refine ⟨U, hU, Xl, hXl, fun x hx => ?_, fun x hx h => hzeroG x hx h⟩
        have hG1 : (mfderiv I 𝓘(ℝ, ℝ × ℝ) G x (Xl x)).1 = mfderiv I 𝓘(ℝ, ℝ) P x (Xl x) :=
          mfderiv_apply_fst_of_prodSpace ((hG x).mdifferentiableAt (by simp)) _
        have hG2 : (mfderiv I 𝓘(ℝ, ℝ × ℝ) G x (Xl x)).2 = mvfderiv I B x (Xl x) :=
          mfderiv_apply_snd_of_prodSpace ((hG x).mdifferentiableAt (by simp)) _
        have hr1 := hrelG x hx
        apply Prod.ext
        · rw [hQ1, ← hG1, hr1]
        · rw [hQ2, ← hG2, hr1]
          change deriv χ (B x) * 0 = 0
          rw [mul_zero]
      · have hBr : r ≤ B x₀ := by
          rcases le_abs'.mp (not_lt.mp hsmall) with h | h
          · linarith
          · exact h
        let W' : (s : ℝ) → TangentSpace 𝓘(ℝ, ℝ) s := fun s => ζ s * κ (1 / 2)
        have hW' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
            (fun s ↦ (⟨s, W' s⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
          contMDiff_vectorSpace_iff_contDiff.mpr (hζ.mul contDiff_const)
        obtain ⟨U, hU, Xl, hXl, hrelP, hzeroP⟩ := exists_local_smoothDerivativeLift_of_surjective
          P hP W' hW' x₀ (hsP x₀ hPx₀ (by linarith))
        have hopen : IsOpen {x : M | r / 2 < B x} := isOpen_lt continuous_const hB.continuous
        refine ⟨U ∩ {x | r / 2 < B x}, inter_mem hU (hopen.mem_nhds (by
          change r / 2 < B x₀
          linarith)), Xl, hXl.mono inter_subset_left, fun x hx => ?_, fun x hx h => ?_⟩
        · have hχx : χ (B x) = 1 / 2 := sideProfile_of_ge hr hx.2.le
          have hBx : r / 2 < B x := hx.2
          have hd0 : deriv χ (B x) = 0 := deriv_sideProfile_eq_zero hr (by
            rw [abs_of_pos (by linarith)]
            exact hBx)
          apply Prod.ext
          · rw [hQ1, hrelP x hx.1]
            change ζ (P x) * κ (1 / 2) = ζ (P x) * κ (χ (B x))
            rw [hχx]
          · rw [hQ2, hd0, zero_mul]
        · have hχx : χ (B x) = 1 / 2 := sideProfile_of_ge hr hx.2.le
          apply hzeroP x hx.1
          have h1 := congrArg Prod.fst h
          change ζ (P x) * κ (χ (B x)) = 0 at h1
          rw [hχx] at h1
          exact h1
    · have hopen : IsOpen (Q ⁻¹' (tsupport Z)ᶜ) :=
        (isClosed_tsupport Z).isOpen_compl.preimage hQ.continuous
      refine ⟨Q ⁻¹' (tsupport Z)ᶜ, hopen.mem_nhds hx₀, fun _ => 0,
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).contMDiffOn,
        fun x hx => ?_, fun _ _ _ => rfl⟩
      rw [map_zero]
      exact (image_eq_zero_of_notMem_tsupport hx).symm
  obtain ⟨X, hrel, hXsupp⟩ := exists_smoothDerivativeLift_of_local Q hQ.continuous Z Hloc
  have hXc : IsCompact (tsupport X) := by
    refine hC.of_isClosed_subset (isClosed_tsupport X) (fun x hx => ?_)
    obtain ⟨h1, h2⟩ := hfar x (hXsupp hx)
    exact ⟨h1, by linarith⟩
  let D := compactSupportFlowDiffeomorph X X.contMDiff hXc
  have hmap : ∀ t x, Q (D t x) = compactSupportFlowDiffeomorph Z hZs hZc t (Q x) :=
    compactSupportFlowDiffeomorph_map_of_mfderiv_eq Q (hQ.of_le (by norm_num)) X X.contMDiff hXc
      Z hZs hZc hrel
  refine ⟨D, contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_zero X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_trans X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_symm X X.contMDiff hXc, fun t x => ?_, fun t x => ?_,
    fun x hx hPx t ht => ?_⟩
  · have h2 : χ (B (D t x)) = χ (B x) := by
      have h := congrArg Prod.snd (hmap t x)
      change χ (B (D t x)) = (compactSupportFlowDiffeomorph Z hZs hZc t (Q x)).2 at h
      rw [h, flow_snd_eq_of_snd_eq_zero Z hZs hZc (fun _ => rfl)]
    rw [← sideProfile_nonneg_iff hr, ← sideProfile_nonneg_iff hr (u := B x)]
    change 0 ≤ χ (B (D t x)) ↔ 0 ≤ χ (B x)
    rw [h2]
  · have h := congrArg Prod.snd (hmap t x)
    change χ (B (D t x)) = (compactSupportFlowDiffeomorph Z hZs hZc t (Q x)).2 at h
    change χ (B (D t x)) = χ (B x)
    rw [h, flow_snd_eq_of_snd_eq_zero Z hZs hZc (fun _ => rfl)]
  · have hw : χ (B x) ∈ Icc c₀ (1 / 2) :=
      ⟨sideProfile_monotone hr hx, sideProfile_le_half r (B x)⟩
    have hone : ∀ s ∈ Ioo (a₀ - η) (b₀ + η), Z (s, χ (B x)) = ((1 : ℝ), (0 : ℝ)) := by
      intro s hs
      change ((ζ s * κ (χ (B x)), (0 : ℝ)) : ℝ × ℝ) = (1, 0)
      rw [hζone s hs, hκone _ hw, mul_one]
    have hfl := flow_fst_eq_of_bump_eq_one Z hZs hZc hone
      (⟨by linarith [hPx.1], by linarith [hPx.2]⟩ : P x ∈ Ioo (a₀ - η) (b₀ + η))
      (show P x + (t - P x) ∈ Ioo (a₀ - η) (b₀ + η) from
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have h := congrArg Prod.fst (hmap (t - P x) x)
    change P (D (t - P x) x) = (compactSupportFlowDiffeomorph Z hZs hZc (t - P x) (Q x)).1 at h
    rw [h]
    change (compactSupportFlowDiffeomorph Z hZs hZc (t - P x) (P x, χ (B x))).1 = t
    rw [hfl]
    ring


end Core

section Trivialization

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

open DifferentialGeometry.Manifold.RegularLevel

/-- **Proper submersions with a side boundary are trivial over intervals, preserving `B` near the
side boundary.** The conclusion of `exists_sideBoundary_interval_trivialization`, and moreover:
for some `r' > 0`, `B (Θ (x, t)) = B x` whenever `B x < r'`; `Θ` is the restriction of a smooth
flow `D` of diffeomorphisms of an open `U ⊇ F₀` (`Θ (x, t) = D t x`) which translates `P` on
`{P = 0, B ≥ -r'}` (also beyond the side boundary) and preserves `B` on `{|B| < r'}`.

The original statement: Let `P` be a
submersion on `Ω = {a < P < b, B ≥ 0}`, also on its side boundary (`(P, B)` a submersion along
`{B = 0}`), and proper on `{B ≥ 0}` over `(a, b)`. For `0 ∈ (a₀, b₀)`, `[a₀, b₀] ⊂ (a, b)`, the
fibre `F₀ = {P = 0, B ≥ 0}` (lane SUB-BDY's manifold-with-boundary structure) gives a smooth
injective map `Θ : F₀ × (a₀, b₀) → Y` over the identity of `(a₀, b₀)`, equal to the inclusion on
`F₀ × {0}`, whose image is `{a₀ < P < b₀, B ≥ 0}` and whose inverse is `y ↦ (R y, P y)` for a map
`R` smooth on an open neighbourhood of that set. -/
theorem exists_sideBoundary_interval_trivialization_preserving {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ ℝ)
    {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B) {a b : ℝ}
    (hreg : ∀ y, P y ∈ Ioo a b → 0 ≤ B y → Surjective (mfderiv I 𝓘(ℝ, ℝ) P y))
    (hregb : ∀ y, P y ∈ Ioo a b → B y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y}))
    {a₀ b₀ : ℝ} (ha₀ : a < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < b) :
    letI := regularSublevelChartedSpace (Ψ := P) (B := B) hdim hP hB
      (fun y hy hBy => hreg y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
      (fun y hy hBy => hregb y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
    let Q : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
    ∃ Θ : {y : Y // P y = 0 ∧ 0 ≤ B y} × Q → Y,
      ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ Θ ∧
      (∀ p, P (Θ p) = p.2 ∧ 0 ≤ B (Θ p)) ∧
      (∀ x, Θ (x, ⟨0, h0⟩) = x) ∧ Injective Θ ∧
      (∃ r' : ℝ, 0 < r' ∧ (∀ p, B p.1 < r' → B (Θ p) = B p.1) ∧
        ∃ (U : Set Y) (hU : IsOpen U),
        ∃ D : ℝ → (⟨U, hU⟩ : TopologicalSpace.Opens Y) ≃ₘ⟮I, I⟯ (⟨U, hU⟩ : TopologicalSpace.Opens Y),
          ContMDiff (𝓘(ℝ).prod I) I ∞
            (fun q : ℝ × (⟨U, hU⟩ : TopologicalSpace.Opens Y) => D q.1 q.2) ∧
          D 0 = Diffeomorph.refl I _ ∞ ∧ (∀ s t, (D s).trans (D t) = D (s + t)) ∧
          (∀ p, ∃ hp : (p.1 : Y) ∈ U, Θ p = (D (p.2 : ℝ) ⟨p.1, hp⟩ : Y)) ∧
          (∀ z : (⟨U, hU⟩ : TopologicalSpace.Opens Y), P z = 0 → -r' ≤ B z →
            ∀ t ∈ Ioo a₀ b₀, P (D t z) = t) ∧
          ∀ (z : (⟨U, hU⟩ : TopologicalSpace.Opens Y)) (t : ℝ), |B z| < r' → B (D t z) = B z) ∧
      ∃ O : Set Y, IsOpen O ∧ (∀ y, P y ∈ Ioo a₀ b₀ → 0 ≤ B y → y ∈ O) ∧
        ∃ R : Y → Y, ContMDiffOn I I ∞ R O ∧
          ∀ y (hy : P y ∈ Ioo a₀ b₀), 0 ≤ B y → ∃ hR : P (R y) = 0 ∧ 0 ≤ B (R y),
            Θ (⟨R y, hR⟩, ⟨P y, hy⟩) = y := by
  let _ := regularSublevelChartedSpace (Ψ := P) (B := B) hdim hP hB
    (fun y hy hBy => hreg y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
    (fun y hy hBy => hregb y (by rw [hy]; exact ⟨ha₀.trans h0.1, h0.2.trans hb₀⟩) hBy)
  let Q : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
  classical
  set a₁ := (a + a₀) / 2 with ha₁
  set b₁ := (b₀ + b) / 2 with hb₁
  obtain ⟨U, hUo, hKU, r, hr, hC, hsP, hsPB⟩ := exists_sideBoundary_margin hP hB
    (by linarith : a < a₁) (by linarith : b₁ < b) hreg hregb hprop
  let U₀ : TopologicalSpace.Opens Y := ⟨U, hUo⟩
  have : SigmaCompactSpace U₀ := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I hUo)
  have hP' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : U₀ => P x) := hP.comp contMDiff_subtype_val
  have hB' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : U₀ => B x) := hB.comp contMDiff_subtype_val
  have hC' : IsCompact {x : U₀ | P x ∈ Icc a₁ b₁ ∧ -r ≤ B x} := by
    rw [Subtype.isCompact_iff]
    convert hC using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hx⟩
      exact ⟨⟨y, hy⟩, hx, rfl⟩
  obtain ⟨D, hDs, hD0, hDtr, -, hinv, hχinv, htr⟩ := exists_sideBoundary_transport_preserving hP' hB'
    (a₁ := a₁) (a₀ := a₀) (b₀ := b₀) (b₁ := b₁) (by linarith) (by linarith [h0.1, h0.2])
    (by linarith) hr hC'
    (fun x _ _ => surjective_mfderiv_comp_opens_val U₀ x ((hP x).mdifferentiableAt (by simp))
      (hsP x x.2))
    (fun x _ hx => surjective_mfderiv_comp_opens_val U₀ x
      (((hP.prodMk_space hB) x).mdifferentiableAt (by simp)) (hsPB x x.2 hx))
  have hIcc : ∀ t ∈ Ioo a₀ b₀, t ∈ Icc a₁ b₁ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem : ∀ x : {y : Y // P y = 0 ∧ 0 ≤ B y}, (x : Y) ∈ U := fun x =>
    hKU x (by rw [x.2.1]; exact hIcc 0 h0) x.2.2
  have hDapp : ∀ s t (x : U₀), D t (D s x) = D (s + t) x := fun s t x =>
    congrArg (fun F : U₀ ≃ₘ⟮I, I⟯ U₀ => F x) (hDtr s t)
  let incl : {y : Y // P y = 0 ∧ 0 ≤ B y} × Q → U₀ := fun p => ⟨p.1, hmem p.1⟩
  have hincl : ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ incl := by
    apply (ContMDiff.subtypeVal_comp_iff U₀ incl).mp
    exact (regularSublevel_contMDiff_val hdim hP hB _ _).comp contMDiff_fst
  let Θ : {y : Y // P y = 0 ∧ 0 ≤ B y} × Q → Y := fun p => (D (p.2 : ℝ) (incl p) : Y)
  have hP0 : ∀ x : {y : Y // P y = 0 ∧ 0 ≤ B y}, P x = 0 := fun x => x.2.1
  have hΘP : ∀ p, P (Θ p) = p.2 := by
    intro p
    have h := htr (incl p) (by have := p.1.2.2; linarith) (by
      change P p.1 ∈ Icc a₀ b₀
      rw [hP0]
      exact ⟨h0.1.le, h0.2.le⟩) p.2 ⟨p.2.2.1.le, p.2.2.2.le⟩
    change P (D ((p.2 : ℝ) - P p.1) (incl p) : Y) = p.2 at h
    rw [hP0, sub_zero] at h
    exact h
  have hpres : ∀ (z : U₀) (t : ℝ), |B z| < r / 4 → B (D t z) = B z := fun z t hz =>
    eq_of_sideProfile_eq hr (by linarith) (hχinv t z)
  refine ⟨Θ, ?_, fun p => ⟨hΘP p, (hinv _ _).2 p.1.2.2⟩, fun x => ?_, ?_,
    ⟨r / 4, by positivity, fun p hp => hpres (incl p) _ (by
        rw [abs_lt]
        exact ⟨by linarith [p.1.2.2], hp⟩),
      U, hUo, D, hDs, hD0, hDtr, fun p => ⟨hmem p.1, rfl⟩, fun z hz hBz t ht => ?_, hpres⟩, U, hUo,
    fun y hy hBy => hKU y (hIcc _ hy) hBy, ?_⟩
  · exact contMDiff_subtype_val.comp (hDs.comp ((contMDiff_subtype_val.comp contMDiff_snd).prodMk
      hincl))
  · change (D 0 (incl (x, ⟨0, h0⟩)) : Y) = x
    rw [hD0]
    rfl
  · intro p q hpq
    have ht : p.2 = q.2 := Subtype.ext ((hΘP p).symm.trans ((congrArg P hpq).trans (hΘP q)))
    have hx : incl p = incl q := by
      have h1 : D (p.2 : ℝ) (incl p) = D (p.2 : ℝ) (incl q) := by
        apply Subtype.ext
        change Θ p = (D (p.2 : ℝ) (incl q) : Y)
        rw [hpq, ht]
      exact (D (p.2 : ℝ)).injective h1
    have hx' : (p.1 : Y) = q.1 := congrArg (fun u : U₀ => (u : Y)) hx
    exact Prod.ext (Subtype.ext hx') ht
  · have h := htr z hBz (by
      rw [hz]
      exact ⟨h0.1.le, h0.2.le⟩) t ⟨ht.1.le, ht.2.le⟩
    change P (D (t - P z) z : Y) = t at h
    rw [hz, sub_zero] at h
    exact h
  · let R : Y → Y := fun y => if hy : y ∈ U then (D (-P y) ⟨y, hy⟩ : Y) else y
    refine ⟨R, fun y hy => ?_, fun y hy hBy => ?_⟩
    · have hne : Nonempty U₀ := ⟨⟨y, hy⟩⟩
      let φ := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U₀ hne
      have hφ : ContMDiffAt I I ∞ φ.symm y := by
        apply φ.symm.contMDiffOn.contMDiffAt
        apply φ.open_target.mem_nhds
        rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
        exact hy
      have hg : ContMDiffAt I I ∞ (fun z => (D (-P z) (φ.symm z) : Y)) y :=
        contMDiff_subtype_val.contMDiffAt.comp y ((hDs.contMDiffAt).comp y
          ((hP.neg y).prodMk hφ))
      apply ContMDiffAt.contMDiffWithinAt
      apply hg.congr_of_eventuallyEq
      filter_upwards [hUo.mem_nhds hy] with z hz
      rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I U₀ hne hz]
      simp only [R, dite_eq_left hz]
    · have hyU : y ∈ U := hKU y (hIcc _ hy) hBy
      have hRy : R y = (D (-P y) ⟨y, hyU⟩ : Y) := by simp only [R, dite_eq_left hyU]
      have hPR : P (R y) = 0 := by
        have h := htr ⟨y, hyU⟩ (by linarith) ⟨hy.1.le, hy.2.le⟩ 0 ⟨h0.1.le, h0.2.le⟩
        rw [hRy]
        change P (D (0 - P y) ⟨y, hyU⟩ : Y) = 0 at h
        rw [zero_sub] at h
        exact h
      have hBR : 0 ≤ B (R y) := by
        rw [hRy]
        exact (hinv (-P y) ⟨y, hyU⟩).2 hBy
      refine ⟨⟨hPR, hBR⟩, ?_⟩
      change (D (P y) (incl (⟨R y, ⟨hPR, hBR⟩⟩, ⟨P y, hy⟩)) : Y) = y
      have hi : incl (⟨R y, ⟨hPR, hBR⟩⟩, ⟨P y, hy⟩) = D (-P y) ⟨y, hyU⟩ :=
        Subtype.ext hRy
      rw [hi, hDapp, neg_add_cancel, hD0]
      rfl


end Trivialization

end DifferentialGeometry.Topology.Ehresmann
