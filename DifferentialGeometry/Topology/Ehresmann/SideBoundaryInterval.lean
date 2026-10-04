import DifferentialGeometry.Topology.Ehresmann.SublevelTransport
import DifferentialGeometry.Topology.Ehresmann.FaceTransport
import DifferentialGeometry.Topology.Ehresmann.HorizontalLift
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice

/-!
# Proper submersions with a side boundary are trivial over intervals

Let `P, B : Y → ℝ` be smooth on a boundaryless manifold. The region `Ω = {a < P < b, 0 ≤ B}` is a
manifold with boundary `{B = 0}` (a "side boundary", transverse to the fibres of `P`). Assume
`P|Ω` is proper onto `(a, b)`, a submersion on `Ω`, and also a submersion on the boundary, i.e.
`(P, B)` is a submersion along `{B = 0}`. Then `P|Ω` is trivial over every compact subinterval.

* `sideProfile`: a smooth monotone profile `χ` of the sign of its argument, constant away from a
  band around `0`.
* `exists_sideBoundary_transport` (core, on a manifold `M`): the lift of `(ζ(s) κ(w), 0)` through
  `Q = (P, χ ∘ B)` exists by local lifts through `(P, B)` (near the side boundary, keeping
  `dB = 0`) and through `P` (away from it), glued by partitions of unity; its flow preserves
  `χ ∘ B`, hence `{B ≥ 0}`, and translates `P` (`flow_fst_eq_of_bump_eq_one`,
  `flow_snd_eq_of_snd_eq_zero`).
* `exists_sideBoundary_margin`: properness and the two submersion conditions give a relatively
  compact open neighbourhood of `P⁻¹[a₁, b₁] ∩ {B ≥ 0}` and a band width `r` for the core.
* `exists_sideBoundary_interval_trivialization`: the fibre `F₀ = {P = 0, B ≥ 0}` (lane SUB-BDY's
  manifold-with-boundary structure) times `(a₀, b₀)` maps smoothly and injectively onto
  `{a₀ < P < b₀, B ≥ 0}` over the identity, with inverse `y ↦ (R y, P y)` for a map `R` smooth on
  an open neighbourhood.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

section Profile

/-- The side profile `χ_r(u) = smoothTransition (u / r + 1/2) - 1/2`: smooth, monotone, of the
sign of `u`, equal to `-1/2` for `u ≤ -r/2` and to `1/2` for `u ≥ r/2`. -/
def sideProfile (r u : ℝ) : ℝ := Real.smoothTransition (u / r + 1 / 2) - 1 / 2

theorem contDiff_sideProfile (r : ℝ) : ContDiff ℝ ∞ (sideProfile r) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const r).add contDiff_const)).sub
    contDiff_const

theorem sideProfile_nonneg_iff {r : ℝ} (hr : 0 < r) {u : ℝ} : 0 ≤ sideProfile r u ↔ 0 ≤ u := by
  unfold sideProfile
  constructor
  · intro h
    by_contra hu
    have harg : u / r + 1 / 2 < 1 / 2 := by
      have : u / r < 0 := div_neg_of_neg_of_pos (lt_of_not_ge hu) hr
      linarith
    linarith [smoothTransition_lt_half harg]
  · intro hu
    have harg : 1 / 2 ≤ u / r + 1 / 2 := by
      have : 0 ≤ u / r := div_nonneg hu hr.le
      linarith
    have := Real.smoothTransition.monotone harg
    rw [DifferentialGeometry.Topology.smoothTransition_half] at this
    linarith

theorem sideProfile_le_half (r u : ℝ) : sideProfile r u ≤ 1 / 2 := by
  unfold sideProfile
  linarith [Real.smoothTransition.le_one (u / r + 1 / 2)]

theorem sideProfile_of_le {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : u ≤ -(r / 2)) :
    sideProfile r u = -(1 / 2) := by
  unfold sideProfile
  rw [Real.smoothTransition.zero_of_nonpos]
  · norm_num
  · have : u / r ≤ -(1 / 2) := by
      rw [div_le_iff₀ hr]
      linarith
    linarith

theorem sideProfile_of_ge {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : r / 2 ≤ u) :
    sideProfile r u = 1 / 2 := by
  unfold sideProfile
  rw [Real.smoothTransition.one_of_one_le]
  · norm_num
  · have : 1 / 2 ≤ u / r := by
      rw [le_div_iff₀ hr]
      linarith
    linarith

theorem neg_half_lt_of_sideProfile_ge {r : ℝ} (hr : 0 < r) {u : ℝ}
    (hu : -(1 / 4) ≤ sideProfile r u) : -(r / 2) < u := by
  by_contra h
  rw [sideProfile_of_le hr (not_lt.mp h)] at hu
  linarith

theorem deriv_sideProfile_eq_zero {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : r / 2 < |u|) :
    deriv (sideProfile r) u = 0 := by
  rcases lt_abs.mp hu with h | h
  · have hev : sideProfile r =ᶠ[𝓝 u] fun _ => 1 / 2 := by
      filter_upwards [lt_mem_nhds h] with v hv
      unfold sideProfile
      rw [Real.smoothTransition.one_of_one_le]
      · norm_num
      · have : 1 / 2 ≤ v / r := by
          rw [le_div_iff₀ hr]
          linarith
        linarith
    rw [hev.deriv_eq, deriv_const]
  · have hev : sideProfile r =ᶠ[𝓝 u] fun _ => -(1 / 2) := by
      filter_upwards [gt_mem_nhds (show u < -(r / 2) by linarith)] with v hv
      exact sideProfile_of_le hr hv.le
    rw [hev.deriv_eq, deriv_const]

end Profile

section Lift

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
/-- Chain rule for a real function after a real-valued map. -/
theorem mvfderiv_comp_real {B : M → ℝ} {x : M} (hB : MDifferentiableAt I 𝓘(ℝ, ℝ) B x)
    {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (B x)) (v : TangentSpace I x) :
    mvfderiv I (fun y => g (B y)) x v = deriv g (B x) * mvfderiv I B x v := by
  have hgm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (B x) := hg.mdifferentiableAt
  have hg' : mvfderiv 𝓘(ℝ, ℝ) g (B x) = fderiv ℝ g (B x) := by
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    rfl
  have hc := mvfderiv_comp_apply x hgm hB v
  change mvfderiv I (g ∘ B) x v = _
  rw [hc, hg']
  have h := fderiv_eq_smul_deriv (f := g) (x := B x) (mvfderiv I B x v)
  rw [smul_eq_mul, mul_comm] at h
  exact h

end Lift

section PlaneFlow

/-- The flow of a compactly supported field on `ℝ × ℝ` equal to `(1, 0)` on a horizontal segment
translates the first coordinate along that segment. -/
theorem flow_fst_eq_of_bump_eq_one
    (Z : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y)
    (hZ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))))
    (hc : IsCompact (tsupport Z)) {A B w s₀ t : ℝ}
    (hone : ∀ r ∈ Ioo A B, Z (r, w) = ((1 : ℝ), (0 : ℝ)))
    (h₀ : s₀ ∈ Ioo A B) (h₁ : s₀ + t ∈ Ioo A B) :
    compactSupportFlowDiffeomorph Z hZ hc t (s₀, w) = (s₀ + t, w) := by
  let γ : ℝ → ℝ × ℝ := fun r ↦ (s₀ + r, w)
  have hγ : IsMIntegralCurveOn γ Z (Ioo (A - s₀) (B - s₀)) := by
    intro r hr
    have hyr : s₀ + r ∈ Ioo A B := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    change HasMFDerivWithinAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) γ (Ioo (A - s₀) (B - s₀)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (s₀ + r, w)))
    rw [hone _ hyr]
    exact ((((hasDerivAt_id r).const_add s₀).prodMk (hasDerivAt_const r w)).hasDerivWithinAt
      ).hasFDerivWithinAt.hasMFDerivWithinAt
  let hcomplete := exists_globalIntegralCurve_of_compactSupport Z hZ hc
  have hzero : (0 : ℝ) ∈ Ioo (A - s₀) (B - s₀) := ⟨by linarith [h₀.1], by linarith [h₀.2]⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero
    (hZ.of_le (by norm_num)) ((curveAt_integralCurve Z hcomplete (s₀, w)).isMIntegralCurveOn _) hγ
    (by simpa only [γ, add_zero] using curveAt_zero Z hcomplete (s₀, w))
  have hh := heq (show t ∈ Ioo (A - s₀) (B - s₀) from
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩)
  change curveAt Z hcomplete (s₀, w) t = (s₀ + t, w)
  exact hh

/-- The flow of a compactly supported field on `ℝ × ℝ` with vanishing second component keeps
the second coordinate. -/
theorem flow_snd_eq_of_snd_eq_zero
    (Z : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y)
    (hZ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))))
    (hc : IsCompact (tsupport Z)) (hsnd : ∀ y, (Z y).2 = 0) (t : ℝ) (y : ℝ × ℝ) :
    (compactSupportFlowDiffeomorph Z hZ hc t y).2 = y.2 := by
  have hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) 1 (Prod.snd : ℝ × ℝ → ℝ) :=
    (contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × ℝ → ℝ)).contMDiff
  have hrel : ∀ x : ℝ × ℝ, mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) Prod.snd x (Z x) =
      (fun _ : ℝ ↦ (0 : TangentSpace 𝓘(ℝ, ℝ) _)) (Prod.snd x) := by
    intro x
    rw [mfderiv_eq_fderiv, fderiv_snd]
    exact hsnd x
  have h0c : IsCompact (tsupport (fun _ : ℝ ↦ (0 : ℝ))) := by
    have he : tsupport (fun _ : ℝ ↦ (0 : ℝ)) = ∅ := tsupport_eq_empty_iff.mpr rfl
    rw [he]
    exact isCompact_empty
  have h := compactSupportFlowDiffeomorph_map_of_mfderiv_eq Prod.snd hsm Z hZ hc
    (fun _ : ℝ ↦ (0 : TangentSpace 𝓘(ℝ, ℝ) _))
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) h0c hrel t y
  rw [h, compactSupportFlowDiffeomorph_zeroField]
  rfl

end PlaneFlow

section Core

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **Side-boundary transport (core).** Let `P, B : M → ℝ` be smooth, `[a₀, b₀] ⊂ (a₁, b₁)`,
`r > 0`, the set `{P ∈ [a₁, b₁], B ≥ -r}` compact, `P` a submersion on it and `(P, B)` a
submersion on its part `{|B| < r}`. Then there is a smooth flow `D` of diffeomorphisms of `M`
preserving `{B ≥ 0}` (in both directions) and translating `P` on `{B ≥ 0} ∩ P⁻¹[a₀, b₀]`. -/
theorem exists_sideBoundary_transport {P B : M → ℝ}
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
      ∀ x, 0 ≤ B x → P x ∈ Icc a₀ b₀ → ∀ t ∈ Icc a₀ b₀, P (D (t - P x) x) = t := by
  classical
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
  let κb : ContDiffBump (1 / 4 : ℝ) := ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩
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
  have hκone : ∀ w ∈ Icc (0 : ℝ) (1 / 2), κ w = 1 := by
    intro w hw
    apply κb.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(3 / 8 : ℝ) ≤ w - 1 / 4 ∧ w - 1 / 4 ≤ 3 / 8
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
  have hκsupp : tsupport κ ⊆ Icc (-(1 / 4)) (3 / 4) := by
    intro w hw
    have h : w ∈ Metric.closedBall (1 / 4 : ℝ) (1 / 2) := by
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
    exact ⟨hζsupp h1, neg_half_lt_of_sideProfile_ge hr (hκsupp h2).1⟩
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
    compactSupportFlowDiffeomorph_symm X X.contMDiff hXc, fun t x => ?_, fun x hx hPx t ht => ?_⟩
  · have h2 : χ (B (D t x)) = χ (B x) := by
      have h := congrArg Prod.snd (hmap t x)
      change χ (B (D t x)) = (compactSupportFlowDiffeomorph Z hZs hZc t (Q x)).2 at h
      rw [h, flow_snd_eq_of_snd_eq_zero Z hZs hZc (fun _ => rfl)]
    rw [← sideProfile_nonneg_iff hr, ← sideProfile_nonneg_iff hr (u := B x)]
    change 0 ≤ χ (B (D t x)) ↔ 0 ≤ χ (B x)
    rw [h2]
  · have hw : χ (B x) ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨(sideProfile_nonneg_iff hr).2 hx, sideProfile_le_half r (B x)⟩
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

section Margin

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_lowerBound_of_isCompact {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsCompact A) {f : X → ℝ} (hf : ContinuousOn f A) (hpos : ∀ x ∈ A, 0 < f x) :
    ∃ m > 0, ∀ x ∈ A, m ≤ f x := by
  rcases A.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [h] at hx
    exact absurd hx (notMem_empty x)
  · obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn h hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]

omit [FiniteDimensional ℝ E] in
/-- The points where a smooth map to a finite-dimensional space is a submersion form an open
set. -/
theorem isOpen_setOf_surjective_mfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : Y → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    IsOpen {y | Surjective (mfderiv I 𝓘(ℝ, F) f y)} :=
  (isOpen_spatial_surjective_mfderiv (I := I) (fun p : Y × ℝ => f p.1)
    (hf.comp contMDiff_fst)).preimage
    (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Y] in
/-- Submersivity is unchanged by restriction to an open subset. -/
theorem surjective_mfderiv_comp_opens_val {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : TopologicalSpace.Opens Y) {f : Y → F} (x : U)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hs : Surjective (mfderiv I 𝓘(ℝ, F) f x)) :
    Surjective (mfderiv I 𝓘(ℝ, F) (fun y : U => f y) x) := by
  intro v
  obtain ⟨w, hw⟩ := hs v
  refine ⟨w, ?_⟩
  have hc := mfderiv_comp (I' := I) x hf (hasMFDerivAt_subtype_val (I := I) U x).mdifferentiableAt
  change mfderiv I 𝓘(ℝ, F) (f ∘ Subtype.val) x w = v
  rw [hc, mfderiv_subtype_val (I := I) U x]
  exact hw

variable [T2Space Y] [SigmaCompactSpace Y]

/-- **Margins near a side boundary.** If `P` is a submersion on `{a < P < b, B ≥ 0}`, `(P, B)` a
submersion on `{a < P < b, B = 0}` and `P` is proper on `{B ≥ 0}` over `(a, b)`, then for
`[a₁, b₁] ⊂ (a, b)` there are an open `U ⊇ P⁻¹[a₁, b₁] ∩ {B ≥ 0}` and `r > 0` such that
`U ∩ P⁻¹[a₁, b₁] ∩ {B ≥ -r}` is compact, `P` is a submersion on `U` and `(P, B)` is a submersion
on `U ∩ {|B| < r}`. -/
theorem exists_sideBoundary_margin {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P)
    (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B) {a b a₁ b₁ : ℝ} (ha : a < a₁) (hb : b₁ < b)
    (hreg : ∀ y, P y ∈ Ioo a b → 0 ≤ B y → Surjective (mfderiv I 𝓘(ℝ, ℝ) P y))
    (hregb : ∀ y, P y ∈ Ioo a b → B y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y})) :
    ∃ U : Set Y, IsOpen U ∧ (∀ y, P y ∈ Icc a₁ b₁ → 0 ≤ B y → y ∈ U) ∧ ∃ r > 0,
      IsCompact {y | y ∈ U ∧ P y ∈ Icc a₁ b₁ ∧ -r ≤ B y} ∧
      (∀ y ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) P y)) ∧
      (∀ y ∈ U, |B y| < r → Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  have hsub : Icc a₁ b₁ ⊆ Ioo a b := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hK := hprop (Icc a₁ b₁) isCompact_Icc hsub
  set K := P ⁻¹' Icc a₁ b₁ ∩ {y | 0 ≤ B y} with hKdef
  let S₁ := {y | Surjective (mfderiv I 𝓘(ℝ, ℝ) P y)}
  let S₂ := {y | Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y)}
  have hS₁ : IsOpen S₁ := isOpen_setOf_surjective_mfderiv hP
  have hS₂ : IsOpen S₂ := isOpen_setOf_surjective_mfderiv (hP.prodMk_space hB)
  have hBpos : IsOpen {y | 0 < B y} := isOpen_lt continuous_const hB.continuous
  have hO : IsOpen (S₁ ∩ (S₂ ∪ {y | 0 < B y})) := hS₁.inter (hS₂.union hBpos)
  have hKO : K ⊆ S₁ ∩ (S₂ ∪ {y | 0 < B y}) := by
    intro y hy
    have hy2 : 0 ≤ B y := hy.2
    refine ⟨hreg y (hsub hy.1) hy2, ?_⟩
    rcases hy2.eq_or_lt with h | h
    · exact Or.inl (hregb y (hsub hy.1) h.symm)
    · exact Or.inr h
  obtain ⟨U, hUo, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  -- the margin from the non-submersive part of `(P, B)`
  have hA₁ : IsCompact (closure U ∩ S₂ᶜ) := hUc.inter_right hS₂.isClosed_compl
  obtain ⟨r₁, hr₁, hA₁r⟩ := exists_pos_lowerBound_of_isCompact hA₁ hB.continuous.continuousOn
    (fun y hy => by
      rcases (hUO hy.1).2 with h | h
      · exact absurd h hy.2
      · exact h)
  -- the margin from the frontier of `U`
  have hA₂ : IsCompact ((closure U \ U) ∩ P ⁻¹' Icc a₁ b₁) :=
    (hUc.diff hUo).inter_right (isClosed_Icc.preimage hP.continuous)
  obtain ⟨r₂, hr₂, hA₂r⟩ := exists_pos_lowerBound_of_isCompact hA₂ (f := fun y => -B y)
    hB.continuous.neg.continuousOn (fun y hy => by
      have hyU : y ∉ U := hy.1.2
      by_contra h
      exact hyU (hKU ⟨hy.2, by
        change 0 ≤ B y
        linarith [not_lt.mp h]⟩))
  have hr : 0 < min r₁ r₂ / 2 := half_pos (lt_min hr₁ hr₂)
  refine ⟨U, hUo, fun y h1 h2 => hKU ⟨h1, h2⟩, min r₁ r₂ / 2, hr, ?_, ?_, ?_⟩
  · have hset : {y | y ∈ U ∧ P y ∈ Icc a₁ b₁ ∧ -(min r₁ r₂ / 2) ≤ B y} =
        closure U ∩ (P ⁻¹' Icc a₁ b₁ ∩ {y | -(min r₁ r₂ / 2) ≤ B y}) := by
      ext y
      constructor
      · rintro ⟨hy, h1, h2⟩
        exact ⟨subset_closure hy, h1, h2⟩
      · rintro ⟨hy, h1, h2⟩
        refine ⟨?_, h1, h2⟩
        by_contra hyU
        have := hA₂r y ⟨⟨hy, hyU⟩, h1⟩
        change -(min r₁ r₂ / 2) ≤ B y at h2
        change r₂ ≤ -B y at this
        linarith [min_le_right r₁ r₂, lt_min hr₁ hr₂]
    rw [hset]
    exact hUc.inter_right ((isClosed_Icc.preimage hP.continuous).inter
      (isClosed_le continuous_const hB.continuous))
  · exact fun y hy => (hUO (subset_closure hy)).1
  · intro y hy hBy
    by_contra h
    have h1 := hA₁r y ⟨subset_closure hy, h⟩
    have h2 := (abs_lt.mp hBy).2
    linarith [min_le_left r₁ r₂, lt_min hr₁ hr₂]

end Margin

section Trivialization

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

open DifferentialGeometry.Manifold.RegularLevel

/-- **Proper submersions with a side boundary are trivial over intervals.** Let `P` be a
submersion on `Ω = {a < P < b, B ≥ 0}`, also on its side boundary (`(P, B)` a submersion along
`{B = 0}`), and proper on `{B ≥ 0}` over `(a, b)`. For `0 ∈ (a₀, b₀)`, `[a₀, b₀] ⊂ (a, b)`, the
fibre `F₀ = {P = 0, B ≥ 0}` (lane SUB-BDY's manifold-with-boundary structure) gives a smooth
injective map `Θ : F₀ × (a₀, b₀) → Y` over the identity of `(a₀, b₀)`, equal to the inclusion on
`F₀ × {0}`, whose image is `{a₀ < P < b₀, B ≥ 0}` and whose inverse is `y ↦ (R y, P y)` for a map
`R` smooth on an open neighbourhood of that set. -/
theorem exists_sideBoundary_interval_trivialization {d : ℕ}
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
  obtain ⟨D, hDs, hD0, hDtr, -, hinv, htr⟩ := exists_sideBoundary_transport hP' hB'
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
    have h := htr (incl p) p.1.2.2 (by
      change P p.1 ∈ Icc a₀ b₀
      rw [hP0]
      exact ⟨h0.1.le, h0.2.le⟩) p.2 ⟨p.2.2.1.le, p.2.2.2.le⟩
    change P (D ((p.2 : ℝ) - P p.1) (incl p) : Y) = p.2 at h
    rw [hP0, sub_zero] at h
    exact h
  refine ⟨Θ, ?_, fun p => ⟨hΘP p, (hinv _ _).2 p.1.2.2⟩, fun x => ?_, ?_, U, hUo,
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
        have h := htr ⟨y, hyU⟩ hBy ⟨hy.1.le, hy.2.le⟩ 0 ⟨h0.1.le, h0.2.le⟩
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
