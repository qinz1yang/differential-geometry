import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Radial gluing of a tube and a flow, finite order (lane CMS3-FLOW2, G2)

Blueprint LFR46 (A:28959–28973): the two formulas of (LFR46.1) agree on an open overlap, define a
`C^n` map, and the inverse is (LFR46.3) `x ↦ ((ℓ − τ x)/ℓ) · Φ⁻¹(φ_{τ x} x)` with the hitting time
`τ`. This is the generic gluing lemma of the smooth suite (`radial_gluing_diffeomorph`, PRIVATE in
`Comparison/Soul/NormalFlowGluing.lean`, order `∞`, `Flow ℝ M`), rewritten for ANY order `n`
and a flow given by its laws. Its hitting-time step used a smooth implicit function theorem; here
`τ` is regular by the explicit local formula `τ x = τ q + ℓ − d (φ_{τ q} x)` (on the seam the flow
moves the level at unit speed: `d (φ_{ℓ − d y} y) = ℓ`), so no IFT is needed.

* `exists_radial_gluing_diffeomorph_ofOrder`: the diffeomorphism `e`, its formula, the inner and
  outer inverse formulas, and the `C^n` regularity of every crossing-time function on `{d > ℓ}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {EM EN : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HM HN : Type*} [TopologicalSpace HM] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ EM HM} {J : ModelWithCorners ℝ EN HN}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace N] [ChartedSpace HN N]

/-- **Radial gluing of a tube and a flow, order `n`.** -/
theorem exists_radial_gluing_diffeomorph_ofOrder {n : ℕ∞ω}
    (L : N → ℝ) (hLc : Continuous L)
    (hLs : ∀ z, 0 < L z → ContMDiffAt J 𝓘(ℝ, ℝ) n L z)
    (scale : ℝ → N → N)
    (hscale : ContMDiff (𝓘(ℝ, ℝ).prod J) J n (fun z : ℝ × N => scale z.1 z.2))
    (hone : ∀ z, scale 1 z = z)
    (hmul : ∀ a b z, scale a (scale b z) = scale (a * b) z)
    (hlength : ∀ a, 0 ≤ a → ∀ z, L (scale a z) = a * L z)
    (d : M → ℝ) (hdc : Continuous d)
    {ε ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδℓ : δ < ℓ) (hε : ℓ + δ < ε)
    (Φ : PartialDiffeomorph J I N M n)
    (hsource : Φ.source = {z | L z < ε}) (htarget : Φ.target = {q | d q < ε})
    (hradius : ∀ z ∈ Φ.source, L z = d (Φ z))
    (ϕ : ℝ → M → M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun z : ℝ × M => ϕ z.1 z.2))
    (hϕ0 : ∀ x, ϕ 0 x = x) (hϕadd : ∀ s t x, ϕ (s + t) x = ϕ s (ϕ t x))
    (hinc : ∀ q, ℓ ≤ d q → ∀ t : ℝ, 0 < t → d q < d (ϕ t q))
    (hcross : ∀ q, ℓ ≤ d q → ∃! t : ℝ, d (ϕ t q) = ℓ)
    (hrad : ∀ z, ℓ - δ < L z → L z < ℓ + δ →
      ϕ (L z - ℓ) (Φ (scale (ℓ / L z) z)) = Φ z) :
    ∃ e : N ≃ₘ^n⟮J, I⟯ M,
      (∀ z, e z = if L z ≤ ℓ then Φ z else ϕ (L z - ℓ) (Φ (scale (ℓ / L z) z))) ∧
      (∀ q, d q ≤ ℓ → e.symm q = Φ.symm q) ∧
      (∀ q, ℓ ≤ d q → ∀ t, d (ϕ t q) = ℓ →
        t ≤ 0 ∧ e.symm q = scale ((ℓ - t) / ℓ) (Φ.symm (ϕ t q))) ∧
      ∀ τ' : M → ℝ, (∀ q, ℓ ≤ d q → d (ϕ (τ' q) q) = ℓ) →
        ContMDiffOn I 𝓘(ℝ, ℝ) n τ' {q | ℓ < d q} := by
  classical
  have hℓε : ℓ < ε := (lt_add_of_pos_right ℓ hδ).trans hε
  have hΦleft (z : N) (hz : z ∈ Φ.source) : Φ.symm (Φ z) = z :=
    Φ.toPartialEquiv.left_inv hz
  have hΦright (q : M) (hq : q ∈ Φ.target) : Φ (Φ.symm q) = q :=
    Φ.toPartialEquiv.right_inv hq
  let nrm : N → N := fun z => scale (ℓ / L z) z
  have hnL (z : N) (hz : 0 < L z) : L (nrm z) = ℓ := by
    change L (scale (ℓ / L z) z) = ℓ
    rw [hlength _ (div_nonneg hℓ.le hz.le), div_mul_cancel₀ _ hz.ne']
  have hnS (z : N) (hz : 0 < L z) : nrm z ∈ Φ.source := by
    rw [hsource]
    change L (nrm z) < ε
    rw [hnL z hz]
    exact hℓε
  have hdn (z : N) (hz : 0 < L z) : d (Φ (nrm z)) = ℓ :=
    (hradius _ (hnS z hz)).symm.trans (hnL z hz)
  have hscale_n (z : N) (hz : 0 < L z) : scale (L z / ℓ) (nrm z) = z := by
    dsimp only [nrm]
    rw [hmul]
    have hc : L z / ℓ * (ℓ / L z) = 1 := by
      rw [div_mul_div_cancel₀ hℓ.ne', div_self hz.ne']
    rw [hc, hone]
  have hn_scale (z : N) (hz : L z = ℓ) (r : ℝ) (hr : 0 < r) :
      nrm (scale (r / ℓ) z) = z := by
    have hlen : L (scale (r / ℓ) z) = r := by
      rw [hlength _ (div_nonneg hr.le hℓ.le), hz, div_mul_cancel₀ _ hℓ.ne']
    dsimp only [nrm]
    rw [hlen, hmul]
    have hc : ℓ / r * (r / ℓ) = 1 := by
      rw [div_mul_div_cancel₀ hr.ne', div_self hℓ.ne']
    rw [hc, hone]
  have hLinv (q : M) (hq : d q < ε) : L (Φ.symm q) = d q := by
    have hqT : q ∈ Φ.target := by rwa [htarget]
    exact (hradius (Φ.symm q) (Φ.map_target hqT)).trans (congrArg d (hΦright q hqT))
  let τ : M → ℝ := fun q => if hq : ℓ ≤ d q then (hcross q hq).choose else 0
  have hτ (q : M) (hq : ℓ ≤ d q) : d (ϕ (τ q) q) = ℓ := by
    simpa only [τ, dite_eq_left hq] using (hcross q hq).choose_spec.1
  have hτunique (q : M) (hq : ℓ ≤ d q) (t : ℝ) (ht : d (ϕ t q) = ℓ) : t = τ q := by
    simpa only [τ, dite_eq_left hq] using (hcross q hq).choose_spec.2 t ht
  have hτnonpos (q : M) (hq : ℓ ≤ d q) : τ q ≤ 0 := by
    by_contra h
    have hh := hinc q hq (τ q) (lt_of_not_ge h)
    rw [hτ q hq] at hh
    exact (not_lt_of_ge hq) hh
  have hτneg (q : M) (hq : ℓ < d q) : τ q < 0 := by
    have hn := hτnonpos q hq.le
    have hne : τ q ≠ 0 := by
      intro h
      have hh := hτ q hq.le
      rw [h, hϕ0] at hh
      exact (ne_of_gt hq) hh
    exact lt_of_le_of_ne hn hne
  let F : N → M := fun z => if L z ≤ ℓ then Φ z else ϕ (L z - ℓ) (Φ (nrm z))
  let G : M → N := fun q => if d q ≤ ℓ then Φ.symm q else
    scale ((ℓ - τ q) / ℓ) (Φ.symm (ϕ (τ q) q))
  have hFinner (z : N) (hz : L z < ℓ + δ) : F z = Φ z := by
    dsimp only [F]
    split_ifs with h
    · rfl
    · exact hrad z (by linarith only [lt_of_not_ge h, hδ]) hz
  have hFouter (z : N) (hz : ℓ < L z) : F z = ϕ (L z - ℓ) (Φ (nrm z)) :=
    ite_eq_right (not_le_of_gt hz)
  have hFdist (z : N) (hz : ℓ < L z) : ℓ < d (F z) := by
    rw [hFouter z hz]
    have hh := hinc (Φ (nrm z))
      (by simpa only [hdn z (hℓ.trans hz)] using (le_rfl : ℓ ≤ ℓ))
      (L z - ℓ) (sub_pos.mpr hz)
    rwa [hdn z (hℓ.trans hz)] at hh
  have hGF : LeftInverse G F := by
    intro z
    by_cases hz : L z ≤ ℓ
    · have hzS : z ∈ Φ.source := by rw [hsource]; exact hz.trans_lt hℓε
      have hd : d (Φ z) ≤ ℓ := by rw [← hradius z hzS]; exact hz
      change G (F z) = z
      rw [show F z = Φ z from ite_eq_left hz]
      change (if d (Φ z) ≤ ℓ then Φ.symm (Φ z) else _) = z
      rw [ite_eq_left hd, hΦleft z hzS]
    · have hz' := lt_of_not_ge hz
      have hdz := hFdist z hz'
      have ht : -(L z - ℓ) = τ (F z) := hτunique (F z) hdz.le _ (by
        rw [hFouter z hz', ← hϕadd, neg_add_cancel, hϕ0]
        exact hdn z (hℓ.trans hz'))
      change (if d (F z) ≤ ℓ then _ else _) = z
      rw [ite_eq_right (not_le_of_gt hdz), ← ht, hFouter z hz', ← hϕadd,
        neg_add_cancel, hϕ0, hΦleft _ (hnS z (hℓ.trans hz'))]
      have hc : (ℓ - -(L z - ℓ)) / ℓ = L z / ℓ := by ring
      rw [hc]
      exact hscale_n z (hℓ.trans hz')
  have hFG : RightInverse G F := by
    intro q
    by_cases hq : d q ≤ ℓ
    · have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans_lt hℓε
      have hz : L (Φ.symm q) ≤ ℓ := by rw [hLinv q (hq.trans_lt hℓε)]; exact hq
      change F (if d q ≤ ℓ then _ else _) = q
      rw [ite_eq_left hq]
      change (if L (Φ.symm q) ≤ ℓ then _ else _) = q
      rw [ite_eq_left hz, hΦright q hqT]
    · have hq' := lt_of_not_ge hq
      let z := Φ.symm (ϕ (τ q) q)
      have hyT : ϕ (τ q) q ∈ Φ.target := by
        rw [htarget]
        change d (ϕ (τ q) q) < ε
        rw [hτ q hq'.le]
        exact hℓε
      have hzL : L z = ℓ := (hLinv _ (by rw [hτ q hq'.le]; exact hℓε)).trans (hτ q hq'.le)
      have hr : ℓ < ℓ - τ q := by linarith only [hτneg q hq']
      have hGq : G q = scale ((ℓ - τ q) / ℓ) z := ite_eq_right hq
      have hLG : L (G q) = ℓ - τ q := by
        rw [hGq, hlength _ (div_nonneg (hℓ.trans hr).le hℓ.le), hzL,
          div_mul_cancel₀ _ hℓ.ne']
      rw [hFouter (G q) (by rw [hLG]; exact hr), hLG, hGq,
        hn_scale z hzL _ (hℓ.trans hr)]
      have htime : ℓ - τ q - ℓ = -τ q := by ring
      rw [htime, show Φ z = ϕ (τ q) q from hΦright _ hyT, ← hϕadd, neg_add_cancel, hϕ0]
  have hGinner (q : M) (hq : d q < ℓ + δ) : G q = Φ.symm q := by
    have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans hε
    have hz : L (Φ.symm q) < ℓ + δ := (hLinv q (hq.trans hε)).trans_lt hq
    have hh := hGF (Φ.symm q)
    rwa [hFinner _ hz, hΦright q hqT] at hh
  have hnSmooth (z : N) (hz : 0 < L z) : ContMDiffAt J J n nrm z :=
    hscale.contMDiffAt.comp z
      (((contDiffAt_const.div contDiffAt_id hz.ne').comp_contMDiffAt (hLs z hz)).prodMk
        contMDiffAt_id)
  have hFsmooth : ContMDiff J I n F := by
    intro z
    by_cases hz : L z < ℓ + δ
    · have hzS : z ∈ Φ.source := by rw [hsource]; exact hz.trans hε
      apply (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hzS)).congr_of_eventuallyEq
      filter_upwards [hLc.continuousAt (Iio_mem_nhds hz)] with w hw
      exact hFinner w hw
    · have hz' : ℓ < L z := by linarith only [le_of_not_gt hz, hδ]
      have hn := hnSmooth z (hℓ.trans hz')
      have hΦn := (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hnS z (hℓ.trans hz')))).comp z hn
      have hs : ContMDiffAt J I n (fun w => ϕ (L w - ℓ) (Φ (nrm w))) z :=
        hϕ.contMDiffAt.comp z (((hLs z (hℓ.trans hz')).sub contMDiffAt_const).prodMk hΦn)
      apply hs.congr_of_eventuallyEq
      filter_upwards [hLc.continuousAt (Ioi_mem_nhds hz')] with w hw
      exact hFouter w hw
  -- on the seam the flow moves the level at unit speed
  have hlevel (y : M) (hy1 : ℓ - δ < d y) (hy2 : d y < ℓ + δ) : d (ϕ (ℓ - d y) y) = ℓ := by
    have hyT : y ∈ Φ.target := by rw [htarget]; exact hy2.trans hε
    set w := Φ.symm y with hw
    have hwL : L w = d y := hLinv y (hy2.trans hε)
    have hwpos : 0 < L w := by rw [hwL]; linarith
    have hh := hrad w (by rw [hwL]; exact hy1) (by rw [hwL]; exact hy2)
    rw [hΦright y hyT] at hh
    have key : ϕ (ℓ - L w) (ϕ (L w - ℓ) (Φ (nrm w))) = Φ (nrm w) := by
      rw [← hϕadd, show ℓ - L w + (L w - ℓ) = 0 by ring, hϕ0]
    have hflow : ϕ (ℓ - d y) y = Φ (nrm w) := by
      rw [← key, hwL]
      congr 1
      rw [← hwL]
      exact hh.symm
    rw [hflow]
    exact hdn w hwpos
  let U : Set M := {q | 0 < d q ∧ d q < ε}
  have hU : IsOpen U := (isOpen_lt continuous_const hdc).inter (isOpen_lt hdc continuous_const)
  have hds : ContMDiffOn I 𝓘(ℝ, ℝ) n d U := by
    intro q hq
    have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.2
    have hpos : 0 < L (Φ.symm q) := by rw [hLinv q hq.2]; exact hq.1
    have hh := (hLs (Φ.symm q) hpos).comp q
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hqT))
    apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [Φ.open_target.mem_nhds hqT] with x hx
    exact (hLinv x (by rwa [htarget] at hx)).symm
  -- the crossing time is `C^n` on `{d > ℓ}` by the local formula
  have hτs (q : M) (hq' : ℓ < d q) : ContMDiffAt I 𝓘(ℝ, ℝ) n τ q := by
    have hy : d (ϕ (τ q) q) = ℓ := hτ q hq'.le
    have hflowq : ContMDiffAt I I n (fun x => ϕ (τ q) x) q :=
      hϕ.contMDiffAt.comp q (contMDiffAt_const.prodMk contMDiffAt_id)
    have hyU : ϕ (τ q) q ∈ U := ⟨by rw [hy]; exact hℓ, by rw [hy]; exact hℓε⟩
    have hdy : ContMDiffAt I 𝓘(ℝ, ℝ) n (fun x => d (ϕ (τ q) x)) q :=
      ((hds _ hyU).contMDiffAt (hU.mem_nhds hyU)).comp q hflowq
    have hcont : ContinuousAt (fun x => d (ϕ (τ q) x)) q := hdy.continuousAt
    have hev1 : ∀ᶠ x in 𝓝 q, d (ϕ (τ q) x) ∈ Ioo (ℓ - δ) (ℓ + δ) :=
      hcont.eventually (Ioo_mem_nhds (by change ℓ - δ < d (ϕ (τ q) q); rw [hy]; linarith)
        (by change d (ϕ (τ q) q) < ℓ + δ; rw [hy]; linarith))
    have hev2 : ∀ᶠ x in 𝓝 q, ℓ < d x := hdc.continuousAt.eventually (Ioi_mem_nhds hq')
    apply ((contMDiffAt_const (c := τ q + ℓ)).sub hdy).congr_of_eventuallyEq
    filter_upwards [hev1, hev2] with x hx1 hx2
    refine (hτunique x hx2.le _ ?_).symm
    have := hlevel (ϕ (τ q) x) hx1.1 hx1.2
    rwa [← hϕadd, show ℓ - d (ϕ (τ q) x) + τ q = τ q + ℓ - d (ϕ (τ q) x) by ring] at this
  have hGsmooth : ContMDiff I J n G := by
    intro q
    by_cases hq : d q < ℓ + δ
    · have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans hε
      apply (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hqT)).congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Iio_mem_nhds hq)] with x hx
      exact hGinner x hx
    · have hq' : ℓ < d q := by linarith only [le_of_not_gt hq, hδ]
      have hys : ContMDiffAt I I n (fun x => ϕ (τ x) x) q :=
        hϕ.contMDiffAt.comp q ((hτs q hq').prodMk contMDiffAt_id)
      have hyT : ϕ (τ q) q ∈ Φ.target := by
        rw [htarget]
        change d (ϕ (τ q) q) < ε
        rw [hτ q hq'.le]
        exact hℓε
      have hzs : ContMDiffAt I J n (fun x => Φ.symm (ϕ (τ x) x)) q :=
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hyT)).comp
          (f := fun x => ϕ (τ x) x) q hys
      have hs : ContMDiffAt I J n
          (fun x => scale ((ℓ - τ x) / ℓ) (Φ.symm (ϕ (τ x) x))) q :=
        hscale.contMDiffAt.comp q
          ((((contDiff_const.sub contDiff_id).div_const ℓ).contDiffAt.comp_contMDiffAt
            (hτs q hq')).prodMk hzs)
      apply hs.congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Ioi_mem_nhds hq')] with x hx
      exact ite_eq_right (not_le_of_gt hx)
  let e : N ≃ₘ^n⟮J, I⟯ M :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      contMDiff_toFun := hFsmooth
      contMDiff_invFun := hGsmooth }
  refine ⟨e, fun _ => rfl, fun q hq => ?_, fun q hq t ht => ?_, fun τ' hτ' q hq => ?_⟩
  · change G q = Φ.symm q
    exact ite_eq_left hq
  · have htq : t = τ q := hτunique q hq t ht
    subst htq
    refine ⟨hτnonpos q hq, ?_⟩
    change G q = _
    rcases eq_or_lt_of_le hq with h | h
    · have hτ0 : τ q = 0 := (hτunique q hq 0 (by rw [hϕ0]; exact h.symm)).symm
      rw [hτ0, hϕ0, sub_zero, div_self hℓ.ne', hone]
      exact ite_eq_left h.symm.le
    · exact ite_eq_right (not_le_of_gt h)
  · have hq' : ℓ < d q := hq
    apply ContMDiffAt.contMDiffWithinAt
    apply (hτs q hq').congr_of_eventuallyEq
    filter_upwards [hdc.continuousAt (Ioi_mem_nhds hq')] with x hx
    exact hτunique x hx.le _ (hτ' x hx.le)

end DifferentialGeometry.Geometry.FiniteSoul
