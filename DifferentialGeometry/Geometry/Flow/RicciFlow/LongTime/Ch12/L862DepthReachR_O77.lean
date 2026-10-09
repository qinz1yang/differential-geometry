import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Reg_O77
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862DepthReach_O63

/-!
# CH12-O77 G3: depth reach of the region invariant `Reg (R⁺)` (Sublemma 86.6 on regions)

`depth_reach_R_O77` = the skeleton of `depth_reach_O63` (depth set `𝒟_R`, restriction, regular
restart off the finite event set, extension `hExt`, `depth_advance_O57`) with the traced moving
family + `hsec` replaced by `Reg_O77`, and the bottom volume of KL82.1 at the restart time taken from
the explicit regional input `hKLvol` (second conjunct of the regional `kl82_1`, O78, at depth
`≤ τ'`; O79 instantiates `τ' := τ₈₂`).  Output: `∀ d ∈ [0, τ')`, a region `Reg_O77` of radius `r`
on `[u − d r², u]` along one centre trace of `x`.

* `reg_restrict_O77`: restriction `[a, u] → [b, u]` (`a ≤ b ≤ u`) along `X.restrictFirst`;
* `reg_concat_O77`: `Reg` of `Z` on `[ae, a]` (ending at `X a`) and of `X` on `[a, u]` give `Reg` of
  `X.concat Z` on `[ae, u]` (events of `(ae, a]` from `Z`, of `(a, u]` from `X`; same convention).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Restriction of a region to a later bottom time. -/
theorem reg_restrict_O77 {N : ObservedHistory.{u}} {a b u : Icc (0 : ℝ) N.horizon}
    (hab : a ≤ b) (hbu : b ≤ u) {hau : a ≤ u} {x : (N.stageAt u).Carrier}
    {X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x}
    {r : ℝ} (h : Reg_O77 N hau X r) :
    Reg_O77 N hbu (X.restrictFirst (N.activeStage_mono hab) (N.activeStage_mono hbu)) r := by
  obtain ⟨hsec, ⟨K, hK⟩, hev⟩ := h
  exact ⟨fun v hbv hvu q hq => hsec v (hab.trans hbv) hvu q hq,
    ⟨K, fun v hbv hvu q hq => hK v (hab.trans hbv) hvu q hq⟩,
    fun i hf hl => hev i ((N.activeStage_mono hab).trans hf) hl⟩

/-- Concatenation of regions along the centre trace (`[ae, a] ++ [a, u]`). -/
theorem reg_concat_O77 {N : ObservedHistory.{u}} {ae a u : Icc (0 : ℝ) N.horizon}
    (haa : ae ≤ a) (hau : a ≤ u) {x : (N.stageAt u).Carrier}
    {X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x}
    {Z : BackwardPointTrace N (N.activeStage ae) (N.activeStage a) (N.activeStage_mono haa)
      (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau))}
    {r : ℝ} (hX : Reg_O77 N hau X r) (hZ : Reg_O77 N haa Z r) :
    Reg_O77 N (haa.trans hau) (X.concat Z) r := by
  obtain ⟨hsecX, ⟨KX, hKX⟩, hevX⟩ := hX
  obtain ⟨hsecZ, ⟨KZ, hKZ⟩, hevZ⟩ := hZ
  refine ⟨fun v hav hvu q hq => ?_, ⟨max KX KZ, fun v hav hvu q hq => ?_⟩, fun i hf hl => ?_⟩
  · rcases le_total v a with hva | hav'
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ (N.activeStage_mono hva)] at hq
      exact hsecZ v hav hva q hq
    · rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (N.activeStage_mono hav')] at hq
      exact hsecX v hav' hvu q hq
  · rcases le_total v a with hva | hav'
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ (N.activeStage_mono hva)] at hq
      exact (hKZ v hav hva q hq).trans (le_max_right _ _)
    · rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (N.activeStage_mono hav')] at hq
      exact (hKX v hav' hvu q hq).trans (le_max_left _ _)
  · by_cases hia : i.succ ≤ N.activeStage a
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ hia,
        BackwardPointTrace.concat_point_of_le X Z _ _ _ (i.castSucc_lt_succ.le.trans hia)]
      exact hevZ i hf hia
    · have hai : N.activeStage a ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_not_ge hia)
      rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (hai.trans i.castSucc_lt_succ.le),
        BackwardPointTrace.concat_point_of_ge X Z _ _ _ hai]
      exact hevX i hai hl

/-- **G3** (`[FROZEN] CH12-O77`, `frozen_depthReachR_O77`): depth reach of the region invariant. -/
theorem depth_reach_R_O77 {w τ' : ℝ} (_hτ' : 0 < τ') (hτ'1 : τ' ≤ 1)
    (hKLvol : ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon)
        (x0 : (H.stageAt top).Carrier) (r0 τ : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        0 < r0 → 0 < τ → τ ≤ τ' → (a : ℝ) = top - τ * r0 ^ 2 →
        Reg_O77 H hat X r0 →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4)) :
    ∀ (H : ObservedHistory.{u}) (E : Set ℝ) (Phi : ℝ → ℝ) (u : Icc (0 : ℝ) H.horizon),
      Perelman.AdmissiblePinchingFunction Phi →
      (∀ v : Icc (0 : ℝ) H.horizon, v ≤ u → ∀ x,
        curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
          (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
      (E ∩ Ioc 0 (u : ℝ)).Finite → (u : ℝ) ∉ E →
    ∀ (x : (H.stageAt u).Carrier) (r c : ℝ), 0 < r → 0 < c → r ^ 2 < u →
      (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u) x r,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage u) u) q (-(r ^ 2)⁻¹)) →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage u) u) x r →
      ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
        ballVolume (H.stageMetric (H.activeStage u) u) x (r / 4) →
      (∀ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ u)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x),
          (0 < (a : ℝ) ∧ (a : ℝ) ∉ E) → (u : ℝ) - r ^ 2 ≤ a →
          Reg_O77 H hau X r →
          ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
            ballVolume (H.stageMetric (H.activeStage a) a)
              (X.point (H.activeStage a) le_rfl (H.activeStage_mono hau)) (r / 4) →
          ∃ (ae : Icc (0 : ℝ) H.horizon) (haa : ae ≤ a)
            (Z : BackwardPointTrace H (H.activeStage ae) (H.activeStage a)
              (H.activeStage_mono haa) (X.point (H.activeStage a) le_rfl (H.activeStage_mono hau))),
            (ae : ℝ) = a - c * r ^ 2 ∧ Reg_O77 H (haa.trans hau) (X.concat Z) r) →
      ∀ d : ℝ, 0 ≤ d → d < τ' →
        ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ u)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x),
          (a : ℝ) = u - d * r ^ 2 ∧ Reg_O77 H hau X r := by
  intro H E Phi u hPhi hpinch hfin hu x r c hr hc hru hsec0 hvol hvol4 hExt
  have hr2 : 0 < r ^ 2 := by positivity
  let 𝒟 : Set ℝ := {d | 0 ≤ d ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ u)
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x),
    (a : ℝ) = u - d * r ^ 2 ∧ Reg_O77 H hau X r}
  -- h0: the singleton trace at the top
  have h0 : (0 : ℝ) ∈ 𝒟 :=
    ⟨le_rfl, u, le_rfl, BackwardPointTrace.singleton H (H.activeStage u) x, by ring,
      reg_top_O77 H u x hsec0⟩
  -- hdown: restriction to a later bottom time
  have hdown : ∀ d ∈ 𝒟, ∀ d' : ℝ, 0 ≤ d' → d' ≤ d → d' ∈ 𝒟 := by
    rintro d ⟨-, a, hau, X, ha, hreg⟩ d' hd' hdd
    have hdr : d' * r ^ 2 ≤ d * r ^ 2 := mul_le_mul_of_nonneg_right hdd hr2.le
    have hab' : (a : ℝ) ≤ u - d' * r ^ 2 := by rw [ha]; linarith
    have hd'r : 0 ≤ d' * r ^ 2 := mul_nonneg hd' hr2.le
    let b : Icc (0 : ℝ) H.horizon :=
      ⟨u - d' * r ^ 2, a.2.1.trans hab', (sub_le_self _ hd'r).trans u.2.2⟩
    have hab : a ≤ b := hab'
    have hbu : b ≤ u := show (u : ℝ) - d' * r ^ 2 ≤ u from sub_le_self _ hd'r
    exact ⟨hd', b, hbu, X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbu),
      rfl, reg_restrict_O77 hab hbu hreg⟩
  -- hstep: advance by `c / 2` (regular restart, regional KL82 bottom volume, `hExt`)
  have hstep : ∀ d ∈ 𝒟, d < τ' → ∃ e ∈ 𝒟, d + c / 2 ≤ e := by
    rintro d ⟨hd0, a, hau, X, ha, hreg⟩ hdτ
    have hd1 : d ≤ 1 := hdτ.le.trans hτ'1
    have hdr1 : d * r ^ 2 ≤ r ^ 2 := by nlinarith
    have hpick : ∃ (as : Icc (0 : ℝ) H.horizon) (has : a ≤ as) (hasu : as ≤ u),
        (0 < (as : ℝ) ∧ (as : ℝ) ∉ E) ∧ (u : ℝ) - r ^ 2 ≤ as ∧
        (as : ℝ) ≤ u - (d - c / 2) * r ^ 2 ∧
        ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage as) as)
            ((X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)).point
              (H.activeStage as) le_rfl (H.activeStage_mono hasu)) (r / 4) := by
      rcases hd0.eq_or_lt with hd | hd
      · -- `d = 0`: restart at the top itself
        subst hd
        have hau' : a = u := Subtype.ext (by rw [ha]; ring)
        subst hau'
        have hx : X.point (H.activeStage a) (H.activeStage_mono hau) le_rfl = x := X.endpoint_eq
        refine ⟨a, le_rfl, hau, ⟨by linarith [hru], hu⟩, by linarith, by nlinarith, ?_⟩
        change ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) (H.activeStage_mono hau) le_rfl) (r / 4)
        rw [hx]
        exact hvol4
      · -- `d > 0`: a regular time in `(u − d r², u − (d − min d (c/2)) r²)`
        set m := min d (c / 2) with hm
        have hm0 : 0 < m := lt_min hd (half_pos hc)
        have hmd : m ≤ d := min_le_left _ _
        have hmc : m ≤ c / 2 := min_le_right _ _
        have hlohi : (a : ℝ) < a + m * r ^ 2 := by
          have : 0 < m * r ^ 2 := mul_pos hm0 hr2
          linarith
        obtain ⟨t, ⟨htlo, hthi⟩, htE⟩ :=
          ((Set.Ioo_infinite hlohi).sdiff hfin).nonempty
        have hmr : m * r ^ 2 ≤ d * r ^ 2 := mul_le_mul_of_nonneg_right hmd hr2.le
        have hmr' : m * r ^ 2 ≤ c / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hmc hr2.le
        have ht0 : 0 < t := by linarith
        have htu : t ≤ u := by linarith
        let as : Icc (0 : ℝ) H.horizon := ⟨t, ht0.le, htu.trans u.2.2⟩
        have has : a ≤ as := show (a : ℝ) ≤ t from htlo.le
        have hasu : as ≤ u := show t ≤ (u : ℝ) from htu
        have htE' : t ∉ E := fun h => htE ⟨h, ht0, htu⟩
        have hd' : 0 < (u - t) / r ^ 2 := div_pos (by linarith) hr2
        have hd'τ : (u - t) / r ^ 2 ≤ τ' := by
          rw [div_le_iff₀ hr2]; nlinarith
        have hast : (as : ℝ) = u - (u - t) / r ^ 2 * r ^ 2 := by
          change t = u - (u - t) / r ^ 2 * r ^ 2
          rw [div_mul_cancel₀ _ hr2.ne']; ring
        refine ⟨as, has, hasu, ⟨ht0, htE'⟩, by linarith, by nlinarith, ?_⟩
        exact hKLvol H u x r ((u - t) / r ^ 2) as hasu
          (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)) hPhi hpinch hr hd'
          hd'τ hast (reg_restrict_O77 has hasu hreg) hvol
    obtain ⟨as, has, hasu, hregt, hlow, hprog, hvolb⟩ := hpick
    obtain ⟨ae, haa, Z, hae, hregZ⟩ :=
      hExt as hasu (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)) hregt hlow
        (reg_restrict_O77 has hasu hreg) hvolb
    have hcr : 0 < c * r ^ 2 := mul_pos hc hr2
    have hae_u : (ae : ℝ) ≤ u := haa.trans hasu
    refine ⟨((u : ℝ) - ae) / r ^ 2, ⟨div_nonneg (by linarith) hr2.le, ae, haa.trans hasu,
      (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)).concat Z,
      by rw [div_mul_cancel₀ _ hr2.ne']; ring, hregZ⟩, ?_⟩
    rw [le_div_iff₀ hr2]
    nlinarith
  intro d hd hdτ
  obtain ⟨-, a, hau, X, ha, hreg⟩ := depth_advance_O57 𝒟 (half_pos hc) h0 hdown hstep d hd hdτ
  exact ⟨a, hau, X, ha, hreg⟩

end GC.LongTime.Ch12
