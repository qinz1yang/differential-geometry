import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862DepthAdvance_O57
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimWindow_O30
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm

/-!
# CH12-O63 G1: depth reach of the unscathed moving family (R5 S4, `[FROZEN] CH12-O63`)

`depth_reach_O63 hw`: with `τ'` the KL82.1 depth of `kl82_1_O36 w`, an extension step `hExt`
(old traced moving family of radius `r` on `[a, u]` + its bottom volume ⟹ extension by `c r²`
along `X.concat Z`) yields a traced moving family of radius `r` on `[u − d r², u]` for every
`0 ≤ d < τ'`.  Depth set `𝒟`; `h0` = singleton trace with the compact-stage `|Rm|` bound,
`hdown` = restriction, `hstep` (`c/2`) = a regular restart time off the finite event set, the
bottom volume (top volume if `d = 0`, KL82.1 second conjunct if `d > 0`), `hExt`; then
`depth_advance_O57`.
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

/-- Restriction of a traced moving family (with its sectional bound) to a later bottom time. -/
theorem family_restrict_O63 {H : ObservedHistory.{u}} {a b t : Icc (0 : ℝ) H.horizon}
    (hab : a ≤ b) (hbt : b ≤ t) {hat : a ≤ t} {x : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x)
    {r : ℝ}
    (hfam : ∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
        ∃ A' : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K')
    (hsec : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) :
    (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvu : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          ((X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)).point
            (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvu)) r,
        ∃ A' : BackwardPointTrace H (H.activeStage b) (H.activeStage v)
            (H.activeStage_mono hbv) q, A'.isRmBoundedBy (hat := hbv) K') ∧
    (∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvu : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          ((X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)).point
            (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvu)) r,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) := by
  obtain ⟨K', hK'⟩ := hfam
  refine ⟨⟨K', fun v hbv hvu q hq => ?_⟩, fun v hbv hvu q hq => hsec v (hab.trans hbv) hvu q hq⟩
  obtain ⟨A', hA'⟩ := hK' v (hab.trans hbv) hvu q hq
  exact ⟨traceRestrict_O30 A' (H.activeStage_mono hab) (H.activeStage_mono hbv),
    isRmBoundedBy_restrict_O30 hab hbv A' hA'⟩

/-- Depth `0`: every point of the time-`t` stage is traced (singleton trace) with one uniform
`|Rm|` bound (compact stage). -/
theorem family_top_O63 (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) :
    ∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (htv : t ≤ v) (_hvt : v ≤ t),
      ∀ q : (H.stageAt v).Carrier,
        ∃ A' : BackwardPointTrace H (H.activeStage t) (H.activeStage v)
            (H.activeStage_mono htv) q, A'.isRmBoundedBy (hat := htv) K' := by
  obtain ⟨B0, hB0, hB⟩ := exists_bound_curvatureDerivativeNorm_of_compactSpace
    (H.stageMetric (H.activeStage t) t) 0
  refine ⟨B0, fun v htv hvt q => ?_⟩
  obtain rfl : v = t := le_antisymm hvt htv
  refine ⟨BackwardPointTrace.singleton H (H.activeStage v) q, ?_, ?_⟩
  · intro s' hs1 hs2
    obtain rfl : s' = v := le_antisymm hs2 hs1
    have h' : Real.sqrt (normSq0S (H.stageMetric (H.activeStage s') s') q 4
        (metricRm04At (H.stageMetric (H.activeStage s') s') q)) ≤ B0 := hB 0 le_rfl q
    exact (Real.sqrt_le_left hB0).mp h'
  · intro i hf hl
    exact absurd (hl.trans hf) (not_le_of_gt (Fin.castSucc_lt_succ (i := i)))

/-- **G1** (`[FROZEN] CH12-O63`): depth reach of the unscathed moving family. -/
theorem depth_reach_O63 {w : ℝ} (hw : 0 < w) :
    ∃ τ' : ℝ, 0 < τ' ∧ τ' ≤ 1 ∧
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
          (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
              ∃ A' : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                  (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K') →
          (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) →
          ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
            ballVolume (H.stageMetric (H.activeStage a) a)
              (X.point (H.activeStage a) le_rfl (H.activeStage_mono hau)) (r / 4) →
          ∃ (ae : Icc (0 : ℝ) H.horizon) (haa : ae ≤ a)
            (Z : BackwardPointTrace H (H.activeStage ae) (H.activeStage a) (H.activeStage_mono haa)
              (X.point (H.activeStage a) le_rfl (H.activeStage_mono hau))),
            (ae : ℝ) = a - c * r ^ 2 ∧
            (∃ K'' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  ((X.concat Z).point (H.activeStage v) (H.activeStage_mono hav)
                    (H.activeStage_mono hvu)) r,
                ∃ A' : BackwardPointTrace H (H.activeStage ae) (H.activeStage v)
                    (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K'') ∧
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  ((X.concat Z).point (H.activeStage v) (H.activeStage_mono hav)
                    (H.activeStage_mono hvu)) r,
                SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹))) →
      ∀ d : ℝ, 0 ≤ d → d < τ' →
        ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ u)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x),
          (a : ℝ) = u - d * r ^ 2 ∧
          (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
              ∃ A' : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                  (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K') ∧
          (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) := by
  obtain ⟨τ', K₀, hτ', hτ'1, _hK₀, hkl⟩ := kl82_1_O36.{u} w hw
  refine ⟨τ', hτ', hτ'1, ?_⟩
  intro H E Phi u hPhi hpinch hfin hu x r c hr hc hru hsec0 hvol hvol4 hExt
  have hr2 : 0 < r ^ 2 := by positivity
  let 𝒟 : Set ℝ := {d | 0 ≤ d ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ u)
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x),
    (a : ℝ) = u - d * r ^ 2 ∧
    (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
        ∃ A' : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K') ∧
    (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) r,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹))}
  -- h0: the singleton trace at the top
  have h0 : (0 : ℝ) ∈ 𝒟 := by
    refine ⟨le_rfl, u, le_rfl, BackwardPointTrace.singleton H (H.activeStage u) x, by ring,
      ?_, ?_⟩
    · obtain ⟨K', hK'⟩ := family_top_O63 H u
      exact ⟨K', fun v hav hvu q _ => hK' v hav hvu q⟩
    · intro v hav hvu q hq
      obtain rfl : v = u := le_antisymm hvu hav
      exact hsec0 q hq
  -- hdown: restriction to a later bottom time
  have hdown : ∀ d ∈ 𝒟, ∀ d' : ℝ, 0 ≤ d' → d' ≤ d → d' ∈ 𝒟 := by
    rintro d ⟨-, a, hau, X, ha, hfam, hsec⟩ d' hd' hdd
    have hdr : d' * r ^ 2 ≤ d * r ^ 2 := mul_le_mul_of_nonneg_right hdd hr2.le
    have hab' : (a : ℝ) ≤ u - d' * r ^ 2 := by rw [ha]; linarith
    have hd'r : 0 ≤ d' * r ^ 2 := mul_nonneg hd' hr2.le
    let b : Icc (0 : ℝ) H.horizon :=
      ⟨u - d' * r ^ 2, a.2.1.trans hab', (sub_le_self _ hd'r).trans u.2.2⟩
    have hab : a ≤ b := hab'
    have hbu : b ≤ u := show (u : ℝ) - d' * r ^ 2 ≤ u from sub_le_self _ hd'r
    obtain ⟨hf, hs⟩ := family_restrict_O63 (hat := hau) hab hbu X hfam hsec
    exact ⟨hd', b, hbu, X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbu),
      rfl, hf, hs⟩
  -- hstep: advance by `c / 2`
  have hstep : ∀ d ∈ 𝒟, d < τ' → ∃ e ∈ 𝒟, d + c / 2 ≤ e := by
    rintro d ⟨hd0, a, hau, X, ha, hfam, hsec⟩ hdτ
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
        obtain ⟨⟨K', hf⟩, hs⟩ := family_restrict_O63 (hat := hau) has hasu X hfam hsec
        have hd' : 0 < (u - t) / r ^ 2 := div_pos (by linarith) hr2
        have hd'τ : (u - t) / r ^ 2 ≤ τ' := by
          rw [div_le_iff₀ hr2]; nlinarith
        have hast : (as : ℝ) = u - (u - t) / r ^ 2 * r ^ 2 := by
          change t = u - (u - t) / r ^ 2 * r ^ 2
          rw [div_mul_cancel₀ _ hr2.ne']; ring
        refine ⟨as, has, hasu, ⟨ht0, htE'⟩, by linarith, by nlinarith, ?_⟩
        exact (hkl H u x r ((u - t) / r ^ 2) K' as hasu
          (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)) hPhi hpinch hr hd'
          hd'τ hast hf hs hvol).2
    obtain ⟨as, has, hasu, hreg, hlow, hprog, hvolb⟩ := hpick
    obtain ⟨hf, hs⟩ := family_restrict_O63 (hat := hau) has hasu X hfam hsec
    obtain ⟨ae, haa, Z, hae, hfam', hsec'⟩ :=
      hExt as hasu (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)) hreg hlow
        hf hs hvolb
    have hcr : 0 < c * r ^ 2 := mul_pos hc hr2
    have hae_u : (ae : ℝ) ≤ u := haa.trans hasu
    refine ⟨((u : ℝ) - ae) / r ^ 2, ⟨div_nonneg (by linarith) hr2.le, ae, haa.trans hasu,
      (X.restrictFirst (H.activeStage_mono has) (H.activeStage_mono hasu)).concat Z,
      by rw [div_mul_cancel₀ _ hr2.ne']; ring, hfam', hsec'⟩, ?_⟩
    rw [le_div_iff₀ hr2]
    nlinarith
  intro d hd hdτ
  obtain ⟨-, a, hau, X, ha, hf, hs⟩ := depth_advance_O57 𝒟 (half_pos hc) h0 hdown hstep d hd hdτ
  exact ⟨a, hau, X, ha, hf, hs⟩

end GC.LongTime.Ch12
