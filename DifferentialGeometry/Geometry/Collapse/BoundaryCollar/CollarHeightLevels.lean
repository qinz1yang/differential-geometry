import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightBCP01
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarBandProduct

/-!
# BCP01: the levels and level bands of the smoothed collar height (C1/C2)

Let `η` be smooth on `W` with `|η − z| < 1/10` on the collar band `2 ≤ z ≤ 98` (row E8; `η` is
arbitrary off the band). The tree's level-torus and band-product kernels
(`CuspEmbedding.exists_diffeomorph_level_torus`, `CuspEmbedding.exists_band_diffeomorph_torus`)
need the GLOBAL level set inside the collar, so `η` is first localised:

* `CuspEmbedding.exists_localized_height`: a smooth `η̃` on `W` equal to `η` near every point of
  `e(12/5 ≤ z ≤ 488/5)`, and every point where `3 ≤ η̃ ≤ 97` lies in `e(12/5 < z < 488/5)`, where
  `η̃ = η`. (`η̃ = −1` on `e(z ≤ 2)`, `100` off `e(z < 98)`, and on `e(2 < z < 98)` the blend
  `η + (1 − φ₊(η))(100 − η) + φ₋(η)(−1 − η)` with cutoffs of `η` itself; `η` is modified only
  where `η < 23/10` or `η > 977/10`.)
* `CuspEmbedding.hasDerivAt_vertical`: along a vertical `s ↦ e(x, s)`, `s > 0`, the derivative of
  `η ∘ e` is `∂_z(η ∘ e)`.
* `CuspEmbedding.bcp01_levels` (BCP01, levels and level bands; `W : CompactCarrier.{0}` as the
  kernels): for the BCP01 height `η` of `CuspEmbedding.bcp01` (the SAME `η` as clauses (a), (b),
  (c)), the localised `η̃` agrees with `η` on `e(12/5 ≤ z ≤ 488/5)`; every level `η̃ = t`,
  `3 ≤ t ≤ 97` (= the level `η = t` inside the collar band) is a smooth torus, and every band
  `η̃⁻¹[a, b]`, `3 ≤ a < b ≤ 97`, is smoothly `T² × [a, b]` preserving `η̃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The blend of the localised height on `e(2 < z < 98)`. -/
def collarLevelBlend (η : W.Carrier → ℝ) (y : W.Carrier) : ℝ :=
  η y + (1 - innerCollarCutoff (977 / 10) (978 / 10) (η y)) * (100 - η y) +
    innerCollarCutoff (11 / 5) (23 / 10) (η y) * (-1 - η y)

theorem contMDiff_collarLevelBlend {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (collarLevelBlend η) :=
  (hη.add ((contMDiff_const.sub ((contDiff_innerCollarCutoff _ _).contMDiff.comp hη)).mul
    (contMDiff_const.sub hη))).add
    (((contDiff_innerCollarCutoff _ _).contMDiff.comp hη).mul (contMDiff_const.sub hη))

theorem collarLevelBlend_of_mid {η : W.Carrier → ℝ} {y : W.Carrier} (h1 : 23 / 10 ≤ η y)
    (h2 : η y ≤ 977 / 10) : collarLevelBlend η y = η y := by
  rw [collarLevelBlend, innerCollarCutoff_of_le (by norm_num) h2,
    innerCollarCutoff_of_ge (by norm_num) h1]
  ring

theorem collarLevelBlend_of_low {η : W.Carrier → ℝ} {y : W.Carrier} (h : η y ≤ 11 / 5) :
    collarLevelBlend η y = -1 := by
  rw [collarLevelBlend, innerCollarCutoff_of_le (by norm_num) (by linarith : η y ≤ 977 / 10),
    innerCollarCutoff_of_le (by norm_num) h]
  ring

theorem collarLevelBlend_of_high {η : W.Carrier → ℝ} {y : W.Carrier} (h : 978 / 10 ≤ η y) :
    collarLevelBlend η y = 100 := by
  rw [collarLevelBlend, innerCollarCutoff_of_ge (by norm_num) h,
    innerCollarCutoff_of_ge (by norm_num) (by linarith : 23 / 10 ≤ η y)]
  ring

/-- Outside the middle range the blend stays outside `[3, 97]`. -/
theorem collarLevelBlend_mem_iff {η : W.Carrier → ℝ} {y : W.Carrier} (h0 : 0 ≤ η y)
    (h100 : η y ≤ 100) (h3 : 3 ≤ collarLevelBlend η y) (h97 : collarLevelBlend η y ≤ 97) :
    collarLevelBlend η y = η y := by
  obtain ⟨hb0, hb1⟩ := innerCollarCutoff_mem (11 / 5) (23 / 10) (η y)
  obtain ⟨ht0, ht1⟩ := innerCollarCutoff_mem (977 / 10) (978 / 10) (η y)
  rcases lt_or_ge (η y) (23 / 10) with hl | hl
  · rw [collarLevelBlend, innerCollarCutoff_of_le (by norm_num) (by linarith : η y ≤ 977 / 10)]
      at h3
    nlinarith
  rcases lt_or_ge (977 / 10) (η y) with hh | hh
  · rw [collarLevelBlend, innerCollarCutoff_of_ge (by norm_num) hl] at h97
    nlinarith
  exact collarLevelBlend_of_mid hl hh

/-- **The localised collar height.** -/
theorem CuspEmbedding.exists_localized_height (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hηz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 10) :
    ∃ η' : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η' ∧
      (∀ p ∈ cuspDomain, 12 / 5 ≤ p.2.val 0 → p.2.val 0 ≤ 488 / 5 →
        η' =ᶠ[𝓝 (e.toFun p)] η) ∧
      ∀ y, 3 ≤ η' y → η' y ≤ 97 →
        ∃ p ∈ cuspDomain, 12 / 5 < p.2.val 0 ∧ p.2.val 0 < 488 / 5 ∧ e.toFun p = y ∧
          η' y = η y := by
  classical
  set O : Set W.Carrier := e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}
    with hO
  set L : Set W.Carrier := e.toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 2} with hL
  have hdom : ∀ {p : CuspHalfSpace} {b : ℝ}, b < cuspDepth → p.2.val 0 ≤ b → p ∈ cuspDomain :=
    fun hb hp => cusp_mem_cuspDomain_of_le hb hp
  have hOo : IsOpen O := by
    refine e.isOpen_image_of_pos ?_ (fun p hp => hdom (by norm_num [cuspDepth]) hp.2.le)
      fun p hp => lt_trans (by norm_num) hp.1
    change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Ioo 2 98)
    exact isOpen_Ioo.preimage (by fun_prop)
  have hmemO : ∀ {p : CuspHalfSpace}, p ∈ cuspDomain → (e.toFun p ∈ O ↔
      2 < p.2.val 0 ∧ p.2.val 0 < 98) := by
    intro p hp
    constructor
    · rintro ⟨q, hq, hqp⟩
      have hqd : q ∈ cuspDomain := hdom (by norm_num [cuspDepth]) hq.2.le
      rw [← e.injOn_cuspDomain hqd hp hqp]
      exact hq
    · intro h
      exact ⟨p, h, rfl⟩
  set η' : W.Carrier → ℝ := fun y =>
    if y ∈ O then collarLevelBlend η y else if y ∈ L then -1 else 100 with hη'
  have hvO : ∀ {y}, y ∈ O → η' y = collarLevelBlend η y := fun hy => by simp [hη', hy]
  have hvL : ∀ {y}, y ∉ O → y ∈ L → η' y = -1 := fun hy hy' => by simp [hη', hy, hy']
  have hvH : ∀ {y}, y ∉ O → y ∉ L → η' y = 100 := fun hy hy' => by simp [hη', hy, hy']
  have hηO : ∀ {p : CuspHalfSpace}, 2 < p.2.val 0 → p.2.val 0 < 98 →
      η (e.toFun p) - 1 / 10 < p.2.val 0 ∧ p.2.val 0 < η (e.toFun p) + 1 / 10 := by
    intro p h1 h2
    have h := abs_lt.mp (hηz p (hdom (by norm_num [cuspDepth]) h2.le) h1.le h2.le)
    constructor <;> linarith [h.1, h.2]
  -- local forms of `η'`
  have hloc_low : ∀ y ∈ L, η' =ᶠ[𝓝 y] fun _ => (-1 : ℝ) := by
    rintro y ⟨p, hp, rfl⟩
    have hN : IsOpen (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 41 / 20}) := by
      refine e.isOpen_image ?_ fun q hq => hdom (by norm_num [cuspDepth]) hq.le
      change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Iio (41 / 20))
      exact isOpen_Iio.preimage (by fun_prop)
    have hp2 : p.2.val 0 ≤ 2 := hp
    have hp41 : p ∈ {p : CuspHalfSpace | p.2.val 0 < 41 / 20} := by
      change p.2.val 0 < 41 / 20
      linarith
    filter_upwards [hN.mem_nhds ⟨p, hp41, rfl⟩] with y hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hqd : q ∈ cuspDomain := hdom (by norm_num [cuspDepth]) hq.le
    rcases le_or_gt (q.2.val 0) 2 with h | h
    · exact hvL (fun h' => by linarith [((hmemO hqd).mp h').1]) ⟨q, h, rfl⟩
    · have hq41 : q.2.val 0 < 41 / 20 := hq
      rw [hvO ((hmemO hqd).mpr ⟨h, by linarith⟩)]
      exact collarLevelBlend_of_low (by linarith [(hηO h (by linarith)).1])
  have hKc : IsClosed (e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 1959 / 20}) :=
    (e.isCompact_image_band (by norm_num [cuspDepth])).isClosed
  have hloc_high : ∀ y, y ∉ O → y ∉ L → η' =ᶠ[𝓝 y] fun _ => (100 : ℝ) := by
    intro y hyO hyL
    have hy : y ∈ (e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 1959 / 20})ᶜ := by
      rintro ⟨p, hp, rfl⟩
      have hpd : p ∈ cuspDomain := hdom (by norm_num [cuspDepth]) hp.2
      rcases le_or_gt (p.2.val 0) 2 with h | h
      · exact hyL ⟨p, h, rfl⟩
      · exact hyO ((hmemO hpd).mpr ⟨h, by linarith [hp.2]⟩)
    filter_upwards [hKc.isOpen_compl.mem_nhds hy] with z hz
    by_cases hzO : z ∈ O
    · rw [hvO hzO]
      obtain ⟨q, hq, rfl⟩ := hzO
      have hq2 : 1959 / 20 < q.2.val 0 := by
        by_contra hle
        exact hz ⟨q, ⟨q.2.property, le_of_not_gt hle⟩, rfl⟩
      exact collarLevelBlend_of_high (by linarith [(hηO hq.1 hq.2).2])
    · refine hvH hzO ?_
      rintro ⟨q, hq, rfl⟩
      exact hz ⟨q, ⟨q.2.property, by linarith [show q.2.val 0 ≤ 2 from hq]⟩, rfl⟩
  have hlocO : ∀ y ∈ O, η' =ᶠ[𝓝 y] collarLevelBlend η := fun y hy => by
    filter_upwards [hOo.mem_nhds hy] with z hz
    exact hvO hz
  refine ⟨η', fun y => ?_, fun p hp h1 h2 => ?_, fun y h3 h97 => ?_⟩
  · by_cases hyO : y ∈ O
    · exact ((contMDiff_collarLevelBlend hη) y).congr_of_eventuallyEq (hlocO y hyO)
    by_cases hyL : y ∈ L
    · exact contMDiffAt_const.congr_of_eventuallyEq (hloc_low y hyL)
    · exact contMDiffAt_const.congr_of_eventuallyEq (hloc_high y hyO hyL)
  · have hpO : e.toFun p ∈ O := (hmemO hp).mpr ⟨by linarith, by linarith⟩
    have hb := hηO (p := p) (by linarith) (by linarith)
    have hN : IsOpen (O ∩ η ⁻¹' Ioo (23 / 10) (977 / 10)) :=
      hOo.inter (isOpen_Ioo.preimage hη.continuous)
    filter_upwards [hN.mem_nhds ⟨hpO, by constructor <;> linarith [hb.1, hb.2]⟩] with z hz
    rw [hvO hz.1]
    exact collarLevelBlend_of_mid hz.2.1.le hz.2.2.le
  · have hyO : y ∈ O := by
      by_contra hyO
      by_cases hyL : y ∈ L
      · rw [hvL hyO hyL] at h3
        norm_num at h3
      · rw [hvH hyO hyL] at h97
        norm_num at h97
    obtain ⟨p, hpr, rfl⟩ := hyO
    have hpd : p ∈ cuspDomain := hdom (by norm_num [cuspDepth]) hpr.2.le
    have hb := hηO hpr.1 hpr.2
    have hval : η' (e.toFun p) = collarLevelBlend η (e.toFun p) := hvO ⟨p, hpr, rfl⟩
    rw [hval] at h3 h97 ⊢
    have heq := collarLevelBlend_mem_iff (by linarith [hb.2, hpr.1]) (by linarith [hb.1, hpr.2])
      h3 h97
    rw [heq] at h3 h97
    exact ⟨p, hpd, by linarith [hb.1], by linarith [hb.2], rfl, heq⟩


/-- The derivative of the half-line lift at a positive point. -/
private theorem collarLevels_hasMFDerivAt_lift {t : ℝ} (ht : 0 < t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t :=
    (contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds ht)).mdifferentiableAt (by simp)
  have hcomp := (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift t)).comp t hd.hasMFDerivAt
  have hid : (fun t' : ℝ => (halfSpaceOneLift t').1 0) =ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    change max t' 0 = t'
    exact max_eq_left ht'.le
  have h1 : T.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t) =
      ContinuousLinearMap.id ℝ ℝ := by
    have h2 := (hcomp.congr_of_eventuallyEq hid.symm).mfderiv
    rw [mfderiv_id] at h2
    exact h2.symm
  have h3 : mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t = T.symm.toContinuousLinearMap := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h4 : T (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t v) = v :=
      congrArg (fun L => L v) h1
    change _ = T.symm v
    conv_rhs => rw [← h4]
    exact (T.symm_apply_apply _).symm
  have h5 : T.symm.toContinuousLinearMap =
      (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    refine ContinuousLinearMap.ext_ring ?_
    change T.symm 1 = (1 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
    rw [one_smul]
    ext i
    fin_cases i
    simp [T]
  exact hd.hasMFDerivAt.congr_mfderiv (h3.trans h5)

/-- Along a vertical `s ↦ e(x, s)`, `0 < s < 100`, the derivative of `f ∘ e` is `∂_z(f ∘ e)`. -/
theorem CuspEmbedding.hasDerivAt_vertical (e : CuspEmbedding W g K δ X) {f : W.Carrier → ℝ}
    {x : Torus} {s : ℝ} (hs : 0 < s) (hs' : s < cuspDepth)
    (hf : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f (e.toFun (x, halfSpaceOneLift s))) :
    HasDerivAt (fun s : ℝ => f (e.toFun (x, halfSpaceOneLift s)))
      (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (f ∘ e.toFun) (x, halfSpaceOneLift s)
        ((0, 0), EuclideanSpace.single 0 1)) s := by
  have hp : ((x, halfSpaceOneLift s) : CuspHalfSpace) ∈ cuspDomain := by
    change (halfSpaceOneLift s).1 0 < cuspDepth
    rw [halfSpaceOneLift_val_zero, max_eq_left hs.le]
    exact hs'
  have he : MDifferentiableAt halfCollarModel W.model e.toFun (x, halfSpaceOneLift s) :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
  have hφ : HasMFDerivAt 𝓘(ℝ, ℝ) halfCollarModel (fun s : ℝ => (x, halfSpaceOneLift s)) s
      ((0 : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))).prod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))) :=
    (hasMFDerivAt_const x s).prodMk (collarLevels_hasMFDerivAt_lift hs)
  set D : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
      →L[ℝ] ℝ := mfderiv halfCollarModel 𝓘(ℝ, ℝ) (f ∘ e.toFun) (x, halfSpaceOneLift s) with hD
  have hcomp := (hf.comp _ he).hasMFDerivAt.comp s hφ
  have hd : HasFDerivAt (fun s : ℝ => f (e.toFun (x, halfSpaceOneLift s)))
      (D.comp ((0 : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))).prod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))))) s :=
    hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  refine hd.hasDerivAt.congr_deriv ?_
  change D ((0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)),
      (1 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = _
  rw [one_smul]
  rfl

/-- **BCP01, levels and level bands (C1/C2)**, for any smooth `η` with `|η − z| < 1/10` and
`∂_z(η ∘ e) > 0` on the band `2 ≤ z ≤ 98` (both are BCP01 clauses): the localised `η'` of
`exists_localized_height` agrees with `η` near `e(12/5 ≤ z ≤ 488/5)`, its points with values in
`[3, 97]` lie there, every level `η' = t`, `3 ≤ t ≤ 97`, is a smooth torus, and every band
`η'⁻¹[a, b]`, `3 ≤ a < b ≤ 97`, is smoothly `T² × [a, b]` preserving `η'`. -/
theorem CuspEmbedding.levels_of_height {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hηz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 10)
    (hvert : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      0 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
        ((0, 0), EuclideanSpace.single 0 1))) :
    ∃ η' : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η' ∧
      (∀ p ∈ cuspDomain, 12 / 5 ≤ p.2.val 0 → p.2.val 0 ≤ 488 / 5 →
        η' =ᶠ[𝓝 (e.toFun p)] η) ∧
      (∀ y, 3 ≤ η' y → η' y ≤ 97 →
        ∃ p ∈ cuspDomain, 12 / 5 < p.2.val 0 ∧ p.2.val 0 < 488 / 5 ∧ e.toFun p = y ∧
          η' y = η y) ∧
      (∀ t : ℝ, 3 ≤ t → t ≤ 97 →
        ∃ cs : ChartedSpace (Topology.Morse.MorseModel 2) {y : W.Carrier // η' y = t},
          letI := cs
          IsManifold 𝓘(ℝ, Topology.Morse.MorseModel 2) ∞ {y : W.Carrier // η' y = t} ∧
          ContMDiff 𝓘(ℝ, Topology.Morse.MorseModel 2) W.model ∞
            (Subtype.val : {y : W.Carrier // η' y = t} → W.Carrier) ∧
          Nonempty ({y : W.Carrier // η' y = t} ≃ₘ⟮𝓘(ℝ, Topology.Morse.MorseModel 2),
            torusModel⟯ Torus)) ∧
      ∀ (a b : ℝ) (hab : a < b), 3 ≤ a → b ≤ 97 →
        haveI : Fact (a < b) := ⟨hab⟩
        ∃ cs : ChartedSpace (Topology.Morse.MorseHalfSpace 2) ↥(η' ⁻¹' Icc a b),
          letI := cs
          IsManifold (Topology.Morse.morseModelWithCornersHalfSpace 2) ∞ ↥(η' ⁻¹' Icc a b) ∧
          ContMDiff (Topology.Morse.morseModelWithCornersHalfSpace 2) W.model ∞
            (fun y : ↥(η' ⁻¹' Icc a b) => (y : W.Carrier)) ∧
          ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1))
              (Topology.Morse.morseModelWithCornersHalfSpace 2) (Torus × Icc a b)
              ↥(η' ⁻¹' Icc a b) ∞,
            ∀ p, η' (D p : W.Carrier) = (p.2 : ℝ) := by
  obtain ⟨η', hη', heq, hin⟩ := e.exists_localized_height hη hηz
  have hlift : ∀ s : ℝ, 0 ≤ s → (halfSpaceOneLift s).1 0 = s := fun s hs => by
    rw [halfSpaceOneLift_val_zero, max_eq_left hs]
  have hdomv : ∀ (x : Torus) {s : ℝ}, 0 ≤ s → s < cuspDepth →
      ((x, halfSpaceOneLift s) : CuspHalfSpace) ∈ cuspDomain := fun x s hs hs' => by
    change (halfSpaceOneLift s).1 0 < cuspDepth
    rw [hlift s hs]
    exact hs'
  have hcontv : ∀ (x : Torus) {s : ℝ}, 0 < s → s < cuspDepth →
      ContinuousAt (fun s : ℝ => e.toFun (x, halfSpaceOneLift s)) s := by
    intro x s hs hs'
    have h1 : ContinuousAt (fun s : ℝ => ((x, halfSpaceOneLift s) : CuspHalfSpace)) s :=
      continuousAt_const.prodMk
        (contMDiffOn_halfSpaceOneLift.continuousOn.continuousAt (Ici_mem_nhds hs))
    exact ContinuousAt.comp (g := e.toFun)
      (f := fun s : ℝ => ((x, halfSpaceOneLift s) : CuspHalfSpace))
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hdomv x hs.le hs'))).continuousAt h1
  -- the vertical derivative of `η'` on `(12/5, 488/5)`
  have hvert' : ∀ x : Torus, ∀ s ∈ Ioo (12 / 5 : ℝ) (488 / 5),
      0 < deriv (fun s : ℝ => η' (e.toFun (x, halfSpaceOneLift s))) s := by
    intro x s hs
    have hs0 : 0 < s := lt_trans (by norm_num) hs.1
    have hs1 : s < cuspDepth := lt_trans hs.2 (by norm_num [cuspDepth])
    have hz : ((x, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 = s := hlift s hs0.le
    have hloc := heq (x, halfSpaceOneLift s) (hdomv x hs0.le hs1) (by rw [hz]; exact hs.1.le)
      (by rw [hz]; exact hs.2.le)
    have hev : (fun s : ℝ => η' (e.toFun (x, halfSpaceOneLift s))) =ᶠ[𝓝 s]
        fun s : ℝ => η (e.toFun (x, halfSpaceOneLift s)) :=
      (hcontv x hs0 hs1).eventually hloc
    rw [hev.deriv_eq, (e.hasDerivAt_vertical hs0 hs1 ((hη _).mdifferentiableAt (by simp))).deriv]
    exact hvert _ (hdomv x hs0.le hs1) (by rw [hz]; linarith [hs.1]) (by rw [hz]; linarith [hs.2])
  -- every vertical crosses every level in `[3, 97]`
  have hcross : ∀ c : ℝ, 3 ≤ c → c ≤ 97 → ∀ x : Torus,
      ∃ s ∈ Ioo (12 / 5 : ℝ) (488 / 5), η' (e.toFun (x, halfSpaceOneLift s)) = c := by
    intro c hc3 hc97 x
    set f : ℝ → ℝ := fun s => η' (e.toFun (x, halfSpaceOneLift s)) with hf
    have hfc : ContinuousOn f (Icc (12 / 5) (488 / 5)) := fun s hs =>
      (hη'.continuous.continuousAt.comp (hcontv x (lt_of_lt_of_le (by norm_num) hs.1)
        (lt_of_le_of_lt hs.2 (by norm_num [cuspDepth])))).continuousWithinAt
    have hval : ∀ s : ℝ, 12 / 5 ≤ s → s ≤ 488 / 5 →
        f s = η (e.toFun (x, halfSpaceOneLift s)) ∧
          |η (e.toFun (x, halfSpaceOneLift s)) - s| < 1 / 10 := by
      intro s h1 h2
      have hz : ((x, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 = s :=
        hlift s (by linarith)
      have hd := hdomv x (s := s) (by linarith) (by norm_num [cuspDepth]; linarith)
      refine ⟨(heq _ hd (by rw [hz]; exact h1) (by rw [hz]; exact h2)).self_of_nhds, ?_⟩
      have h := hηz _ hd (by rw [hz]; linarith) (by rw [hz]; linarith)
      rwa [hz] at h
    obtain ⟨hlo, hlo'⟩ := hval (12 / 5) le_rfl (by norm_num)
    obtain ⟨hhi, hhi'⟩ := hval (488 / 5) (by norm_num) le_rfl
    have hflo : f (12 / 5) < c := by
      rw [hlo]
      linarith [(abs_lt.mp hlo').2]
    have hfhi : c < f (488 / 5) := by
      rw [hhi]
      linarith [(abs_lt.mp hhi').1]
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num) hfc ⟨hflo.le, hfhi.le⟩
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, hfs⟩
    · rintro rfl
      exact hflo.ne hfs
    · rintro rfl
      exact hfhi.ne' hfs
  -- points with values in `[3, 97]` lie on the verticals over `(12/5, 488/5)`
  have hband : ∀ y, 3 ≤ η' y → η' y ≤ 97 →
      ∃ x : Torus, ∃ s ∈ Ioo (12 / 5 : ℝ) (488 / 5), e.toFun (x, halfSpaceOneLift s) = y := by
    intro y h3 h97
    obtain ⟨p, -, h1, h2, rfl, -⟩ := hin y h3 h97
    refine ⟨p.1, p.2.val 0, ⟨h1, h2⟩, ?_⟩
    rw [halfSpaceOneLift_val_zero_self p.2]
  refine ⟨η', hη', heq, hin, fun t ht3 ht97 => ?_, fun a b hab ha3 hb97 => ?_⟩
  · exact e.exists_diffeomorph_level_torus hη' (by norm_num) (by norm_num [cuspDepth]) hvert'
      (hcross t ht3 ht97) (fun y hy => hband y (hy ▸ ht3) (hy ▸ ht97))
  · obtain ⟨cs, hm, hval, -, D, hD⟩ := e.exists_band_diffeomorph_torus hη' hab (by norm_num)
      (by norm_num [cuspDepth]) hvert' (hcross a ha3 (by linarith))
      (fun y hy => hband y (le_trans ha3 hy.1) (le_trans hy.2 hb97))
    exact ⟨cs, hm, hval, D, hD⟩

end DifferentialGeometry.Geometry.Collapse
