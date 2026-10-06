import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# Distance windows in the cusps of a hyperbolic truncation (S26)

For a truncation `T` of a finite-volume hyperbolic model `H` and a cusp `φ = T.cuspMap i`
(an exact isometry from `dz² + e^{-z} q`):

* `isOpen_image_height_gt_S26`: `φ(T² × (a, ∞))` is open for `a ≥ 0`;
* `ofReal_height_sub_le_edist_S26`: leaving `φ(T² × (a, ∞))` from `φ q` costs `z(q) - a`;
* `ball_subset_window_S26`: the ball `B(φ q, r)`, `r < z(q)`, lies in `φ{|z - z(q)| < r}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) (i : Fin T.count)

/-- The positive-height part of the half collar. -/
def cuspPos_S26 : Set CuspHalfSpace := {q | 0 < q.2.val 0}

theorem isOpen_cuspPos_S26 : IsOpen cuspPos_S26 :=
  isOpen_lt continuous_const continuous_cusp_height

theorem contMDiff_cuspMap_S26 : ContMDiff halfCollarModel (𝓡 3) 1 (T.cuspMap i) :=
  (T.cuspEmbedding i).contMDiff.of_le (by simp)

theorem injective_cuspMap_S26 : Injective (T.cuspMap i) :=
  (T.cuspEmbedding i).isEmbedding.injective

theorem injective_mfderiv_cuspMap_S26 (p : CuspHalfSpace) :
    Injective (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) p) :=
  (T.cuspEmbedding i).isImmersion.mfderiv_injective (by simp) p

theorem isInvertible_mfderiv_cuspMap_S26 (p : CuspHalfSpace) :
    (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) p).IsInvertible := by
  have hdim : Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Module.finrank_prod]
  let L : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) p
  exact ⟨(L.toLinearMap.linearEquivOfInjective (injective_mfderiv_cuspMap_S26 T i p)
    hdim).toContinuousLinearEquiv, ContinuousLinearMap.ext fun v => rfl⟩

/-- Open subsets of positive height have open images. -/
theorem isOpen_image_of_subset_pos_S26 {V : Set CuspHalfSpace} (hV : IsOpen V)
    (hVp : V ⊆ cuspPos_S26) : IsOpen (T.cuspMap i '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨Φ, hpΦ, hΦV, heq, -, -⟩ := exists_finiteInteriorPatch (n := 1) le_rfl hV
    ((contMDiff_cuspMap_S26 T i).contMDiffOn) hp
    (cusp_isInteriorPoint_of_height_pos (hVp hp)) BoundarylessManifold.isInteriorPoint
    (by simp [Module.finrank_prod]) (injective_mfderiv_cuspMap_S26 T i p)
  have htarget : T.cuspMap i p ∈ Φ.target := by
    rw [heq hpΦ]
    exact Φ.map_source hpΦ
  apply Filter.mem_of_superset (Φ.open_target.mem_nhds htarget)
  intro z hzΦ
  have hsource := Φ.map_target hzΦ
  exact ⟨Φ.symm z, hΦV hsource, (heq hsource).trans (Φ.right_inv' hzΦ)⟩

/-- **(1)** The part of a cusp above height `a ≥ 0` is open. -/
theorem isOpen_image_height_gt_S26 {a : ℝ} (ha : 0 ≤ a) :
    IsOpen (T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0}) :=
  isOpen_image_of_subset_pos_S26 T i (isOpen_lt continuous_const continuous_cusp_height)
    fun _ hq => lt_of_le_of_lt ha hq

theorem contMDiffOn_invFunOn_S26 :
    ContMDiffOn (𝓡 3) halfCollarModel 1 (invFunOn (T.cuspMap i) cuspPos_S26)
      (T.cuspMap i '' cuspPos_S26) :=
  contMDiffOn_invFunOn_of_isInvertible_mfderiv isOpen_cuspPos_S26
    (contMDiff_cuspMap_S26 T i).contMDiffOn (injective_cuspMap_S26 T i).injOn
    (fun _ hV hVo => isOpen_image_of_subset_pos_S26 T i hVo hV)
    fun p _ => isInvertible_mfderiv_cuspMap_S26 T i p

/-- Curve lifting through the positive-height part of the cusp. -/
theorem exists_lift_S26 {γ : ℝ → H.Carrier} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ s) (hγU : MapsTo γ s (T.cuspMap i '' cuspPos_S26)) :
    ∃ c : ℝ → CuspHalfSpace, ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c s ∧
      ∀ t ∈ s, T.cuspMap i (c t) = γ t :=
  ⟨invFunOn (T.cuspMap i) cuspPos_S26 ∘ γ, (contMDiffOn_invFunOn_S26 T i).comp hγ hγU,
    fun _ ht => invFunOn_eq (hγU ht)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Height changes by at most the length along a lifted `C¹` curve. -/
theorem ofReal_abs_height_sub_le_pathELength_S26 {c : ℝ → CuspHalfSpace} {a b : ℝ}
    (hab : a ≤ b) (hc : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc a b)) :
    letI : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
      ⟨H.metric.toRiemannianMetric⟩
    ENNReal.ofReal |(c b).2.val 0 - (c a).2.val 0| ≤
      pathELength (𝓡 3) (T.cuspMap i ∘ c) a b := by
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  let A : ℝ → ℝ := fun t => (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).2 0
  have hdiff : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
    fun t ht => (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hheight : ENNReal.ofReal |(c b).2.val 0 - (c a).2.val 0| ≤
      ∫⁻ t in Ioo a b, ENNReal.ofReal |A t| := by
    have hζ : ContDiffOn ℝ 1 (fun s => (c s).2.val 0) (Icc a b) := by
      have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
          ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘
            (𝓡∂ 1) ∘ Prod.snd ∘ c) (Icc a b) :=
        (ContinuousLinearMap.contMDiff _).comp_contMDiffOn
          ((𝓡∂ 1).contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hc))
      exact contMDiffOn_iff_contDiffOn.mp h1
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hζ hab
    rw [← restrict_Ioo_eq_restrict_Icc] at h
    rw [Real.enorm_eq_ofReal_abs] at h
    refine h.trans (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_)
    have hsnd := (hasMFDerivAt_snd (c t)).comp t (hdiff t ht).hasMFDerivAt
    have hderiv := (hasDerivAt_val_zero_of_hasMFDerivAt hsnd).deriv
    change ‖deriv (fun s => (c s).2.val 0) t‖ₑ ≤ _
    rw [show (fun s => (c s).2.val 0) = fun s => ((Prod.snd ∘ c) s).val 0 from rfl, hderiv,
      Real.enorm_eq_ofReal_abs]
    rfl
  have hpt : ∀ t ∈ Ioo a b, ENNReal.ofReal |A t| ≤
      ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ c) t 1‖ₑ := by
    intro t ht
    have hed : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) (c t) :=
      ((contMDiff_cuspMap_S26 T i) (c t)).mdifferentiableAt one_ne_zero
    rw [mfderiv_comp t hed (hdiff t ht)]
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    apply ENNReal.ofReal_le_ofReal
    change |v.2 0| ≤
      Real.sqrt (H.metric.inner (T.cuspMap i (c t))
        (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (c t) v)
        (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (c t) v))
    rw [T.cuspIsometry i (c t) v v, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_height_le_cusp_inner (T.cusp i) (c t) v)
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  exact hheight.trans (setLIntegral_mono' measurableSet_Ioo hpt)

/-- A closed height band of the cusp has compact image. -/
theorem isCompact_image_band_S26 (α β : ℝ) :
    IsCompact (T.cuspMap i '' {p : CuspHalfSpace | α ≤ p.2.val 0 ∧ p.2.val 0 ≤ β}) := by
  have hset : {p : CuspHalfSpace | α ≤ p.2.val 0 ∧ p.2.val 0 ≤ β} =
      (fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace)) ''
        (univ ×ˢ Icc (max α 0) β) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(q.1, q.2.1 0), ⟨mem_univ _, max_le h1 q.2.2, h2⟩, ?_⟩
      exact Prod.ext rfl (halfSpaceOneLift_val_zero_self q.2)
    · rintro ⟨p, ⟨-, hp1, hp2⟩, rfl⟩
      have h0 : (halfSpaceOneLift p.2).1 0 = p.2 := by
        rw [halfSpaceOneLift_val_zero, max_eq_left ((le_max_right α 0).trans hp1)]
      change α ≤ (halfSpaceOneLift p.2).1 0 ∧ (halfSpaceOneLift p.2).1 0 ≤ β
      rw [h0]
      exact ⟨(le_max_left α 0).trans hp1, hp2⟩
  have hK : IsCompact ((univ : Set Torus) ×ˢ Icc (max α 0) β) :=
    isCompact_univ.prod isCompact_Icc
  have hPc : ContinuousOn (fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace))
      (univ ×ˢ Icc (max α 0) β) :=
    contMDiffOn_cuspVertical.continuousOn.mono
      (prod_mono subset_rfl fun s hs => (le_max_right α 0).trans hs.1)
  have hband : IsCompact {p : CuspHalfSpace | α ≤ p.2.val 0 ∧ p.2.val 0 ≤ β} := by
    rw [hset]
    exact hK.image_of_continuousOn hPc
  exact hband.image (contMDiff_cuspMap_S26 T i).continuous

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **First exit.** A `C¹` curve on `[0, b]` from `φ q` ending outside `φ{z > a}` (`a ≥ 0`,
`a < z(q)`) has length at least `z(q) - a`. -/
theorem ofReal_height_sub_le_pathELength_S26 {γ : ℝ → H.Carrier} {b : ℝ} (hb : 0 ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 b)) (q : CuspHalfSpace) {a : ℝ} (ha : 0 ≤ a)
    (hq : a < q.2.val 0) (h0 : γ 0 = T.cuspMap i q)
    (h1 : γ b ∉ T.cuspMap i '' {q' : CuspHalfSpace | a < q'.2.val 0}) :
    letI : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
      ⟨H.metric.toRiemannianMetric⟩
    ENNReal.ofReal (q.2.val 0 - a) ≤ pathELength (𝓡 3) γ 0 b := by
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  set V : Set CuspHalfSpace := {q' | a < q'.2.val 0} with hV
  have hVp : V ⊆ cuspPos_S26 := fun _ hq' => lt_of_le_of_lt ha hq'
  have hU : IsOpen (T.cuspMap i '' V) := isOpen_image_height_gt_S26 T i ha
  have hγc : ContinuousOn γ (Icc 0 b) := hγ.continuousOn
  by_contra hcon
  push Not at hcon
  have hfin : pathELength (𝓡 3) γ 0 b ≠ ⊤ := ne_top_of_lt hcon
  set ℓ := (pathELength (𝓡 3) γ 0 b).toReal with hℓ
  have hℓeq : ENNReal.ofReal ℓ = pathELength (𝓡 3) γ 0 b := ENNReal.ofReal_toReal hfin
  have hℓa : ℓ < q.2.val 0 - a := by
    rw [← hℓeq] at hcon
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mp hcon
  -- the first exit time
  set A : Set ℝ := Icc 0 b ∩ γ ⁻¹' (T.cuspMap i '' V)ᶜ with hA
  have hAc : IsClosed A := hγc.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have hbA : b ∈ A := ⟨⟨hb, le_rfl⟩, h1⟩
  have hAne : A.Nonempty := ⟨b, hbA⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf A with hs
  have hsA : s ∈ A := hAc.csInf_mem hAne hAbdd
  have hsb : s ≤ b := csInf_le hAbdd hbA
  have hbefore : ∀ t ∈ Ico 0 s, γ t ∈ T.cuspMap i '' V := by
    intro t ht
    by_contra hc
    exact absurd (csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans hsb⟩, hc⟩) (not_le.mpr ht.2)
  have hs0 : 0 < s := by
    rcases hsA.1.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hsA.2
      rw [← heq, h0]
      exact ⟨q, hq, rfl⟩
  -- before the exit time the curve stays in a compact band
  set Kb := T.cuspMap i '' {p : CuspHalfSpace | q.2.val 0 - ℓ ≤ p.2.val 0 ∧
    p.2.val 0 ≤ q.2.val 0 + ℓ} with hKb
  have hKc : IsClosed Kb := (isCompact_image_band_S26 T i _ _).isClosed
  have hinK : ∀ t ∈ Ico 0 s, γ t ∈ Kb := by
    intro t ht
    have hmaps : MapsTo γ (Icc 0 t) (T.cuspMap i '' cuspPos_S26) := by
      intro r hr
      exact image_mono hVp (hbefore r ⟨hr.1, hr.2.trans_lt ht.2⟩)
    obtain ⟨c, hc, hce⟩ := exists_lift_S26 T i
      (hγ.mono (Icc_subset_Icc le_rfl (ht.2.le.trans hsb))) hmaps
    have hc0 : c 0 = q := injective_cuspMap_S26 T i ((hce 0 ⟨le_rfl, ht.1⟩).trans h0)
    have hlen := ofReal_abs_height_sub_le_pathELength_S26 T i ht.1 hc
    rw [hc0] at hlen
    have hlen' : ENNReal.ofReal |(c t).2.val 0 - q.2.val 0| ≤ ENNReal.ofReal ℓ := by
      rw [hℓeq]
      calc _ ≤ pathELength (𝓡 3) (T.cuspMap i ∘ c) 0 t := hlen
        _ = pathELength (𝓡 3) γ 0 t := pathELength_congr fun r hr => hce r hr
        _ ≤ pathELength (𝓡 3) γ 0 b := pathELength_mono le_rfl (ht.2.le.trans hsb)
    have habs := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hlen'
    rw [abs_le] at habs
    refine ⟨c t, ⟨by linarith [habs.1], by linarith [habs.2]⟩, hce t ⟨ht.1, le_rfl⟩⟩
  have hcl : γ s ∈ Kb := by
    have hcw : ContinuousWithinAt γ (Ico 0 s) s :=
      (hγc s hsA.1).mono (fun t ht => ⟨ht.1, ht.2.le.trans hsb⟩)
    have hmem : s ∈ closure (Ico 0 s) := by
      rw [closure_Ico hs0.ne]
      exact ⟨hs0.le, le_rfl⟩
    have himg : γ '' Ico 0 s ⊆ Kb := by
      rintro _ ⟨t, ht, rfl⟩
      exact hinK t ht
    exact hKc.closure_subset_iff.mpr himg (hcw.mem_closure_image hmem)
  obtain ⟨p, hp, hps⟩ := hcl
  exact hsA.2 (hps ▸ ⟨p, show a < p.2.val 0 by linarith [hp.1], rfl⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **(2)** Leaving the part of a cusp above height `a ≥ 0` from `φ q` costs `z(q) - a`. -/
theorem ofReal_height_sub_le_edist_S26 (q : CuspHalfSpace) {a : ℝ} (ha : 0 ≤ a)
    (hq : a < q.2.val 0) {y : H.Carrier}
    (hy : y ∉ T.cuspMap i '' {q' : CuspHalfSpace | a < q'.2.val 0}) :
    ENNReal.ofReal (q.2.val 0 - a) ≤ riemannianEDistOf H.metric (T.cuspMap i q) y := by
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  refine le_of_forall_gt fun r hr => ?_
  change Manifold.riemannianEDist (𝓡 3) (T.cuspMap i q) y < r at hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  exact lt_of_le_of_lt (ofReal_height_sub_le_pathELength_S26 T i zero_le_one hγ q ha hq hγ0
    (hγ1 ▸ hy)) hlen

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **(3)** A ball of radius `r < z(q)` about `φ q` lies in the height window `|z - z(q)| < r`. -/
theorem ball_subset_window_S26 (q : CuspHalfSpace) {r : ℝ} (hr : 0 < r) (hq : r < q.2.val 0) :
    riemannianBallOf H.metric (T.cuspMap i q) r ⊆
      T.cuspMap i '' {q' : CuspHalfSpace | |q'.2.val 0 - q.2.val 0| < r} := by
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  intro y hy
  change Manifold.riemannianEDist (𝓡 3) (T.cuspMap i q) y < ENNReal.ofReal r at hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  have ha : 0 ≤ q.2.val 0 - r := by linarith
  have haq : q.2.val 0 - r < q.2.val 0 := by linarith
  have hstay : MapsTo γ (Icc 0 1) (T.cuspMap i '' cuspPos_S26) := by
    intro t ht
    by_contra hcon
    have hout : γ t ∉ T.cuspMap i '' {q' : CuspHalfSpace | q.2.val 0 - r < q'.2.val 0} :=
      fun hm => hcon (image_mono (fun _ hq' => lt_of_le_of_lt ha hq') hm)
    have h := ofReal_height_sub_le_pathELength_S26 T i ht.1 (hγ.mono (Icc_subset_Icc le_rfl ht.2))
      q ha haq hγ0 hout
    rw [sub_sub_cancel] at h
    exact absurd (h.trans (pathELength_mono le_rfl ht.2)) (not_le.mpr hlen)
  obtain ⟨c, hc, hce⟩ := exists_lift_S26 T i hγ hstay
  have hc0 : c 0 = q := injective_cuspMap_S26 T i ((hce 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hlen' := ofReal_abs_height_sub_le_pathELength_S26 T i zero_le_one hc
  rw [hc0] at hlen'
  have hcongr : pathELength (𝓡 3) (T.cuspMap i ∘ c) 0 1 = pathELength (𝓡 3) γ 0 1 :=
    pathELength_congr fun t ht => hce t ht
  rw [hcongr] at hlen'
  refine ⟨c 1, ?_, (hce 1 ⟨zero_le_one, le_rfl⟩).trans hγ1⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hr).mp (lt_of_le_of_lt hlen' hlen)

end GC.LongTime.Ch12
