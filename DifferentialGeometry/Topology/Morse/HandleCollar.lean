import DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Handle.Collar
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

private abbrev CollarDomain (k l : ℕ) := (CellBoundary k × EuclideanSpace ℝ (Fin l)) × ℝ

private def collarPole (k : ℕ) [NeZero k] : CellBoundary k :=
  ⟨EuclideanSpace.single ⟨0, NeZero.pos k⟩ 1, by simp⟩

private def collarRadicand {n k : ℕ} (ε r : ℝ) (p : CollarDomain k (n - k)) : ℝ :=
  2 * ε + r ^ 2 * ‖p.1.2‖ ^ 2 - 2 * p.2

private def collarModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CollarDomain k (n - k)) : MorseModel n :=
  recombine hk (Real.sqrt (collarRadicand ε r p) • p.1.1.val) (r • p.1.2)

private def collarUnit {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (y : MorseModel n) : CellBoundary k :=
  if h : negPart hk y = 0 then collarPole k else
    ⟨‖negPart hk y‖⁻¹ • negPart hk y, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩

private def collarModelInverse {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) (y : MorseModel n) : CollarDomain k (n - k) :=
  ((collarUnit hk y, r⁻¹ • posPart hk y),
    ε + (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) / 2)

private theorem collarUnit_val {n k : ℕ} (hk : k ≤ n) [NeZero k]
    {y : MorseModel n} (hy : negPart hk y ≠ 0) :
    (collarUnit hk y).val = ‖negPart hk y‖⁻¹ • negPart hk y := by
  simp only [collarUnit, dif_neg hy]

private theorem continuous_collarRadicand {n k : ℕ} (ε r : ℝ) :
    Continuous (collarRadicand (n := n) (k := k) ε r) := by
  unfold collarRadicand
  fun_prop

private theorem continuous_collarModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) :
    Continuous (collarModelPoint hk ε r) := by
  have hu : Continuous (fun p : CollarDomain k (n - k) => p.1.1.val) := by fun_prop
  have hv : Continuous (fun p : CollarDomain k (n - k) => p.1.2) := by fun_prop
  have hs : Continuous (fun p : CollarDomain k (n - k) =>
      Real.sqrt (collarRadicand ε r p)) :=
    Real.continuous_sqrt.comp (continuous_collarRadicand ε r)
  exact (continuous_recombine hk).comp
    ((hs.smul hu).prodMk ((continuous_const (y := r)).smul hv))

private theorem collarModelPoint_neg_norm {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CollarDomain k (n - k)) :
    ‖negPart hk (collarModelPoint hk ε r p)‖ = Real.sqrt (collarRadicand ε r p) := by
  rw [collarModelPoint, negPart_recombine, norm_smul, p.1.1.property, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem collarModelPoint_neg_ne_zero {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CollarDomain k (n - k)) (hp : 0 < collarRadicand ε r p) :
    negPart hk (collarModelPoint hk ε r p) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [collarModelPoint_neg_norm]
  exact (Real.sqrt_pos.2 hp).ne'

private theorem collarModelPoint_normalForm {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (p : CollarDomain k (n - k)) (hp : 0 ≤ collarRadicand ε r p) :
    morseNormalForm hk c (collarModelPoint hk ε r p) = c - ε + p.2 := by
  have hs : ‖r • p.1.2‖ ^ 2 = r ^ 2 * ‖p.1.2‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [morseNormalForm_split, collarModelPoint_neg_norm,
    collarModelPoint, posPart_recombine, hs, Real.sq_sqrt hp]
  dsimp [collarRadicand]
  ring

private theorem collarModelInverse_left {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) (hr : r ≠ 0) (p : CollarDomain k (n - k))
    (hp : 0 < collarRadicand ε r p) :
    collarModelInverse hk ε r (collarModelPoint hk ε r p) = p := by
  have hpos := Real.sqrt_pos.2 hp
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      change (collarUnit hk (collarModelPoint hk ε r p)).val = p.1.1.val
      rw [collarUnit_val hk (collarModelPoint_neg_ne_zero hk ε r p hp),
        collarModelPoint_neg_norm, collarModelPoint, negPart_recombine,
        smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    · change r⁻¹ • posPart hk (collarModelPoint hk ε r p) = p.1.2
      rw [collarModelPoint, posPart_recombine, smul_smul, inv_mul_cancel₀ hr, one_smul]
  · have h := collarModelPoint_normalForm hk (0 : ℝ) ε r p hp.le
    rw [morseNormalForm_split] at h
    change ε + (‖posPart hk (collarModelPoint hk ε r p)‖ ^ 2 -
      ‖negPart hk (collarModelPoint hk ε r p)‖ ^ 2) / 2 = p.2
    linarith

private theorem collarModelInverse_radicand {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) (hr : r ≠ 0) (y : MorseModel n) :
    collarRadicand ε r (collarModelInverse hk ε r y) = ‖negPart hk y‖ ^ 2 := by
  have hs : r ^ 2 * ‖r⁻¹ • posPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
  dsimp [collarRadicand, collarModelInverse]
  rw [hs]
  ring

private theorem collarModelInverse_right {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) (hr : r ≠ 0) (y : MorseModel n) (hy : negPart hk y ≠ 0) :
    collarModelPoint hk ε r (collarModelInverse hk ε r y) = y := by
  unfold collarModelPoint
  rw [collarModelInverse_radicand hk ε r hr y, Real.sqrt_sq (norm_nonneg _)]
  change recombine hk (‖negPart hk y‖ • (collarUnit hk y).val)
    (r • (r⁻¹ • posPart hk y)) = y
  rw [collarUnit_val hk hy, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy),
    one_smul, smul_smul, mul_inv_cancel₀ hr, one_smul, recombine_decompose]

private theorem continuousOn_collarUnit {n k : ℕ} (hk : k ≤ n) [NeZero k] :
    ContinuousOn (collarUnit hk) {y : MorseModel n | negPart hk y ≠ 0} := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have h : ContinuousOn (fun y : MorseModel n => ‖negPart hk y‖⁻¹ • negPart hk y)
      {y : MorseModel n | negPart hk y ≠ 0} :=
    ((continuous_negPart hk).norm.continuousOn.inv₀
      (fun y hy => norm_ne_zero_iff.mpr hy)).smul (continuous_negPart hk).continuousOn
  exact h.congr (fun y hy => collarUnit_val hk hy)

private theorem continuousOn_collarModelInverse {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) :
    ContinuousOn (collarModelInverse hk ε r) {y : MorseModel n | negPart hk y ≠ 0} := by
  have hv : Continuous (fun y : MorseModel n => r⁻¹ • posPart hk y) :=
    (continuous_const (y := r⁻¹)).smul (continuous_posPart hk)
  have ht : Continuous (fun y : MorseModel n =>
      ε + (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) / 2) := by
    exact continuous_const.add (((continuous_posPart hk).norm.pow 2).sub
      ((continuous_negPart hk).norm.pow 2) |>.div_const 2)
  exact ((continuousOn_collarUnit hk).prodMk hv.continuousOn).prodMk ht.continuousOn

private def collarModelChart {n k : ℕ} (hk : k ≤ n) [NeZero k]
    (ε r : ℝ) (hr : r ≠ 0) : OpenPartialHomeomorph (CollarDomain k (n - k)) (MorseModel n) where
  toFun := collarModelPoint hk ε r
  invFun := collarModelInverse hk ε r
  source := {p | 0 < collarRadicand ε r p}
  target := {y | negPart hk y ≠ 0}
  map_source' := collarModelPoint_neg_ne_zero hk ε r
  map_target' := by
    intro y hy
    change 0 < collarRadicand ε r (collarModelInverse hk ε r y)
    rw [collarModelInverse_radicand hk ε r hr y]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hy)
  left_inv' := collarModelInverse_left hk ε r hr
  right_inv' := collarModelInverse_right hk ε r hr
  open_source := isOpen_lt continuous_const (continuous_collarRadicand ε r)
  open_target := isOpen_ne_fun (continuous_negPart hk) continuous_const
  continuousOn_toFun := (continuous_collarModelPoint hk ε r).continuousOn
  continuousOn_invFun := continuousOn_collarModelInverse hk ε r

private theorem contDiff_collarNegPart {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ ∞ (negPart hk) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℝ ∞ (fun y : MorseModel n => y (negIdx hk i))
  fun_prop

private theorem contDiff_collarPosPart {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ ∞ (posPart hk) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℝ ∞ (fun y : MorseModel n => y (posIdx hk i))
  fun_prop

private theorem contDiff_collarRecombine {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := by
  apply contDiff_pi.2
  intro i
  by_cases hi : i.val < k
  · simp only [recombine, dif_pos hi]
    fun_prop
  · simp only [recombine, dif_neg hi]
    fun_prop

section Smooth

variable {n k : ℕ} (hk : k ≤ n) [NeZero k]

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold

local notation "Iext" =>
  (ModelWithCorners.prod (ModelWithCorners.prod (𝓡 (k - 1)) (𝓡 (n - k))) 𝓘(ℝ, ℝ))

private theorem contMDiffOn_collarUnit :
    ContMDiffOn 𝓘(ℝ, MorseModel n) (𝓡 (k - 1)) ∞ (collarUnit hk)
      {y : MorseModel n | negPart hk y ≠ 0} := by
  let U : TopologicalSpace.Opens (MorseModel n) :=
    ⟨{y | negPart hk y ≠ 0}, isOpen_ne_fun (continuous_negPart hk) continuous_const⟩
  have hnorm : ContDiffOn ℝ ∞ (fun y : MorseModel n => ‖negPart hk y‖) U :=
    (contDiff_collarNegPart hk).contDiffOn.norm ℝ (fun y hy => hy)
  have ha : ContDiffOn ℝ ∞ (fun y : MorseModel n => ‖negPart hk y‖⁻¹ • negPart hk y) U :=
    (hnorm.inv (fun y hy => norm_ne_zero_iff.mpr hy)).smul
      (contDiff_collarNegPart hk).contDiffOn
  have hv : ContMDiff 𝓘(ℝ, MorseModel n) (𝓡 k) ∞ (fun y : U => (collarUnit hk y.val).val) := by
    intro y
    have hval : ContMDiffOn 𝓘(ℝ, MorseModel n) (𝓡 k) ∞
        (fun y : MorseModel n => (collarUnit hk y).val) U :=
      ha.contMDiffOn.congr (fun y hy => collarUnit_val hk hy)
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, MorseModel n)) (I' := 𝓡 k)
      (U := U) (f := fun y : MorseModel n => (collarUnit hk y).val) (x := y)).mpr
      ((hval y.val y.property).contMDiffAt (U.isOpen.mem_nhds y.property))
  have hs := hv.codRestrict_sphere (n := k - 1)
    (fun y => (cellBoundarySphereHomeomorph k (collarUnit hk y.val)).property)
  have h : ContMDiff 𝓘(ℝ, MorseModel n) (𝓡 (k - 1)) ∞
      (fun y : U => collarUnit hk y.val) :=
    (cellBoundarySphereDiffeomorph k).symm.contMDiff.comp hs
  intro y hy
  exact ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, MorseModel n)) (I' := 𝓡 (k - 1))
    (U := U) (f := collarUnit hk) (x := ⟨y, hy⟩)).mp (h ⟨y, hy⟩)).contMDiffWithinAt

private theorem contMDiffOn_collarModelInverse (ε r : ℝ) :
    ContMDiffOn 𝓘(ℝ, MorseModel n) Iext ∞ (collarModelInverse hk ε r)
      {y : MorseModel n | negPart hk y ≠ 0} := by
  have hv : ContMDiff 𝓘(ℝ, MorseModel n) (𝓡 (n - k)) ∞
      (fun y : MorseModel n => r⁻¹ • posPart hk y) :=
    ((contDiff_const (c := r⁻¹)).smul (contDiff_collarPosPart hk)).contMDiff
  have ht : ContDiff ℝ ∞ (fun y : MorseModel n =>
      ε + (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) / 2) :=
    contDiff_const.add ((((contDiff_norm_sq ℝ).comp (contDiff_collarPosPart hk)).sub
      ((contDiff_norm_sq ℝ).comp (contDiff_collarNegPart hk))).div_const 2)
  exact ((contMDiffOn_collarUnit hk).prodMk hv.contMDiffOn).prodMk ht.contMDiff.contMDiffOn

private theorem contMDiffOn_collarModelPoint (ε r : ℝ) :
    ContMDiffOn Iext 𝓘(ℝ, MorseModel n) ∞ (collarModelPoint hk ε r)
      {p | 0 < collarRadicand ε r p} := by
  have hu : ContMDiff Iext (𝓡 k) ∞ (fun p : CollarDomain k (n - k) => p.1.1.val) :=
    (cellBoundaryInclusion_contMDiff k).comp contMDiff_fst.fst
  have hv : ContMDiff Iext (𝓡 (n - k)) ∞ (fun p : CollarDomain k (n - k) => p.1.2) :=
    contMDiff_fst.snd
  have ht : ContMDiff Iext 𝓘(ℝ, ℝ) ∞ (fun p : CollarDomain k (n - k) => p.2) :=
    contMDiff_snd
  have ha : ContMDiff Iext 𝓘(ℝ, ℝ) ∞ (collarRadicand (n := n) (k := k) ε r) :=
    (contMDiff_const.add (contMDiff_const.mul ((contDiff_norm_sq ℝ).contMDiff.comp hv))).sub
      (contMDiff_const.mul ht)
  have hsqrt : ContDiffOn ℝ ∞ Real.sqrt (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.sqrt (fun y hy => ne_of_gt hy)
  have hs : ContMDiffOn Iext 𝓘(ℝ, ℝ) ∞
      (fun p : CollarDomain k (n - k) => Real.sqrt (collarRadicand ε r p))
      {p | 0 < collarRadicand ε r p} :=
    hsqrt.contMDiffOn.comp ha.contMDiffOn (fun p hp => hp)
  have hrconst : ContMDiff Iext 𝓘(ℝ, ℝ) ∞
      (fun _ : CollarDomain k (n - k) => r) := contMDiff_const
  have hpair : ContMDiffOn Iext 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) ∞
      (fun p : CollarDomain k (n - k) =>
        (Real.sqrt (collarRadicand ε r p) • p.1.1.val, r • p.1.2))
      {p | 0 < collarRadicand ε r p} := by
    apply (contMDiffOn_prod_module_iff _).mpr
    exact ⟨hs.smul hu.contMDiffOn, (hrconst.smul hv).contMDiffOn⟩
  exact (contDiff_collarRecombine hk).contMDiff.comp_contMDiffOn hpair

end Smooth

private theorem collarModelPoint_zero {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : AttachingRegion k (n - k)) :
    collarModelPoint hk ε r ((p.1, p.2.val), 0) = cocoreModelPoint hk ε r p := by
  simp only [collarModelPoint, collarRadicand, mul_zero, sub_zero, cocoreModelPoint,
    negPart_cellMap_smul]

private theorem exists_product_interval_subset {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (ε : ℝ) (hε : 0 < ε)
    (N : Set (X × ℝ)) (hN : IsOpen N) (hzero : ∀ p : X, (p, 0) ∈ N) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∀ (p : X) (t : ℝ), t ∈ Set.Ioo (-δ) δ → (p, t) ∈ N := by
  have hzero' : (Set.univ : Set X) ×ˢ {(0 : ℝ)} ⊆ N := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero p
  obtain ⟨U, V, _, hV, hU, hV0, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hN hzero'
  obtain ⟨a, ha, hab⟩ := Metric.isOpen_iff.mp hV 0 (hV0 (by simp))
  let δ := min a (ε / 2)
  have hδ : 0 < δ := lt_min ha (by positivity)
  refine ⟨δ, hδ, ?_, ?_⟩
  · have hle : δ ≤ ε / 2 := min_le_right _ _
    linarith
  · intro p t ht
    have habs : |t| < a := (abs_lt.2 ht).trans_le (min_le_left _ _)
    have htV : t ∈ V := hab (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using habs)
    exact hUV ⟨hU (Set.mem_univ p), htV⟩

private theorem modelHandleRoundMap_eq_modelHandleMap_of_flat
    {n k : ℕ} (hk : k ≤ n) {ε r δ θ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hr : 0 < r)
    (p : StandardHandle k (n - k))
    (hflatδ : ‖p.2.val‖ ^ 2 < 1 - δ / r ^ 2)
    (hflatθ : ‖p.2.val‖ ^ 2 < 1 - θ / r ^ 2) :
    modelHandleRoundMap hk ε r δ θ p = modelHandleMap hk ε r p := by
  have hnorm : ‖p.1.val‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖p.1.val‖ := by linarith [norm_nonneg p.1.val]
    simpa using sq_le_sq' hneg p.1.property
  have hq := modelRoundCapQ_eq_r2b_of_flat hε hδ hθ hr hnorm
    (sq_nonneg ‖p.2.val‖) hflatδ hflatθ
  have hpos : (Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1.val‖ ^ 2) (‖p.2.val‖ ^ 2)) /
      ‖p.2.val‖) • p.2.val = r • p.2.val := by
    by_cases hv : p.2.val = 0
    · simp [hv]
    · have hne : ‖p.2.val‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hsqrt : Real.sqrt (r ^ 2 * ‖p.2.val‖ ^ 2) = r * ‖p.2.val‖ := by
        rw [← mul_pow, Real.sqrt_sq (mul_nonneg hr.le (norm_nonneg _))]
      rw [hq, hsqrt]
      congr 1
      exact mul_div_cancel_right₀ r hne
  simp only [modelHandleRoundMap, modelHandleMap, hpos]

private theorem flat_collar_time_mem {ε r Δ b : ℝ}
    (hε : 0 < ε) (hΔ : 0 < Δ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (s : Set.Ico (0 : ℝ) 1) (hs : s.val < Δ / (2 * ε + r ^ 2)) :
    (2 * ε + r ^ 2 * b) * (2 * s.val - s.val ^ 2) / 2 ∈ Set.Ioo (-Δ) Δ := by
  let B := 2 * ε + r ^ 2 * b
  let C := 2 * ε + r ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by
    dsimp [B, C]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (sq_nonneg r)]
  have hs0 : 0 ≤ s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hCs : C * s.val < Δ := by
    have h := (lt_div_iff₀ hC).mp hs
    simpa only [mul_comm] using h
  have hτ0 : 0 ≤ B * (2 * s.val - s.val ^ 2) / 2 := by
    have hprod : 0 ≤ s.val * (2 - s.val) := mul_nonneg hs0 (by linarith)
    exact div_nonneg (mul_nonneg hB.le (by nlinarith)) (by norm_num)
  have hτs : B * (2 * s.val - s.val ^ 2) / 2 ≤ B * s.val := by
    nlinarith [mul_nonneg hB.le (sq_nonneg s.val)]
  have hBs : B * s.val ≤ C * s.val := mul_le_mul_of_nonneg_right hBC hs0
  exact ⟨by change -Δ < B * (2 * s.val - s.val ^ 2) / 2; linarith,
    lt_of_le_of_lt (hτs.trans hBs) hCs⟩

private theorem flat_collar_parameter_inverse {ε r b : ℝ}
    (hε : 0 < ε) (hb0 : 0 ≤ b) (s : Set.Ico (0 : ℝ) 1) :
    1 - Real.sqrt (1 -
      2 * ((2 * ε + r ^ 2 * b) * (2 * s.val - s.val ^ 2) / 2) /
        (2 * ε + r ^ 2 * b)) = s.val := by
  have hB : 2 * ε + r ^ 2 * b ≠ 0 := by positivity
  have he : 1 -
      2 * ((2 * ε + r ^ 2 * b) * (2 * s.val - s.val ^ 2) / 2) /
        (2 * ε + r ^ 2 * b) = (1 - s.val) ^ 2 := by
    field_simp [hB]
    ring
  rw [he, Real.sqrt_sq (by linarith [s.property.2] : 0 ≤ 1 - s.val)]
  ring

private theorem handleRoundEmbedding_attachingCollar_eq_cocore_collar_of_flat
    {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hr : 0 < r)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (Φ : OpenPartialHomeomorph ((CellBoundary k × EuclideanSpace ℝ (Fin (n - k))) × ℝ) M)
    (hformula : ∀ p, Φ p = data.χ (recombine hk
      (Real.sqrt (2 * ε + r ^ 2 * ‖p.1.2‖ ^ 2 - 2 * p.2) • p.1.1.val) (r • p.1.2)))
    (hwidth : ∀ (p : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-Δ) Δ →
      ((p.1, p.2.val), t) ∈ Φ.source)
    (hheight : ∀ p ∈ Φ.source, f (Φ p) = c - ε + p.2)
    (p : AttachingRegion k (n - k)) (s : Set.Ico (0 : ℝ) 1)
    (hflatδ : ‖p.2.val‖ ^ 2 < 1 - δ / r ^ 2)
    (hflatθ : ‖p.2.val‖ ^ 2 < 1 - θ / r ^ 2)
    (hs : s.val < Δ / (2 * ε + r ^ 2)) :
    let τ := (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
    let q : StandardHandle k (n - k) := (Handle.attachingCollar k (n - k)) (p, s)
    τ ∈ Set.Ioo (-Δ) Δ ∧
      ((p.1, p.2.val), τ) ∈ Φ.source ∧
      handleRoundEmbedding hk c ε r δ θ data q = Φ ((p.1, p.2.val), τ) ∧
      Φ.symm (handleRoundEmbedding hk c ε r δ θ data q) = ((p.1, p.2.val), τ) ∧
      f (handleRoundEmbedding hk c ε r δ θ data q) = c - ε + τ ∧
      1 - Real.sqrt (1 - 2 * τ / (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2)) = s.val := by
  let τ := (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
  let q : StandardHandle k (n - k) := (Handle.attachingCollar k (n - k)) (p, s)
  have hq : q = (Homotopy.radialStep k (Homotopy.icoToI s)
      (cellBoundaryInclusion k p.1), p.2) := Handle.attachingCollar_apply k (n - k) p s
  have hq₁ : q.1.val = (1 - s.val) • p.1.val := by rw [hq]; rfl
  have hq₂ : q.2 = p.2 := by rw [hq]
  have hb1 : ‖p.2.val‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖p.2.val‖ := by linarith [norm_nonneg p.2.val]
    simpa using sq_le_sq' hneg p.2.property
  have hτ := flat_collar_time_mem hε hΔ (sq_nonneg ‖p.2.val‖) hb1 s hs
  have hsource := hwidth p τ hτ
  have hB : 0 ≤ 2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2 := by positivity
  have hsqrt : Real.sqrt (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2 - 2 * τ) =
      Real.sqrt (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (1 - s.val) := by
    have he : 2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2 - 2 * τ =
        (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (1 - s.val) ^ 2 := by dsimp [τ]; ring
    rw [he, Real.sqrt_mul hB, Real.sqrt_sq (by linarith [s.property.2])]
  have hagree : handleRoundEmbedding hk c ε r δ θ data q = Φ ((p.1, p.2.val), τ) := by
    rw [handleRoundEmbedding, modelHandleRoundMap_eq_modelHandleMap_of_flat hk hε hδ hθ hr q
      (by simpa only [hq₂] using hflatδ) (by simpa only [hq₂] using hflatθ), hformula]
    congr 1
    dsimp only [modelHandleMap]
    rw [hq₁, hq₂, smul_smul, hsqrt]
  exact ⟨hτ, hsource, hagree, by rw [hagree, Φ.left_inv hsource],
    by rw [hagree]; exact hheight _ hsource,
    flat_collar_parameter_inverse hε (sq_nonneg ‖p.2.val‖) s⟩

section Ambient

variable {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
  (data : MorseChart n k hk c I f)

private def collarChartNeighborhood : Set (MorseModel n) :=
  {y | morseNorm n y < data.R ∧ ‖y‖ < data.R'}

private theorem isOpen_collarChartNeighborhood :
    IsOpen (collarChartNeighborhood hk c data) := by
  have hm : Continuous (morseNorm n) :=
    continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin n => ℝ))
  exact (isOpen_lt hm continuous_const).inter (isOpen_lt continuous_norm continuous_const)

private def collarAmbientChart [NeZero k] (hr : r ≠ 0) :
    OpenPartialHomeomorph (CollarDomain k (n - k)) M :=
  (collarModelChart hk ε r hr).trans
    (data.χ.restrOpen (collarChartNeighborhood hk c data)
      (isOpen_collarChartNeighborhood hk c data))

private theorem collarAmbientChart_apply [NeZero k] (hr : r ≠ 0)
    (p : CollarDomain k (n - k)) :
    collarAmbientChart hk c ε r data hr p = data.χ (collarModelPoint hk ε r p) := rfl

private theorem collarAmbientChart_height [NeZero k] (hr : r ≠ 0)
    (p : CollarDomain k (n - k))
    (hp : p ∈ (collarAmbientChart hk c ε r data hr).source) :
    f (collarAmbientChart hk c ε r data hr p) = c - ε + p.2 := by
  have hR : morseNorm n (collarModelPoint hk ε r p) ≤ data.R := hp.2.2.1.le
  rw [collarAmbientChart_apply, data.hnorm _ hR]
  exact collarModelPoint_normalForm hk c ε r p hp.1.le

private theorem collarAmbientChart_inverse_time [NeZero k] (hr : r ≠ 0)
    (x : M) (hx : x ∈ (collarAmbientChart hk c ε r data hr).target) :
    ((collarAmbientChart hk c ε r data hr).symm x).2 = f x - (c - ε) := by
  have h := data.hnorm (data.χ.symm x) hx.1.2.1.le
  rw [data.χ.right_inv hx.1.1, morseNormalForm_split] at h
  change ε + (‖posPart hk (data.χ.symm x)‖ ^ 2 -
    ‖negPart hk (data.χ.symm x)‖ ^ 2) / 2 = f x - (c - ε)
  linarith

variable [NeZero k]

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold

local notation "Iext" =>
  (ModelWithCorners.prod (ModelWithCorners.prod (𝓡 (k - 1)) (𝓡 (n - k))) 𝓘(ℝ, ℝ))

private theorem contMDiffOn_collarAmbientChart (hr : r ≠ 0) :
    ContMDiffOn Iext I ∞ (collarAmbientChart hk c ε r data hr)
      (collarAmbientChart hk c ε r data hr).source := by
  have hc : ContMDiffOn Iext 𝓘(ℝ, MorseModel n) ∞ (collarModelPoint hk ε r)
      (collarAmbientChart hk c ε r data hr).source :=
    (contMDiffOn_collarModelPoint hk ε r).mono (fun p hp => hp.1)
  change ContMDiffOn Iext I ∞ (fun p => data.χ (collarModelPoint hk ε r p))
    (collarAmbientChart hk c ε r data hr).source
  exact data.hχon.comp hc (fun p hp => by
    have hnorm : ‖collarModelPoint hk ε r p‖ < data.R' := hp.2.2.2
    change collarModelPoint hk ε r p ∈ Metric.ball 0 data.R'
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm)

private theorem contMDiffOn_collarAmbientChart_symm (hr : r ≠ 0) :
    ContMDiffOn I Iext ∞ (collarAmbientChart hk c ε r data hr).symm
      (collarAmbientChart hk c ε r data hr).target := by
  have hχ : ContMDiffOn I 𝓘(ℝ, MorseModel n) ∞ data.χ.symm
      (collarAmbientChart hk c ε r data hr).target :=
    data.hχsymmOn.mono (fun x hx =>
      ⟨data.χ.symm x, by simpa only [Metric.mem_ball, dist_zero_right] using hx.1.2.2,
        data.χ.right_inv hx.1.1⟩)
  exact (contMDiffOn_collarModelInverse hk ε r).comp hχ (fun x hx => hx.2)

private theorem collarAmbientChart_source_zero (hr : r ≠ 0) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (p : AttachingRegion k (n - k)) :
    ((p.1, p.2.val), 0) ∈ (collarAmbientChart hk c ε r data hr).source := by
  have hpR := (cocoreModelPoint_norm_le hk ε r hε.le p).trans_lt hR
  have hpR' := (morseNorm_piNorm_le (cocoreModelPoint hk ε r p)).trans_lt
    ((cocoreModelPoint_norm_le hk ε r hε.le p).trans_lt hR')
  change 0 < collarRadicand ε r ((p.1, p.2.val), 0) ∧
    collarModelPoint hk ε r ((p.1, p.2.val), 0) ∈ data.χ.source ∧
      collarModelPoint hk ε r ((p.1, p.2.val), 0) ∈ collarChartNeighborhood hk c data
  rw [collarModelPoint_zero]
  refine ⟨?_, data.hχsrc _ hpR.le, hpR, hpR'⟩
  simp only [collarRadicand, mul_zero, sub_zero]
  positivity

private theorem exists_collarAmbientChart_width (hr : r ≠ 0) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R') :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∀ (p : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
        ((p.1, p.2.val), t) ∈ (collarAmbientChart hk c ε r data hr).source := by
  let j : AttachingRegion k (n - k) × ℝ → CollarDomain k (n - k) :=
    fun q => ((q.1.1, q.1.2.val), q.2)
  have hj : Continuous j := by fun_prop
  have hopen : IsOpen (j ⁻¹' (collarAmbientChart hk c ε r data hr).source) :=
    (collarAmbientChart hk c ε r data hr).open_source.preimage hj
  exact exists_product_interval_subset ε hε _ hopen
    (fun p => collarAmbientChart_source_zero hk c ε r data hr hε hR hR' p)

theorem exists_cocore_collar (hr : r ≠ 0) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R') :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∃ Φ : OpenPartialHomeomorph ((CellBoundary k × EuclideanSpace ℝ (Fin (n - k))) × ℝ) M,
        ContMDiffOn Iext I ∞ Φ Φ.source ∧
        ContMDiffOn I Iext ∞ Φ.symm Φ.target ∧
        (∀ p, Φ p = data.χ (recombine hk
          (Real.sqrt (2 * ε + r ^ 2 * ‖p.1.2‖ ^ 2 - 2 * p.2) • p.1.1.val) (r • p.1.2))) ∧
        (∀ x ∈ Φ.target,
          (Φ.symm x).1.1.val = ‖negPart hk (data.χ.symm x)‖⁻¹ • negPart hk (data.χ.symm x) ∧
          (Φ.symm x).1.2 = r⁻¹ • posPart hk (data.χ.symm x) ∧
          (Φ.symm x).2 = f x - (c - ε)) ∧
        (∀ p ∈ Φ.source, f (Φ p) = c - ε + p.2) ∧
        (∀ (p : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
          ((p.1, p.2.val), t) ∈ Φ.source) ∧
        (∀ p : AttachingRegion k (n - k),
          Φ ((p.1, p.2.val), 0) = (cocoreAttachingEmbedding hk c ε r data hε hR.le p).val) ∧
        (∀ (δ₁ θ : ℝ), 0 < δ₁ → 0 < θ → 0 < r →
          ∀ (p : AttachingRegion k (n - k)) (s : Set.Ico (0 : ℝ) 1),
            ‖p.2.val‖ ^ 2 < 1 - δ₁ / r ^ 2 →
            ‖p.2.val‖ ^ 2 < 1 - θ / r ^ 2 → s.val < δ / (2 * ε + r ^ 2) →
            let τ := (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
            let q : StandardHandle k (n - k) := (Handle.attachingCollar k (n - k)) (p, s)
            τ ∈ Set.Ioo (-δ) δ ∧ ((p.1, p.2.val), τ) ∈ Φ.source ∧
              handleRoundEmbedding hk c ε r δ₁ θ data q = Φ ((p.1, p.2.val), τ) ∧
              Φ.symm (handleRoundEmbedding hk c ε r δ₁ θ data q) = ((p.1, p.2.val), τ) ∧
              f (handleRoundEmbedding hk c ε r δ₁ θ data q) = c - ε + τ ∧
              1 - Real.sqrt (1 - 2 * τ / (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2)) = s.val) := by
  obtain ⟨δ, hδ, hδε, hwidth⟩ := exists_collarAmbientChart_width hk c ε r data hr hε hR hR'
  refine ⟨δ, hδ, hδε, collarAmbientChart hk c ε r data hr,
    contMDiffOn_collarAmbientChart hk c ε r data hr,
    contMDiffOn_collarAmbientChart_symm hk c ε r data hr, ?_, ?_,
    collarAmbientChart_height hk c ε r data hr, hwidth, ?_, ?_⟩
  · intro p
    rfl
  · intro x hx
    refine ⟨?_, rfl, collarAmbientChart_inverse_time hk c ε r data hr x hx⟩
    exact collarUnit_val hk hx.2
  · intro p
    rw [collarAmbientChart_apply, collarModelPoint_zero]
    rfl
  · intro δ₁ θ hδ₁ hθ hrpos p s hflatδ hflatθ hs
    exact handleRoundEmbedding_attachingCollar_eq_cocore_collar_of_flat hk c ε r δ₁ θ data
      hε hδ₁ hθ hrpos δ hδ (collarAmbientChart hk c ε r data hr)
      (fun _ => rfl) hwidth (collarAmbientChart_height hk c ε r data hr)
      p s hflatδ hflatθ hs

section Closed

variable [NeZero (n - k)] [I.Boundaryless] [IsManifold I ∞ M]

attribute [local instance] closedCellChartedSpace

local notation "Iclosed" =>
  (ModelWithCorners.prod (ModelWithCorners.prod (𝓡 (k - 1))
    (modelWithCornersEuclideanHalfSpace (((n - k) - 1) + 1))) 𝓘(ℝ, ℝ))

private theorem isSmoothEmbedding_collar_restrict (δ : ℝ)
    (Φ : OpenPartialHomeomorph (CollarDomain k (n - k)) M)
    (hΦ : ContMDiffOn Iext I ∞ Φ Φ.source)
    (hΦsymm : ContMDiffOn I Iext ∞ Φ.symm Φ.target)
    (hwidth : ∀ (p : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
      ((p.1, p.2.val), t) ∈ Φ.source) :
    let T : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-δ) δ, isOpen_Ioo⟩
    Manifold.IsSmoothEmbedding Iclosed I ∞
      (fun p : AttachingRegion k (n - k) × T => Φ ((p.1.1, p.1.2.val), p.2.val)) := by
  let T : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-δ) δ, isOpen_Ioo⟩
  let j : AttachingRegion k (n - k) × T → CollarDomain k (n - k) :=
    fun p => ((p.1.1, p.1.2.val), p.2.val)
  let _ : ChartedSpace (EuclideanHalfSpace (((n - k) - 1) + 1))
      (ClosedCell (((n - k) - 1) + 1)) := closedCellChartedSpaceSucc ((n - k) - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace (((n - k) - 1) + 1)) ∞
      (ClosedCell (((n - k) - 1) + 1)) := closedCellIsManifold ((n - k) - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace (((n - k) - 1) + 1)) ∞
      (ClosedCell (n - k)) := isManifoldOfHomeomorph
        (modelWithCornersEuclideanHalfSpace (((n - k) - 1) + 1)) (closedCellReindexHomeo (n - k))
  have hj : Manifold.IsSmoothEmbedding Iclosed Iext ∞ j :=
    ((Manifold.IsSmoothEmbedding.id (I := 𝓡 (k - 1)) (n := ∞)
      (M := CellBoundary k)).prodMap (isSmoothEmbedding_coe_closedCell (n - k))).prodMap
        (Manifold.IsSmoothEmbedding.of_opens (I := 𝓘(ℝ, ℝ)) (n := ∞) T)
  let Ψ : PartialDiffeomorph Iext I (CollarDomain k (n - k)) M ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := hΦ
      contMDiffOn_invFun := hΦsymm }
  have hlocal : IsLocalDiffeomorphOn Iext I ∞ Φ (Set.range j) := by
    rintro ⟨y, p, rfl⟩
    exact Ψ.isLocalDiffeomorphAt Iext I ∞ (hwidth p.1 p.2.val p.2.property)
  have himm := hj.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero hlocal (by simp)
  let j' : AttachingRegion k (n - k) × T → Φ.source :=
    fun p => ⟨j p, hwidth p.1 p.2.val p.2.property⟩
  have hj' : Topology.IsEmbedding j' :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hj.isEmbedding
  exact ⟨himm, Φ.isEmbedding_restrict.comp hj'⟩

theorem exists_isSmoothEmbedding_cocore_collar (hr : r ≠ 0) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R') :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∃ Φ : OpenPartialHomeomorph ((CellBoundary k × EuclideanSpace ℝ (Fin (n - k))) × ℝ) M,
        ContMDiffOn Iext I ∞ Φ Φ.source ∧
        ContMDiffOn I Iext ∞ Φ.symm Φ.target ∧
        (∀ p, Φ p = data.χ (recombine hk
          (Real.sqrt (2 * ε + r ^ 2 * ‖p.1.2‖ ^ 2 - 2 * p.2) • p.1.1.val) (r • p.1.2))) ∧
        (∀ x ∈ Φ.target,
          (Φ.symm x).1.1.val = ‖negPart hk (data.χ.symm x)‖⁻¹ • negPart hk (data.χ.symm x) ∧
          (Φ.symm x).1.2 = r⁻¹ • posPart hk (data.χ.symm x) ∧
          (Φ.symm x).2 = f x - (c - ε)) ∧
        (∀ p ∈ Φ.source, f (Φ p) = c - ε + p.2) ∧
        (∀ (p : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
          ((p.1, p.2.val), t) ∈ Φ.source) ∧
        (∀ p : AttachingRegion k (n - k),
          Φ ((p.1, p.2.val), 0) = (cocoreAttachingEmbedding hk c ε r data hε hR.le p).val) ∧
        (let T : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-δ) δ, isOpen_Ioo⟩
         Manifold.IsSmoothEmbedding Iclosed I ∞
           (fun p : AttachingRegion k (n - k) × T => Φ ((p.1.1, p.1.2.val), p.2.val))) ∧
        (∀ (δ₁ θ : ℝ), 0 < δ₁ → 0 < θ → 0 < r →
          ∀ (p : AttachingRegion k (n - k)) (s : Set.Ico (0 : ℝ) 1),
            ‖p.2.val‖ ^ 2 < 1 - δ₁ / r ^ 2 →
            ‖p.2.val‖ ^ 2 < 1 - θ / r ^ 2 → s.val < δ / (2 * ε + r ^ 2) →
            let τ := (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
            let q : StandardHandle k (n - k) := (Handle.attachingCollar k (n - k)) (p, s)
            τ ∈ Set.Ioo (-δ) δ ∧ ((p.1, p.2.val), τ) ∈ Φ.source ∧
              handleRoundEmbedding hk c ε r δ₁ θ data q = Φ ((p.1, p.2.val), τ) ∧
              Φ.symm (handleRoundEmbedding hk c ε r δ₁ θ data q) = ((p.1, p.2.val), τ) ∧
              f (handleRoundEmbedding hk c ε r δ₁ θ data q) = c - ε + τ ∧
              1 - Real.sqrt (1 - 2 * τ / (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2)) = s.val) := by
  obtain ⟨δ, hδ, hδε, Φ, hΦ, hΦsymm, hformula, hinverse, hheight, hwidth, hzero, hflat⟩ :=
    exists_cocore_collar hk c ε r data hr hε hR hR'
  exact ⟨δ, hδ, hδε, Φ, hΦ, hΦsymm, hformula, hinverse, hheight, hwidth, hzero,
    isSmoothEmbedding_collar_restrict δ Φ hΦ hΦsymm hwidth, hflat⟩

end Closed

end Ambient

end

end DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
