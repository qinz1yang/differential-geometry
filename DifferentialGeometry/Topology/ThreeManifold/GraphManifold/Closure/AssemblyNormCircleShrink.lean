import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBoxBlend
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate

/-!
# FC42 normalization, packet N1 (c): the circle region with shrunk corner charts

Lane ASM-NRM (frozen text `build-logs/scratch/ASM-NRM/Targets.lean`, section N1 (c)). For
`0 < ε ≤ 1/2`, `CircleRegion.shrink R ε` has the same base, domain, projection, trivializations,
defining functions and cornered base as `R` (hence the same cornered region, `region_shrink`), and

* the corner charts `cornerChart' k = cornerChart k ∘ (ε • ·)` on `rimBox 2`
  (image `cornerChart k '' rimBox (2 ε)`, `shrink_cornerChart_target`), scales `ε λₖ`;
* the re-chosen common rounding `shrinkRounding ε`: `-(λₖ g_ε (cornerChart k)⁻¹)` on the target of
  corner chart `k` (`g_ε = boxBlend ε`), the old rounding elsewhere. It equals the old rounding off
  the compact sets `cornerChart k '' closedBox (3/2)` (`shrink_rounding_eq_of_not_mem`), is smooth,
  regular at its zero level (`fderiv_boxBlend_ne_zero` and the bijective chart differential), is
  `-(ε λₖ ψ_std)` on the new charts, agrees with the cornered base off the new unit boxes
  (`boxBlend_nonneg_iff` and the chart description of the cornered base) and has compact sublevel.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The closed box `|x|, |y| ≤ 3/2`, the support of the change of rounding. -/
def changeBox : Set (ℝ × ℝ) :=
  {v | |v.1| ≤ 3 / 2 ∧ |v.2| ≤ 3 / 2}

theorem isCompact_changeBox : IsCompact changeBox := by
  have h : changeBox = Icc (-(3 / 2 : ℝ)) (3 / 2) ×ˢ Icc (-(3 / 2 : ℝ)) (3 / 2) := by
    ext v
    simp only [changeBox, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [h]
  exact isCompact_Icc.prod isCompact_Icc

theorem changeBox_subset_rimBox_two : changeBox ⊆ rimBox 2 :=
  fun _ hv => ⟨hv.1.trans_lt (by norm_num), hv.2.trans_lt (by norm_num)⟩

theorem rimBox_three_halves_subset_changeBox : rimBox (3 / 2) ⊆ changeBox :=
  fun _ hv => ⟨hv.1.le, hv.2.le⟩

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-! ## Chart facts of the circle region -/

theorem cornerChart_target_eq {k k' : Fin R.cornerCount} {b : R.Base}
    (hk : b ∈ (R.cornerChart k).target) (hk' : b ∈ (R.cornerChart k').target) : k = k' := by
  by_contra hne
  exact Set.disjoint_left.mp (R.cornerChart_disjoint hne) hk hk'

theorem mem_source_of_mem_rimBox (k : Fin R.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    v ∈ (R.cornerChart k).source := by
  rw [R.cornerChart_source]
  exact hv

theorem mem_target_of_mem_rimBox (k : Fin R.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    R.cornerChart k v ∈ (R.cornerChart k).target :=
  (R.cornerChart k).map_source (R.mem_source_of_mem_rimBox k hv)

theorem symm_mem_rimBox (k : Fin R.cornerCount) {b : R.Base} (hb : b ∈ (R.cornerChart k).target) :
    (R.cornerChart k).symm b ∈ rimBox 2 := by
  rw [← R.cornerChart_source k]
  exact (R.cornerChart k).map_target hb

theorem cornerChart_symm_apply (k : Fin R.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    (R.cornerChart k).symm (R.cornerChart k v) = v :=
  (R.cornerChart k).left_inv (R.mem_source_of_mem_rimBox k hv)

theorem isCompact_chart_image (k : Fin R.cornerCount) {A : Set (ℝ × ℝ)} (hA : IsCompact A)
    (hA2 : A ⊆ rimBox 2) : IsCompact (R.cornerChart k '' A) :=
  hA.image_of_continuousOn ((R.cornerChart k).contMDiffOn.continuousOn.mono
    (hA2.trans (R.cornerChart_source k).symm.subset))

/-- In a corner chart, the cornered base is the closed quadrant. -/
theorem cornerChart_mem_cornerBase_iff {k : Fin R.cornerCount} {w : ℝ × ℝ} (hw : w ∈ rimBox 2) :
    R.cornerChart k w ∈ R.cornerBase ↔ (0 ≤ w.1 ∧ 0 ≤ w.2) := by
  rw [R.cornerBase_eq, mem_ofPred_eq]
  have hsc := R.cornerScale_pos k
  constructor
  · intro h
    have h1 := h (R.cornerFirst k)
    have h2 := h (R.cornerSecond k)
    rw [R.chart_first k w hw] at h1
    rw [R.chart_second k w hw] at h2
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩ l
    by_cases hl1 : l = R.cornerFirst k
    · rw [hl1, R.chart_first k w hw]
      nlinarith
    by_cases hl2 : l = R.cornerSecond k
    · rw [hl2, R.chart_second k w hw]
      nlinarith
    exact (R.chart_other k l w hl1 hl2 hw).le

/-! ## The re-chosen rounding -/

open Classical in
/-- The re-chosen rounding: `-(λₖ g_ε(chartₖ⁻¹ b))` on the target of corner chart `k`, the old
rounding elsewhere. -/
def shrinkRounding (ε : ℝ) (b : R.Base) : ℝ :=
  if h : ∃ k, b ∈ (R.cornerChart k).target then
    -(R.cornerScale h.choose * boxBlend ε ((R.cornerChart h.choose).symm b))
  else R.rounding b

theorem shrinkRounding_of_mem (ε : ℝ) {k : Fin R.cornerCount} {b : R.Base}
    (hb : b ∈ (R.cornerChart k).target) :
    R.shrinkRounding ε b = -(R.cornerScale k * boxBlend ε ((R.cornerChart k).symm b)) := by
  have h : ∃ k, b ∈ (R.cornerChart k).target := ⟨k, hb⟩
  rw [shrinkRounding, dite_eq_left h, R.cornerChart_target_eq h.choose_spec hb]

theorem shrinkRounding_of_not_mem (ε : ℝ) {b : R.Base} (hb : ∀ k, b ∉ (R.cornerChart k).target) :
    R.shrinkRounding ε b = R.rounding b := by
  rw [shrinkRounding, dite_eq_right (fun ⟨k, hk⟩ => hb k hk)]

/-- Off the compact change sets, the re-chosen rounding is the old one. -/
theorem shrinkRounding_eq_of_not_mem (ε : ℝ) {b : R.Base}
    (hb : b ∉ ⋃ k, R.cornerChart k '' changeBox) : R.shrinkRounding ε b = R.rounding b := by
  by_cases h : ∃ k, b ∈ (R.cornerChart k).target
  · obtain ⟨k, hk⟩ := h
    have hw := R.symm_mem_rimBox k hk
    have hbw : R.cornerChart k ((R.cornerChart k).symm b) = b := (R.cornerChart k).right_inv hk
    have hnot : (R.cornerChart k).symm b ∉ rimBox (3 / 2) := fun hw' =>
      hb (mem_iUnion.mpr ⟨k, _, rimBox_three_halves_subset_changeBox hw', hbw⟩)
    rw [R.shrinkRounding_of_mem ε hk, boxBlend_eq_of_not_mem hnot, ← R.rounding_chart k _ hw, hbw]
  · exact R.shrinkRounding_of_not_mem ε fun k hk => h ⟨k, hk⟩

theorem isClosed_iUnion_changeBox :
    IsClosed (⋃ k, R.cornerChart k '' changeBox) :=
  isClosed_iUnion_of_finite fun k =>
    (R.isCompact_chart_image k isCompact_changeBox changeBox_subset_rimBox_two).isClosed

theorem shrinkRounding_eventuallyEq_of_mem (ε : ℝ) {k : Fin R.cornerCount} {b : R.Base}
    (hb : b ∈ (R.cornerChart k).target) :
    R.shrinkRounding ε =ᶠ[𝓝 b]
      fun b' => -(R.cornerScale k * boxBlend ε ((R.cornerChart k).symm b')) := by
  filter_upwards [(R.cornerChart k).open_target.mem_nhds hb] with b' hb'
  exact R.shrinkRounding_of_mem ε hb'

theorem shrinkRounding_eventuallyEq_of_not_mem (ε : ℝ) {b : R.Base}
    (hb : b ∉ ⋃ k, R.cornerChart k '' changeBox) : R.shrinkRounding ε =ᶠ[𝓝 b] R.rounding := by
  filter_upwards [R.isClosed_iUnion_changeBox.isOpen_compl.mem_nhds hb] with b' hb'
  exact R.shrinkRounding_eq_of_not_mem ε hb'

theorem not_mem_changeBox_of_not_mem_target {b : R.Base} (hb : ∀ k, b ∉ (R.cornerChart k).target) :
    b ∉ ⋃ k, R.cornerChart k '' changeBox := by
  intro h
  obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.mp h
  exact hb k (R.mem_target_of_mem_rimBox k (changeBox_subset_rimBox_two hv))

theorem contMDiffAt_chartRounding (ε : ℝ) {k : Fin R.cornerCount} {b : R.Base}
    (hb : b ∈ (R.cornerChart k).target) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun b' => -(R.cornerScale k * boxBlend ε ((R.cornerChart k).symm b'))) b := by
  have hs : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (R.cornerChart k).symm b :=
    (R.cornerChart k).symm.contMDiffOn.contMDiffAt ((R.cornerChart k).open_target.mem_nhds hb)
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ fun w => -(R.cornerScale k * boxBlend ε w) :=
    (contDiff_const.mul (contDiff_boxBlend ε)).neg.contMDiff
  exact hG.contMDiffAt.comp b hs

theorem contMDiff_shrinkRounding (ε : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (R.shrinkRounding ε) := by
  intro b
  by_cases h : ∃ k, b ∈ (R.cornerChart k).target
  · obtain ⟨k, hk⟩ := h
    exact (R.contMDiffAt_chartRounding ε hk).congr_of_eventuallyEq
      (R.shrinkRounding_eventuallyEq_of_mem ε hk)
  · have hb := R.not_mem_changeBox_of_not_mem_target fun k hk => h ⟨k, hk⟩
    exact (R.rounding_smooth b).congr_of_eventuallyEq (R.shrinkRounding_eventuallyEq_of_not_mem ε hb)

theorem continuous_shrinkRounding (ε : ℝ) : Continuous (R.shrinkRounding ε) :=
  (R.contMDiff_shrinkRounding ε).continuous

/-- Regularity of the re-chosen rounding inside a corner chart. -/
theorem mfderiv_chartRounding_ne_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {k : Fin R.cornerCount} {b : R.Base} (hb : b ∈ (R.cornerChart k).target)
    (hzero : boxBlend ε ((R.cornerChart k).symm b) = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun b' => -(R.cornerScale k * boxBlend ε ((R.cornerChart k).symm b'))) b ≠ 0 := by
  have hsymm : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (R.cornerChart k).symm b :=
    (R.cornerChart k).symm.mdifferentiableAt (by simp) hb
  have hGd : HasFDerivAt (fun v : ℝ × ℝ => -(R.cornerScale k * boxBlend ε v))
      (-(R.cornerScale k • fderiv ℝ (boxBlend ε) ((R.cornerChart k).symm b)))
      ((R.cornerChart k).symm b) := by
    have h0 := ((contDiff_boxBlend ε).differentiable (by simp) ((R.cornerChart k).symm b)).hasFDerivAt
    exact (h0.const_mul (R.cornerScale k)).neg
  have hcomp := (hasMFDerivAt_iff_hasFDerivAt.mpr hGd).comp b hsymm.hasMFDerivAt
  simp only [Function.comp_def] at hcomp
  rw [hcomp.mfderiv]
  intro h0
  have hloc : IsLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (R.cornerChart k).symm b :=
    (R.cornerChart k).symm.isLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ hb
  obtain ⟨e, he⟩ := hloc.isInvertible_mfderiv (by simp)
  have h1 := DFunLike.congr_fun h0 (e.symm ((1, 1) : ℝ × ℝ))
  have h2 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (R.cornerChart k).symm b (e.symm ((1, 1) : ℝ × ℝ)) =
      ((1, 1) : ℝ × ℝ) := by
    rw [← he]
    exact e.apply_symm_apply _
  have h3 : (-(R.cornerScale k • fderiv ℝ (boxBlend ε) ((R.cornerChart k).symm b)))
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (R.cornerChart k).symm b (e.symm ((1, 1) : ℝ × ℝ))) = 0 := h1
  rw [h2] at h3
  simp only [neg_apply, smul_apply, smul_eq_mul, fderiv_boxBlend_diag hε hε1 hzero, mul_one] at h3
  exact (R.cornerScale_pos k).ne' (neg_eq_zero.mp h3)

theorem shrinkRounding_regular {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (b : R.Base)
    (hb : R.shrinkRounding ε b = 0) : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.shrinkRounding ε) b ≠ 0 := by
  by_cases h : ∃ k, b ∈ (R.cornerChart k).target
  · obtain ⟨k, hk⟩ := h
    rw [(R.shrinkRounding_eventuallyEq_of_mem ε hk).mfderiv_eq]
    rw [R.shrinkRounding_of_mem ε hk] at hb
    have hz : boxBlend ε ((R.cornerChart k).symm b) = 0 := by
      have hsc := (R.cornerScale_pos k).ne'
      have : R.cornerScale k * boxBlend ε ((R.cornerChart k).symm b) = 0 := neg_eq_zero.mp hb
      exact (mul_eq_zero.mp this).resolve_left hsc
    exact R.mfderiv_chartRounding_ne_zero hε hε1 hk hz
  · have hb' := R.not_mem_changeBox_of_not_mem_target fun k hk => h ⟨k, hk⟩
    rw [(R.shrinkRounding_eventuallyEq_of_not_mem ε hb').mfderiv_eq]
    rw [R.shrinkRounding_eq_of_not_mem ε hb'] at hb
    exact R.rounding_regular b hb

/-! ## The shrunk corner charts -/

/-- The shrunk corner chart `cornerChart k ∘ (ε • ·)`. -/
def shrinkChart (ε : ℝ) (hε : 0 < ε) (k : Fin R.cornerCount) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) R.Base ∞ :=
  (boxScaling ε hε).trans (R.cornerChart k)

theorem shrinkChart_apply (ε : ℝ) (hε : 0 < ε) (k : Fin R.cornerCount) (v : ℝ × ℝ) :
    R.shrinkChart ε hε k v = R.cornerChart k (ε • v) :=
  rfl

theorem shrinkChart_source {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (k : Fin R.cornerCount) :
    (R.shrinkChart ε hε k).source = rimBox 2 := by
  ext v
  change v ∈ rimBox 2 ∩ (fun v => ε • v) ⁻¹' (R.cornerChart k).source ↔ v ∈ rimBox 2
  rw [R.cornerChart_source]
  exact ⟨fun h => h.1, fun h => ⟨h, smul_mem_rimBox hε (by linarith) h⟩⟩

theorem shrinkChart_target {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (k : Fin R.cornerCount) :
    (R.shrinkChart ε hε k).target = R.cornerChart k '' rimBox (2 * ε) := by
  ext b
  change b ∈ (R.cornerChart k).target ∩ (R.cornerChart k).symm ⁻¹' rimBox (2 * ε) ↔ _
  constructor
  · rintro ⟨hb, hbs⟩
    exact ⟨_, hbs, (R.cornerChart k).right_inv hb⟩
  · rintro ⟨w, hw, rfl⟩
    have hw2 : w ∈ rimBox 2 := rimBox_mono (by linarith) hw
    refine ⟨R.mem_target_of_mem_rimBox k hw2, ?_⟩
    have h := R.cornerChart_symm_apply k hw2
    change (R.cornerChart k).symm (R.cornerChart k w) ∈ rimBox (2 * ε)
    rw [h]
    exact hw

theorem shrinkChart_target_subset {ε : ℝ} (hε : 0 < ε) (k : Fin R.cornerCount) :
    (R.shrinkChart ε hε k).target ⊆ (R.cornerChart k).target :=
  fun _ hb => hb.1

theorem shrinkChart_image_rimBox_one {ε : ℝ} (hε : 0 < ε) (k : Fin R.cornerCount) :
    R.shrinkChart ε hε k '' rimBox 1 = R.cornerChart k '' rimBox ε := by
  ext b
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨ε • v, ?_, rfl⟩
    have h := (smul_mem_rimBox_iff hε (r := 1)).mpr hv
    rwa [one_mul] at h
  · rintro ⟨w, hw, rfl⟩
    refine ⟨ε⁻¹ • w, ?_, ?_⟩
    · rw [← smul_mem_rimBox_iff hε, one_mul, smul_inv_smul₀ hε.ne']
      exact hw
    · change R.cornerChart k (ε • ε⁻¹ • w) = _
      rw [smul_inv_smul₀ hε.ne']

/-! ## The fields of the shrunk circle region -/

variable {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
include hε hε1

theorem shrink_mem_rimBox {v : ℝ × ℝ} (hv : v ∈ rimBox 2) : ε • v ∈ rimBox 2 :=
  smul_mem_rimBox hε (by linarith) hv

theorem shrink_chart_first (k : Fin R.cornerCount) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    R.defining (R.cornerFirst k) (R.shrinkChart ε hε k v) = -(ε * R.cornerScale k * v.1) := by
  rw [shrinkChart_apply, R.chart_first k _ (shrink_mem_rimBox hε hε1 hv)]
  simp only [Prod.smul_fst, smul_eq_mul]
  ring

theorem shrink_chart_second (k : Fin R.cornerCount) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    R.defining (R.cornerSecond k) (R.shrinkChart ε hε k v) = -(ε * R.cornerScale k * v.2) := by
  rw [shrinkChart_apply, R.chart_second k _ (shrink_mem_rimBox hε hε1 hv)]
  simp only [Prod.smul_snd, smul_eq_mul]
  ring

theorem shrink_chart_other (k : Fin R.cornerCount) (l : Fin R.definingCount) (v : ℝ × ℝ)
    (h1 : l ≠ R.cornerFirst k) (h2 : l ≠ R.cornerSecond k) (hv : v ∈ rimBox 2) :
    R.defining l (R.shrinkChart ε hε k v) < 0 := by
  rw [shrinkChart_apply]
  exact R.chart_other k l _ h1 h2 (shrink_mem_rimBox hε hε1 hv)

theorem shrink_rounding_chart (k : Fin R.cornerCount) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    R.shrinkRounding ε (R.shrinkChart ε hε k v) =
      -(ε * R.cornerScale k * standardRimRounding v) := by
  have hv2 := shrink_mem_rimBox hε hε1 hv
  rw [shrinkChart_apply, R.shrinkRounding_of_mem ε (R.mem_target_of_mem_rimBox k hv2),
    R.cornerChart_symm_apply k hv2, boxBlend_smul hε hε1 hv]
  ring

theorem shrink_rounding_agree :
    {b | R.shrinkRounding ε b ≤ 0} \ (⋃ k, R.shrinkChart ε hε k '' rimBox 1) =
      R.cornerBase \ ⋃ k, R.shrinkChart ε hε k '' rimBox 1 := by
  simp only [R.shrinkChart_image_rimBox_one hε]
  ext b
  simp only [mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hU⟩
    refine ⟨?_, hU⟩
    by_cases h : ∃ k, b ∈ (R.cornerChart k).target
    · obtain ⟨k, hk⟩ := h
      have hw := R.symm_mem_rimBox k hk
      have hbw : R.cornerChart k ((R.cornerChart k).symm b) = b := (R.cornerChart k).right_inv hk
      have hnot : (R.cornerChart k).symm b ∉ rimBox ε := fun h =>
        hU (mem_iUnion.mpr ⟨k, _, h, hbw⟩)
      rw [R.shrinkRounding_of_mem ε hk] at hb
      have hg : 0 ≤ boxBlend ε ((R.cornerChart k).symm b) := by
        have hsc := R.cornerScale_pos k
        by_contra hneg
        rw [not_le] at hneg
        nlinarith
      rw [← hbw]
      exact (R.cornerChart_mem_cornerBase_iff hw).mpr ((boxBlend_nonneg_iff hε hε1 hnot).mp hg)
    · rw [R.shrinkRounding_of_not_mem ε fun k hk => h ⟨k, hk⟩] at hb
      have hU1 : b ∉ ⋃ k, R.cornerChart k '' rimBox 1 := by
        intro h1
        obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.mp h1
        exact h ⟨k, R.mem_target_of_mem_rimBox k (rimBox_mono (by norm_num) hv)⟩
      exact (CircleRegion.rounding_le_zero_iff hU1).mp hb
  · rintro ⟨hb, hU⟩
    refine ⟨?_, hU⟩
    by_cases h : ∃ k, b ∈ (R.cornerChart k).target
    · obtain ⟨k, hk⟩ := h
      have hw := R.symm_mem_rimBox k hk
      have hbw : R.cornerChart k ((R.cornerChart k).symm b) = b := (R.cornerChart k).right_inv hk
      have hnot : (R.cornerChart k).symm b ∉ rimBox ε := fun h =>
        hU (mem_iUnion.mpr ⟨k, _, h, hbw⟩)
      rw [← hbw] at hb
      have hq := (R.cornerChart_mem_cornerBase_iff hw).mp hb
      have hg := (boxBlend_nonneg_iff hε hε1 hnot).mpr hq
      rw [R.shrinkRounding_of_mem ε hk]
      have hsc := R.cornerScale_pos k
      nlinarith
    · rw [R.shrinkRounding_of_not_mem ε fun k hk => h ⟨k, hk⟩]
      have hU1 : b ∉ ⋃ k, R.cornerChart k '' rimBox 1 := by
        intro h1
        obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.mp h1
        exact h ⟨k, R.mem_target_of_mem_rimBox k (rimBox_mono (by norm_num) hv)⟩
      exact (CircleRegion.rounding_le_zero_iff hU1).mpr hb

omit hε hε1 in
theorem shrink_rounded_compact : IsCompact {b | R.shrinkRounding ε b ≤ 0} := by
  have hK : IsCompact ({b | R.rounding b ≤ 0} ∪ ⋃ k, R.cornerChart k '' changeBox) :=
    R.rounded_compact.union (isCompact_iUnion fun k =>
      R.isCompact_chart_image k isCompact_changeBox changeBox_subset_rimBox_two)
  refine hK.of_isClosed_subset (isClosed_le (R.continuous_shrinkRounding ε) continuous_const) ?_
  intro b hb
  by_cases h : b ∈ ⋃ k, R.cornerChart k '' changeBox
  · exact Or.inr h
  · left
    change R.rounding b ≤ 0
    rw [← R.shrinkRounding_eq_of_not_mem ε h]
    exact hb

omit hε1 in
theorem shrink_cornerChart_disjoint :
    Pairwise fun k k' => Disjoint (R.shrinkChart ε hε k).target (R.shrinkChart ε hε k').target :=
  fun k k' hkk' => (R.cornerChart_disjoint hkk').mono (R.shrinkChart_target_subset hε k)
    (R.shrinkChart_target_subset hε k')

omit hε1 in
theorem shrink_corner_center (b : R.Base) (l l' : Fin R.definingCount) (hll' : l ≠ l')
    (hl : R.defining l b = 0) (hl' : R.defining l' b = 0) :
    ∃ k, b = R.shrinkChart ε hε k (0, 0) := by
  obtain ⟨k, hk⟩ := R.corner_center b l l' hll' hl hl'
  refine ⟨k, ?_⟩
  have h0 : ε • ((0, 0) : ℝ × ℝ) = (0, 0) := by simp
  rw [shrinkChart_apply, h0]
  exact hk

omit hε1 in
theorem shrink_cornerScale_pos (k : Fin R.cornerCount) : 0 < ε * R.cornerScale k :=
  mul_pos hε (R.cornerScale_pos k)

omit hε hε1

/-! ## The shrunk circle region -/

/-- **N1. The circle region with shrunk corner charts and re-chosen rounding.** CHANGES: the corner
charts (`cornerChart ∘ (ε •)`, a common linear scaling), the scales `ε λ` and the rounding
function `shrinkRounding ε` (hence the rounded region). UNCHANGED: base, domain, projection,
trivializations, defining functions, cornered base (hence the cornered region). -/
def shrink (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : CircleRegion W :=
  { R with
    cornerChart := R.shrinkChart ε hε
    cornerChart_source := R.shrinkChart_source hε hε1
    cornerChart_disjoint := R.shrink_cornerChart_disjoint hε
    cornerScale := fun k => ε * R.cornerScale k
    cornerScale_pos := R.shrink_cornerScale_pos hε
    chart_first := R.shrink_chart_first hε hε1
    chart_second := R.shrink_chart_second hε hε1
    chart_other := R.shrink_chart_other hε hε1
    corner_center := R.shrink_corner_center hε
    rounding := R.shrinkRounding ε
    rounding_smooth := R.contMDiff_shrinkRounding ε
    rounding_regular := R.shrinkRounding_regular hε hε1
    rounding_chart := R.shrink_rounding_chart hε hε1
    rounding_agree := R.shrink_rounding_agree hε hε1
    rounded_compact := R.shrink_rounded_compact }

variable (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)

theorem shrink_cornerChart (k : Fin R.cornerCount) :
    (R.shrink ε hε hε1).cornerChart k = R.shrinkChart ε hε k :=
  rfl

theorem shrink_cornerChart_apply (k : Fin R.cornerCount) (v : ℝ × ℝ) :
    (R.shrink ε hε hε1).cornerChart k v = R.cornerChart k (ε • v) :=
  rfl

theorem shrink_cornerChart_target (k : Fin R.cornerCount) :
    ((R.shrink ε hε hε1).cornerChart k).target = R.cornerChart k '' rimBox (2 * ε) :=
  R.shrinkChart_target hε hε1 k

theorem shrink_cornerScale (k : Fin R.cornerCount) :
    (R.shrink ε hε hε1).cornerScale k = ε * R.cornerScale k :=
  rfl

theorem shrink_rounding : (R.shrink ε hε hε1).rounding = R.shrinkRounding ε :=
  rfl

theorem shrink_proj : (R.shrink ε hε hε1).proj = R.proj :=
  rfl

theorem shrink_cornerBase : (R.shrink ε hε hε1).cornerBase = R.cornerBase :=
  rfl

theorem shrink_rounding_eq_of_not_mem {b : R.Base}
    (hb : b ∉ ⋃ k, R.cornerChart k '' {v | |v.1| ≤ 3 / 2 ∧ |v.2| ≤ 3 / 2}) :
    (R.shrink ε hε hε1).rounding b = R.rounding b :=
  R.shrinkRounding_eq_of_not_mem ε hb

/-- **The cornered region does not change.** -/
theorem region_shrink : (R.shrink ε hε hε1).region = R.region :=
  rfl

theorem roundingSupport_shrink (k : Fin R.cornerCount) :
    (R.shrink ε hε hε1).roundingSupport k ⊆ R.roundingSupport k := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, R.shrinkChart_target_subset hε k hx, rfl⟩

end CircleRegion

end GC.GraphManifold.Assembly
