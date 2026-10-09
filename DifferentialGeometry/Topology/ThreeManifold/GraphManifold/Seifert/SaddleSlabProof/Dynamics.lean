import DifferentialGeometry.Topology.Morse.Strip.StripFlow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Model

/-!
# The flow of a one-saddle strip near the saddle

Lane RG03c. Let `D` be a gradient-like strip with the single critical point `p`, whose chart
`ch D` has index one, small radius `r = (ch D).r₀` and model radius `rmD D ≥ 8 r`. Inside the
annulus `r < |y| < rmD D` the flow, read in the chart, keeps `saddleK` and lowers `saddleQ` at
unit speed (`chart_ode`, `exists_flow_chart_local`). With `ε = r²` the box
`saddleBox ε = {|saddleQ| ≤ ε, |saddleK| ≤ ε}` contains the small ball, and a flow line that starts
outside its image `boxSet D` cannot enter it while moving towards the lower level of the box
from at most its upper level, or towards the upper level from at least its lower level
(`flow_notMem_boxSet_desc`, `_asc`). `flow_chart_eq` follows a model flow line through the
annulus for a prescribed time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

def saddleBox (ε : ℝ) : Set (MorseModel 2) := {y | |saddleQ y| ≤ ε ∧ |saddleK y| ≤ ε}

def openBox (ε : ℝ) : Set (MorseModel 2) := {y | |saddleQ y| < ε ∧ |saddleK y| < ε}

theorem continuous_saddleQ : Continuous saddleQ := by
  unfold saddleQ
  fun_prop

theorem continuous_saddleK : Continuous saddleK := by
  unfold saddleK
  fun_prop

theorem isClosed_saddleBox (ε : ℝ) : IsClosed (saddleBox ε) :=
  (isClosed_le (continuous_abs.comp continuous_saddleQ) continuous_const).inter
    (isClosed_le (continuous_abs.comp continuous_saddleK) continuous_const)

theorem isOpen_openBox (ε : ℝ) : IsOpen (openBox ε) :=
  (isOpen_lt (continuous_abs.comp continuous_saddleQ) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_saddleK) continuous_const)

theorem morseNorm_lt_iff {c : ℝ} (hc : 0 ≤ c) (y : MorseModel 2) :
    morseNorm 2 y < c ↔ y 0 ^ 2 + y 1 ^ 2 < c ^ 2 := by
  rw [← morseNorm_sq_two]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).symm

theorem morseNorm_le_iff {c : ℝ} (hc : 0 ≤ c) (y : MorseModel 2) :
    morseNorm 2 y ≤ c ↔ y 0 ^ 2 + y 1 ^ 2 ≤ c ^ 2 := by
  rw [← morseNorm_sq_two]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).symm

theorem saddleBox_normSq {ε : ℝ} {y : MorseModel 2} (hy : y ∈ saddleBox ε) :
    y 0 ^ 2 + y 1 ^ 2 ≤ 4 * ε := by
  have h := normSq_le_two_mul y
  linarith [hy.1, hy.2]

theorem isCompact_saddleBox (ε : ℝ) : IsCompact (saddleBox ε) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_saddleBox ε) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 * (|ε| + 1), fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := saddleBox_normSq hy
  have hle : ∀ i, ‖y i‖ ≤ 2 * (|ε| + 1) := by
    intro i
    rw [Real.norm_eq_abs]
    have hi : y i ^ 2 ≤ 4 * (|ε| + 1) ^ 2 := by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), le_abs_self ε,
        abs_nonneg ε]
    have := abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (|ε| + 1)] : y i ^ 2 ≤
      (2 * (|ε| + 1)) ^ 2) (by positivity)
    exact abs_le.mpr this
  exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr hle

theorem saddleBox_of_morseNorm_le {r : ℝ} (hr : 0 ≤ r) {y : MorseModel 2}
    (hy : morseNorm 2 y ≤ r) : y ∈ openBox (r ^ 2) ∨ y = 0 → y ∈ saddleBox (r ^ 2) := by
  intro _
  have h := (morseNorm_le_iff hr y).mp hy
  have hq := two_abs_saddleQ_le y
  have hk := two_abs_saddleK_le y
  constructor <;> nlinarith [abs_nonneg (saddleQ y), abs_nonneg (saddleK y)]

theorem openBox_of_morseNorm_lt {r : ℝ} (hr : 0 ≤ r) {y : MorseModel 2}
    (hy : morseNorm 2 y < r) : y ∈ openBox (r ^ 2) := by
  have h := (morseNorm_lt_iff hr y).mp hy
  have hq := two_abs_saddleQ_le y
  have hk := two_abs_saddleK_le y
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  constructor <;> nlinarith [abs_nonneg (saddleQ y), abs_nonneg (saddleK y)]

theorem openBox_subset_saddleBox (ε : ℝ) : openBox ε ⊆ saddleBox ε :=
  fun _ hy => ⟨hy.1.le, hy.2.le⟩

theorem normSq_of_saddleBox_not_openBox {ε : ℝ} {y : MorseModel 2} (hn : y ∉ openBox ε) :
    2 * ε ≤ y 0 ^ 2 + y 1 ^ 2 := by
  have hq := two_abs_saddleQ_le y
  have hk := two_abs_saddleK_le y
  simp only [openBox, mem_ofPred_eq, not_and_or, not_lt] at hn
  rcases hn with h | h <;> linarith

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ} {p : M}

def ch (D : GradientLikeStrip I f a b {p}) : MorseNormalChart I f p :=
  D.chart p (Finset.mem_singleton_self p)

def rmD (D : GradientLikeStrip I f a b {p}) : ℝ := D.rm p (Finset.mem_singleton_self p)

def annulus (D : GradientLikeStrip I f a b {p}) : Set (MorseModel 2) :=
  {y | (ch D).r₀ < morseNorm 2 y ∧ morseNorm 2 y < rmD D}

def boxSet (D : GradientLikeStrip I f a b {p}) : Set M :=
  (ch D).χ '' saddleBox ((ch D).r₀ ^ 2)

variable (D : GradientLikeStrip I f a b {p})

theorem r₀_pos : 0 < (ch D).r₀ := (ch D).hr₀

theorem rmD_le_R : rmD D ≤ (ch D).R := (D.hrm p (Finset.mem_singleton_self p)).2

theorem rmD_lt_R' : rmD D < (ch D).R' := D.rm_lt_R' p (Finset.mem_singleton_self p)

theorem lt_rmD_subset_ball :
    {y : MorseModel 2 | morseNorm 2 y < rmD D} ⊆ Metric.ball 0 (ch D).R' :=
  (ch D).lt_subset_ball (rmD_lt_R' D).le

theorem annulus_subset_ball : annulus D ⊆ Metric.ball 0 (ch D).R' :=
  fun _ hy => lt_rmD_subset_ball D hy.2

theorem isOpen_annulus : IsOpen (annulus D) :=
  (isOpen_lt continuous_const continuous_morseNorm).inter (isOpen_morseNorm_lt _)

theorem isOpen_image_annulus : IsOpen ((ch D).χ '' annulus D) :=
  ((ch D).χ.isOpen_image_iff_of_subset_source
    ((annulus_subset_ball D).trans (ch D).hball)).2 (isOpen_annulus D)

theorem saddleBox_subset_lt (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    saddleBox ((ch D).r₀ ^ 2) ⊆ {y | morseNorm 2 y < rmD D} := by
  intro y hy
  have h := saddleBox_normSq hy
  have hr := r₀_pos D
  rw [mem_ofPred_eq, morseNorm_lt_iff (by linarith)]
  nlinarith

theorem saddleBox_subset_ball (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    saddleBox ((ch D).r₀ ^ 2) ⊆ Metric.ball 0 (ch D).R' :=
  (saddleBox_subset_lt D hrm).trans (lt_rmD_subset_ball D)

theorem isCompact_boxSet (hrm : 8 * (ch D).r₀ ≤ rmD D) : IsCompact (boxSet D) :=
  (isCompact_saddleBox _).image_of_continuousOn
    ((ch D).χ.continuousOn.mono ((saddleBox_subset_ball D hrm).trans (ch D).hball))

theorem isOpen_image_openBox (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    IsOpen ((ch D).χ '' openBox ((ch D).r₀ ^ 2)) :=
  ((ch D).χ.isOpen_image_iff_of_subset_source
    (((openBox_subset_saddleBox _).trans (saddleBox_subset_ball D hrm)).trans (ch D).hball)).2
    (isOpen_openBox _)

theorem f_chart (hk : (ch D).k = 1) {y : MorseModel 2} (hy : morseNorm 2 y < rmD D) :
    f ((ch D).χ y) = f p + saddleQ y := by
  rw [(ch D).hnorm y (hy.le.trans (rmD_le_R D)), morseNormalForm_eq_saddleQ _ hk]

theorem chart_mem_annulus_of_box {y : MorseModel 2} (hrm : 8 * (ch D).r₀ ≤ rmD D)
    (hy : y ∈ saddleBox ((ch D).r₀ ^ 2)) (hn : y ∉ openBox ((ch D).r₀ ^ 2)) :
    y ∈ annulus D := by
  have h := normSq_of_saddleBox_not_openBox hn
  have hr := r₀_pos D
  refine ⟨?_, saddleBox_subset_lt D hrm hy⟩
  by_contra hc
  rw [not_lt, morseNorm_le_iff hr.le] at hc
  nlinarith

theorem smallBall_subset_boxSet {q : M} (hq : q ∈ ({p} : Finset M)) :
    D.smallBall q hq ⊆ boxSet D := by
  obtain rfl := Finset.mem_singleton.mp hq
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, openBox_subset_saddleBox _ (openBox_of_morseNorm_lt (r₀_pos D).le hy), rfl⟩

theorem chart_notMem_smallBall {y : MorseModel 2} (hy : y ∈ annulus D) {q : M}
    (hq : q ∈ ({p} : Finset M)) : (ch D).χ y ∉ D.smallBall q hq := by
  obtain rfl := Finset.mem_singleton.mp hq
  rintro ⟨w, hw, hwy⟩
  have hws : w ∈ (ch D).χ.source := (ch D).hball (mem_ball_of_morseNorm_lt
    ((show morseNorm 2 w < (ch D).r₀ from hw).trans (D.r₀_lt_R' _ hq)))
  have hys : y ∈ (ch D).χ.source := (ch D).hball (annulus_subset_ball D hy)
  have hwy' : w = y := (ch D).χ.injOn hws hys hwy
  have : morseNorm 2 w < (ch D).r₀ := hw
  rw [hwy'] at this
  exact lt_asymm this hy.1

variable [T2Space M] [I.Boundaryless]

theorem f_flow_of_avoid_small (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ}
    (hx : f x ∈ Icc a b) (hxT : f x - T ∈ Icc a b)
    (havoid : ∀ s ∈ uIcc 0 T, D.flow s x ∉ D.smallBall p (Finset.mem_singleton_self p)) :
    ∀ s ∈ uIcc 0 T, f (D.flow s x) = f x - s :=
  GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc hf hx hxT fun s hs q hq hmem =>
    havoid s hs ((Finset.mem_singleton.mp hq : q = p) ▸ hmem)

theorem f_flow_of_avoid_box (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ}
    (hx : f x ∈ Icc a b) (hxT : f x - T ∈ Icc a b)
    (havoid : ∀ s ∈ uIcc 0 T, D.flow s x ∉ boxSet D) :
    ∀ s ∈ uIcc 0 T, f (D.flow s x) = f x - s :=
  GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc hf hx hxT
    fun s hs q hq hmem => havoid s hs (smallBall_subset_boxSet (q := q) D hq hmem)

theorem chart_ode (hk : (ch D).k = 1) {x : M} {t₀ t₁ : ℝ}
    (hin : ∀ u ∈ Icc t₀ t₁, D.flow u x ∈ (ch D).χ '' annulus D) :
    ∀ u ∈ Icc t₀ t₁,
      saddleK ((ch D).χ.symm (D.flow u x)) = saddleK ((ch D).χ.symm (D.flow t₀ x)) ∧
      saddleQ ((ch D).χ.symm (D.flow u x)) =
        saddleQ ((ch D).χ.symm (D.flow t₀ x)) - (u - t₀) := by
  set z : ℝ → MorseModel 2 := fun s => (ch D).χ.symm (D.flow s x) with hz
  have hder : ∀ u ∈ Icc t₀ t₁,
      HasDerivAt z (ModelField.modelField 1 (ch D).r₀ (z u)) u := by
    intro u hu
    have h := GradientLikeStrip.hasDerivAt_symm_flow (D := D) (Finset.mem_singleton_self p)
      (image_mono (fun y (hy : y ∈ annulus D) => hy.2) (hin u hu))
    have hk' : (D.chart p (Finset.mem_singleton_self p)).k = 1 := hk
    rw [hk'] at h
    exact h
  have hann : ∀ u ∈ Icc t₀ t₁, z u ∈ annulus D := fun u hu =>
    (ch D).symm_mem (annulus_subset_ball D) (hin u hu)
  have hK : ∀ u ∈ Icc t₀ t₁, saddleK (z u) = saddleK (z t₀) := by
    refine constant_of_has_deriv_right_zero ?_ ?_
    · exact fun u hu => (hasDerivAt_saddleK_curve (hder u hu)).continuousAt.continuousWithinAt
    · exact fun u hu =>
        (hasDerivAt_saddleK_curve (hder u (Ico_subset_Icc_self hu))).hasDerivWithinAt
  have hQ : ∀ u ∈ Icc t₀ t₁, saddleQ (z u) + u = saddleQ (z t₀) + t₀ := by
    have hd : ∀ u ∈ Icc t₀ t₁, HasDerivAt (fun s => saddleQ (z s) + s) 0 u := by
      intro u hu
      have h := (hasDerivAt_saddleQ_curve (hder u hu)).add (hasDerivAt_id u)
      have hθ := theta_mul_normSq (r₀_pos D)
        (show (ch D).r₀ / 2 ≤ morseNorm 2 (z u) by linarith [(hann u hu).1, r₀_pos D])
      rw [hθ, neg_add_cancel] at h
      exact h
    refine constant_of_has_deriv_right_zero ?_ ?_
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hd u (Ico_subset_Icc_self hu)).hasDerivWithinAt
  intro u hu
  refine ⟨hK u hu, ?_⟩
  have := hQ u hu
  linarith

theorem exists_flow_chart_local (hk : (ch D).k = 1) {y : MorseModel 2} (hy : y ∈ annulus D) :
    ∃ η > 0, ∀ u ∈ Icc (-η) η, ∃ z ∈ annulus D, D.flow u ((ch D).χ y) = (ch D).χ z ∧
      saddleK z = saddleK y ∧ saddleQ z = saddleQ y - u := by
  have h0 : D.flow 0 ((ch D).χ y) ∈ (ch D).χ '' annulus D := by
    rw [GradientLikeStrip.flow_zero]
    exact mem_image_of_mem _ hy
  obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open (isOpen_image_annulus D) h0
  have hin : ∀ u ∈ Icc (-δ) δ, D.flow u ((ch D).χ y) ∈ (ch D).χ '' annulus D := by
    intro u hu
    exact hδO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hode := chart_ode D hk hin
  have hys : (ch D).χ.symm ((ch D).χ y) = y :=
    (ch D).χ.left_inv ((ch D).hball (annulus_subset_ball D hy))
  have h00 := hode 0 ⟨by linarith, by linarith⟩
  rw [GradientLikeStrip.flow_zero, hys] at h00
  refine ⟨δ, hδ, fun u hu => ⟨(ch D).χ.symm (D.flow u ((ch D).χ y)),
    (ch D).symm_mem (annulus_subset_ball D) (hin u hu),
    ((ch D).symm_image_eq (image_mono (annulus_subset_ball D) (hin u hu))).symm, ?_, ?_⟩⟩
  · rw [(hode u hu).1, ← h00.1]
  · rw [(hode u hu).2]
    linarith [h00.2]

omit [I.Boundaryless] in
theorem isClosed_boxSet (hrm : 8 * (ch D).r₀ ≤ rmD D) : IsClosed (boxSet D) :=
  (isCompact_boxSet D hrm).isClosed

theorem flow_notMem_boxSet_desc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) {x : M} (hx : x ∉ boxSet D)
    (hfx : f x ≤ f p + (ch D).r₀ ^ 2) (hxab : f x ∈ Icc a b) {T : ℝ}
    (hxT : a ≤ f x - T) : ∀ s ∈ Icc 0 T, D.flow s x ∉ boxSet D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₀, hs₀, hs₀m⟩ := hcon
  set Q : Set ℝ := {s | s ∈ Icc 0 T ∧ D.flow s x ∈ boxSet D} with hQdef
  have hQc : IsClosed Q :=
    isClosed_Icc.inter ((isClosed_boxSet D hrm).preimage (D.continuous_flow_curve x))
  have hQne : Q.Nonempty := ⟨s₀, hs₀, hs₀m⟩
  have hQbdd : BddBelow Q := ⟨0, fun s hs => hs.1.1⟩
  set s₁ := sInf Q with hs₁def
  have hs₁ : s₁ ∈ Q := hQc.csInf_mem hQne hQbdd
  have hmin : ∀ s ∈ Ico 0 s₁, D.flow s x ∉ boxSet D := fun s hs hmem =>
    (not_le.2 hs.2) (csInf_le hQbdd ⟨⟨hs.1, hs.2.le.trans hs₁.1.2⟩, hmem⟩)
  have hs₁pos : 0 < s₁ := by
    refine lt_of_le_of_ne hs₁.1.1 fun h => hx ?_
    have := hs₁.2
    rw [← h, GradientLikeStrip.flow_zero] at this
    exact this
  obtain ⟨y₁, hy₁, hxy₁⟩ := hs₁.2
  have hcontra : ∃ s ∈ Ico 0 s₁, D.flow s x ∈ boxSet D := by
    by_cases hint : y₁ ∈ openBox ((ch D).r₀ ^ 2)
    · have hO : D.flow s₁ x ∈ (ch D).χ '' openBox ((ch D).r₀ ^ 2) := hxy₁ ▸ mem_image_of_mem _ hint
      obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open (isOpen_image_openBox D hrm) hO
      refine ⟨max 0 (s₁ - δ / 2), ⟨le_max_left _ _, max_lt hs₁pos (by linarith)⟩, ?_⟩
      have hm := hδO (max 0 (s₁ - δ / 2)) ⟨?_, ?_⟩
      · exact image_mono (openBox_subset_saddleBox _) hm
      · rcases le_total 0 (s₁ - δ / 2) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
      · exact (max_le hs₁pos.le (by linarith)).trans (by linarith)
    · have hann := chart_mem_annulus_of_box D hrm hy₁ hint
      have hfs₁ : f (D.flow s₁ x) = f x - s₁ := by
        refine f_flow_of_avoid_small D hf hxab ⟨by linarith [hs₁.1.2], by linarith [hxab.2]⟩
          (fun s hs => ?_) s₁ right_mem_uIcc
        rw [uIcc_of_le hs₁pos.le] at hs
        rcases hs.2.lt_or_eq with h | h
        · exact fun hm => hmin s ⟨hs.1, h⟩ (smallBall_subset_boxSet D _ hm)
        · rw [h, ← hxy₁]
          exact chart_notMem_smallBall D hann _
      have hq₁ : saddleQ y₁ < (ch D).r₀ ^ 2 := by
        have h1 := f_chart D hk (saddleBox_subset_lt D hrm hy₁)
        rw [hxy₁, hfs₁] at h1
        linarith
      obtain ⟨η, hη, hloc⟩ := exists_flow_chart_local D hk hann
      set u := min (min η s₁) ((ch D).r₀ ^ 2 - saddleQ y₁) / 2 with hu
      have hm1 : 0 < min (min η s₁) ((ch D).r₀ ^ 2 - saddleQ y₁) :=
        lt_min (lt_min hη hs₁pos) (by linarith)
      have hu0 : 0 < u := by positivity
      have hmη : min (min η s₁) ((ch D).r₀ ^ 2 - saddleQ y₁) ≤ η :=
        (min_le_left _ _).trans (min_le_left _ _)
      have hms : min (min η s₁) ((ch D).r₀ ^ 2 - saddleQ y₁) ≤ s₁ :=
        (min_le_left _ _).trans (min_le_right _ _)
      have hmq : min (min η s₁) ((ch D).r₀ ^ 2 - saddleQ y₁) ≤ (ch D).r₀ ^ 2 - saddleQ y₁ :=
        min_le_right _ _
      obtain ⟨z, -, hz, hzk, hzq⟩ := hloc (-u) ⟨by linarith, by linarith⟩
      refine ⟨s₁ + -u, ⟨by linarith, by linarith⟩, ?_⟩
      rw [GradientLikeStrip.flow_add, ← hxy₁, hz]
      refine mem_image_of_mem _ ⟨?_, ?_⟩
      · rw [hzq, abs_le]
        have := (abs_le.mp hy₁.1).1
        constructor <;> linarith
      · rw [hzk]
        exact hy₁.2
  obtain ⟨s, hs, hmem⟩ := hcontra
  exact hmin s hs hmem

theorem flow_notMem_boxSet_asc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) {x : M} (hx : x ∉ boxSet D)
    (hfx : f p - (ch D).r₀ ^ 2 ≤ f x) (hxab : f x ∈ Icc a b) {T : ℝ}
    (hxT : f x + T ≤ b) : ∀ s ∈ Icc (-T) 0, D.flow s x ∉ boxSet D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₀, hs₀, hs₀m⟩ := hcon
  set Q : Set ℝ := {s | s ∈ Icc (-T) 0 ∧ D.flow s x ∈ boxSet D} with hQdef
  have hQc : IsClosed Q :=
    isClosed_Icc.inter ((isClosed_boxSet D hrm).preimage (D.continuous_flow_curve x))
  have hQne : Q.Nonempty := ⟨s₀, hs₀, hs₀m⟩
  have hQbdd : BddAbove Q := ⟨0, fun s hs => hs.1.2⟩
  set s₁ := sSup Q with hs₁def
  have hs₁ : s₁ ∈ Q := hQc.csSup_mem hQne hQbdd
  have hmax : ∀ s ∈ Ioc s₁ 0, D.flow s x ∉ boxSet D := fun s hs hmem =>
    (not_le.2 hs.1) (le_csSup hQbdd ⟨⟨hs₁.1.1.trans hs.1.le, hs.2⟩, hmem⟩)
  have hs₁neg : s₁ < 0 := by
    refine lt_of_le_of_ne hs₁.1.2 fun h => hx ?_
    have := hs₁.2
    rw [h, GradientLikeStrip.flow_zero] at this
    exact this
  obtain ⟨y₁, hy₁, hxy₁⟩ := hs₁.2
  have hcontra : ∃ s ∈ Ioc s₁ 0, D.flow s x ∈ boxSet D := by
    by_cases hint : y₁ ∈ openBox ((ch D).r₀ ^ 2)
    · have hO : D.flow s₁ x ∈ (ch D).χ '' openBox ((ch D).r₀ ^ 2) :=
        hxy₁ ▸ mem_image_of_mem _ hint
      obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open (isOpen_image_openBox D hrm) hO
      refine ⟨min 0 (s₁ + δ / 2), ⟨lt_min hs₁neg (by linarith), min_le_left _ _⟩, ?_⟩
      have hm := hδO (min 0 (s₁ + δ / 2)) ⟨?_, ?_⟩
      · exact image_mono (openBox_subset_saddleBox _) hm
      · exact le_min (by linarith) (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
    · have hann := chart_mem_annulus_of_box D hrm hy₁ hint
      have hfs₁ : f (D.flow s₁ x) = f x - s₁ := by
        refine f_flow_of_avoid_small D hf hxab ⟨by linarith [hxab.1], by linarith [hs₁.1.1]⟩
          (fun s hs => ?_) s₁ right_mem_uIcc
        rw [uIcc_of_ge hs₁neg.le] at hs
        rcases hs.1.lt_or_eq with h | h
        · exact fun hm => hmax s ⟨h, hs.2⟩ (smallBall_subset_boxSet D _ hm)
        · rw [← h, ← hxy₁]
          exact chart_notMem_smallBall D hann _
      have hq₁ : -((ch D).r₀ ^ 2) < saddleQ y₁ := by
        have h1 := f_chart D hk (saddleBox_subset_lt D hrm hy₁)
        rw [hxy₁, hfs₁] at h1
        linarith
      obtain ⟨η, hη, hloc⟩ := exists_flow_chart_local D hk hann
      set u := min (min η (-s₁)) (saddleQ y₁ + (ch D).r₀ ^ 2) / 2 with hu
      have hm1 : 0 < min (min η (-s₁)) (saddleQ y₁ + (ch D).r₀ ^ 2) :=
        lt_min (lt_min hη (by linarith)) (by linarith)
      have hu0 : 0 < u := by positivity
      have hmη : min (min η (-s₁)) (saddleQ y₁ + (ch D).r₀ ^ 2) ≤ η :=
        (min_le_left _ _).trans (min_le_left _ _)
      have hms : min (min η (-s₁)) (saddleQ y₁ + (ch D).r₀ ^ 2) ≤ -s₁ :=
        (min_le_left _ _).trans (min_le_right _ _)
      have hmq : min (min η (-s₁)) (saddleQ y₁ + (ch D).r₀ ^ 2) ≤
          saddleQ y₁ + (ch D).r₀ ^ 2 := min_le_right _ _
      obtain ⟨z, -, hz, hzk, hzq⟩ := hloc u ⟨by linarith, by linarith⟩
      refine ⟨s₁ + u, ⟨by linarith, by linarith⟩, ?_⟩
      rw [GradientLikeStrip.flow_add, ← hxy₁, hz]
      refine mem_image_of_mem _ ⟨?_, ?_⟩
      · rw [hzq, abs_le]
        have := (abs_le.mp hy₁.1).2
        constructor <;> linarith
      · rw [hzk]
        exact hy₁.2
  obtain ⟨s, hs, hmem⟩ := hcontra
  exact hmax s hs hmem

theorem chart_ode_uIcc (hk : (ch D).k = 1) {x : M} {T : ℝ}
    (hin : ∀ u ∈ uIcc 0 T, D.flow u x ∈ (ch D).χ '' annulus D) :
    ∀ u ∈ uIcc 0 T,
      saddleK ((ch D).χ.symm (D.flow u x)) = saddleK ((ch D).χ.symm (D.flow 0 x)) ∧
      saddleQ ((ch D).χ.symm (D.flow u x)) = saddleQ ((ch D).χ.symm (D.flow 0 x)) - u := by
  rcases le_total 0 T with hT | hT
  · rw [uIcc_of_le hT] at hin ⊢
    intro u hu
    have h := chart_ode D hk hin u hu
    rw [sub_zero] at h
    exact h
  · rw [uIcc_of_ge hT] at hin ⊢
    intro u hu
    have h := chart_ode D hk hin
    have hu' := h u hu
    have h0 := h 0 ⟨hT, le_rfl⟩
    constructor
    · rw [hu'.1, h0.1]
    · rw [hu'.2, h0.2]
      ring

theorem mul_pos_of_ne_zero_on {g : ℝ → ℝ} {u₀ u₁ : ℝ} (hg : ContinuousOn g (uIcc u₀ u₁))
    (hne : ∀ u ∈ uIcc u₀ u₁, g u ≠ 0) : 0 < g u₀ * g u₁ := by
  by_contra h
  have h0n := hne u₀ left_mem_uIcc
  have h1n := hne u₁ right_mem_uIcc
  have h0 : (0 : ℝ) ∈ uIcc (g u₀) (g u₁) := by
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne h0n with h1 | h1 <;> rcases lt_or_gt_of_ne h1n with h2 | h2
    · exact absurd (mul_pos_of_neg_of_neg h1 h2) h
    · left; exact ⟨h1.le, h2.le⟩
    · right; exact ⟨h2.le, h1.le⟩
    · exact absurd (mul_pos h1 h2) h
  obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc hg h0
  exact hne c hc hgc

theorem flow_chart_eq (hk : (ch D).k = 1) {y : MorseModel 2} {T : ℝ} (i : Fin 2)
    (hgood : ∀ w : MorseModel 2, saddleK w = saddleK y →
      saddleQ w ∈ uIcc (saddleQ y) (saddleQ y - T) → w ∈ annulus D ∧ w i ≠ 0) :
    ∃ z, D.flow T ((ch D).χ y) = (ch D).χ z ∧ saddleQ z = saddleQ y - T ∧
      saddleK z = saddleK y ∧ 0 < z i * y i := by
  have hy := hgood y rfl left_mem_uIcc
  set x := (ch D).χ y with hx
  set z : ℝ → MorseModel 2 := fun s => (ch D).χ.symm (D.flow s x) with hzdef
  have hys : (ch D).χ.symm x = y :=
    (ch D).χ.left_inv ((ch D).hball (annulus_subset_ball D hy.1))
  have hz0 : z 0 = y := by
    simp only [hzdef, GradientLikeStrip.flow_zero]
    exact hys
  set S : Set (MorseModel 2) := {w | saddleK w = saddleK y ∧
    saddleQ w ∈ uIcc (saddleQ y) (saddleQ y - T) ∧ 0 ≤ w i * y i} with hSdef
  have hSann : S ⊆ annulus D := fun w hw => (hgood w hw.1 hw.2.1).1
  have hSclosed : IsClosed S := by
    refine (isClosed_eq continuous_saddleK continuous_const).inter
      ((isClosed_Icc.preimage continuous_saddleQ).inter ?_)
    exact isClosed_le continuous_const ((continuous_apply i).mul continuous_const)
  have hSsub : S ⊆ saddleBox (|saddleQ y| + |T| + |saddleK y|) := by
    intro w hw
    refine ⟨?_, ?_⟩
    · have h := hw.2.1
      rw [mem_uIcc] at h
      rw [abs_le]
      have h1 := le_abs_self (saddleQ y)
      have h2 := neg_abs_le (saddleQ y)
      have h3 := le_abs_self T
      have h4 := neg_abs_le T
      have h5 := abs_nonneg (saddleK y)
      rcases h with ⟨h6, h7⟩ | ⟨h6, h7⟩ <;> constructor <;> linarith
    · rw [hw.1]
      have := abs_nonneg (saddleQ y)
      have := abs_nonneg T
      linarith
  have hSc : IsCompact S := (isCompact_saddleBox _).of_isClosed_subset hSclosed hSsub
  have hχS : IsCompact ((ch D).χ '' S) :=
    hSc.image_of_continuousOn ((ch D).χ.continuousOn.mono
      ((hSann.trans (annulus_subset_ball D)).trans (ch D).hball))
  set Q : Set ℝ := {s | D.flow s x ∈ (ch D).χ '' S} with hQdef
  have hQc : IsClosed Q := hχS.isClosed.preimage (D.continuous_flow_curve x)
  have h0Q : (0 : ℝ) ∈ Q := by
    change D.flow 0 x ∈ (ch D).χ '' S
    rw [GradientLikeStrip.flow_zero]
    exact mem_image_of_mem _ ⟨rfl, left_mem_uIcc, mul_self_nonneg _⟩
  have hkey : ∀ s', s' ∈ uIcc 0 T →
      (∀ u ∈ uIcc 0 s', D.flow u x ∈ (ch D).χ '' annulus D) →
      D.flow s' x ∈ (ch D).χ '' S ∧ saddleQ (z s') = saddleQ y - s' ∧
        saddleK (z s') = saddleK y := by
    intro s' hs' hin
    have hode := chart_ode_uIcc D hk hin
    have hzu : ∀ u ∈ uIcc 0 s', saddleK (z u) = saddleK y ∧ saddleQ (z u) = saddleQ y - u := by
      intro u hu
      have h := hode u hu
      rw [GradientLikeStrip.flow_zero, hys] at h
      exact h
    have hrange : ∀ u ∈ uIcc 0 s', saddleQ (z u) ∈ uIcc (saddleQ y) (saddleQ y - T) := by
      intro u hu
      rw [(hzu u hu).2]
      have hu' : u ∈ uIcc 0 T := uIcc_subset_uIcc left_mem_uIcc hs' hu
      rw [mem_uIcc] at hu' ⊢
      rcases hu' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    have hne : ∀ u ∈ uIcc 0 s', z u i ≠ 0 := fun u hu =>
      (hgood (z u) (hzu u hu).1 (hrange u hu)).2
    have hcont : ContinuousOn (fun u => z u i) (uIcc 0 s') := by
      refine (continuous_apply i).comp_continuousOn ?_
      refine (ch D).χ.continuousOn_symm.comp (D.continuous_flow_curve x).continuousOn ?_
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hin u hu
      change D.flow u x ∈ (ch D).χ.target
      rw [← hwu]
      exact (ch D).χ.map_source ((ch D).hball (annulus_subset_ball D hw))
    have hsign : 0 < z 0 i * z s' i := mul_pos_of_ne_zero_on hcont hne
    rw [hz0] at hsign
    have hmem : z s' ∈ S := ⟨(hzu s' right_mem_uIcc).1, hrange s' right_mem_uIcc, by
      rw [mul_comm]; exact hsign.le⟩
    refine ⟨?_, (hzu s' right_mem_uIcc).2, (hzu s' right_mem_uIcc).1⟩
    rw [← (ch D).symm_image_eq (image_mono (annulus_subset_ball D) (hin s' right_mem_uIcc))]
    exact mem_image_of_mem _ hmem
  have hQann : ∀ s ∈ Q, D.flow s x ∈ (ch D).χ '' annulus D := fun s hs => image_mono hSann hs
  have hall : ∀ s ∈ uIcc 0 T, s ∈ Q := by
    rcases le_total 0 T with hT | hT
    · rw [uIcc_of_le hT]
      refine Icc_subset_of_isClosed_of_step hQc h0Q fun t ht hIcc => ?_
      obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open (isOpen_image_annulus D)
        (hQann t (hIcc ⟨ht.1, le_rfl⟩))
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + δ) T, lt_min (by linarith) ht.2,
        fun s' hs' => ?_⟩
      have hs'T : s' ∈ uIcc 0 T := by
        rw [uIcc_of_le hT]
        exact ⟨by linarith [hs'.1, ht.1], hs'.2.trans (min_le_right _ _)⟩
      refine (hkey s' hs'T fun u hu => ?_).1
      rw [uIcc_of_le (by linarith [hs'.1, ht.1])] at hu
      rcases le_total u t with hut | hut
      · exact hQann u (hIcc ⟨hu.1, hut⟩)
      · exact hδO u ⟨by linarith, hu.2.trans (hs'.2.trans (min_le_left _ _))⟩
    · rw [uIcc_of_ge hT]
      have h := Icc_neg_subset_of_isClosed_of_step (T := -T) hQc h0Q fun t ht hIcc => by
        obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open (isOpen_image_annulus D)
          (hQann t (hIcc ⟨le_rfl, ht.2⟩))
        have htT : T < t := by
          have := ht.1
          rw [neg_neg] at this
          exact this
        refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨max (t - δ) T,
          show max (t - δ) T < t from max_lt (by linarith) htT, fun s' hs' => ?_⟩
        have hs'T : s' ∈ uIcc 0 T := by
          rw [uIcc_of_ge hT]
          exact ⟨(le_max_right _ _).trans hs'.1, by linarith [hs'.2, ht.2]⟩
        refine (hkey s' hs'T fun u hu => ?_).1
        rw [uIcc_of_ge (by linarith [hs'.2, ht.2])] at hu
        rcases le_total t u with htu | htu
        · exact hQann u (hIcc ⟨htu, hu.2⟩)
        · exact hδO u ⟨(le_max_left _ _).trans (hs'.1.trans hu.1), by linarith⟩
      rw [neg_neg] at h
      exact h
  have hT := hkey T right_mem_uIcc fun u hu => hQann u (hall u (by
    exact uIcc_subset_uIcc left_mem_uIcc right_mem_uIcc hu))
  obtain ⟨w, hw, hwx⟩ := hT.1
  have hzw : z T = w := by
    simp only [hzdef]
    rw [← hwx]
    exact (ch D).χ.left_inv ((ch D).hball (annulus_subset_ball D (hSann hw)))
  refine ⟨w, hwx.symm, hzw ▸ hT.2.1, hzw ▸ hT.2.2, ?_⟩
  have hwi : w i ≠ 0 := (hgood w hw.1 hw.2.1).2
  exact lt_of_le_of_ne hw.2.2 (mul_ne_zero hwi hy.2).symm

end GC.Seifert.SaddleSlabProof
