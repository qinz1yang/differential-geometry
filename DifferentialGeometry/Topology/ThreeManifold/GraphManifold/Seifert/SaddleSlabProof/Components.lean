import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Arcs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.LevelCircle

/-!
# The lower level of a one-saddle strip

Lane RG03c. For the strip `D` with `ε = r₀²` put `arc D σ t`, the image of the bottom point
`χ (footPt ε σ t)` under the downward flow for the time `f p - ε - a`; it lies on the lower level.
`lowDomain D` is the open set of points whose downward flow to the lower level avoids the box.
`eq_arc_of_flow_mem_boxSet`: an upward flow line from the lower level that meets the box starts
on an attaching arc `arc D σ t` with `|saddleK (footPt ε σ t)| ≤ ε`.
`connectedComponentIn_eq_arc`: if `f ⁻¹' [a, b]` is connected, every connected component of the
lower level contains `arc D 1 0` or `arc D (-1) 0`. Otherwise its points, flowed upwards, would
form a nonempty compact subset of the slab which is also relatively open and misses `p`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

variable {H : Type} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ} {p : M}

variable (D : GradientLikeStrip I f a b {p})

def eps : ℝ := (ch D).r₀ ^ 2

theorem eps_pos : 0 < eps D := by
  unfold eps
  have := r₀_pos D
  positivity

variable [T2Space M] [I.Boundaryless]

def lowDomain : Set M := {x | ∀ s ∈ uIcc 0 (f x - a), D.flow s x ∉ boxSet D}

def arc (σ t : ℝ) : M := D.flow (f p - eps D - a) ((ch D).χ (footPt (eps D) σ t))

omit [T2Space M] [I.Boundaryless] in
theorem morseNorm_footPt_lt (hrm : 8 * (ch D).r₀ ≤ rmD D) {σ t : ℝ} (hσ : σ ^ 2 = 1)
    (ht : t ^ 2 ≤ 3 * eps D) : morseNorm 2 (footPt (eps D) σ t) < rmD D := by
  have hr := r₀_pos D
  rw [morseNorm_lt_iff (by linarith)]
  have h := Real.sq_sqrt (show 0 ≤ 2 * eps D + t ^ 2 by have := eps_pos D; positivity)
  simp only [footPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_pow, h, hσ]
  unfold eps at ht ⊢
  nlinarith

omit [T2Space M] [I.Boundaryless] in
theorem f_chart_footPt (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) {σ t : ℝ}
    (hσ : σ ^ 2 = 1) (ht : t ^ 2 ≤ 3 * eps D) :
    f ((ch D).χ (footPt (eps D) σ t)) = f p - eps D := by
  rw [f_chart D hk (morseNorm_footPt_lt D hrm hσ ht), saddleQ_footPt (eps_pos D).le hσ]
  ring

theorem f_flow_from_bottom (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (ha : a < f p - eps D) (hb : f p - eps D ≤ b) {z : M} (hz : f z = f p - eps D) {s : ℝ}
    (hs : s ∈ Icc 0 (f p - eps D - a)) : f (D.flow s z) = f z - s := by
  have h := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hf (x := z)
    (T := f p - eps D - a) ⟨by rw [hz]; linarith, by rw [hz]; exact hb⟩
    ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
    (fun y hy q hq hyq => by
      obtain rfl := Finset.mem_singleton.mp hq
      have h1 := abs_f_sub_lt_of_mem_smallBall D hk hyq
      rw [hz, mem_uIcc] at hy
      have he := eps_pos D
      unfold eps at hy he ha
      rw [abs_lt] at h1
      rcases hy with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> linarith [h1.1])
  exact h s (by rw [uIcc_of_le (by linarith [hs.1, hs.2])]; exact hs)

theorem f_arc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - eps D) (hb : f p - eps D ≤ b) {σ t : ℝ}
    (hσ : σ ^ 2 = 1) (ht : t ^ 2 ≤ 3 * eps D) : f (arc D σ t) = a := by
  have hz := f_chart_footPt D hk hrm hσ ht
  unfold arc
  rw [f_flow_from_bottom D hf hk ha hb hz ⟨by linarith, le_rfl⟩, hz]
  ring

theorem eq_footPt_of_saddleQ {ε : ℝ} {w : MorseModel 2} (hw : saddleQ w = -ε) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ w = footPt ε σ (w 1) := by
  have hw0 : w 0 ^ 2 = 2 * ε + w 1 ^ 2 := by
    unfold saddleQ at hw
    linarith
  have hsq : Real.sqrt (2 * ε + w 1 ^ 2) = |w 0| := by
    rw [← hw0, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 (w 0) with h | h
  · refine ⟨1, by norm_num, ?_⟩
    ext i
    fin_cases i
    · simp only [footPt, hsq, abs_of_nonneg h, one_mul]
      rfl
    · simp only [footPt]
      rfl
  · refine ⟨-1, by norm_num, ?_⟩
    ext i
    fin_cases i
    · simp only [footPt, hsq, abs_of_neg h, neg_one_mul, neg_neg]
      rfl
    · simp only [footPt]
      rfl

theorem sq_le_of_abs_saddleK_footPt {ε σ t : ℝ} (hε : 0 < ε) (hσ : σ ^ 2 = 1)
    (hK : |saddleK (footPt ε σ t)| ≤ 2 * ε) : t ^ 2 ≤ 2 * ε := by
  rw [saddleK_footPt] at hK
  by_contra hcon
  push Not at hcon
  have hs : 0 ≤ Real.sqrt (2 * ε + t ^ 2) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * ε + t ^ 2 by positivity)
  have habs : |σ * t * Real.sqrt (2 * ε + t ^ 2)| ^ 2 = t ^ 2 * (2 * ε + t ^ 2) := by
    rw [sq_abs, mul_pow, mul_pow, hσ, hs2, one_mul]
  have h1 : |σ * t * Real.sqrt (2 * ε + t ^ 2)| ^ 2 ≤ (2 * ε) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hK 2
  rw [habs] at h1
  nlinarith

theorem eq_arc_of_flow_mem_boxSet (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - eps D) {y : M} (hy : f y = a) {s : ℝ}
    (hsb : a + s ≤ b) {u : ℝ} (hu : u ∈ Icc 0 s) (hmem : D.flow (-u) y ∈ boxSet D) :
    ∃ σ t, σ ^ 2 = 1 ∧ |saddleK (footPt (eps D) σ t)| ≤ eps D ∧ y = arc D σ t ∧
      f p - eps D - a ≤ s := by
  obtain ⟨w, hw, hwq, hyw, hs⟩ := eq_flow_of_flow_mem_boxSet D hf hk hrm ha hy hsb hu hmem
  obtain ⟨σ, hσ, hwσ⟩ := eq_footPt_of_saddleQ hwq
  refine ⟨σ, w 1, hσ, ?_, ?_, by rw [show eps D = (ch D).r₀ ^ 2 from rfl]; exact hs⟩
  · rw [show eps D = (ch D).r₀ ^ 2 from rfl, ← hwσ]
    exact hw.2
  · unfold arc
    rw [show eps D = (ch D).r₀ ^ 2 from rfl, ← hwσ]
    exact hyw

theorem ordConnected_attach {ε σ : ℝ} (hσ : σ ^ 2 = 1) (c : ℝ) :
    OrdConnected {t : ℝ | |saddleK (footPt ε σ t)| ≤ c} := by
  have hval : ∀ t, |saddleK (footPt ε σ t)| = |t| * Real.sqrt (2 * ε + t ^ 2) := by
    intro t
    rw [saddleK_footPt, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have : |σ| = 1 := by
      have h := sq_abs σ
      rw [hσ] at h
      nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
    rw [this, one_mul]
  refine ⟨fun x hx y hy t ht => ?_⟩
  simp only [mem_ofPred_eq, hval] at hx hy ⊢
  have hmax : |t| ≤ max |x| |y| := by
    rcases le_total 0 t with h | h
    · exact (abs_of_nonneg h ▸ (ht.2.trans (le_abs_self y))).trans (le_max_right _ _)
    · have : -t ≤ -x := by linarith [ht.1]
      exact (abs_of_nonpos h ▸ (this.trans (neg_le_abs x))).trans (le_max_left _ _)
  have hmono : ∀ {r s : ℝ}, |r| ≤ |s| →
      |r| * Real.sqrt (2 * ε + r ^ 2) ≤ |s| * Real.sqrt (2 * ε + s ^ 2) := by
    intro r s hrs
    apply mul_le_mul hrs (Real.sqrt_le_sqrt (by nlinarith [sq_abs r, sq_abs s, abs_nonneg r]))
      (Real.sqrt_nonneg _) (abs_nonneg _)
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h] at hmax
    exact (hmono hmax).trans hy
  · rw [max_eq_left h] at hmax
    exact (hmono hmax).trans hx

theorem isOpen_lowDomain (hf : Continuous f) (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    IsOpen (lowDomain D) := by
  have hC : IsClosed (boxSet D) := isClosed_boxSet D hrm
  set G : ℝ × M → M := fun q => D.flow (q.1 * (f q.2 - a)) q.2 with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun q : ℝ × M => (q.1 * (f q.2 - a), q.2)) :=
      (continuous_fst.mul ((hf.comp continuous_snd).sub continuous_const)).prodMk continuous_snd
    exact D.continuous_flow_joint.comp h1
  have hΩ : lowDomain D = {x | ∀ l ∈ Icc (0 : ℝ) 1, G (l, x) ∉ boxSet D} := by
    ext x
    exact forall_mem_uIcc_zero_iff (P := fun s => D.flow s x ∉ boxSet D)
  rw [hΩ, isOpen_iff_forall_mem_open]
  intro x hx
  have hsub : Icc (0 : ℝ) 1 ×ˢ {x} ⊆ G ⁻¹' (boxSet D)ᶜ := by
    rintro ⟨l, x'⟩ ⟨hl, hx'⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hx l hl
  obtain ⟨u, v, -, hv, hsu, hxv, huv⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    (hC.isOpen_compl.preimage hGc) hsub
  exact ⟨v, fun x' hx' l hl => huv ⟨hsu hl, hx'⟩, hv, hxv rfl⟩

theorem contDiff_footPt {ε : ℝ} (hε : 0 < ε) (σ : ℝ) : ContDiff ℝ ∞ (footPt ε σ) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (2 * ε + t ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t => by positivity
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul hs
  · exact contDiff_id

omit [T2Space M] [I.Boundaryless] in
theorem footPt_mem_ball (hrm : 8 * (ch D).r₀ ≤ rmD D) {σ t : ℝ} (hσ : σ ^ 2 = 1)
    (ht : t ^ 2 ≤ 3 * eps D) : footPt (eps D) σ t ∈ Metric.ball (0 : MorseModel 2) (ch D).R' :=
  lt_rmD_subset_ball D (morseNorm_footPt_lt D hrm hσ ht)

theorem contMDiffAt_arc (hrm : 8 * (ch D).r₀ ≤ rmD D) {σ t : ℝ} (hσ : σ ^ 2 = 1)
    (ht : t ^ 2 ≤ 3 * eps D) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (arc D σ) t := by
  have hχ : ContMDiffAt 𝓘(ℝ, MorseModel 2) I ∞ (ch D).χ (footPt (eps D) σ t) :=
    (ch D).hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds (footPt_mem_ball D hrm hσ ht))
  exact (D.contMDiff_flow _).contMDiffAt.comp t
    (hχ.comp t (contDiff_footPt (eps_pos D) σ).contMDiff.contMDiffAt)

theorem sq_eq_one_cases {σ : ℝ} (hσ : σ ^ 2 = 1) : σ = 1 ∨ σ = -1 := by
  have h : (σ - 1) * (σ + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

theorem connectedComponentIn_eq_arc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - eps D) (hb : f p + eps D < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsPreconnected (f ⁻¹' Icc a b)) {y : M}
    (hy : f y = a) :
    arc D 1 0 ∈ connectedComponentIn (f ⁻¹' {a}) y ∨
      arc D (-1) 0 ∈ connectedComponentIn (f ⁻¹' {a}) y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hab : a < b := by have := eps_pos D; linarith
  have hε := eps_pos D
  set S := f ⁻¹' Icc a b with hSdef
  set L := f ⁻¹' {a} with hLdef
  set Cy := connectedComponentIn L y with hCydef
  have hyL : y ∈ L := hy
  have hLS : L ⊆ S := fun x hx => ⟨le_of_eq hx.symm, (show f x = a from hx) ▸ hab.le⟩
  have hLc : IsClosed L := isClosed_eq hf.continuous continuous_const
  have hCyL : Cy ⊆ L := connectedComponentIn_subset L y
  have hCyimg : Cy = Subtype.val '' connectedComponent (⟨y, hyL⟩ : L) :=
    connectedComponentIn_eq_image hyL
  have hCyc : IsCompact Cy := by
    refine (hcpt.of_isClosed_subset ?_ (hCyL.trans hLS))
    rw [hCyimg]
    exact hLc.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have := locallyConnectedSpace_level (Module.finrank_fin_fun ℝ) hf hab hreg
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := (⟨y, hyL⟩ : L)))
  have hVL : ∀ x ∈ L, x ∈ V ↔ x ∈ Cy := by
    intro x hx
    rw [hCyimg]
    constructor
    · intro hxV
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [← hVeq]
      exact hxV
    · rintro ⟨z, hz, rfl⟩
      rw [← hVeq] at hz
      exact hz
  have hattach : ∀ σ : ℝ, σ ^ 2 = 1 → arc D σ 0 ∉ Cy → ∀ t,
      |saddleK (footPt (eps D) σ t)| ≤ eps D → arc D σ t ∉ Cy := by
    intro σ hσ h0 t ht hmem
    set A := arc D σ '' {t : ℝ | |saddleK (footPt (eps D) σ t)| ≤ eps D} with hAdef
    have hsq : ∀ t' : ℝ, |saddleK (footPt (eps D) σ t')| ≤ eps D → t' ^ 2 ≤ 2 * eps D :=
      fun t' ht' => sq_le_of_abs_saddleK_footPt hε hσ (ht'.trans (by linarith))
    have hApre : IsPreconnected A := by
      refine ((ordConnected_attach hσ _).isPreconnected).image _ ?_
      intro t' ht'
      exact (contMDiffAt_arc D hrm hσ ((hsq t' ht').trans (by linarith))).continuousAt
        |>.continuousWithinAt
    have hAL : A ⊆ L := by
      rintro _ ⟨t', ht', rfl⟩
      exact f_arc D hf hk hrm ha (by linarith) hσ ((hsq t' ht').trans (by linarith))
    have h0A : arc D σ 0 ∈ A := ⟨0, by
      change |saddleK (footPt (eps D) σ 0)| ≤ eps D
      rw [saddleK_footPt, mul_zero, zero_mul, abs_zero]
      exact hε.le, rfl⟩
    have hsub := hApre.subset_connectedComponentIn ⟨t, ht, rfl⟩ hAL
    rw [← connectedComponentIn_eq hmem] at hsub
    exact h0 (hsub h0A)
  have hnobox : ∀ y' ∈ Cy, ∀ s ∈ Icc 0 (b - a), ∀ u ∈ Icc 0 s, D.flow (-u) y' ∉ boxSet D := by
    intro y' hy' s hs u hu hbox
    obtain ⟨σ, t, hσ, ht, rfl, -⟩ := eq_arc_of_flow_mem_boxSet D hf hk hrm ha (hCyL hy')
      (by linarith [hs.2]) hu hbox
    rcases sq_eq_one_cases hσ with rfl | rfl
    · exact hattach 1 (by norm_num) h1 t ht hy'
    · exact hattach (-1) (by norm_num) h2 t ht hy'
  have hflowCy : ∀ y' ∈ Cy, ∀ s ∈ Icc 0 (b - a), f (D.flow (-s) y') = a + s ∧
      D.flow (-s) y' ∈ lowDomain D ∧ D.π a (D.flow (-s) y') = y' := by
    intro y' hy' s hs
    have hfy : f y' = a := hCyL hy'
    have hf' : f (D.flow (-s) y') = a + s := by
      have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := y') (T := -s)
        ⟨hfy.ge, hfy.le.trans hab.le⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩
        (fun v hv q hq hvq => by
          obtain rfl := Finset.mem_singleton.mp hq
          rw [uIcc_of_ge (by linarith [hs.1])] at hv
          refine hnobox y' hy' s hs (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩ ?_
          rw [neg_neg]
          exact smallBall_subset_boxSet D hq hvq)
        (-s) right_mem_uIcc
      rw [h, hfy]
      ring
    refine ⟨hf', fun u hu => ?_, ?_⟩
    · rw [hf', add_sub_cancel_left, uIcc_of_le hs.1] at hu
      rw [GradientLikeStrip.flow_flow, show -s + u = -(s - u) by ring]
      exact hnobox y' hy' s hs (s - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    · change D.flow (f (D.flow (-s) y') - a) (D.flow (-s) y') = y'
      rw [hf', add_sub_cancel_left, GradientLikeStrip.flow_flow_neg]
  set T := (fun q : ℝ × M => D.flow (-q.1) q.2) '' (Icc 0 (b - a) ×ˢ Cy) with hTdef
  have hTc : IsCompact T := (isCompact_Icc.prod hCyc).image
    (D.continuous_flow_joint.comp (continuous_fst.neg.prodMk continuous_snd))
  set U := lowDomain D ∩ D.π a ⁻¹' V with hUdef
  have hUo : IsOpen U :=
    (isOpen_lowDomain D hf.continuous hrm).inter (hV.preimage (D.continuous_π hf a))
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨s, y'⟩, ⟨hs, hy'⟩, rfl⟩
    obtain ⟨-, hlow, hπ⟩ := hflowCy y' hy' s hs
    refine ⟨hlow, ?_⟩
    change D.π a (D.flow (-s) y') ∈ V
    rw [hπ]
    exact (hVL y' (hCyL hy')).mpr hy'
  have hSUT : S ∩ U ⊆ T := by
    rintro x ⟨hxS, hxlow, hxV⟩
    have hT0 : 0 ≤ f x - a := by linarith [hxS.1]
    have hfπ : f (D.π a x) = a := by
      have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := x)
        (T := f x - a) hxS ⟨by linarith, by linarith [hxS.1]⟩
        (fun v hv q hq hvq => by
          obtain rfl := Finset.mem_singleton.mp hq
          exact hxlow v hv (smallBall_subset_boxSet D hq hvq))
        (f x - a) right_mem_uIcc
      change f (D.flow (f x - a) x) = a
      rw [h]
      ring
    have hπCy : D.π a x ∈ Cy := (hVL _ hfπ).mp hxV
    refine ⟨⟨f x - a, D.π a x⟩, ⟨⟨hT0, by linarith [hxS.2]⟩, hπCy⟩, ?_⟩
    change D.flow (-(f x - a)) (D.flow (f x - a) x) = x
    rw [GradientLikeStrip.flow_neg_flow]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) U Tᶜ hUo hTc.isClosed.isOpen_compl
    (fun x hx => by
      by_cases hxT : x ∈ T
      · exact Or.inl (hTU hxT)
      · exact Or.inr hxT)
    (by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxS hxU hxT
      exact hxT (hSUT ⟨hxS, hxU⟩)) with hSU | hST
  · have hpS : p ∈ S := ⟨by linarith, by linarith⟩
    have hp := (hSU hpS).1 0 left_mem_uIcc
    apply hp
    rw [GradientLikeStrip.flow_zero]
    refine ⟨0, ?_, (ch D).hχ0⟩
    simp only [saddleBox, mem_ofPred_eq, saddleQ, saddleK]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_self, zero_div, abs_zero, mul_zero]
    exact ⟨sq_nonneg _, sq_nonneg _⟩
  · have hyT : y ∈ T := ⟨⟨0, y⟩, ⟨⟨le_rfl, by linarith⟩, mem_connectedComponentIn hyL⟩, by
      simp only [neg_zero, GradientLikeStrip.flow_zero]⟩
    exact hST (hLS hyL) hyT

end GC.Seifert.SaddleSlabProof
