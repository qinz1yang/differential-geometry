import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Dynamics

/-!
# Attaching arcs of a one-saddle strip

Lane RG03c. Let `D` be a gradient-like strip on `f ⁻¹' [a, b]` with the single critical point
`p` of index one, `ε = r₀²` and `a < f p - ε`. The small ball lies in `|f - f p| < ε / 2` and the
box `boxSet D` in `|f - f p| ≤ ε`. `eq_flow_of_flow_mem_boxSet`: if the upward flow line of a
point `y` of the lower level meets the box within time `s`, then it first meets the box on the
bottom level `f = f p - ε`, at a point `χ w` with `saddleQ w = -ε` and `|saddleK w| ≤ ε`, after the
time `f p - ε - a ≤ s`, so `y` is the image of `χ w` under the downward flow for that time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ} {p : M}

variable (D : GradientLikeStrip I f a b {p})

theorem abs_f_sub_lt_of_mem_smallBall (hk : (ch D).k = 1) {x : M}
    (hx : x ∈ D.smallBall p (Finset.mem_singleton_self p)) :
    |f x - f p| < (ch D).r₀ ^ 2 / 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : morseNorm 2 y < (ch D).r₀ := hy
  change |f ((ch D).χ y) - f p| < _
  rw [f_chart D hk (hy'.trans (D.r₀_lt_rm p (Finset.mem_singleton_self p))),
    add_sub_cancel_left]
  have h2 := two_abs_saddleQ_le y
  have h3 := (morseNorm_lt_iff (r₀_pos D).le y).mp hy'
  linarith

theorem f_mem_of_mem_boxSet (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) {x : M}
    (hx : x ∈ boxSet D) : f x ∈ Icc (f p - (ch D).r₀ ^ 2) (f p + (ch D).r₀ ^ 2) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [f_chart D hk (saddleBox_subset_lt D hrm hy)]
  have h := abs_le.mp hy.1
  constructor <;> linarith [h.1, h.2]

variable [T2Space M] [I.Boundaryless]

theorem eq_flow_of_flow_mem_boxSet (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - (ch D).r₀ ^ 2) {y : M} (hy : f y = a)
    {s : ℝ} (hsb : a + s ≤ b) {u : ℝ} (hu : u ∈ Icc 0 s) (hmem : D.flow (-u) y ∈ boxSet D) :
    ∃ w ∈ saddleBox ((ch D).r₀ ^ 2), saddleQ w = -((ch D).r₀ ^ 2) ∧
      y = D.flow (f p - (ch D).r₀ ^ 2 - a) ((ch D).χ w) ∧ f p - (ch D).r₀ ^ 2 - a ≤ s := by
  set ε := (ch D).r₀ ^ 2 with hε
  set Qs : Set ℝ := {v | v ∈ Icc 0 s ∧ D.flow (-v) y ∈ boxSet D} with hQsdef
  have hQc : IsClosed Qs := isClosed_Icc.inter ((isClosed_boxSet D hrm).preimage
    ((D.continuous_flow_curve y).comp continuous_neg))
  have hQne : Qs.Nonempty := ⟨u, hu, hmem⟩
  have hQbdd : BddBelow Qs := ⟨0, fun v hv => hv.1.1⟩
  set u₁ := sInf Qs with hu₁def
  have hu₁ : u₁ ∈ Qs := hQc.csInf_mem hQne hQbdd
  have hmin : ∀ v ∈ Ico 0 u₁, D.flow (-v) y ∉ boxSet D := fun v hv hv' =>
    (not_le.2 hv.2) (csInf_le hQbdd ⟨⟨hv.1, hv.2.le.trans hu₁.1.2⟩, hv'⟩)
  have hab : a ≤ b := by linarith [hu.1, hu.2]
  have hu₁pos : 0 < u₁ := by
    refine lt_of_le_of_ne hu₁.1.1 fun h => ?_
    have h1 := hu₁.2
    rw [← h, neg_zero, GradientLikeStrip.flow_zero] at h1
    have h2 := (f_mem_of_mem_boxSet D hk hrm h1).1
    linarith
  have hunit : ∀ v ∈ Ico 0 u₁, f (D.flow (-v) y) = a + v := by
    intro v hv
    have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := y) (T := -v)
      ⟨hy.ge, hy.le.trans hab⟩ ⟨by linarith [hv.1], by linarith [hv.2, hu₁.1.2]⟩
      (fun v' hv' q hq hq' => by
        obtain rfl := Finset.mem_singleton.mp hq
        rw [uIcc_of_ge (by linarith [hv.1])] at hv'
        refine hmin (-v') ⟨by linarith [hv'.2], by linarith [hv'.1, hv.2]⟩ ?_
        rw [neg_neg]
        exact smallBall_subset_boxSet D hq hq')
      (-v) right_mem_uIcc
    rw [h, hy]
    ring
  have hunit₁ : f (D.flow (-u₁) y) = a + u₁ := by
    have hcl : IsClosed {v : ℝ | f (D.flow (-v) y) = a + v} :=
      isClosed_eq (hf.continuous.comp ((D.continuous_flow_curve y).comp continuous_neg))
        (continuous_const.add continuous_id)
    have hsub : closure (Ico 0 u₁) ⊆ {v : ℝ | f (D.flow (-v) y) = a + v} :=
      closure_minimal hunit hcl
    rw [closure_Ico hu₁pos.ne] at hsub
    exact hsub ⟨hu₁pos.le, le_rfl⟩
  have hbox₁ := f_mem_of_mem_boxSet D hk hrm hu₁.2
  have hlev : a + u₁ = f p - ε := by
    refine le_antisymm ?_ (hunit₁ ▸ hbox₁.1)
    by_contra hcon
    push Not at hcon
    set v₂ := f p - ε - a with hv₂
    have hv₂mem : v₂ ∈ Ico 0 u₁ := ⟨by linarith, by linarith⟩
    have hw₂ := hmin v₂ hv₂mem
    have hfw₂ : f (D.flow (-v₂) y) = f p - ε := by
      rw [hunit v₂ hv₂mem]
      ring
    have hasc := flow_notMem_boxSet_asc D hf hk hrm hw₂ hfw₂.ge
      ⟨by linarith, by linarith [hu₁.1.2]⟩ (T := u₁ - v₂) (by linarith [hu₁.1.2])
      (-(u₁ - v₂)) ⟨le_rfl, by linarith [hv₂mem.2]⟩
    apply hasc
    rw [GradientLikeStrip.flow_flow]
    have : -v₂ + -(u₁ - v₂) = -u₁ := by ring
    rw [this]
    exact hu₁.2
  obtain ⟨w, hw, hwz⟩ := hu₁.2
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · have h1 := f_chart D hk (saddleBox_subset_lt D hrm hw)
    rw [hwz, hunit₁, hlev] at h1
    linarith
  · rw [hwz, show f p - ε - a = u₁ by linarith, GradientLikeStrip.flow_flow_neg]
  · linarith [hu₁.1.2]

end GC.Seifert.SaddleSlabProof
