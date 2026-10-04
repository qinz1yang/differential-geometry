import DifferentialGeometry.Topology.Morse.Strip.Foundations.GradientLike
import DifferentialGeometry.Topology.Manifold.BoundaryVectorField

/-!
# Gradient-like strips with prescribed Morse charts

Lane RG03c. `exists_gradientLikeStrip_of_charts` is `exists_gradientLikeStrip` of
`Morse/Strip/Foundations/GradientLike.lean` with the chart family given as input, so that two
different surfaces can be equipped with charts of the same small radius `r₀`; the regular part
of the field comes from `Manifold.exists_contMDiff_boundary_tangent_vector_field`, so no
`SigmaCompactSpace` is needed.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ}

theorem exists_gradientLikeStrip_of_charts [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (hf : MorseStrip I f a b) (crit : Finset M)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ Morse.IsCriticalPointAt I f x)
    (chart : ∀ p ∈ crit, MorseNormalChart I f p)
    (hr₀ : ∀ p hp, 8 * (chart p hp).r₀ < (chart p hp).R)
    (hdisj : ∀ p hp q hq, p ≠ q → Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
      ((chart q hq).χ '' Metric.ball 0 (chart q hq).R'))
    (hstrip : ∀ p hp, (chart p hp).χ '' Metric.ball 0 (chart p hp).R' ⊆ f ⁻¹' Ioo a b) :
    ∃ D : GradientLikeStrip I f a b crit,
      (∀ p hp, D.chart p hp = (chart p hp).halve (hr₀ p hp)) ∧
      ∀ p hp, D.rm p hp = (chart p hp).R / 2 := by
  have hfc : Continuous f := hf.smooth.continuous
  set B : Set M := ⋃ q : {q // q ∈ crit},
    (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} with hBdef
  have hBopen : IsOpen B := isOpen_iUnion fun q => (chart q.1 q.2).isOpen_image_of_lt
    (by linarith [(chart q.1 q.2).hr₀R, (chart q.1 q.2).hRR', (chart q.1 q.2).hr₀])
  set Kreg := f ⁻¹' Icc a b \ B with hKdef
  have hKc : IsCompact Kreg := hf.compact.diff hBopen
  have hKreg : ∀ x ∈ Kreg, ¬ Morse.IsCriticalPointAt I f x := by
    rintro x ⟨hx1, hx2⟩ hc
    have hxo : f x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx1.1 fun h => hf.regular x (Or.inl h.symm) hc,
        lt_of_le_of_ne hx1.2 fun h => hf.regular x (Or.inr h) hc⟩
    have hxc : x ∈ crit := (hcrit x).2 ⟨hxo, hc⟩
    exact hx2 (mem_iUnion.2 ⟨⟨x, hxc⟩, (chart x hxc).p_mem_image_lt (chart x hxc).hr₀⟩)
  obtain ⟨X, hX, hXc, -, hrateX, ⟨U, -, hKU, -, hunitX⟩, -⟩ :=
    Manifold.exists_contMDiff_boundary_tangent_vector_field (n := 0) (D := univ)
      hKc isOpen_univ (subset_univ _) hf.smooth (fun x hx _ => hKreg x hx)
      (by intro x hx; simp only [frontier_univ, inter_empty, mem_empty_iff_false] at hx)
  let Vr : (x : M) → TangentSpace I x := fun x => -X x
  have hVr : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, Vr x⟩ : TangentBundle I M)) := hX.neg_section
  have hVrc : IsCompact (tsupport Vr) := by
    refine hXc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro x hx hzero
    apply hx
    change -(X x : Fin n → ℝ) = 0
    change (X x : Fin n → ℝ) = 0 at hzero
    rw [hzero, neg_zero]
  have hVrK : ∀ x ∈ Kreg, dfV I f Vr x = -1 := by
    intro x hx
    change (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (-X x)) = -1
    rw [map_neg, map_neg, hunitX x (hKU hx)]
  have hVrb : ∀ x, -1 ≤ dfV I f Vr x ∧ dfV I f Vr x ≤ 0 := by
    intro x
    change -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (-X x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (-X x)) ≤ 0
    rw [map_neg, map_neg]
    have h := hrateX x
    constructor <;> linarith [h.1, h.2]
  set V := glued chart Vr with hVdef
  have hmodel_bounds : ∀ q x, -1 ≤ dfV I f (modelPart chart q) x ∧
      dfV I f (modelPart chart q) x ≤ 0 :=
    fun q x => (chart q.1 q.2).dfV_push_modelY_bounds hf.smooth x
  have hb01 : ∀ q x, 0 ≤ bumpFun chart q x ∧ bumpFun chart q x ≤ 1 := fun q x =>
    ⟨(chart q.1 q.2).pushFun_bumpY_nonneg x, (chart q.1 q.2).pushFun_bumpY_le_one x⟩
  have hneg1 : ∀ q x, bumpFun chart q x ≠ 0 →
      x ∉ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} →
      dfV I f (modelPart chart q) x = -1 := by
    intro q x hq hx
    obtain ⟨y, hy, rfl⟩ := (chart q.1 q.2).mem_of_pushFun_bumpY_ne_zero hq
    exact (chart q.1 q.2).dfV_push_modelY_eq_neg_one hf.smooth hy
      (not_lt.1 fun h => hx ⟨y, h, rfl⟩)
  have hlt0 : ∀ q x, bumpFun chart q x ≠ 0 → x ∉ crit → dfV I f (modelPart chart q) x < 0 := by
    intro q x hq hx
    obtain ⟨y, hy, rfl⟩ := (chart q.1 q.2).mem_of_pushFun_bumpY_ne_zero hq
    refine (chart q.1 q.2).dfV_push_modelY_neg hf.smooth hy fun h0 => hx ?_
    rw [h0, (chart q.1 q.2).hχ0]
    exact q.2
  have hsum01 := fun x => sum_bumpFun_mem_Icc hdisj x
  have hb1 : ∀ q x, x ∈ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} →
      bumpFun chart q x = 1 := by
    rintro q x ⟨y, hy, rfl⟩
    exact (chart q.1 q.2).pushFun_bumpY_chart_eq_one
      (by
        have := hr₀ q.1 q.2
        have := (chart q.1 q.2).hr₀
        simp only [Set.mem_ofPred_eq] at hy
        linarith)
  have hterm2 : ∀ x, ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x ≤ 0 :=
    fun x => Finset.sum_nonpos fun q _ => by nlinarith [hb01 q x, hmodel_bounds q x]
  have hrate : ∀ x, -1 ≤ dfV I f V x ∧ dfV I f V x ≤ 0 := by
    intro x
    rw [hVdef, dfV_glued]
    obtain ⟨hS0, hS1⟩ := hsum01 x
    have hVr' : -1 ≤ dfV I f Vr x ∧ dfV I f Vr x ≤ 0 := hVrb x
    have hterm1 : -∑ q : {q // q ∈ crit}, bumpFun chart q x ≤
        ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun q _ => by nlinarith [hb01 q x, hmodel_bounds q x]
    have := hterm2 x
    constructor <;> nlinarith
  have hunit : ∀ x ∈ f ⁻¹' Icc a b,
      (∀ q : {q // q ∈ crit}, x ∉ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀}) →
      dfV I f V x = -1 := by
    intro x hx hxB
    have hxK : x ∈ Kreg := ⟨hx, fun h => by
      obtain ⟨q, hq⟩ := mem_iUnion.1 h
      exact hxB q hq⟩
    have hVrx : dfV I f Vr x = -1 := hVrK x hxK
    rw [hVdef, dfV_glued, hVrx]
    have : ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x =
        ∑ q : {q // q ∈ crit}, -(bumpFun chart q x) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : bumpFun chart q x = 0
      · rw [hq]; ring
      · rw [hneg1 q x hq (hxB q)]; ring
    rw [this, Finset.sum_neg_distrib]
    ring
  have hneg : ∀ x ∈ f ⁻¹' Icc a b, x ∉ crit → dfV I f V x < 0 := by
    intro x hx hxc
    rw [hVdef, dfV_glued]
    obtain ⟨hS0, hS1⟩ := hsum01 x
    have hVr' : -1 ≤ dfV I f Vr x ∧ dfV I f Vr x ≤ 0 := hVrb x
    have ht2 := hterm2 x
    rcases hS1.lt_or_eq with hS | hS
    · have hxK : x ∈ Kreg := by
        refine ⟨hx, fun h => ?_⟩
        obtain ⟨q, hq⟩ := mem_iUnion.1 h
        have h1 := hb1 q x hq
        have hsum : ∑ q' : {q // q ∈ crit}, bumpFun chart q' x = 1 := by
          rw [sum_eq_single_of_unique hdisj (q₀ := q) (by rw [h1]; exact one_ne_zero) _
            fun q' hq' => hq']
          exact h1
        linarith
      have hVrx : dfV I f Vr x = -1 := hVrK x hxK
      rw [hVrx]
      nlinarith
    · have hex : ∃ q, bumpFun chart q x ≠ 0 := by
        by_contra h
        have := sum_bumpFun_eq_zero fun q => of_not_not fun hq => h ⟨q, hq⟩
        linarith
      obtain ⟨q₀, hq₀⟩ := hex
      have h1 : ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x =
          bumpFun chart q₀ x * dfV I f (modelPart chart q₀) x :=
        sum_eq_single_of_unique hdisj hq₀ _ fun q hq => by rw [hq, zero_mul]
      have h2 : ∑ q : {q // q ∈ crit}, bumpFun chart q x = bumpFun chart q₀ x :=
        sum_eq_single_of_unique hdisj hq₀ _ fun q hq => hq
      have hq₀1 : bumpFun chart q₀ x = 1 := by rw [← h2]; exact hS
      rw [h1, hS, sub_self, zero_mul, add_zero, hq₀1, one_mul]
      exact hlt0 q₀ x hq₀ hxc
  have hmodel : ∀ p hp, ∀ y, morseNorm n y < (chart p hp).R / 2 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (chart p hp).χ.symm ((chart p hp).χ y) (V ((chart p hp).χ y)) =
        ModelField.modelField (chart p hp).k (chart p hp).r₀ y := by
    intro p hp y hy
    have hq₀1 : bumpFun chart ⟨p, hp⟩ ((chart p hp).χ y) = 1 :=
      (chart p hp).pushFun_bumpY_chart_eq_one hy.le
    have hq₀ne : bumpFun chart ⟨p, hp⟩ ((chart p hp).χ y) ≠ 0 := by
      rw [hq₀1]; exact one_ne_zero
    have hV : V ((chart p hp).χ y) = modelPart chart ⟨p, hp⟩ ((chart p hp).χ y) := by
      rw [hVdef]
      unfold glued
      rw [sum_eq_single_of_unique hdisj hq₀ne
        (fun q => bumpFun chart q ((chart p hp).χ y) • modelPart chart q ((chart p hp).χ y))
        (fun q hq => by rw [hq, zero_smul]),
        sum_eq_single_of_unique hdisj hq₀ne _ (fun q hq => hq), hq₀1, one_smul, sub_self,
        zero_smul, add_zero]
    rw [hV]
    exact (chart p hp).pullback_push_modelY (by linarith [hy, (chart p hp).R_pos])
  refine ⟨{ V := V
            smooth := contMDiff_glued hVr
            compact := isCompact_tsupport_glued hVrc
            rate := hrate
            chart := fun p hp => (chart p hp).halve (hr₀ p hp)
            disjoint := fun p hp q hq hpq => hdisj p hp q hq hpq
            inStrip := fun p hp => hstrip p hp
            unit := fun x hx hxB => hunit x hx fun q => hxB q.1 q.2
            neg := hneg
            rm := fun p hp => (chart p hp).R / 2
            hrm := fun p hp => ⟨by
              have := hr₀ p hp
              have := (chart p hp).hr₀
              simp only [MorseNormalChart.halve_r₀]
              linarith, le_rfl⟩
            model := fun p hp y hy => hmodel p hp y hy }, fun p hp => rfl, fun p hp => rfl⟩

end

end DifferentialGeometry.Topology
