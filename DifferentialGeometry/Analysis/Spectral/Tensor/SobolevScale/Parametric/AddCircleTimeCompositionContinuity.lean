import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleLpCompositionContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTimeTameComposition
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_tendsto_timeL2_affine_comp
    {X V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : Filter X}
    (H : ℝ × V →L[ℝ] Y) (T : ℝ)
    (f : X → V) (f₀ : V) (u : X → timeL2 V T) (u₀ : timeL2 V T)
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    ∃ (q : X → timeL2 Y T) (q₀ : timeL2 Y T),
      Tendsto q l (𝓝 q₀) ∧
      (∀ x, q x =ᵐ[timeMeasure T] fun t => H (t, f x + u x t)) ∧
      q₀ =ᵐ[timeMeasure T] fun t => H (t, f₀ + u₀ t) := by
  let A := H.comp (ContinuousLinearMap.inr ℝ ℝ V)
  let B : V →L[ℝ] timeL2 V T := Lp.constL 2 (timeMeasure T) ℝ
  have htime : MemLp (fun t : ℝ => H (t, 0)) 2 (timeMeasure T) :=
    memLp_of_continuousOn
      (H.continuous.comp_continuousOn (continuousOn_id.prodMk continuousOn_const))
  let qtime := htime.toLp (fun t : ℝ => H (t, 0))
  let make := fun v : V => fun w : timeL2 V T =>
    qtime + A.compLpL 2 (timeMeasure T) (B v + w)
  have heval (v : V) (w : timeL2 V T) :
      make v w =ᵐ[timeMeasure T] fun t => H (t, v + w t) := by
    have hconst : B v =ᵐ[timeMeasure T] fun _ => v := Lp.coeFn_const _ _ _
    filter_upwards [Lp.coeFn_add qtime (A.compLpL 2 (timeMeasure T) (B v + w)),
      htime.coeFn_toLp, A.coeFn_compLpL (B v + w), Lp.coeFn_add (B v) w,
      hconst] with t hadd ht hA hsum hB
    dsimp only [make]
    change qtime t = H (t, 0) at ht
    simp only [Pi.add_apply] at hadd hsum
    rw [hadd, ht, hA, hsum, hB]
    change H (t, 0) + H (0, v + w t) = H (t, v + w t)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  refine ⟨fun x => make (f x) (u x), make f₀ u₀, ?_,
    fun x => heval (f x) (u x), heval f₀ u₀⟩
  exact tendsto_const_nhds.add
    ((A.compLpL 2 (timeMeasure T)).continuous.tendsto _ |>.comp
      (((B.continuous.tendsto f₀).comp hf).add hu))

theorem tendsto_timeL2_scalarHs_composition_firstJet
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t)))) ⊆ U) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (t, f x + u x t) i)‖) ≤ R) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q A hRange hRange₀ hBound hEval hEval₀
  obtain ⟨q, q₀, hq, hqe, hqe₀⟩ := exists_tendsto_timeL2_affine_comp H T f f₀ u u₀ hf hu
  apply tendsto_lp_scalarHs_composition_of_lower_order_bound (timeMeasure T)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) g k F hF hU hK hKU R q q₀ a a₀ hq
  · intro x
    filter_upwards [hqe x, hRange x] with t hqt ht
    rw [hqt]
    exact ht
  · filter_upwards [hqe₀, hRange₀] with t hqt ht
    rw [hqt]
    exact ht
  · intro x
    filter_upwards [hqe x, hBound x] with t hqt ht
    rw [hqt]
    exact ht
  · intro x
    filter_upwards [hqe x, hEval x] with t hqt ht
    rw [hqt]
    exact ht
  · filter_upwards [hqe₀, hEval₀] with t hqt ht
    rw [hqt]
    exact ht

private theorem tendsto_timeL2_scalarHs_composition_firstJet_of_eventually
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (t, f x + u x t) i)‖) ≤ R) →
    (∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (t, f₀ + u₀ t) i)‖) ≤ R) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  classical
  intro P H J Q A hRange hRange₀ hBound hBound₀ hEval hEval₀
  let good := fun x =>
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f x + u x t)))) ⊆ K) ∧
    (∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (H (t, f x + u x t) i)‖) ≤ R) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f x + u x t))) z))
  have hg : ∀ᶠ x in l, good x := hRange.and (hBound.and hEval)
  let fc := fun x => if good x then f x else f₀
  let uc := fun x => if good x then u x else u₀
  let ac := fun x => if good x then a x else a₀
  have hfEq : f =ᶠ[l] fc := hg.mono fun x hx => by simp only [fc, if_pos hx]
  have huEq : u =ᶠ[l] uc := hg.mono fun x hx => by simp only [uc, if_pos hx]
  have haEq : ac =ᶠ[l] a := hg.mono fun x hx => by simp only [ac, if_pos hx]
  have hc : Tendsto ac l (𝓝 a₀) := by
    apply tendsto_timeL2_scalarHs_composition_firstJet g k T F hF hU hK hKU R
      fc f₀ uc u₀ ac a₀ (hf.congr' hfEq) (hu.congr' huEq)
    · intro x
      by_cases hx : good x
      · simpa only [fc, uc, if_pos hx] using hx.1
      · simpa only [fc, uc, if_neg hx] using hRange₀
    · exact hRange₀.mono fun t ht => ht.trans hKU
    · intro x
      by_cases hx : good x
      · simpa only [fc, uc, if_pos hx] using hx.2.1
      · simpa only [fc, uc, if_neg hx] using hBound₀
    · intro x
      by_cases hx : good x
      · simpa only [fc, uc, ac, if_pos hx] using hx.2.2
      · simpa only [fc, uc, ac, if_neg hx] using hEval₀
    · exact hEval₀
  exact hc.congr' haEq

private theorem exists_eventually_sum_norm_le_of_tendstoUniformlyOn
    {X ι : Type*} [Fintype ι] {l : Filter X}
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    (T : ℝ) (q : X → ℝ → PiLp 2 V) (q₀ : ℝ → PiLp 2 V)
    (hq₀ : ContinuousOn q₀ (Icc 0 T)) (hq : TendstoUniformlyOn q q₀ l (Icc 0 T)) :
    ∃ R : ℝ, (∀ᶠ x in l, ∀ t ∈ Icc 0 T, (∑ i, ‖q x t i‖) ≤ R) ∧
      ∀ t ∈ Icc 0 T, (∑ i, ‖q₀ t i‖) ≤ R := by
  classical
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.bddAbove_image hq₀.norm
  refine ⟨(Fintype.card ι : ℝ) * (1 + R₀), ?_, ?_⟩
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hq 1 zero_lt_one] with x hx
    intro t ht
    have hnorm : ‖q x t‖ ≤ 1 + R₀ := by
      calc
        ‖q x t‖ ≤ ‖q x t - q₀ t‖ + ‖q₀ t‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 + R₀ := add_le_add (by
          simpa only [dist_eq_norm, norm_sub_rev] using (hx t ht).le)
          (hR₀ (mem_image_of_mem _ ht))
    calc
      (∑ i, ‖q x t i‖) ≤ ∑ _i : ι, (1 + R₀) :=
        Finset.sum_le_sum (fun i _ => (PiLp.norm_apply_le _ i).trans hnorm)
      _ = _ := by simp [mul_add]
  · intro t ht
    have hnorm : ‖q₀ t‖ ≤ 1 + R₀ :=
      (hR₀ (mem_image_of_mem _ ht)).trans (by linarith)
    calc
      (∑ i, ‖q₀ t i‖) ≤ ∑ _i : ι, (1 + R₀) :=
        Finset.sum_le_sum (fun i _ => (PiLp.norm_apply_le _ i).trans hnorm)
      _ = _ := by simp [mul_add]

private theorem firstJet_normalized_projection_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (z : timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (y : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1))) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ)))
    let Hlow := C.comp (scalarHsTimeFirstJet (ι := ι) g (k + 1))
    y =ᵐ[timeMeasure T] (fun t => B (z t)) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => A)
      (H (t, v + z t))) =ᵐ[timeMeasure T] fun t => Hlow (t, B v + y t) := by
  intro P H A B C Hlow hy
  have hraw := scalarHsTimeCoordinate_firstJetHs_inclusion_ae_eq
    (ι := ι) g (show k + 1 ≤ k + 2 by omega) T v z y hy
  filter_upwards [hraw] with t ht
  have hnormalize (s : PiLp 2
      (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => A) (P s) =
        C (ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by exact_mod_cast (show k + 1 ≤ k + 2 by omega) :
              ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))) s) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  change ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => A)
    (P (scalarHsTimeCoordinate g _ (t, firstJetHs g _ (v + z t)))) = _
  exact (hnormalize _).trans (congrArg C ht)

private theorem exists_eventually_firstJet_lower_order_bound
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    ∃ R : ℝ,
      (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
        (∑ i, ‖A (H (t, f x + u x t) i)‖) ≤ R) ∧
      ∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (H (t, f₀ + u₀ t) i)‖) ≤ R := by
  intro P H A B hwu hwu₀
  let C := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ)))
  let Hlow := C.comp (scalarHsTimeFirstJet (ι := ι) g (k + 1))
  let q := fun x t => Hlow (t, B (f x) + w x t)
  let q₀ := fun t => Hlow (t, B f₀ + w₀ t)
  have hq₀ : ContinuousOn q₀ (Icc 0 T) :=
    Hlow.continuous.comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_const.add hw₀))
  have hstate : TendstoUniformlyOn
      (fun x t => B (f x) + w x t) (fun t => B f₀ + w₀ t) l (Icc 0 T) :=
    (((B.continuous.tendsto f₀).comp hf).tendstoUniformlyOn_const (Icc 0 T)).add hw
  let D := Hlow.comp (ContinuousLinearMap.inr ℝ ℝ _)
  have htime : TendstoUniformlyOn (fun (_ : X) t => Hlow (t, 0))
      (fun t => Hlow (t, 0)) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε
  have hq : TendstoUniformlyOn q q₀ l (Icc 0 T) := by
    have h := htime.add (D.uniformContinuous.comp_tendstoUniformlyOn hstate)
    have heq (t : ℝ)
        (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1))) :
        Hlow (t, 0) + D v = Hlow (t, v) := by
      change Hlow (t, 0) + Hlow (0, v) = Hlow (t, v)
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    change TendstoUniformlyOn
      (fun x t => Hlow (t, 0) + D (B (f x) + w x t))
      (fun t => Hlow (t, 0) + D (B f₀ + w₀ t)) l (Icc 0 T) at h
    simpa only [heq] using h
  obtain ⟨R, hR, hR₀⟩ :=
    exists_eventually_sum_norm_le_of_tendstoUniformlyOn T q q₀ hq₀ hq
  refine ⟨R, ?_, ?_⟩
  · filter_upwards [hR] with x hx
    filter_upwards [firstJet_normalized_projection_ae g k T (f x) (u x) (w x) (hwu x),
      ae_restrict_mem measurableSet_Icc] with t ht htt
    have heq := congrArg (fun v => ∑ i, ‖v i‖) ht
    exact heq.le.trans (hx t htt)
  · filter_upwards [firstJet_normalized_projection_ae g k T f₀ u₀ w₀ hwu₀,
      ae_restrict_mem measurableSet_Icc] with t ht htt
    have heq := congrArg (fun v => ∑ i, ‖v i‖) ht
    exact heq.le.trans (hR₀ t htt)

theorem tendsto_timeL2_scalarHs_composition_firstJet_of_tendstoUniformlyOn
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q B hwu hwu₀ hRange hRange₀ hEval hEval₀
  obtain ⟨R, hR, hR₀⟩ := exists_eventually_firstJet_lower_order_bound
    g k T f f₀ u u₀ w w₀ hf hw₀ hw hwu hwu₀
  exact tendsto_timeL2_scalarHs_composition_firstJet_of_eventually
    g k T F hF hU hK hKU R f f₀ u u₀ a a₀ hf hu
    hRange hRange₀ hR hR₀ hEval hEval₀

private theorem tendsto_timeL2_piLp_of_coord
    {X ι V : Type*} [Fintype ι] {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (T : ℝ)
    (a : X → timeL2 (PiLp 2 (fun _ : ι => V)) T)
    (a₀ : timeL2 (PiLp 2 (fun _ : ι => V)) T)
    (ha : ∀ j, Tendsto
      (fun x => Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) (a x) j) l
      (𝓝 (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) a₀ j))) :
    Tendsto a l (𝓝 a₀) := by
  let E := Lp.piLpEquiv (𝕜 := ℝ) (X := fun _ : ι => V) (timeMeasure T)
  have hpi : Tendsto (fun x j => E (a x) j) l (𝓝 (fun j => E a₀ j)) :=
    tendsto_pi_nhds.mpr ha
  have hE : Tendsto (fun x => E (a x)) l (𝓝 (E a₀)) :=
    (PiLp.continuous_toLp 2 (fun _ : ι => timeL2 V T)).continuousAt.tendsto.comp hpi
  have h := E.symm.continuous.tendsto (E a₀) |>.comp hE
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using h

theorem tendsto_timeL2_vectorHs_composition_firstJet_of_tendstoUniformlyOn
    {X ι κ : Type*} [Fintype ι] [Fintype κ] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (F : (Option (ι ⊕ ι) → ℝ) → (κ → ℝ)) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))) T)
    (a₀ : timeL2 (PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z j, scalarH1ToContinuous g (J (a x t j)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f x + u x t))) z) j) →
    (∀ᵐ t ∂timeMeasure T, ∀ z j, scalarH1ToContinuous g (J (a₀ t j)) z =
      F (scalarH1PiToContinuous g (Q (H (t, f₀ + u₀ t))) z) j) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q B hwu hwu₀ hRange hRange₀ hEval hEval₀
  let E := Lp.piLpEquiv (𝕜 := ℝ) (X := fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))
    (timeMeasure T)
  have hcoord (j : κ) : Tendsto (fun x => E (a x) j) l (𝓝 (E a₀ j)) := by
    apply tendsto_timeL2_scalarHs_composition_firstJet_of_tendstoUniformlyOn
      g k T (fun z => F z j) (contDiffOn_pi.mp hF j) hU hK hKU f f₀ u u₀
      (fun x => E (a x) j) (E a₀ j) w w₀ hf hu hw₀ hw hwu hwu₀ hRange hRange₀
    · filter_upwards [hEval] with x hx
      filter_upwards [hx, Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) (a x) j]
        with t ht hEt
      intro z
      rw [hEt]
      exact ht z j
    · filter_upwards [hEval₀, Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) a₀ j]
        with t ht hEt
      intro z
      rw [hEt]
      exact ht z j
  exact tendsto_timeL2_piLp_of_coord T a a₀ hcoord

end AddCircle

end

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_tendsto_timeL2_affine_comp_timeShift
    {X V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : Filter X}
    (H : ℝ × V →L[ℝ] Y) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ)
    (f : X → V) (f₀ : V) (u : X → timeL2 V T) (u₀ : timeL2 V T)
    (hσ : Tendsto σ l (𝓝 σ₀)) (hf : Tendsto f l (𝓝 f₀))
    (hu : Tendsto u l (𝓝 u₀)) :
    ∃ (q : X → timeL2 Y T) (q₀ : timeL2 Y T),
      Tendsto q l (𝓝 q₀) ∧
      (∀ x, q x =ᵐ[timeMeasure T] fun t => H (σ x + t, f x + u x t)) ∧
      q₀ =ᵐ[timeMeasure T] fun t => H (σ₀ + t, f₀ + u₀ t) := by
  obtain ⟨r, r₀, hr, hre, hre₀⟩ :=
    exists_tendsto_timeL2_affine_comp H T f f₀ u u₀ hf hu
  let C : ℝ →L[ℝ] timeL2 Y T :=
    (Lp.constL 2 (timeMeasure T) ℝ).comp (H.comp (ContinuousLinearMap.inl ℝ ℝ V))
  have hCe (s : ℝ) : C s =ᵐ[timeMeasure T] fun _ => H (s, 0) :=
    Lp.coeFn_const _ _ _
  have heq (s t : ℝ) (v : V) : H (s, 0) + H (t, v) = H (s + t, v) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, zero_add]
  refine ⟨fun x => C (σ x) + r x, C σ₀ + r₀,
    ((C.continuous.tendsto σ₀).comp hσ).add hr, ?_, ?_⟩
  · intro x
    filter_upwards [Lp.coeFn_add (C (σ x)) (r x), hCe (σ x), hre x]
      with t hadd hc ht
    simpa only [Pi.add_apply, hc, ht, heq] using hadd
  · filter_upwards [Lp.coeFn_add (C σ₀) r₀, hCe σ₀, hre₀] with t hadd hc ht
    simpa only [Pi.add_apply, hc, ht, heq] using hadd

theorem tendsto_timeL2_scalarHs_composition_firstJet_timeShift
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t)))) ⊆ U) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (σ x + t, f x + u x t) i)‖) ≤ R) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q A hRange hRange₀ hBound hEval hEval₀
  obtain ⟨q, q₀, hq, hqe, hqe₀⟩ := exists_tendsto_timeL2_affine_comp_timeShift
    H T σ σ₀ f f₀ u u₀ hσ hf hu
  apply tendsto_lp_scalarHs_composition_of_lower_order_bound (timeMeasure T)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) g k F hF hU hK hKU R q q₀ a a₀ hq
  · intro x
    filter_upwards [hqe x, hRange x] with t hqt ht
    rw [hqt]
    exact ht
  · filter_upwards [hqe₀, hRange₀] with t hqt ht
    rw [hqt]
    exact ht
  · intro x
    filter_upwards [hqe x, hBound x] with t hqt ht
    rw [hqt]
    exact ht
  · intro x
    filter_upwards [hqe x, hEval x] with t hqt ht
    rw [hqt]
    exact ht
  · filter_upwards [hqe₀, hEval₀] with t hqt ht
    rw [hqt]
    exact ht

private theorem tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_eventually
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (σ x + t, f x + u x t) i)‖) ≤ R) →
    (∀ᵐ t ∂timeMeasure T,
      (∑ i, ‖A (H (σ₀ + t, f₀ + u₀ t) i)‖) ≤ R) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  classical
  intro P H J Q A hRange hRange₀ hBound hBound₀ hEval hEval₀
  let good := fun x =>
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t)))) ⊆ K) ∧
    (∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (H (σ x + t, f x + u x t) i)‖) ≤ R) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t))) z))
  have hg : ∀ᶠ x in l, good x := hRange.and (hBound.and hEval)
  let σc := fun x => if good x then σ x else σ₀
  let fc := fun x => if good x then f x else f₀
  let uc := fun x => if good x then u x else u₀
  let ac := fun x => if good x then a x else a₀
  have hσEq : σ =ᶠ[l] σc := hg.mono fun x hx => by simp only [σc, if_pos hx]
  have hfEq : f =ᶠ[l] fc := hg.mono fun x hx => by simp only [fc, if_pos hx]
  have huEq : u =ᶠ[l] uc := hg.mono fun x hx => by simp only [uc, if_pos hx]
  have haEq : ac =ᶠ[l] a := hg.mono fun x hx => by simp only [ac, if_pos hx]
  have hc : Tendsto ac l (𝓝 a₀) := by
    apply tendsto_timeL2_scalarHs_composition_firstJet_timeShift
      g k T σc σ₀ (hσ.congr' hσEq) F hF hU hK hKU R
      fc f₀ uc u₀ ac a₀ (hf.congr' hfEq) (hu.congr' huEq)
    · intro x
      by_cases hx : good x
      · simpa only [σc, fc, uc, if_pos hx] using hx.1
      · simpa only [σc, fc, uc, if_neg hx] using hRange₀
    · exact hRange₀.mono fun t ht => ht.trans hKU
    · intro x
      by_cases hx : good x
      · simpa only [σc, fc, uc, if_pos hx] using hx.2.1
      · simpa only [σc, fc, uc, if_neg hx] using hBound₀
    · intro x
      by_cases hx : good x
      · simpa only [σc, fc, uc, ac, if_pos hx] using hx.2.2
      · simpa only [σc, fc, uc, ac, if_neg hx] using hEval₀
    · exact hEval₀
  exact hc.congr' haEq

private theorem exists_eventually_firstJet_lower_order_bound_timeShift
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    ∃ R : ℝ,
      (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
        (∑ i, ‖A (H (σ x + t, f x + u x t) i)‖) ≤ R) ∧
      ∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (H (σ₀ + t, f₀ + u₀ t) i)‖) ≤ R := by
  classical
  intro P H A B hwu hwu₀
  obtain ⟨R, hR, hR₀⟩ := exists_eventually_firstJet_lower_order_bound
    g k T f f₀ u u₀ w w₀ hf hw₀ hw hwu hwu₀
  let c : ℝ → ℝ := fun s => ∑ i, ‖A (H (s, 0) i)‖
  have hc : Continuous c := by
    apply continuous_finsetSum
    intro i _
    exact (A.continuous.comp ((PiLp.continuous_apply 2 _ i).comp
      (H.continuous.comp (continuous_id.prodMk continuous_const)))).norm
  have hσbound : ∀ᶠ x in l, c (σ x) ≤ c σ₀ + 1 :=
    (((hc.tendsto σ₀).comp hσ).eventually
      (gt_mem_nhds (lt_add_one (c σ₀)))).mono fun _ hx => hx.le
  have hshift (s t : ℝ)
      (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) :
      (∑ i, ‖A (H (s + t, v) i)‖) ≤ c s + ∑ i, ‖A (H (t, v) i)‖ := by
    have heq : H (s + t, v) = H (s, 0) + H (t, v) := by
      rw [← map_add]
      congr 1
      simp only [Prod.mk_add_mk, zero_add]
    rw [heq]
    calc
      (∑ i, ‖A ((H (s, 0) + H (t, v)) i)‖) ≤
          ∑ i, (‖A (H (s, 0) i)‖ + ‖A (H (t, v) i)‖) := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [PiLp.add_apply, map_add] using norm_add_le (A (H (s, 0) i)) (A (H (t, v) i))
      _ = c s + ∑ i, ‖A (H (t, v) i)‖ := Finset.sum_add_distrib
  refine ⟨(c σ₀ + 1) + R, ?_, ?_⟩
  · filter_upwards [hσbound, hR] with x hx hxR
    filter_upwards [hxR] with t ht
    exact (hshift (σ x) t (f x + u x t)).trans (add_le_add hx ht)
  · filter_upwards [hR₀] with t ht
    exact (hshift σ₀ t (f₀ + u₀ t)).trans
      (add_le_add (le_add_of_nonneg_right zero_le_one) ht)

theorem tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a x t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g (J (a₀ t)) z =
      F (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t))) z)) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q B hwu hwu₀ hRange hRange₀ hEval hEval₀
  obtain ⟨R, hR, hR₀⟩ := exists_eventually_firstJet_lower_order_bound_timeShift
    g k T σ σ₀ hσ f f₀ u u₀ w w₀ hf hw₀ hw hwu hwu₀
  exact tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_eventually
    g k T σ σ₀ hσ F hF hU hK hKU R f f₀ u u₀ a a₀ hf hu
    hRange hRange₀ hR hR₀ hEval hEval₀

theorem tendsto_timeL2_vectorHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    {X ι κ : Type*} [Fintype ι] [Fintype κ] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (F : (Option (ι ⊕ ι) → ℝ) → (κ → ℝ)) {U K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : X → timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (u₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (a : X → timeL2 (PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))) T)
    (a₀ : timeL2 (PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))) T)
    (w : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (w₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T)) (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H := P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    (∀ x, w x =ᵐ[timeMeasure T] fun t => B (u x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => B (u₀ t)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z j, scalarH1ToContinuous g (J (a x t j)) z =
      F (scalarH1PiToContinuous g (Q (H (σ x + t, f x + u x t))) z) j) →
    (∀ᵐ t ∂timeMeasure T, ∀ z j, scalarH1ToContinuous g (J (a₀ t j)) z =
      F (scalarH1PiToContinuous g (Q (H (σ₀ + t, f₀ + u₀ t))) z) j) →
    Tendsto a l (𝓝 a₀) := by
  intro P H J Q B hwu hwu₀ hRange hRange₀ hEval hEval₀
  let E := Lp.piLpEquiv (𝕜 := ℝ) (X := fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 2))
    (timeMeasure T)
  have hcoord (j : κ) : Tendsto (fun x => E (a x) j) l (𝓝 (E a₀ j)) := by
    apply tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
      g k T σ σ₀ hσ (fun z => F z j) (contDiffOn_pi.mp hF j) hU hK hKU f f₀ u u₀
      (fun x => E (a x) j) (E a₀ j) w w₀ hf hu hw₀ hw hwu hwu₀ hRange hRange₀
    · filter_upwards [hEval] with x hx
      filter_upwards [hx, Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) (a x) j]
        with t ht hEt
      intro z
      rw [hEt]
      exact ht z j
    · filter_upwards [hEval₀, Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) a₀ j]
        with t ht hEt
      intro z
      rw [hEt]
      exact ht z j
  exact tendsto_timeL2_piLp_of_coord T a a₀ hcoord

end AddCircle

end
