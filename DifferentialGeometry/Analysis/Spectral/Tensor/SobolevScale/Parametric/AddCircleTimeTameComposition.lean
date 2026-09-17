import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTimeComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTameComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFirstJet
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

noncomputable section
open scoped Manifold ContDiff ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem memLp_scalarHsTimeCoordinate_firstJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) (T : ℝ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) T) :
    MemLp (fun t => scalarHsTimeCoordinate g (n : ℝ)
      (t, firstJetHs g n (f₀ + u t))) 2 (timeMeasure T) := by
  let V := PiLp 2 (fun _ : ι ⊕ ι => TensorHs g 0 0 (n : ℝ))
  have ht : MemLp (fun t : ℝ => (t, (0 : V))) 2 (timeMeasure T) :=
    memLp_of_continuousOn (continuousOn_id.prodMk continuousOn_const)
  have hu : MemLp (fun t => f₀ + u t) 2 (timeMeasure T) :=
    (memLp_const f₀).add (Lp.memLp u)
  have hj := (firstJetHs (ι := ι) g n).comp_memLp' hu
  have hp : MemLp (fun t => (t, firstJetHs g n (f₀ + u t))) 2
      (timeMeasure T) := by
    have hh := ht.add ((ContinuousLinearMap.inr ℝ ℝ V).comp_memLp' hj)
    apply hh.ae_eq
    filter_upwards [] with t
    simp only [Function.comp_apply, Pi.add_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  have hf := (scalarHsTimeCoordinate (ι := ι ⊕ ι) g (n : ℝ)).comp_memLp' hp
  exact hf

theorem scalarHsTimeCoordinate_firstJetHs_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (T : ℝ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show ((1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hn 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
      (scalarHsTimeCoordinate g (n : ℝ) (t, firstJetHs g n (f₀ + u t)))) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g (t, L (firstJetHs g 1 (K f₀ + w t)))) := by
  intro J K L hw
  filter_upwards [hw] with t ht
  rw [tensorHsInclusion_scalarHsTimeCoordinate]
  congr 1
  apply Prod.ext
  · rfl
  · have hh := congrArg (fun A => A (f₀ + u t))
      (firstJetHs_comp_tensorHsInclusion (ι := ι) g hn)
    change firstJetHs g 1 (K (f₀ + u t)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (show ((1 : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast hn))
          (firstJetHs g n (f₀ + u t)) at hh
    rw [map_add, ← ht] at hh
    rw [hh]
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl

theorem exists_timeL2_scalarH2_composition_firstJet
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 1) (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let q := fun t => scalarH1TimeCoordinate g (t, L (firstJetHs g 1 (K f₀ + w t)))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
      (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K L q hwu hRange hEval
  let V := fun t => scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
    (t, firstJetHs g 2 (f₀ + u t))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
  let v := fun t => P (V t)
  have hV := memLp_scalarHsTimeCoordinate_firstJetHs g 2 T f₀ u
  have hv := P.comp_memLp' hV
  have hproject := scalarHsTimeCoordinate_firstJetHs_ae_eq g (by decide : 1 ≤ 2)
    T f₀ u w hwu
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ 2)
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
  have hqv : (fun t => Q (v t)) =ᵐ[timeMeasure T] q := by
    filter_upwards [hproject] with t ht
    refine Eq.trans ?_ ht
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hq : ContinuousOn q (Icc 0 T) := by
    exact (scalarH1TimeCoordinate g).continuous.comp_continuousOn
      (continuousOn_id.prodMk (L.continuous.comp_continuousOn
        ((firstJetHs g 1).continuous.comp_continuousOn (continuousOn_const.add hw))))
  let e : Icc (0 : ℝ) T × AddCircle (1 : ℝ) → (Option (ι ⊕ ι) → ℝ) :=
    fun p => scalarH1PiToContinuous g (q p.1) p.2
  have he : Continuous e := by
    have hqr : Continuous (fun t : Icc (0 : ℝ) T => q t) := continuousOn_iff_continuous_domRestrict.mp hq
    exact continuous_eval.comp
      (((scalarH1PiToContinuous g).continuous.comp (hqr.comp continuous_fst)).prodMk
        continuous_snd)
  have hcompact : IsCompact (range e) := isCompact_range he
  have hsub : range e ⊆ S := by
    rintro y ⟨⟨t, x⟩, rfl⟩
    exact hRange t t.2 (mem_range_self x)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
    ae_restrict_mem measurableSet_Icc
  apply exists_lp_scalarH2_composition_of_h1_bound (timeMeasure T) g F hF hS
    hcompact hsub hv ha (R := (Fintype.card (Option (ι ⊕ ι)) : ℝ) * C)
  · filter_upwards [ht, hqv] with t htt hqt
    change range (scalarH1PiToContinuous g (Q (v t))) ⊆ range e
    rw [hqt]
    rintro y ⟨x, rfl⟩
    exact ⟨(⟨t, htt⟩, x), rfl⟩
  · filter_upwards [ht, hqv] with t htt hqt
    change (∑ i, ‖Q (v t) i‖) ≤ _
    rw [hqt]
    calc
      _ ≤ ∑ _i : Option (ι ⊕ ι), ‖q t‖ :=
        Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = (Fintype.card (Option (ι ⊕ ι)) : ℝ) * ‖q t‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC t htt) (by positivity)
  · filter_upwards [hEval, hqv] with t het hqt
    change ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (Q (v t)) x)
    rw [hqt]
    exact het

theorem exists_timeL2_scalarH2_composition_firstJet_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (R : ℝ) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
    let V := fun t z => P (scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
      (t, firstJetHs g 2 z))
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 2))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T ≤ 1 →
      ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T,
      ∀ a : ℝ → TensorHs g 0 0 1, AEStronglyMeasurable a (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (V t (f₀ + u t)))) ⊆ K) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (f₀ + u t)) i‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
        F (scalarH1PiToContinuous g (Q (V t (f₀ + u t))) x)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  classical
  intro P V Q
  obtain ⟨C₀, hC₀, hc⟩ := exists_lp_scalarH2_composition_bound_of_h1_bound
    (Ω := ℝ) g F hF hS hK hKS R
  let X := PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))
  let H : ℝ × X →L[ℝ] PiLp 2 (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 2) :=
    P.comp ((scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)).comp
      ((ContinuousLinearMap.fst ℝ ℝ X).prod
        ((firstJetHs g 2).comp (ContinuousLinearMap.snd ℝ ℝ X))))
  let c := (Fintype.card (Option (ι ⊕ ι)) : ℝ)
  let B := ‖H‖ * (2 + ‖f₀‖)
  have hc₀ : 0 ≤ c := Nat.cast_nonneg _
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (by positivity)
  let C := C₀ * (1 + c * B)
  have hC : 0 ≤ C := mul_nonneg hC₀ (by positivity)
  refine ⟨C, hC, ?_⟩
  intro T hT u a ha hRange hBound hEval
  have hraw := memLp_scalarHsTimeCoordinate_firstJetHs g 2 T f₀ u
  have hmem := P.comp_memLp' hraw
  obtain ⟨a₂, ha₂, hnorm⟩ := hc (timeMeasure T) hmem a ha hRange hBound hEval
  refine ⟨a₂, ha₂, ?_⟩
  have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
    ae_restrict_mem measurableSet_Icc
  have hpoint : ∀ᵐ t ∂timeMeasure T, ‖a₂ t‖ ≤ C * (1 + ‖u t‖) := by
    filter_upwards [hnorm, ht] with t hnt htt
    have hp : ‖(t, f₀ + u t)‖ ≤ 1 + ‖f₀‖ + ‖u t‖ := by
      rw [Prod.norm_def]
      apply max_le
      · rw [Real.norm_eq_abs, abs_of_nonneg htt.1]
        exact (htt.2.trans hT).trans (by linarith [norm_nonneg f₀, norm_nonneg (u t)])
      · exact (norm_add_le _ _).trans (by linarith)
    have hV : ‖V t (f₀ + u t)‖ ≤ B * (1 + ‖u t‖) := by
      change ‖H (t, f₀ + u t)‖ ≤ _
      calc
        _ ≤ ‖H‖ * ‖(t, f₀ + u t)‖ := H.le_opNorm _
        _ ≤ ‖H‖ * (1 + ‖f₀‖ + ‖u t‖) :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ ≤ B * (1 + ‖u t‖) := by
          dsimp only [B]
          nlinarith [norm_nonneg H, norm_nonneg f₀, norm_nonneg (u t),
            mul_nonneg (norm_nonneg H) (mul_nonneg (norm_nonneg f₀) (norm_nonneg (u t)))]
    have hsum : (∑ i, ‖V t (f₀ + u t) i‖) ≤ c * ‖V t (f₀ + u t)‖ := by
      calc
        _ ≤ ∑ _i : Option (ι ⊕ ι), ‖V t (f₀ + u t)‖ :=
          Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
        _ = _ := by simp [c]
    calc
      ‖a₂ t‖ ≤ C₀ * (1 + ∑ i, ‖V t (f₀ + u t) i‖) := hnt
      _ ≤ C₀ * (1 + c * (B * (1 + ‖u t‖))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (hsum.trans (mul_le_mul_of_nonneg_left hV hc₀))) hC₀
      _ ≤ C * (1 + ‖u t‖) := by
        dsimp only [C]
        nlinarith [mul_nonneg hC₀ (norm_nonneg (u t))]
  calc
    ‖a₂‖ ≤ C * ‖u‖ + Real.sqrt T * C := by
      apply timeL2_norm_le_of_ae_affine_bound a₂ u hC hC
      filter_upwards [hpoint] with t htt
      nlinarith [htt]
    _ = C * (Real.sqrt T + ‖u‖) := by ring

theorem scalarHsTimeCoordinate_firstJetHs_inclusion_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (T : ℝ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 1)))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) => J)
      (scalarHsTimeCoordinate g (m : ℝ) (t, firstJetHs g m (f₀ + u t)))) =ᵐ[timeMeasure T]
      (fun t => scalarHsTimeCoordinate g (n : ℝ) (t, firstJetHs g n (K f₀ + w t))) := by
  intro J K hw
  filter_upwards [hw] with t ht
  rw [tensorHsInclusion_scalarHsTimeCoordinate_eq]
  congr 1
  apply Prod.ext
  · rfl
  · have hh := congrArg (fun A => A (f₀ + u t))
      (firstJetHs_comp_tensorHsInclusion (ι := ι) g h)
    change firstJetHs g n (K (f₀ + u t)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι => J)
        (firstJetHs g m (f₀ + u t)) at hh
    rw [map_add, ← ht] at hh
    exact hh.symm

theorem exists_timeL2_scalarHs_composition_firstJet
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 ((k : ℝ) + 1))
    (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let q := fun t => scalarH1TimeCoordinate g
      (t, L (firstJetHs g (k + 1) (K f₀ + w t)))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (J (a t)) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ aHigh : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T,
      (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
        (aHigh t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K J L q hwu hRange hEval
  let V := fun t => scalarHsTimeCoordinate g ((k + 2 : ℕ) : ℝ)
    (t, firstJetHs g (k + 2) (f₀ + u t))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
  let v := fun t => P (V t)
  have hV := memLp_scalarHsTimeCoordinate_firstJetHs g (k + 2) T f₀ u
  have hv := P.comp_memLp' hV
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
  let B := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ)))
  let qLow := fun t => B (scalarHsTimeCoordinate g ((k + 1 : ℕ) : ℝ)
    (t, firstJetHs g (k + 1) (K f₀ + w t)))
  have hlow := scalarHsTimeCoordinate_firstJetHs_inclusion_ae_eq g
    (by omega : k + 1 ≤ k + 2) T f₀ u w hwu
  have hqLow : (fun t => ContinuousLinearMap.piLpMap 2
      (fun _ : Option (ι ⊕ ι) => A) (v t)) =ᵐ[timeMeasure T] qLow := by
    filter_upwards [hlow] with t ht
    refine Eq.trans ?_ (congrArg B ht)
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hqLowContinuous : ContinuousOn qLow (Icc 0 T) :=
    B.continuous.comp_continuousOn ((scalarHsTimeCoordinate g _).continuous.comp_continuousOn
      (continuousOn_id.prodMk
        ((firstJetHs g (k + 1)).continuous.comp_continuousOn (continuousOn_const.add hw))))
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2))
  have hproject (t : ℝ) : ContinuousLinearMap.piLpMap 2
      (fun _ : Option (ι ⊕ ι) => J) (qLow t) = q t := by
    have hh := tensorHsInclusion_scalarHsTimeCoordinate g
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      (t, firstJetHs g (k + 1) (K f₀ + w t))
    refine Eq.trans ?_ hh
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hqv : (fun t => Q (v t)) =ᵐ[timeMeasure T] q := by
    filter_upwards [hqLow] with t ht
    rw [← hproject t, ← ht]
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hq : ContinuousOn q (Icc 0 T) := by
    exact (scalarH1TimeCoordinate g).continuous.comp_continuousOn
      (continuousOn_id.prodMk (L.continuous.comp_continuousOn
        ((firstJetHs g (k + 1)).continuous.comp_continuousOn (continuousOn_const.add hw))))
  let e : Icc (0 : ℝ) T × AddCircle (1 : ℝ) → (Option (ι ⊕ ι) → ℝ) :=
    fun p => scalarH1PiToContinuous g (q p.1) p.2
  have he : Continuous e := by
    have hqr : Continuous (fun t : Icc (0 : ℝ) T => q t) :=
      continuousOn_iff_continuous_domRestrict.mp hq
    exact continuous_eval.comp
      (((scalarH1PiToContinuous g).continuous.comp (hqr.comp continuous_fst)).prodMk continuous_snd)
  have hcompact : IsCompact (range e) := isCompact_range he
  have hsub : range e ⊆ S := by
    rintro y ⟨⟨t, x⟩, rfl⟩
    exact hRange t t.2 (mem_range_self x)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hqLowContinuous
  have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  apply exists_lp_scalarHs_composition_of_lower_order_bound (timeMeasure T) g k F hF hS
    hcompact hsub hv ha (R := (Fintype.card (Option (ι ⊕ ι)) : ℝ) * C)
  · filter_upwards [ht, hqv] with t htt hqt
    change range (scalarH1PiToContinuous g (Q (v t))) ⊆ range e
    rw [hqt]
    rintro y ⟨x, rfl⟩
    exact ⟨(⟨t, htt⟩, x), rfl⟩
  · filter_upwards [ht, hqLow] with t htt hqt
    change (∑ i, ‖ContinuousLinearMap.piLpMap 2
      (fun _ : Option (ι ⊕ ι) => A) (v t) i‖) ≤ _
    rw [hqt]
    calc
      _ ≤ ∑ _i : Option (ι ⊕ ι), ‖qLow t‖ :=
        Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = (Fintype.card (Option (ι ⊕ ι)) : ℝ) * ‖qLow t‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC t htt) (by positivity)
  · filter_upwards [hEval, hqv] with t het hqt
    change ∀ x, scalarH1ToContinuous g (J (a t)) x =
      F (scalarH1PiToContinuous g (Q (v t)) x)
    rw [hqt]
    exact het

theorem exists_timeL2_scalarH2_composition_firstJet_norm_le_of_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (R B : ℝ) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
    let V := fun t z => P (scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
      (t, firstJetHs g 2 z))
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 2))
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)), ‖f‖ ≤ B →
      ∀ T : ℝ, T ≤ 1 →
      ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T,
      ∀ a : ℝ → TensorHs g 0 0 1, AEStronglyMeasurable a (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (V t (f + u t)))) ⊆ K) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (f + u t)) i‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
        F (scalarH1PiToContinuous g (Q (V t (f + u t))) x)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  intro P V Q
  let X := PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))
  obtain ⟨C₀, hC₀, hc⟩ := exists_timeL2_scalarH2_composition_firstJet_norm_le
    g (0 : X) F hF hS hK hKS R
  refine ⟨C₀ * (1 + max B 0), mul_nonneg hC₀ (by positivity), ?_⟩
  intro f hf T hT u a ha hRange hBound hEval
  let v : timeL2 X T := DifferentialGeometry.Analysis.Parabolic.TimeSobolev.const T f + u
  have hv : v =ᵐ[timeMeasure T] (fun t => f + u t) := by
    filter_upwards [Lp.coeFn_add (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.const T f) u,
      DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeFn_const (T := T) f] with t hsum hconst
    simpa only [v, Pi.add_apply, hconst] using hsum
  have hRv : ∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (V t (0 + v t)))) ⊆ K := by
    filter_upwards [hRange, hv] with t ht heq
    simpa only [zero_add, heq] using ht
  have hBv : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (0 + v t)) i‖) ≤ R := by
    filter_upwards [hBound, hv] with t ht heq
    simpa only [zero_add, heq] using ht
  have hEv : ∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (Q (V t (0 + v t))) x) := by
    filter_upwards [hEval, hv] with t ht heq
    simpa only [zero_add, heq] using ht
  obtain ⟨a₂, ha₂, hnorm⟩ := hc T hT v a ha hRv hBv hEv
  refine ⟨a₂, ha₂, hnorm.trans ?_⟩
  have hvnorm : ‖v‖ ≤ Real.sqrt T * max B 0 + ‖u‖ := by
    calc
      ‖v‖ ≤ ‖DifferentialGeometry.Analysis.Parabolic.TimeSobolev.const T f‖ + ‖u‖ := norm_add_le _ _
      _ = Real.sqrt T * ‖f‖ + ‖u‖ := by rw [DifferentialGeometry.Analysis.Parabolic.TimeSobolev.norm_const]
      _ ≤ _ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hf.trans (le_max_left B 0)) (Real.sqrt_nonneg T)) le_rfl
  calc
    C₀ * (Real.sqrt T + ‖v‖) ≤ C₀ * (Real.sqrt T + (Real.sqrt T * max B 0 + ‖u‖)) := by gcongr
    _ ≤ (C₀ * (1 + max B 0)) * (Real.sqrt T + ‖u‖) := by
      nlinarith [mul_nonneg (mul_nonneg hC₀ (le_max_right B 0)) (norm_nonneg u)]

variable {ν : Type*} [Fintype ν]

theorem exists_timeL2_vectorH2_composition_firstJet_norm_le_of_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (ι ⊕ ι) → ℝ) → ν → ℝ) {S K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (R B : ℝ) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
    let V := fun t z => P (scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
      (t, firstJetHs g 2 z))
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 2))
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)), ‖f‖ ≤ B →
      ∀ T : ℝ, T ≤ 1 →
      ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T,
      ∀ a : ℝ → PiLp 2 (fun _ : ν => TensorHs g 0 0 1), AEStronglyMeasurable a (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (V t (f + u t)))) ⊆ K) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (f + u t)) i‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x j, scalarH1ToContinuous g (a t j) x =
        F (scalarH1PiToContinuous g (Q (V t (f + u t))) x) j) →
      ∃ a₂ : timeL2 (PiLp 2 (fun _ : ν => TensorHs g 0 0 2)) T,
        (fun t => (ContinuousLinearMap.piLpMap 2 fun _ : ν => tensorHsInclusion
          (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)) (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  classical
  intro P V Q
  choose C hC hc using fun j : ν =>
    exists_timeL2_scalarH2_composition_firstJet_norm_le_of_norm_le
      g (fun z => F z j) (contDiffOn_pi.mp hF j) hS hK hKS R B
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro f hf T hT u a ha hRange hBound hEval
  have hcoord (j : ν) := hc j f hf T hT u (fun t => a t j)
    ((PiLp.continuous_apply 2 (fun _ : ν => TensorHs g 0 0 1) j).comp_aestronglyMeasurable ha)
    hRange hBound (by filter_upwards [hEval] with t ht using fun x => ht x j)
  choose v hv hvnorm using hcoord
  let e₂ := Lp.piLpEquiv (𝕜 := ℝ) (X := fun _ : ν => TensorHs g 0 0 2) (timeMeasure T)
  let vpi : PiLp 2 (fun _ : ν => timeL2 (TensorHs g 0 0 2) T) := WithLp.toLp 2 v
  let a₂ := e₂.symm vpi
  have ha₂ : ∀ᵐ t ∂timeMeasure T, ∀ j, a₂ t j = v j t := by
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) vpi] with t ht
    intro j
    exact congrArg (fun z : PiLp 2 (fun _ : ν => TensorHs g 0 0 2) => z j) ht
  have ha₂norm : ‖a₂‖ ≤ ∑ j, ‖v j‖ := by
    change ‖e₂.symm vpi‖ ≤ _
    rw [e₂.symm.norm_map]
    have hs : vpi = ∑ j, PiLp.single 2 j (v j) := by
      apply PiLp.ext
      intro j
      simp [vpi]
    rw [hs]
    simpa only [PiLp.norm_single] using norm_sum_le Finset.univ
      (fun j : ν => (PiLp.single 2 j (v j) :
        PiLp 2 (fun _ : ν => timeL2 (TensorHs g 0 0 2) T)))
  refine ⟨a₂, ?_, ha₂norm.trans ?_⟩
  · filter_upwards [ha₂, Filter.eventually_all.mpr hv] with t ht hvt
    apply PiLp.ext
    intro j
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t j) = a t j
    rw [ht j]
    exact hvt j
  · calc
      ∑ j, ‖v j‖ ≤ ∑ j, C j * (Real.sqrt T + ‖u‖) :=
        Finset.sum_le_sum (fun j _ => hvnorm j)
      _ = (∑ j, C j) * (Real.sqrt T + ‖u‖) := (Finset.sum_mul _ _ _).symm

theorem exists_timeL2_scalarHs_composition_norm_le_of_lower_order_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) T,
      ∀ a : ℝ → TensorHs g 0 0 ((k : ℝ) + 1),
      AEStronglyMeasurable a (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖L (u t i)‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (K₁ (a t)) x =
        F (scalarH1PiToContinuous g (P (u t)) x)) →
      ∃ v : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T,
        (fun t => L (v t)) =ᵐ[timeMeasure T] a ∧
        ‖v‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  intro J P L K₁
  obtain ⟨C₀, hC₀, hc⟩ := exists_lp_scalarHs_composition_bound_of_lower_order_bound
    (Ω := ℝ) g k F hF hU hK hKU R
  let c := (Fintype.card ι : ℝ)
  have hc₀ : 0 ≤ c := Nat.cast_nonneg _
  refine ⟨C₀ * (1 + c), mul_nonneg hC₀ (by positivity), ?_⟩
  intro u a ha hRange hBound hEval
  obtain ⟨v, hv, hnorm⟩ := hc (timeMeasure T) (Lp.memLp u) a ha hRange hBound hEval
  refine ⟨v, hv, ?_⟩
  have hpoint : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ (C₀ * c) * ‖u t‖ + C₀ := by
    filter_upwards [hnorm] with t ht
    have hsum : (∑ i, ‖u t i‖) ≤ c * ‖u t‖ := by
      calc
        _ ≤ ∑ _i : ι, ‖u t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
        _ = _ := by simp [c]
    calc
      ‖v t‖ ≤ C₀ * (1 + ∑ i, ‖u t i‖) := ht
      _ ≤ C₀ * (1 + c * ‖u t‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC₀
      _ = (C₀ * c) * ‖u t‖ + C₀ := by ring
  calc
    ‖v‖ ≤ (C₀ * c) * ‖u‖ + Real.sqrt T * C₀ :=
      timeL2_norm_le_of_ae_affine_bound v u (mul_nonneg hC₀ hc₀) hC₀ hpoint
    _ ≤ (C₀ * (1 + c)) * (Real.sqrt T + ‖u‖) := by
      nlinarith [mul_nonneg hC₀ (norm_nonneg u),
        mul_nonneg (mul_nonneg hC₀ hc₀) (Real.sqrt_nonneg T)]

def scalarHsTimeFirstJet
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 (n : ℝ)) :=
  (scalarHsTimeCoordinate g (n : ℝ)).comp
    ((ContinuousLinearMap.fst ℝ ℝ _).prod
      ((firstJetHs g n).comp (ContinuousLinearMap.snd ℝ ℝ _)))

omit [Fintype ι] in
@[simp] theorem scalarHsTimeFirstJet_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) :
    scalarHsTimeFirstJet g n p = scalarHsTimeCoordinate g (n : ℝ) (p.1, firstJetHs g n p.2) := rfl

theorem exists_timeL2_scalarHs_composition_firstJet_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (T : ℝ) (hT : T ≤ 1)
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S K : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (R : ℝ) :
    let P : PiLp 2 (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) →L[ℝ]
        PiLp 2 (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 ((k : ℝ) + 2)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (k : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ)))
    let H : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1)) →L[ℝ]
        PiLp 2 (fun _ : Option (ι ⊕ ι) => TensorHs g 0 0 ((k : ℝ) + 2)) :=
      P.comp (scalarHsTimeFirstJet (ι := ι) g (k + 2))
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ a : ℝ → TensorHs g 0 0 ((k : ℝ) + 1), AEStronglyMeasurable a (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (H (t, f₀ + u t)))) ⊆ K) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (H (t, f₀ + u t) i)‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (J (a t)) x =
        F (scalarH1PiToContinuous g (Q (H (t, f₀ + u t))) x)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 ((k : ℝ) + 2)) T,
        (fun t => A (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  intro P H Q A J
  obtain ⟨C₀, hC₀, hc⟩ := exists_timeL2_scalarHs_composition_norm_le_of_lower_order_bound
    (ι := Option (ι ⊕ ι)) g k T F hF hS hK hKS R
  let B := ‖H‖ * (2 + ‖f₀‖)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg H) (by positivity)
  refine ⟨C₀ * (1 + B), mul_nonneg hC₀ (by positivity), ?_⟩
  intro u a ha hRange hBound hEval
  obtain ⟨v, hv, hvnorm⟩ := exists_timeL2_affine_comp_norm_le H f₀ T hT u
  have hvRange : ∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (Q (v t))) ⊆ K := by
    filter_upwards [hv, hRange] with t hvt ht
    rw [hvt]
    exact ht
  have hvBound : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖A (v t i)‖) ≤ R := by
    filter_upwards [hv, hBound] with t hvt ht
    rw [hvt]
    exact ht
  have hvEval : ∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (J (a t)) x =
      F (scalarH1PiToContinuous g (Q (v t)) x) := by
    filter_upwards [hv, hEval] with t hvt ht
    rw [hvt]
    exact ht
  obtain ⟨a₂, ha₂, ha₂norm⟩ := hc v a ha hvRange hvBound hvEval
  refine ⟨a₂, ha₂, ?_⟩
  calc
    ‖a₂‖ ≤ C₀ * (Real.sqrt T + ‖v‖) := ha₂norm
    _ ≤ C₀ * (Real.sqrt T + B * (Real.sqrt T + ‖u‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hvnorm) hC₀
    _ ≤ C₀ * (1 + B) * (Real.sqrt T + ‖u‖) := by
      nlinarith [mul_nonneg hC₀ (norm_nonneg u)]

end AddCircle
