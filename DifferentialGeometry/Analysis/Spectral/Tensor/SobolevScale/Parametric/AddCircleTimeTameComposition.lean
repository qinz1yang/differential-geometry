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

end AddCircle
