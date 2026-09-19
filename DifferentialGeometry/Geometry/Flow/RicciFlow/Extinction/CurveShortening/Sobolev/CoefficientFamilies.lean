import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Regularity

open private
  CircleHsPi
  circleHsPiInclusion
  extendClosedBall
  circleHsPiCongr
  circleHsPiCongr_apply
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  circleFirstJet
  ScalarVectorTimeCoefficients
  ScalarVectorTimeCoefficients.radius
  ScalarVectorTimeCoefficients.radius_pos
  ScalarVectorTimeCoefficients.diffusion
  ScalarVectorTimeCoefficients.reaction
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients.radius
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients.radius_pos
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients.diffusion
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients.reaction from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  circle_firstJetHs_normalized
  DifferentialGeometry.Analysis.Parabolic.circle_firstJetHs_normalized from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
open private
  referenceCircleCoefficientFacts
  reference_jet_add_correction_eq
  reference_coefficients_eq_at_translated_state
  fixedAmbientSobolev
  continuous_fixedAmbientSobolev
  DifferentialGeometry.Analysis.Parabolic.referenceCircleCoefficientFacts
  DifferentialGeometry.Analysis.Parabolic.reference_jet_add_correction_eq
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_coefficients_eq_at_translated_state
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.continuous_fixedAmbientSobolev
  DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  circle_firstJetHs_eq_of_projection
  scalarVectorTimeCoefficients_successor_order
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.circle_firstJetHs_eq_of_projection
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.scalarVectorTimeCoefficients_successor_order from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Regularity
open private
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions

noncomputable section

open Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_firstJet_tendstoUniformlyOn
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (f : X → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto f l (𝓝 f₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let q := fun x t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P (f x) + J (w x t)))
    let q₀ := fun t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P f₀ + J (w₀ t)))
    ContinuousOn q₀ (Icc 0 T) ∧ TendstoUniformlyOn q q₀ l (Icc 0 T) := by
  intro q q₀
  let A := (scalarH1PiToContinuous (ι := Option (Fin n ⊕ Fin n)) g₀).comp
    (scalarH1TimeCoordinate (ι := Fin n ⊕ Fin n) g₀)
  let B := A.comp (ContinuousLinearMap.inr ℝ ℝ _)
  have hstate : TendstoUniformlyOn
      (fun x t => P (f x) + J (w x t))
      (fun t => P f₀ + J (w₀ t)) l (Icc 0 T) :=
    (((P.continuous.tendsto f₀).comp hf).tendstoUniformlyOn_const (Icc 0 T)).add
      (J.uniformContinuous.comp_tendstoUniformlyOn hw)
  have htime : TendstoUniformlyOn (fun (_ : X) t => A (t, 0))
      (fun t => A (t, 0)) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε
  have heq (t : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) :
      A (t, 0) + B v = A (t, v) := by
    change A (t, 0) + A (0, v) = A (t, v)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  refine ⟨?_, ?_⟩
  · exact A.continuous.comp_continuousOn
      (continuousOn_id.prodMk
        (continuousOn_const.add (J.continuous.comp_continuousOn hw₀)))
  · have h := htime.add (B.uniformContinuous.comp_tendstoUniformlyOn hstate)
    change TendstoUniformlyOn
      (fun x t => A (t, 0) + B (P (f x) + J (w x t)))
      (fun t => A (t, 0) + B (P f₀ + J (w₀ t))) l (Icc 0 T) at h
    simp only [heq] at h
    change TendstoUniformlyOn (fun x t => A (t, P (f x) + J (w x t)))
      (fun t => A (t, P f₀ + J (w₀ t))) l (Icc 0 T)
    exact h

private theorem reference_firstJet_exists_compact_range
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (fcenter : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)} (hS : IsOpen S)
    {δ ρ : ℝ} (hTρ : T ≤ ρ)
    (alpha : Metric.closedBall fcenter δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fcenter δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleCoefficientFacts g₀ fcenter P J F G S δ ρ alpha reaction)
    (f : X → Metric.closedBall fcenter δ) (f₀ : Metric.closedBall fcenter δ)
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto (fun x => (f x).val) l (𝓝 f₀.val))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, ‖w₀ t‖ ≤ ρ) :
    let q := fun x t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P (f x).val + J (w x t)))
    let q₀ := fun t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P f₀.val + J (w₀ t)))
    ∃ K : Set (Option (Fin n ⊕ Fin n) → ℝ), IsCompact K ∧ K ⊆ S ∧
      (∀ t ∈ Icc 0 T, range (q₀ t) ⊆ K) ∧
      ∀ᶠ x in l, ∀ t ∈ Icc 0 T, range (q x t) ⊆ K := by
  intro q q₀
  obtain ⟨hq₀, hq⟩ := reference_firstJet_tendstoUniformlyOn g₀ T P J
    (fun x => (f x).val) f₀.val w w₀ hf hw₀ hw
  have hmap : ∀ t ∈ Icc 0 T, ∀ z, q₀ t z ∈ S := by
    intro t ht z
    exact hcoeff.1 f₀ t ⟨ht.1, ht.2.trans hTρ⟩ (w₀ t) (hbound t ht)
      (mem_range_self z)
  obtain ⟨K, hK, hKS, hlim, hevent⟩ :=
    hq.exists_isCompact_eventually_forall_eval_mem isCompact_Icc hq₀ hS hmap
  refine ⟨K, hK, hKS, ?_, ?_⟩
  · intro t ht z hz
    obtain ⟨a, rfl⟩ := hz
    exact interior_subset (hlim t ht a)
  · filter_upwards [hevent] with x hx
    intro t ht z hz
    obtain ⟨a, rfl⟩ := hz
    exact hx t ht a

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_timeFirstJet_projection_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let KHigh := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
          ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    let J₀ := circleFirstJet (ι := Fin n) g₀
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := J₀.comp K₀
    let C := circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
    let J := J₀.comp C.toLinearIsometry.toContinuousLinearMap
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    R fHigh = f →
    w =ᵐ[timeMeasure T] (fun t => KHigh (V t)) →
    (fun t => QH (Hjet (t, fHigh + V t))) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g₀ (t, P f + J (w t))) := by
  intro R KHigh J₀ K₀ P C J PH Hjet AH QH hf hw
  have hraw := AddCircle.scalarHsTimeCoordinate_firstJetHs_ae_eq
    (ι := Fin n) g₀ (show 1 ≤ k + 1 + 2 by omega) T fHigh V w hw
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hbase : C (KHigh fHigh) = K₀ f := by
    rw [← hf]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rw [circleHsPiCongr_apply, hcongr]
    rfl
  filter_upwards [hraw] with t ht
  have hnormalize : QH (Hjet (t, fHigh + V t)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by exact_mod_cast (show 1 ≤ k + 1 + 2 by omega) :
            (1 : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ)))
        (AddCircle.scalarHsTimeCoordinate g₀ ((k + 1 + 2 : ℕ) : ℝ)
          (t, AddCircle.firstJetHs g₀ (k + 1 + 2) (fHigh + V t))) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  rw [hnormalize, ht]
  have hnormalized := circle_firstJetHs_normalized g₀ (KHigh fHigh + w t)
  rw [← hnormalized]
  change scalarH1TimeCoordinate g₀ (t, J₀ (C (KHigh fHigh + w t))) = _
  rw [map_add, hbase, map_add]
  rfl

private theorem reference_high_coefficients_eval_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    {δ ρ : ℝ} (f : Metric.closedBall f₀ δ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let KHigh := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
          ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    let J₀ := circleFirstJet (ι := Fin n) g₀
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction →
    R fHigh = f.val →
    w =ᵐ[timeMeasure T] (fun t => KHigh (V t)) →
    (∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 ρ ∧ ‖w t‖ ≤ ρ) →
    (fun t => AH (a t)) =ᵐ[timeMeasure T] (fun t => alpha f t (w t)) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b t))
      =ᵐ[timeMeasure T] (fun t => reaction f t (w t)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z,
      scalarH1ToContinuous g₀ (AH (a t)) z =
        F (scalarH1PiToContinuous g₀ (QH (Hjet (t, fHigh + V t))) z)) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ z j,
      scalarH1ToContinuous g₀ (AH (b t j)) z =
        G (scalarH1PiToContinuous g₀ (QH (Hjet (t, fHigh + V t))) z) j) := by
  intro R KHigh J₀ K₀ P J PH Hjet AH QH hcoeff hf hw hbound ha hb
  have hjet := reference_timeFirstJet_projection_ae g₀ k T fHigh f.val V w hf hw
  have hcoord (t : ℝ) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, P f.val + J (w t))) z =
        (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (w t)) i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => exact scalarH1TimeCoordinate_eval_some g₀ _ _ i
  constructor
  · filter_upwards [ha, hjet, hbound] with t hat hjt hbt
    intro z
    rw [hat, hjt, hcoord]
    exact hcoeff.2.1 f t hbt.1 (w t) hbt.2 z
  · filter_upwards [hb, hjet, hbound] with t hbt hjt hboundt
    intro z j
    have hbj := congrArg (fun v => v j) hbt
    change AH (b t j) = reaction f t (w t) j at hbj
    rw [hbj, hjt, hcoord]
    exact hcoeff.2.2 f t hboundt.1 (w t) hboundt.2 z j

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_timeFirstJet_exists_compact_range
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (fcenter : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)} (hS : IsOpen S)
    {δ ρ : ℝ} (hTρ : T ≤ ρ)
    (alpha : Metric.closedBall fcenter δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fcenter δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (f : X → Metric.closedBall fcenter δ) (f₀ : Metric.closedBall fcenter δ)
    (fHigh : X → CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (fHigh₀ : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : X → timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (V₀ : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto (fun x => (f x).val) l (𝓝 f₀.val))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let KHigh := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
          ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    let J₀ := circleFirstJet (ι := Fin n) g₀
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    referenceCircleCoefficientFacts g₀ fcenter P J F G S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    R fHigh₀ = f₀.val →
    (∀ x, w x =ᵐ[timeMeasure T] fun t => KHigh (V x t)) →
    w₀ =ᵐ[timeMeasure T] (fun t => KHigh (V₀ t)) →
    (∀ t ∈ Icc 0 T, ‖w₀ t‖ ≤ ρ) →
    ∃ K : Set (Option (Fin n ⊕ Fin n) → ℝ), IsCompact K ∧ K ⊆ S ∧
      (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
        range (scalarH1PiToContinuous g₀ (QH (Hjet (t, fHigh x + V x t)))) ⊆ K) ∧
      ∀ᵐ t ∂timeMeasure T,
        range (scalarH1PiToContinuous g₀ (QH (Hjet (t, fHigh₀ + V₀ t)))) ⊆ K := by
  intro R KHigh J₀ K₀ P J PH Hjet AH QH hcoeff hfHigh hfHigh₀ hwV hwV₀ hbound
  obtain ⟨K, hK, hKS, hlim, hevent⟩ :=
    reference_firstJet_exists_compact_range g₀ T fcenter P J F G hS hTρ
      alpha reaction hcoeff f f₀ w w₀ hf hw₀ hw hbound
  refine ⟨K, hK, hKS, ?_, ?_⟩
  · filter_upwards [hevent] with x hx
    have hjet := reference_timeFirstJet_projection_ae g₀ k T
      (fHigh x) (f x).val (V x) (w x) (hfHigh x) (hwV x)
    filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t hjt htt
    rw [hjt]
    exact hx t htt
  · have hjet := reference_timeFirstJet_projection_ae g₀ k T
      fHigh₀ f₀.val V₀ w₀ hfHigh₀ hwV₀
    filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t hjt htt
    rw [hjt]
    exact hlim t htt

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_translated_high_state
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (fcenter f : CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (hW : ContinuousOn W (Icc 0 T)) :
    let B := circleHsPiInclusion g₀ (Fin n)
      (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let C : CircleHsPi g₀ (Fin n) ((k : ℝ) + 4) →L[ℝ]
        timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T :=
      Lp.constL 2 (timeMeasure T) ℝ
    let Z := C (f - fcenter) + V
    let Y := fun t => B (f - fcenter) + W t
    W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    ContinuousOn Y (Icc 0 T) ∧
      Y =ᵐ[timeMeasure T] (fun t => B (Z t)) ∧
      (∀ᵐ t ∂timeMeasure T, fcenter + Z t = f + V t) ∧
      ∀ t, B fcenter + Y t = B f + W t := by
  intro B C Z Y hWV
  have hconst : C (f - fcenter) =ᵐ[timeMeasure T] fun _ => f - fcenter :=
    Lp.coeFn_const _ _ _
  have hZ : Z =ᵐ[timeMeasure T] fun t => f - fcenter + V t := by
    filter_upwards [Lp.coeFn_add (C (f - fcenter)) V, hconst] with t ht hc
    change Z t = _ at ht
    simpa only [Pi.add_apply, hc] using ht
  refine ⟨continuousOn_const.add hW, ?_, ?_, ?_⟩
  · filter_upwards [hZ, hWV] with t hz hw
    change B (f - fcenter) + W t = B (Z t)
    rw [hz, map_add, hw]
  · filter_upwards [hZ] with t ht
    rw [ht]
    abel
  · intro t
    change B fcenter + (B (f - fcenter) + W t) = B f + W t
    rw [map_sub]
    abel

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_successor_coefficient_projection_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (K : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hbase : u₀ = P f₀) (hJK : ∀ v, J (K v) = P v)
    {δ ρ : ℝ} (f : Metric.closedBall f₀ δ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
    (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T) :
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let P₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 3)
    (fun t => P₂ (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂)
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)))
        =ᵐ[timeMeasure T] b₂ →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f.val - f₀) + w t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (K (f.val - f₀) + w t))) →
    T ≤ ρ → T ≤ ScalarVectorTimeCoefficients.radius C →
    (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T,
      ‖J (K (f.val - f₀) + w t)‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    (fun t => AH (aHigh t)) =ᵐ[timeMeasure T] (fun t => alpha f t (w t)) ∧
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t))
      =ᵐ[timeMeasure T] (fun t => reaction f t (w t)) := by
  intro Q P₂ A₂ AH haHigh hbHigh ha₂ hb₂ hTρ hTC hw hJ
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
    ae_restrict_mem measurableSet_Icc
  have heq (t : ℝ) (htt : t ∈ Icc 0 T) :=
    reference_coefficients_eq_at_translated_state g₀ f₀ P J K F G S u₀ C hbase hJK
      alpha reaction hcoeff f (w t) t ⟨htt.1, htt.2.trans hTρ⟩
      ⟨htt.1, htt.2.trans hTC⟩ (hw t htt) (hJ t htt)
  constructor
  · filter_upwards [haHigh, htime] with t ht htt
    calc
      AH (aHigh t) = A₂ (P₂ (Q (aHigh t))) := by
        apply TensorHs.ext
        rfl
      _ = A₂ (a₂ t) := congrArg A₂ ht
      _ = _ := (ha₂ t htt).trans (heq t htt).1.symm
  · filter_upwards [hbHigh, htime] with t ht htt
    have hinclusion : ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t) =
        ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂)
            (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    rw [hinclusion, ht]
    exact (hb₂ t htt).trans (heq t htt).2.symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open Filter Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_firstJet_tendstoUniformlyOn_of_tendsto_immersion
    {X : Type*} {N : ℕ} {l : Filter X}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (P : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin N ⊕ Fin N) 1)
    (J : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin N ⊕ Fin N) 1)
    (d : X → SmoothImmersion (I := I) (M := M))
    (d₀ : SmoothImmersion (I := I) (M := M))
    (hd : Tendsto d l (@nhds _ (smoothImmersionTopology e) d₀))
    {σ : ℝ} (hσ : ((1 : ℕ) : ℝ) + 1 ≤ σ)
    (W : X → ℝ → CircleHsPi g₀ (Fin N) σ)
    (W₀ : ℝ → CircleHsPi g₀ (Fin N) σ)
    (hW₀ : ContinuousOn W₀ (Icc 0 T))
    (hW : TendstoUniformlyOn W W₀ l (Icc 0 T)) :
    let K := circleHsPiInclusion g₀ (Fin N) hσ
    let q := fun x t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀
        (t, P (fixedAmbientSobolev e g₀ (d x)) + J (K (W x t))))
    let q₀ := fun t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀
        (t, P (fixedAmbientSobolev e g₀ d₀) + J (K (W₀ t))))
    ContinuousOn q₀ (Icc 0 T) ∧ TendstoUniformlyOn q q₀ l (Icc 0 T) := by
  let := smoothImmersionTopology e
  intro K q q₀
  have hf : Tendsto (fun x => fixedAmbientSobolev e g₀ (d x)) l
      (𝓝 (fixedAmbientSobolev e g₀ d₀)) :=
    ((continuous_fixedAmbientSobolev e g₀).tendsto d₀).comp hd
  have hw₀ : ContinuousOn (fun t => K (W₀ t)) (Icc 0 T) :=
    K.continuous.comp_continuousOn hW₀
  have hw : TendstoUniformlyOn (fun x t => K (W x t))
      (fun t => K (W₀ t)) l (Icc 0 T) :=
    K.uniformContinuous.comp_tendstoUniformlyOn hW
  exact DifferentialGeometry.Analysis.Parabolic.reference_firstJet_tendstoUniformlyOn
    g₀ T P J (fun x => fixedAmbientSobolev e g₀ (d x))
    (fixedAmbientSobolev e g₀ d₀) (fun x t => K (W x t))
    (fun t => K (W₀ t)) hf hw₀ hw

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_successor_coefficients
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (fcenter fHigh : CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (u₀ : CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {δ ρ : ℝ} (f : Metric.closedBall f₀ δ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2) :
    let R₄ := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let R₃ := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 3)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let w := fun t => K (R₃ (W t))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 3)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let P₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    u₀ = P f₀ → R₄ fcenter = f₀ → R₄ fHigh = f.val →
    referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction →
    ContinuousOn W (Icc 0 T) → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    T ≤ ρ → T ≤ ScalarVectorTimeCoefficients.radius C →
    (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T,
      ‖J (K (f.val - f₀) + w t)‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) = alpha f t (w t)) →
    (∀ t ∈ Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) = reaction f t (w t)) →
    ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
      (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T),
      (fun t => P₂ (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂)
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)))
          =ᵐ[timeMeasure T] b₂ ∧
      (fun t => AH (aHigh t)) =ᵐ[timeMeasure T] (fun t => alpha f t (w t)) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t))
        =ᵐ[timeMeasure T] (fun t => reaction f t (w t)) := by
  intro R₄ R₃ B K₀ P K J w A₂ AH Q P₂ hbase hcenter hf hcoeff hW hWV
    hTρ hTC hw hJ ha₂ hb₂
  let Cconst : CircleHsPi g₀ (Fin n) ((k : ℝ) + 4) →L[ℝ]
      timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T := Lp.constL 2 (timeMeasure T) ℝ
  let Z := Cconst (fHigh - fcenter) + V
  let Y := fun t => B (fHigh - fcenter) + W t
  obtain ⟨hY, hYZ, _, _⟩ := reference_translated_high_state g₀ k T fcenter fHigh V W hW hWV
  let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
  let JHigh := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
  have hRB (v : CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) : R₃ (B v) = R₄ v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hJK (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) : J (K v) = P v := by
    have h := reference_jet_add_correction_eq g₀ 0 v
    change P 0 + J (K v) = P (0 + v) at h
    simpa only [map_zero, zero_add] using h
  have hJHigh (v : CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) : JHigh v = P (R₃ v) := by
    let Rnat := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
    have hnat := circle_firstJetHs_eq_of_projection g₀ k v (Rnat v) rfl
    change JHigh v = circleFirstJet g₀
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3) (Rnat v)) at hnat
    refine hnat.trans ?_
    change circleFirstJet g₀
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3) (Rnat v)) =
        circleFirstJet g₀ (K₀ (R₃ v))
    apply congrArg (circleFirstJet (ι := Fin n) g₀)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hjet (t : ℝ) : JHigh (Y t) = J (K (f.val - f₀) + w t) := by
    rw [hJHigh]
    change P (R₃ (B (fHigh - fcenter) + W t)) = _
    rw [map_add, hRB, map_sub, hf, hcenter, map_add, map_add, hJK]
    change P (f.val - f₀) + P (R₃ (W t)) = P (f.val - f₀) + J (K (R₃ (W t)))
    rw [hJK]
  have heq (t : ℝ) (htt : t ∈ Icc 0 T) :=
    reference_coefficients_eq_at_translated_state g₀ f₀ P J K F G S u₀ C hbase hJK
      alpha reaction hcoeff f (w t) t ⟨htt.1, htt.2.trans hTρ⟩
      ⟨htt.1, htt.2.trans hTC⟩ (hw t htt) (hJ t htt)
  have haC (t : ℝ) (htt : t ∈ Icc 0 T) : A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f.val - f₀) + w t)) :=
    (ha₂ t htt).trans (heq t htt).1
  have hbC (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (f.val - f₀) + w t)) :=
    (hb₂ t htt).trans (heq t htt).2
  let E₄ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith : ((k + 1 + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 4)
  let fcRaw := E₄ fcenter
  let Kraw := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
  have hKraw : Kraw fcRaw = E (B fcenter) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hcenterRaw : u₀ = L (AddCircle.firstJetHs g₀ (k + 2) (Kraw fcRaw)) := by
    rw [hKraw]
    change u₀ = JHigh (B fcenter)
    rw [hJHigh, hRB, hcenter]
    exact hbase
  obtain ⟨a, b, aHigh, bHigh, hresult⟩ :=
    scalarVectorTimeCoefficients_successor_order g₀ F G S u₀ C hF hG hS k fcRaw
      hcenterRaw T hTC Z Y hY hYZ
      (fun t htt => by rw [hjet]; exact hJ t htt) a₂ b₂
      (fun t htt => by rw [hjet]; exact haC t htt)
      (fun t htt => by rw [hjet]; exact hbC t htt)
  have haHigh := hresult.2.2.2.2.2.2.2.2.1
  have hbHigh := hresult.2.2.2.2.2.2.2.2.2
  obtain ⟨haActual, hbActual⟩ := reference_successor_coefficient_projection_ae
    g₀ k T f₀ P J K F G S u₀ C hbase hJK f alpha reaction hcoeff w a₂ b₂
      aHigh bHigh haHigh hbHigh haC hbC hTρ hTC hw hJ
  exact ⟨aHigh, bHigh, haHigh, hbHigh, haActual, hbActual⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_scalarHsTimeFirstJet_projection
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ)
    (fHigh v : CircleHsPi g₀ (Fin n) ((m : ℝ) + 1))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (w : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
          norm_num; linarith : ((1 : ℕ) : ℝ) + 2 ≤ (m : ℝ) + 1)
    let K := circleHsPiInclusion g₀ (Fin n)
      (by have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
          norm_num; linarith : ((1 : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
            linarith : (1 : ℝ) ≤ (m : ℝ)))
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let C := circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
    let J := (circleFirstJet (ι := Fin n) g₀).comp C.toLinearIsometry.toContinuousLinearMap
    R fHigh = f → K v = w →
    Q (AddCircle.scalarHsTimeFirstJet g₀ m (t, fHigh + v)) =
      scalarH1TimeCoordinate g₀ (t, P f + J w) := by
  intro R K Q K₀ P C J hf hv
  have hcongr {a b : ℝ} (h : a = b) (u : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h u).coeff = u.coeff := by
    cases h
    rfl
  have hbase : C (K fHigh) = K₀ f := by
    rw [← hf]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rw [circleHsPiCongr_apply, hcongr]
    rfl
  let Qjet := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
          linarith : (1 : ℝ) ≤ (m : ℝ)))
  have hj : Qjet (AddCircle.firstJetHs g₀ m (fHigh + v)) = P f + J w := by
    let Qone := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    have hjet := congrArg (fun A => A (fHigh + v))
      (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := Fin n) g₀
        (show 1 ≤ m by omega))
    change AddCircle.firstJetHs g₀ 1 (K (fHigh + v)) = _ at hjet
    have hnormalized := circle_firstJetHs_normalized g₀ (K (fHigh + v))
    have hraw : Qjet (AddCircle.firstJetHs g₀ m (fHigh + v)) =
        Qone (AddCircle.firstJetHs g₀ 1 (K (fHigh + v))) := by
      rw [hjet]
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    rw [hraw, ← hnormalized, map_add, hv, map_add, hbase, map_add]
    rfl
  change Q (AddCircle.scalarHsTimeCoordinate g₀ (m : ℝ)
    (t, AddCircle.firstJetHs g₀ m (fHigh + v))) = _
  rw [AddCircle.tensorHsInclusion_scalarHsTimeCoordinate]
  exact congrArg (fun u => scalarH1TimeCoordinate g₀ (t, u)) hj

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_coefficients_continuousOn
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction)
    (hσlo : -ρ ≤ σ) (hσhi : σ + T ≤ ρ) (hbound : ∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) :
    ContinuousOn (fun t => alpha f (σ + t) (W t)) (Icc 0 T) ∧
      ContinuousOn (fun t => reaction f (σ + t) (W t)) (Icc 0 T) := by
  classical
  let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 1)
  let U := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ (1 : ℝ))
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A)
  let E := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => U)
  let q := fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (W t))
  let qraw := fun t => E (q t)
  have hq : ContinuousOn q (Icc 0 T) :=
    (scalarH1TimeCoordinate g₀).continuous.comp_continuousOn
      ((continuousOn_const.add continuousOn_id).prodMk
        (continuousOn_const.add (J.continuous.comp_continuousOn hW)))
  have hqraw : ContinuousOn qraw (Icc 0 T) := E.continuous.comp_continuousOn hq
  have hproject (t : ℝ) : Q (qraw t) = q t := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : σ + t ∈ Icc (-ρ) ρ :=
    by constructor <;> linarith [ht.1, ht.2]
  have hRange : ∀ t ∈ Icc 0 T,
      range (scalarH1PiToContinuous g₀ (Q (qraw t))) ⊆ S := by
    intro t ht
    rw [hproject]
    exact hcoeff.1 f (σ + t) (htime t ht) (W t) (hbound t ht)
  obtain ⟨araw, haraw, haeval⟩ := AddCircle.exists_continuousOn_scalarHs_composition
    g₀ 0 F hF hS qraw hqraw hRange
  choose braw hbraw hbeval using fun j : Fin n =>
    AddCircle.exists_continuousOn_scalarHs_composition
      g₀ 0 (fun z => G z j) (contDiffOn_pi.mp hG j) hS qraw hqraw hRange
  have hcoords (t : ℝ) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (q t) z =
        (fun i => match i with
          | none => σ + t
          | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (W t)) i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  have hae (t : ℝ) (ht : t ∈ Icc 0 T) :
      alpha f (σ + t) (W t) = A (araw t) := by
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro z
    rw [haeval t ht z, hproject, hcoords]
    exact hcoeff.2.1 f (σ + t) (htime t ht) (W t) (hbound t ht) z
  have hbe (j : Fin n) (t : ℝ) (ht : t ∈ Icc 0 T) :
      reaction f (σ + t) (W t) j = A (braw j t) := by
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro z
    rw [hbeval j t ht z, hproject, hcoords]
    exact hcoeff.2.2 f (σ + t) (htime t ht) (W t) (hbound t ht) z j
  refine ⟨(A.continuous.comp_continuousOn haraw).congr hae, ?_⟩
  have hb : ContinuousOn (fun t => WithLp.toLp 2 (fun j => A (braw j t))) (Icc 0 T) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (continuousOn_pi.mpr (fun j => A.continuous.comp_continuousOn (hbraw j)))
  apply hb.congr
  intro t ht
  exact PiLp.ext (fun j => hbe j t ht)

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_timeFirstJet_h2
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
    let Hjet := PH.comp ((AddCircle.scalarHsTimeFirstJet g₀ 2).comp
      ((ContinuousLinearMap.fst ℝ ℝ _).prod
        (E.comp (ContinuousLinearMap.snd ℝ ℝ _))))
    let qHigh := fun t => Hjet (σ + t, f + V t)
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A₂)
    let q := fun t => scalarH1TimeCoordinate g₀ (σ + t, P f + J (W t))
    W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    MemLp qHigh 2 (timeMeasure T) ∧ (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] q := by
  intro B K₀ P J A₂ E PH Hjet qHigh QH q hWV
  have hmemHigh : MemLp qHigh 2 (timeMeasure T) := by
    have htime : MemLp (fun t : ℝ => (σ + t, (0 : CircleHsPi g₀ (Fin n)
        (((1 : ℕ) : ℝ) + 2)))) 2 (timeMeasure T) :=
      memLp_of_continuousOn ((continuousOn_const.add continuousOn_id).prodMk continuousOn_const)
    have hstate : MemLp (fun t => f + V t) 2 (timeMeasure T) :=
      (memLp_const f).add (Lp.memLp V)
    have hpair := htime.add ((ContinuousLinearMap.inr ℝ ℝ _).comp_memLp' hstate)
    have hp : MemLp (fun t => (σ + t, f + V t)) 2 (timeMeasure T) := by
      apply hpair.ae_eq
      filter_upwards [] with t
      simp only [Function.comp_apply, Pi.add_apply, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    exact Hjet.comp_memLp' hp
  have hproject : (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] q := by
    filter_upwards [hWV] with t hwt
    have hf : circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 1) (E f) = f := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    have hw : circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1) (E (V t)) = W t := by
      rw [hwt]
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    have hj := reference_scalarHsTimeFirstJet_projection g₀ 2 (by omega) (σ + t)
      (E f) (E (V t)) f (W t) hf hw
    refine Eq.trans ?_ hj
    change QH (PH (AddCircle.scalarHsTimeFirstJet g₀ 2 (σ + t, E (f + V t)))) = _
    rw [map_add]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact ⟨hmemHigh, hproject⟩

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_h2_coefficients_of_timeFirstJet
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (qHigh : ℝ → PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) => TensorHs g₀ 0 0 2))
    (hmemHigh : MemLp qHigh 2 (timeMeasure T)) :
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A₂)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (fun t => QH (qHigh t)) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (W t))) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) →
    ∃ (a₂ : timeL2 (TensorHs g₀ 0 0 2) T)
      (b₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T),
      (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T] (fun t => alpha f (σ + t) (W t)) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (W t)) := by
  classical
  intro K₀ P J A₂ QH hcoeff hproject hσlo hσhi hbound
  obtain ⟨hac, hbc⟩ := reference_shifted_coefficients_continuousOn
    g₀ T σ fref f P J W hW F G hF hG hS alpha reaction hcoeff hσlo hσhi hbound
  have ha := (memLp_of_continuousOn hac).aestronglyMeasurable
  have hb := (memLp_of_continuousOn hbc).aestronglyMeasurable
  let q := fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (W t))
  change (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] q at hproject
  have hq : ContinuousOn q (Icc 0 T) :=
    (scalarH1TimeCoordinate g₀).continuous.comp_continuousOn
      ((continuousOn_const.add continuousOn_id).prodMk
        (continuousOn_const.add (J.continuous.comp_continuousOn hW)))
  let e : Icc (0 : ℝ) T × AddCircle (1 : ℝ) → (Option (Fin n ⊕ Fin n) → ℝ) :=
    fun p => scalarH1PiToContinuous g₀ (q p.1) p.2
  have he : Continuous e := by
    have hqr : Continuous (fun t : Icc (0 : ℝ) T => q t) :=
      continuousOn_iff_continuous_domRestrict.mp hq
    exact continuous_eval.comp
      (((scalarH1PiToContinuous g₀).continuous.comp (hqr.comp continuous_fst)).prodMk
        continuous_snd)
  have hK : IsCompact (range e) := isCompact_range he
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : σ + t ∈ Icc (-ρ) ρ :=
    by constructor <;> linarith [ht.1, ht.2]
  have hKS : range e ⊆ S := by
    rintro z ⟨⟨t, x⟩, rfl⟩
    exact hcoeff.1 f (σ + t) (htime t t.2) (W t) (hbound t t.2) (mem_range_self x)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  let Rbound := (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * D
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have hRange : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (qHigh t))) ⊆ range e := by
    filter_upwards [hproject, hmem] with t ht htt
    rw [ht]
    rintro z ⟨x, rfl⟩
    exact ⟨(⟨t, htt⟩, x), rfl⟩
  have hBound : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖A₂ (qHigh t i)‖) ≤ Rbound := by
    filter_upwards [hproject, hmem] with t ht htt
    change (∑ i, ‖QH (qHigh t) i‖) ≤ _
    rw [ht]
    calc
      _ ≤ ∑ _i : Option (Fin n ⊕ Fin n), ‖q t‖ :=
        Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖q t‖ := by simp
      _ ≤ Rbound := mul_le_mul_of_nonneg_left (hD t htt) (by positivity)
  have hcoords (t : ℝ) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (q t) z =
        (fun i => match i with
          | none => σ + t
          | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (W t)) i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  have hEval : ∀ᵐ t ∂timeMeasure T,
      (∀ z, scalarH1ToContinuous g₀ (alpha f (σ + t) (W t)) z =
        F (scalarH1PiToContinuous g₀ (QH (qHigh t)) z)) ∧
      (∀ z j, scalarH1ToContinuous g₀ (reaction f (σ + t) (W t) j) z =
        G (scalarH1PiToContinuous g₀ (QH (qHigh t)) z) j) := by
    filter_upwards [hproject, hmem] with t ht htt
    constructor
    · intro z
      rw [ht, hcoords]
      exact hcoeff.2.1 f (σ + t) (htime t htt) (W t) (hbound t htt) z
    · intro z j
      rw [ht, hcoords]
      exact hcoeff.2.2 f (σ + t) (htime t htt) (W t) (hbound t htt) z j
  obtain ⟨a₂, ha₂⟩ := AddCircle.exists_lp_scalarH2_composition_of_h1_bound
    (timeMeasure T) g₀ F hF hS hK hKS hmemHigh ha hRange hBound
      (hEval.mono fun _ ht => ht.1)
  have hbcoord (j : Fin n) := AddCircle.exists_lp_scalarH2_composition_of_h1_bound
    (timeMeasure T) g₀ (fun z => G z j) (contDiffOn_pi.mp hG j) hS hK hKS hmemHigh
      ((PiLp.continuous_apply 2 (fun _ : Fin n => TensorHs g₀ 0 0 1) j).comp_aestronglyMeasurable
        hb)
      hRange hBound (hEval.mono fun _ ht => fun z => ht.2 z j)
  choose bcoord hbcoord using hbcoord
  let E₂ := Lp.piLpEquiv (𝕜 := ℝ) (X := fun _ : Fin n => TensorHs g₀ 0 0 2) (timeMeasure T)
  let bpi : PiLp 2 (fun _ : Fin n => timeL2 (TensorHs g₀ 0 0 2) T) := WithLp.toLp 2 bcoord
  let b₂ := E₂.symm bpi
  refine ⟨a₂, b₂, ha₂, ?_⟩
  filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) bpi,
    Filter.eventually_all.mpr hbcoord] with t ht hc
  apply PiLp.ext
  intro j
  have hj := congrArg (fun v => v j) ht
  change b₂ t j = bcoord j t at hj
  change A₂ (b₂ t j) = reaction f (σ + t) (W t) j
  rw [hj]
  exact hc j

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_h2_coefficients_timeShift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) :
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) →
    ∃ (a₂ : timeL2 (TensorHs g₀ 0 0 2) T)
      (b₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T),
      (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T] (fun t => alpha f (σ + t) (W t)) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (W t)) := by
  intro B K₀ P J A₂ hcoeff hWV hσlo hσhi hbound
  let E := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
  let Hjet := PH.comp ((AddCircle.scalarHsTimeFirstJet g₀ 2).comp
    ((ContinuousLinearMap.fst ℝ ℝ _).prod
      (E.comp (ContinuousLinearMap.snd ℝ ℝ _))))
  let qHigh := fun t => Hjet (σ + t, f.val + V t)
  obtain ⟨hmemHigh, hproject⟩ := reference_shifted_timeFirstJet_h2 g₀ T σ f.val V W hWV
  exact reference_exists_h2_coefficients_of_timeFirstJet g₀ T σ fref f W hW
    F G hF hG hS alpha reaction qHigh hmemHigh hcoeff hproject hσlo hσhi hbound

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_successor_timeFirstJet
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let qHigh := fun t => Hjet (σ + t, fHigh + V t)
    let AL := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let PL := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ)))
    let qLow := fun t => PL (AddCircle.scalarHsTimeFirstJet g₀ (k + 1 + 1)
      (σ + t, B fHigh + W t))
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    let Aone := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let QL := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => Aone)
    let qPhys := fun t => scalarH1TimeCoordinate g₀
      (σ + t, P f + J (L (W t)))
    R fHigh = f → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    MemLp qHigh 2 (timeMeasure T) ∧
      (fun t => ContinuousLinearMap.piLpMap 2
        (fun _ : Option (Fin n ⊕ Fin n) => AL) (qHigh t)) =ᵐ[timeMeasure T] qLow ∧
      ContinuousOn qLow (Icc 0 T) ∧
      (∀ t, QL (qLow t) = qPhys t) ∧
      (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] qPhys := by
  intro R L B K₀ P J AH PH Hjet qHigh AL PL qLow QH Aone QL qPhys hf hWV
  have hqHigh : MemLp qHigh 2 (timeMeasure T) := by
    have hbase := PH.comp_memLp'
      (AddCircle.memLp_scalarHsTimeCoordinate_firstJetHs g₀ (k + 1 + 2) T fHigh V)
    have hh := (memLp_const (Hjet (σ, 0))).add hbase
    apply hh.ae_eq
    filter_upwards [] with t
    change Hjet (σ, 0) + Hjet (t, fHigh + V t) = Hjet (σ + t, fHigh + V t)
    rw [← map_add]
    simp only [Prod.mk_add_mk, zero_add]
  have hHighLow : (fun t => ContinuousLinearMap.piLpMap 2
      (fun _ : Option (Fin n ⊕ Fin n) => AL) (qHigh t)) =ᵐ[timeMeasure T] qLow := by
    filter_upwards [hWV] with t hwt
    let Jraw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 1 + 1 : ℕ) : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ))
    have hraw := congrArg (fun A => A (fHigh + V t))
      (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := Fin n) g₀
        (show k + 1 + 1 ≤ k + 1 + 2 by omega))
    change AddCircle.firstJetHs g₀ (k + 1 + 1) (B (fHigh + V t)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n => Jraw)
        (AddCircle.firstJetHs g₀ (k + 1 + 2) (fHigh + V t)) at hraw
    rw [map_add, ← hwt] at hraw
    have htime := AddCircle.tensorHsInclusion_scalarHsTimeCoordinate_eq g₀
      (by push_cast; linarith : ((k + 1 + 1 : ℕ) : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ))
      (σ + t, AddCircle.firstJetHs g₀ (k + 1 + 2) (fHigh + V t))
    rw [← hraw] at htime
    refine Eq.trans ?_ (congrArg PL htime)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hqLow : ContinuousOn qLow (Icc 0 T) :=
    PL.continuous.comp_continuousOn
      ((AddCircle.scalarHsTimeFirstJet g₀ (k + 1 + 1)).continuous.comp_continuousOn
        ((continuousOn_const.add continuousOn_id).prodMk (continuousOn_const.add hW)))
  have hLowPhys (t : ℝ) : QL (qLow t) = qPhys t := by
    let Rlow := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    have hbase : Rlow (B fHigh) = f := by
      refine Eq.trans ?_ hf
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    have h := reference_scalarHsTimeFirstJet_projection g₀ (k + 1 + 1)
      (by omega) (σ + t) (B fHigh) (W t) f (L (W t)) hbase rfl
    refine Eq.trans ?_ h
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hHighPhys : (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] qPhys := by
    filter_upwards [hHighLow] with t ht
    rw [← hLowPhys, ← ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact ⟨hqHigh, hHighLow, hqLow, hLowPhys, hHighPhys⟩

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_successor_coefficients_of_timeFirstJet
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (ha₂ : AEStronglyMeasurable a₂ (timeMeasure T))
    (hb₂ : AEStronglyMeasurable b₂ (timeMeasure T))
    (qHigh : ℝ → PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)))
    (qLow : ℝ → PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hqHigh : MemLp qHigh 2 (timeMeasure T))
    (hqLow : ContinuousOn qLow (Icc 0 T)) :
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let AL := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let Aone := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let QL := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => Aone)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (fun t => ContinuousLinearMap.piLpMap 2
      (fun _ : Option (Fin n ⊕ Fin n) => AL) (qHigh t)) =ᵐ[timeMeasure T] qLow →
    (∀ t, QL (qLow t) = scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (w t))) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
    (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f (σ + t) (w t)) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t)) =ᵐ[timeMeasure T]
      (fun t => reaction f (σ + t) (w t)) →
    ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
      (bHigh : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T),
      (fun t => P₂ (aHigh t)) =ᵐ[timeMeasure T] a₂ ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂) (bHigh t))
        =ᵐ[timeMeasure T] b₂ ∧
      (fun t => AH (aHigh t)) =ᵐ[timeMeasure T]
        (fun t => alpha f (σ + t) (w t)) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (w t)) := by
  classical
  intro K₀ P J A₂ P₂ AH AL Aone QL hcoeff hHighLow hLowPhys hσlo hσhi hbound hae hbe
  let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
  let qPhys := fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (w t))
  change ∀ t, QL (qLow t) = qPhys t at hLowPhys
  have hHighPhys : (fun t => QH (qHigh t)) =ᵐ[timeMeasure T] qPhys := by
    filter_upwards [hHighLow] with t ht
    rw [← hLowPhys, ← ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hqPhys : ContinuousOn qPhys (Icc 0 T) := by
    exact (QL.continuous.comp_continuousOn hqLow).congr (fun t _ => (hLowPhys t).symm)
  let e : Icc (0 : ℝ) T × AddCircle (1 : ℝ) → (Option (Fin n ⊕ Fin n) → ℝ) :=
    fun p => scalarH1PiToContinuous g₀ (qPhys p.1) p.2
  have he : Continuous e := by
    have hqr : Continuous (fun t : Icc (0 : ℝ) T => qPhys t) :=
      continuousOn_iff_continuous_domRestrict.mp hqPhys
    exact continuous_eval.comp
      (((scalarH1PiToContinuous g₀).continuous.comp (hqr.comp continuous_fst)).prodMk
        continuous_snd)
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : σ + t ∈ Icc (-ρ) ρ :=
    by constructor <;> linarith [ht.1, ht.2]
  have hK : IsCompact (range e) := isCompact_range he
  have hKS : range e ⊆ S := by
    rintro z ⟨⟨t, x⟩, rfl⟩
    exact hcoeff.1 f (σ + t) (htime t t.2) (w t) (hbound t t.2) (mem_range_self x)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hqLow
  let Rbound := (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * D
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have hRange : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (qHigh t))) ⊆ range e := by
    filter_upwards [hHighPhys, hmem] with t ht htt
    rw [ht]
    rintro z ⟨x, rfl⟩
    exact ⟨(⟨t, htt⟩, x), rfl⟩
  have hBound : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖AL (qHigh t i)‖) ≤ Rbound := by
    filter_upwards [hHighLow, hmem] with t ht htt
    change (∑ i, ‖ContinuousLinearMap.piLpMap 2
      (fun _ : Option (Fin n ⊕ Fin n) => AL) (qHigh t) i‖) ≤ _
    rw [ht]
    calc
      _ ≤ ∑ _i : Option (Fin n ⊕ Fin n), ‖qLow t‖ :=
        Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖qLow t‖ := by simp
      _ ≤ Rbound := mul_le_mul_of_nonneg_left (hD t htt) (by positivity)
  have hcoords (t : ℝ) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (qPhys t) z =
        (fun i => match i with
          | none => σ + t
          | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (w t)) i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  have hEval : ∀ᵐ t ∂timeMeasure T,
      (∀ z, scalarH1ToContinuous g₀ (A₂ (a₂ t)) z =
        F (scalarH1PiToContinuous g₀ (QH (qHigh t)) z)) ∧
      (∀ z j, scalarH1ToContinuous g₀ (A₂ (b₂ t j)) z =
        G (scalarH1PiToContinuous g₀ (QH (qHigh t)) z) j) := by
    filter_upwards [hHighPhys, hmem, hae, hbe] with t ht htt hat hbt
    constructor
    · intro z
      rw [hat, ht, hcoords]
      exact hcoeff.2.1 f (σ + t) (htime t htt) (w t) (hbound t htt) z
    · intro z j
      have hh := congrArg (fun v => v j) hbt
      change A₂ (b₂ t j) = reaction f (σ + t) (w t) j at hh
      rw [hh, ht, hcoords]
      exact hcoeff.2.2 f (σ + t) (htime t htt) (w t) (hbound t htt) z j
  have liftScalar (H : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
      (hH : ContDiffOn ℝ ∞ H S) (c₂ : ℝ → TensorHs g₀ 0 0 2)
      (hc₂ : AEStronglyMeasurable c₂ (timeMeasure T))
      (hEval₂ : ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g₀ (A₂ (c₂ t)) z =
        H (scalarH1PiToContinuous g₀ (QH (qHigh t)) z)) :
      ∃ cHigh : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T,
        (fun t => P₂ (cHigh t)) =ᵐ[timeMeasure T] c₂ := by
    obtain ⟨C, hC, hc⟩ := AddCircle.exists_scalarHs_composition_bound_of_lower_order_bound
      g₀ (k + 1) H hH hS hK hKS Rbound
    let bnorm := fun t => C * (1 + (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖qHigh t‖)
    have hbnorm : MemLp bnorm 2 (timeMeasure T) :=
      ((memLp_const (1 : ℝ)).add
        (hqHigh.norm.const_mul (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ))).const_mul C
    have hlift : ∀ᵐ t ∂timeMeasure T,
        ∃ v : TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2), P₂ v = c₂ t ∧ ‖v‖ ≤ bnorm t := by
      filter_upwards [hRange, hBound, hEval₂] with t hrt hbt het
      obtain ⟨v, hv, hve⟩ := hc (qHigh t) hrt hbt
      refine ⟨v, ?_, ?_⟩
      · apply tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)
        apply scalarH1ToContinuous_injective g₀
        apply ContinuousMap.ext
        intro z
        have hinc : A₂ (P₂ v) = AH v := by
          apply TensorHs.ext
          rfl
        rw [hinc]
        exact (hve z).trans (het z).symm
      · have hsum : (∑ i, ‖qHigh t i‖) ≤
            (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖qHigh t‖ := by
          calc
            _ ≤ ∑ _i : Option (Fin n ⊕ Fin n), ‖qHigh t‖ :=
              Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
            _ = _ := by simp
        exact hv.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
    obtain ⟨cHigh, hcHigh, _⟩ := exists_lp_lift_of_ae_exists_norm_le P₂.continuous
      (tensorHsInclusion_injective (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)) hc₂ hbnorm hlift
    exact ⟨cHigh, hcHigh⟩
  obtain ⟨aHigh, haHigh⟩ := liftScalar F hF a₂ ha₂ (hEval.mono fun _ ht => ht.1)
  have hbcoord (j : Fin n) := liftScalar (fun z => G z j) (contDiffOn_pi.mp hG j)
    (fun t => b₂ t j)
    ((PiLp.continuous_apply 2 (fun _ : Fin n => TensorHs g₀ 0 0 2) j).comp_aestronglyMeasurable
      hb₂)
    (hEval.mono fun _ ht => fun z => ht.2 z j)
  choose bcoord hbcoord using hbcoord
  let E := Lp.piLpEquiv (𝕜 := ℝ)
    (X := fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) (timeMeasure T)
  let bpi : PiLp 2 (fun _ : Fin n => timeL2
      (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T) := WithLp.toLp 2 bcoord
  let bHigh := E.symm bpi
  have hbHigh : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂) (bHigh t))
      =ᵐ[timeMeasure T] b₂ := by
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) bpi,
      Filter.eventually_all.mpr hbcoord] with t ht hc
    apply PiLp.ext
    intro j
    have hj := congrArg (fun v => v j) ht
    change bHigh t j = bcoord j t at hj
    change P₂ (bHigh t j) = b₂ t j
    rw [hj]
    exact hc j
  refine ⟨aHigh, bHigh, haHigh, hbHigh, ?_, ?_⟩
  · filter_upwards [haHigh, hae] with t ht hat
    calc
      AH (aHigh t) = A₂ (P₂ (aHigh t)) := by apply TensorHs.ext; rfl
      _ = A₂ (a₂ t) := congrArg A₂ ht
      _ = _ := hat
  · filter_upwards [hbHigh, hbe] with t ht hbt
    have hinc : ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t) =
        ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂) (bHigh t)) := by
      apply PiLp.ext
      intro j
      apply TensorHs.ext
      rfl
    rw [hinc, ht]
    exact hbt

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_successor_coefficients_timeShift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (ha₂ : AEStronglyMeasurable a₂ (timeMeasure T))
    (hb₂ : AEStronglyMeasurable b₂ (timeMeasure T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    R fHigh = f.val → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W t)‖ ≤ ρ) →
    (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f (σ + t) (L (W t))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t)) =ᵐ[timeMeasure T]
      (fun t => reaction f (σ + t) (L (W t))) →
    ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
      (bHigh : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T),
      (fun t => P₂ (aHigh t)) =ᵐ[timeMeasure T] a₂ ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P₂) (bHigh t))
        =ᵐ[timeMeasure T] b₂ ∧
      (fun t => AH (aHigh t)) =ᵐ[timeMeasure T]
        (fun t => alpha f (σ + t) (L (W t))) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (L (W t))) := by
  intro R L B K₀ P J A₂ P₂ AH hcoeff hf hWV hσlo hσhi hbound hae hbe
  let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; rfl :
        ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
  let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
  let qHigh := fun t => Hjet (σ + t, fHigh + V t)
  let PL := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; rfl :
        ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ)))
  let qLow := fun t => PL (AddCircle.scalarHsTimeFirstJet g₀ (k + 1 + 1)
    (σ + t, B fHigh + W t))
  obtain ⟨hqHigh, hHighLow, hqLow, hLowPhys, _⟩ :=
    reference_shifted_successor_timeFirstJet g₀ k T σ f.val fHigh V W hW hf hWV
  exact reference_exists_successor_coefficients_of_timeFirstJet g₀ k T σ fref f
    (fun t => L (W t)) F G hF hG hS alpha reaction a₂ b₂ ha₂ hb₂
    qHigh qLow hqHigh hqLow hcoeff hHighLow hLowPhys hσlo hσhi hbound hae hbe

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_seed_state_projection
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let Bseed := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let V₃ := R.compLpL 2 (timeMeasure T) V
    let W₂ := fun t => L (W t)
    R fHigh = f →
    W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    ContinuousOn W₂ (Icc 0 T) ∧
      W₂ =ᵐ[timeMeasure T] (fun t => Bseed (V₃ t)) ∧
      (fun t => R (fHigh + V t)) =ᵐ[timeMeasure T] (fun t => f + V₃ t) := by
  intro R L B Bseed V₃ W₂ hf hWV
  have hlow := tensorHsPi_ae_eq_of_inclusion g₀ 0 0
    (by push_cast; linarith :
      ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    V W hWV.symm
  refine ⟨L.continuous.comp_continuousOn hW, hlow.symm, ?_⟩
  filter_upwards [R.coeFn_compLpL V] with t ht
  change V₃ t = R (V t) at ht
  rw [map_add, hf, ht]

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_high_coefficients_timeShift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    R fHigh = f.val → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W t)‖ ≤ ρ) →
    ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
      (bHigh : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T),
      (fun t => AH (aHigh t)) =ᵐ[timeMeasure T]
        (fun t => alpha f (σ + t) (L (W t))) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (bHigh t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (L (W t))) := by
  intro R L B K₀ P J AH hcoeff hf hWV hσlo hσhi hbound
  let V₃ := R.compLpL 2 (timeMeasure T) V
  let w := fun t => L (W t)
  obtain ⟨hw, hVw, _⟩ :=
    reference_seed_state_projection g₀ k T fHigh f.val V W hW hf hWV
  obtain ⟨a₂, b₂, ha₂, hb₂⟩ := reference_exists_h2_coefficients_timeShift
    g₀ T σ fref f V₃ w hw F G hF hG hS alpha reaction
    hcoeff hVw hσlo hσhi hbound
  obtain ⟨aHigh, bHigh, _, _, haHigh, hbHigh⟩ :=
    reference_exists_successor_coefficients_timeShift g₀ k T σ fref f fHigh V W hW
      F G hF hG hS alpha reaction a₂ b₂ (Lp.memLp a₂).aestronglyMeasurable (Lp.memLp b₂).aestronglyMeasurable
      hcoeff hf hWV hσlo hσhi hbound ha₂ hb₂
  exact ⟨aHigh, bHigh, haHigh, hbHigh⟩

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_firstJet_exists_compact_range
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (f : X → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto f l (𝓝 f₀))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ)) (hS : IsOpen S) :
    let q := fun x t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (σ x + t, P (f x) + J (w x t)))
    let q₀ := fun t => scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (σ₀ + t, P f₀ + J (w₀ t)))
    (∀ t ∈ Icc 0 T, ∀ z, q₀ t z ∈ S) →
    ∃ K : Set (Option (Fin n ⊕ Fin n) → ℝ),
      IsCompact K ∧ K ⊆ S ∧
      (∀ t ∈ Icc 0 T, ∀ z, q₀ t z ∈ interior K) ∧
      ∀ᶠ x in l, ∀ t ∈ Icc 0 T, ∀ z, q x t z ∈ K := by
  intro q q₀ hmap₀
  let A := (scalarH1PiToContinuous (ι := Option (Fin n ⊕ Fin n)) g₀).comp
    (scalarH1TimeCoordinate (ι := Fin n ⊕ Fin n) g₀)
  let Atime := A.comp (ContinuousLinearMap.inl ℝ ℝ _)
  have htime (s t : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) :
      Atime s + A (t, v) = A (s + t, v) := by
    change A (s, 0) + A (t, v) = A (s + t, v)
    rw [← map_add]
    simp only [Prod.mk_add_mk, zero_add]
  obtain ⟨hqbase₀, hqbase⟩ := reference_firstJet_tendstoUniformlyOn
    g₀ T P J f f₀ w w₀ hf hw₀ hw
  have hq : TendstoUniformlyOn q q₀ l (Icc 0 T) := by
    have h := (((Atime.continuous.tendsto σ₀).comp hσ).tendstoUniformlyOn_const
      (Icc 0 T)).add hqbase
    change TendstoUniformlyOn
      (fun x t => Atime (σ x) + A (t, P (f x) + J (w x t)))
      (fun t => Atime σ₀ + A (t, P f₀ + J (w₀ t))) l (Icc 0 T) at h
    simp only [htime] at h
    change TendstoUniformlyOn
      (fun x t => A (σ x + t, P (f x) + J (w x t)))
      (fun t => A (σ₀ + t, P f₀ + J (w₀ t))) l (Icc 0 T)
    exact h
  have hq₀ : ContinuousOn q₀ (Icc 0 T) := by
    have h : ContinuousOn (fun t => Atime σ₀ + A (t, P f₀ + J (w₀ t))) (Icc 0 T) :=
      continuousOn_const.add hqbase₀
    simp only [htime] at h
    change ContinuousOn (fun t => A (σ₀ + t, P f₀ + J (w₀ t))) (Icc 0 T)
    exact h
  exact hq.exists_isCompact_eventually_forall_eval_mem isCompact_Icc hq₀ hS hmap₀

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_h2_time_first_jet_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (fLow : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (fHigh : CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((0 + 1 : ℕ) : ℝ) + 1)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 1 ≤ ((0 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((0 + 1 : ℕ) : ℝ) + 1 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num :
        (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num :
          ((0 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (0 + 2))
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    R fHigh = fLow → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    (fun t => QH (Hjet (σ + t, fHigh + V t))) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g₀ (σ + t, P fLow + J (L (W t)))) := by
  intro R L B K₀ P J AH PH Hjet QH hf hWV
  let Vlow := R.compLpL 2 (timeMeasure T) V
  let Blow := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  have hWVlow : (fun t => L (W t)) =ᵐ[timeMeasure T] fun t => Blow (Vlow t) := by
    filter_upwards [hWV, R.coeFn_compLpL V] with t hwt hRt
    change Vlow t = R (V t) at hRt
    rw [hwt, hRt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hseed := (reference_shifted_timeFirstJet_h2 g₀ T σ fLow Vlow
    (fun t => L (W t)) hWVlow).2
  let E := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  have hjet : (fun t => QH (Hjet (σ + t, fHigh + V t))) =ᵐ[timeMeasure T]
      fun t => scalarH1TimeCoordinate g₀ (σ + t, P fLow + J (L (W t))) := by
    filter_upwards [hseed, R.coeFn_compLpL V] with t ht hRt
    change Vlow t = R (V t) at hRt
    have hstate : E (fLow + Vlow t) = fHigh + V t := by
      rw [← hf, hRt]
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    refine Eq.trans ?_ ht
    change QH (Hjet (σ + t, fHigh + V t)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2))
        (ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
          (AddCircle.scalarHsTimeFirstJet g₀ 2 (σ + t, E (fLow + Vlow t))))
    rw [hstate]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact hjet

private theorem reference_h2_coefficients_eval_timeShift_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (fHigh : CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((0 + 1 : ℕ) : ℝ) + 1))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (a : timeL2 (TensorHs g₀ 0 0 (((0 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2)) T) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 1 ≤ ((0 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((0 + 1 : ℕ) : ℝ) + 1 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num :
        (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num :
          ((0 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (0 + 2))
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    R fHigh = f.val → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W t)‖ ≤ ρ) →
    (fun t => AH (a t)) =ᵐ[timeMeasure T]
      (fun t => alpha f (σ + t) (L (W t))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b t))
      =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (L (W t))) →
    ((fun t => QH (Hjet (σ + t, fHigh + V t))) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (L (W t))))) ∧
    (∀ᵐ t ∂timeMeasure T,
      (∀ z, scalarH1ToContinuous g₀ (AH (a t)) z =
        F (scalarH1PiToContinuous g₀ (QH (Hjet (σ + t, fHigh + V t))) z)) ∧
      (∀ z j, scalarH1ToContinuous g₀ (AH (b t j)) z =
        G (scalarH1PiToContinuous g₀ (QH (Hjet (σ + t, fHigh + V t))) z) j)) := by
  intro R L B K₀ P J AH PH Hjet QH hcoeff hf hWV hσlo hσhi hbound ha hb
  have hjet := reference_h2_time_first_jet_ae g₀ T σ f.val fHigh V W hf hWV
  have hcoords (s : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (s, v)) z =
        (fun i => match i with | none => s | some i => scalarH1ToContinuous g₀ (v i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  refine ⟨hjet, ?_⟩
  filter_upwards [ha, hb, hjet, ae_restrict_mem measurableSet_Icc] with t hat hbt hjt htt
  have htime : σ + t ∈ Icc (-ρ) ρ := by
    constructor <;> linarith [htt.1, htt.2]
  have hjval (z : AddCircle (1 : ℝ)) :=
    (congrArg (fun v : CircleHsPi g₀ (Option (Fin n ⊕ Fin n)) 1 =>
      scalarH1PiToContinuous g₀ v z) hjt).trans
        (hcoords (σ + t) (P f.val + J (L (W t))) z)
  constructor
  · intro z
    exact (congrArg (fun v => scalarH1ToContinuous g₀ v z) hat).trans
      ((hcoeff.2.1 f (σ + t) htime (L (W t)) (hbound t htt) z).trans
        (congrArg F (hjval z).symm))
  · intro z j
    have hbj := congrArg (fun v => v j) hbt
    change AH (b t j) = reaction f (σ + t) (L (W t)) j at hbj
    exact (congrArg (fun v => scalarH1ToContinuous g₀ v z) hbj).trans
      ((hcoeff.2.2 f (σ + t) htime (L (W t)) (hbound t htt) z j).trans
        (congrArg (fun v => G v j) (hjval z).symm))


private theorem reference_selected_h2_coefficients_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (fcenter : CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1))
    (Δ : X → CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1))
    (Δ₀ : CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1))
    (hΔ : Tendsto Δ l (𝓝 Δ₀))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ}
    (f : X → Metric.closedBall fref δ) (f₀ : Metric.closedBall fref δ)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (V : X → timeL2
      (CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1)) T)
    (V₀ : timeL2 (CircleHsPi g₀ (Fin n) (((0 + 2 : ℕ) : ℝ) + 1)) T)
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((0 + 1 : ℕ) : ℝ) + 1))
    (W₀ : ℝ → CircleHsPi g₀ (Fin n) (((0 + 1 : ℕ) : ℝ) + 1))
    (a : X → timeL2 (TensorHs g₀ 0 0 (((0 : ℕ) : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g₀ 0 0 (((0 : ℕ) : ℝ) + 2)) T)
    (b : X → timeL2 (CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2)) T)
    (b₀ : timeL2 (CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2)) T)
    (hV : Tendsto V l (𝓝 V₀))
    (hW₀ : ContinuousOn W₀ (Icc 0 T))
    (hW : TendstoUniformlyOn W W₀ l (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by norm_num :
        ((1 : ℕ) : ℝ) + 1 ≤ ((0 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((0 + 1 : ℕ) : ℝ) + 1 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num :
        (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, R (fcenter + Δ x) = (f x).val) → R (fcenter + Δ₀) = f₀.val →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => B (V x t)) →
    W₀ =ᵐ[timeMeasure T] (fun t => B (V₀ t)) →
    (∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    -ρ ≤ σ₀ → σ₀ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W₀ t)‖ ≤ ρ) →
    (∀ᶠ x in l, (fun t => AH (a x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (fun t => AH (a₀ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f₀ (σ₀ + t) (L (W₀ t))) →
    (∀ᶠ x in l, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (L (W x t)))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₀ t))
      =ᵐ[timeMeasure T] (fun t => reaction f₀ (σ₀ + t) (L (W₀ t))) →
    Tendsto (fun x => (a x, b x)) l (𝓝 (a₀, b₀)) := by
  intro R L B K₀ P J AH hcoeff hf hf₀ hWV hWV₀ hgood hσlo hσhi hbound₀ ha ha₀ hb hb₀
  let fHigh := fun x => fcenter + Δ x
  let fHigh₀ := fcenter + Δ₀
  let w := fun x t => L (W x t)
  let w₀ := fun t => L (W₀ t)
  have hfHigh : Tendsto fHigh l (𝓝 fHigh₀) := tendsto_const_nhds.add hΔ
  have hfLow : Tendsto (fun x => (f x).val) l (𝓝 f₀.val) := by
    have h := (R.continuous.tendsto fHigh₀).comp hfHigh
    change Tendsto (fun x => R (fcenter + Δ x)) l (𝓝 (R (fcenter + Δ₀))) at h
    simpa only [hf, hf₀] using h
  have hw₀ : ContinuousOn w₀ (Icc 0 T) := L.continuous.comp_continuousOn hW₀
  have hw : TendstoUniformlyOn w w₀ l (Icc 0 T) :=
    L.uniformContinuous.comp_tendstoUniformlyOn hW
  let q₀ := fun t => scalarH1PiToContinuous g₀
    (scalarH1TimeCoordinate g₀ (σ₀ + t, P f₀.val + J (w₀ t)))
  have hmap₀ : ∀ t ∈ Icc 0 T, ∀ z, q₀ t z ∈ S := by
    intro t ht z
    have htt : σ₀ + t ∈ Icc (-ρ) ρ := by
      constructor <;> linarith [ht.1, ht.2]
    exact hcoeff.1 f₀ (σ₀ + t) htt (w₀ t) (hbound₀ t ht) (mem_range_self z)
  obtain ⟨K, hK, hKS, hlim, hfamily⟩ :=
    reference_shifted_firstJet_exists_compact_range g₀ T P J σ σ₀ hσ
      (fun x => (f x).val) f₀.val w w₀ hfLow hw₀ hw S hS hmap₀
  let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num :
        ((0 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ)))
  let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (0 + 2))
  let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
  have hData := (hgood.and (ha.and hb)).mono fun x hx =>
    reference_h2_coefficients_eval_timeShift_ae g₀ T (σ x) fref (f x)
      (fHigh x) (V x) (W x) F G alpha reaction (a x) (b x)
      hcoeff (hf x) (hWV x) hx.1.1 hx.1.2.1 hx.1.2.2 hx.2.1 hx.2.2
  have hData₀ := reference_h2_coefficients_eval_timeShift_ae g₀ T σ₀ fref f₀
    fHigh₀ V₀ W₀ F G alpha reaction a₀ b₀ hcoeff hf₀ hWV₀ hσlo hσhi hbound₀ ha₀ hb₀
  have hrange : ∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (Hjet (σ x + t, fHigh x + V x t)))) ⊆ K := by
    filter_upwards [hfamily, hData] with x hx hdx
    filter_upwards [hdx.1, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [ht]
    rintro z ⟨y, rfl⟩
    exact hx t htt y
  have hrange₀ : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (Hjet (σ₀ + t, fHigh₀ + V₀ t)))) ⊆ K := by
    filter_upwards [hData₀.1, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [ht]
    rintro z ⟨y, rfl⟩
    exact interior_subset (hlim t htt y)
  have haT := AddCircle.tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    g₀ 0 T σ σ₀ hσ F hF hS hK hKS fHigh fHigh₀ V V₀ a a₀ W W₀
    hfHigh hV hW₀ hW hWV hWV₀ hrange hrange₀
    (hData.mono fun _ hx => hx.2.mono fun _ ht => ht.1) (hData₀.2.mono fun _ ht => ht.1)
  have hbT := AddCircle.tendsto_timeL2_vectorHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    g₀ 0 T σ σ₀ hσ G hG hS hK hKS fHigh fHigh₀ V V₀ b b₀ W W₀
    hfHigh hV hW₀ hW hWV hWV₀ hrange hrange₀
    (hData.mono fun _ hx => hx.2.mono fun _ ht => ht.2) (hData₀.2.mono fun _ ht => ht.2)
  exact haT.prodMk_nhds hbT

private theorem reference_high_coefficients_eval_timeShift_ae
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (V : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (a : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    R fHigh = f.val → W =ᵐ[timeMeasure T] (fun t => B (V t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W t)‖ ≤ ρ) →
    (fun t => AH (a t)) =ᵐ[timeMeasure T]
      (fun t => alpha f (σ + t) (L (W t))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b t))
      =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (L (W t))) →
    ((fun t => QH (Hjet (σ + t, fHigh + V t))) =ᵐ[timeMeasure T]
      (fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (L (W t))))) ∧
    (∀ᵐ t ∂timeMeasure T,
      (∀ z, scalarH1ToContinuous g₀ (AH (a t)) z =
        F (scalarH1PiToContinuous g₀ (QH (Hjet (σ + t, fHigh + V t))) z)) ∧
      (∀ z j, scalarH1ToContinuous g₀ (AH (b t j)) z =
        G (scalarH1PiToContinuous g₀ (QH (Hjet (σ + t, fHigh + V t))) z) j)) := by
  intro R L B K₀ P J AH PH Hjet QH hcoeff hf hWV hσlo hσhi hbound ha hb
  let KHigh := circleHsPiInclusion g₀ (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
  have hwV : (fun t => L (W t)) =ᵐ[timeMeasure T] fun t => KHigh (V t) := by
    filter_upwards [hWV] with t ht
    rw [ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hjet : (fun t => QH (Hjet (σ + t, fHigh + V t))) =ᵐ[timeMeasure T]
      fun t => scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (L (W t))) := by
    filter_upwards [hwV] with t ht
    have h := reference_scalarHsTimeFirstJet_projection g₀ (k + 1 + 2)
      (by omega) (σ + t) fHigh (V t) f.val (L (W t)) hf ht.symm
    refine Eq.trans ?_ h
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hcoords (s : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (s, v)) z =
        (fun i => match i with | none => s | some i => scalarH1ToContinuous g₀ (v i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  refine ⟨hjet, ?_⟩
  filter_upwards [ha, hb, hjet, ae_restrict_mem measurableSet_Icc] with t hat hbt hjt htt
  have htime : σ + t ∈ Icc (-ρ) ρ := by
    constructor <;> linarith [htt.1, htt.2]
  constructor
  · intro z
    rw [hat, hjt, hcoords]
    exact hcoeff.2.1 f (σ + t) htime (L (W t)) (hbound t htt) z
  · intro z j
    have hbj := congrArg (fun v => v j) hbt
    change AH (b t j) = reaction f (σ + t) (L (W t)) j at hbj
    rw [hbj, hjt, hcoords]
    exact hcoeff.2.2 f (σ + t) htime (L (W t)) (hbound t htt) z j

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_selected_coefficients_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (fcenter : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (Δ : X → CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (Δ₀ : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (hΔ : Tendsto Δ l (𝓝 Δ₀))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ}
    (f : X → Metric.closedBall fref δ) (f₀ : Metric.closedBall fref δ)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (V : X → timeL2
      (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (V₀ : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (W₀ : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (a : X → timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b : X → timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b₀ : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T)
    (hV : Tendsto V l (𝓝 V₀))
    (hW₀ : ContinuousOn W₀ (Icc 0 T))
    (hW : TendstoUniformlyOn W W₀ l (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, R (fcenter + Δ x) = (f x).val) → R (fcenter + Δ₀) = f₀.val →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => B (V x t)) →
    W₀ =ᵐ[timeMeasure T] (fun t => B (V₀ t)) →
    (∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    -ρ ≤ σ₀ → σ₀ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W₀ t)‖ ≤ ρ) →
    (∀ᶠ x in l, (fun t => AH (a x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (fun t => AH (a₀ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f₀ (σ₀ + t) (L (W₀ t))) →
    (∀ᶠ x in l, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (L (W x t)))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₀ t))
      =ᵐ[timeMeasure T] (fun t => reaction f₀ (σ₀ + t) (L (W₀ t))) →
    Tendsto (fun x => (a x, b x)) l (𝓝 (a₀, b₀)) := by
  intro R L B K₀ P J AH hcoeff hf hf₀ hWV hWV₀ hgood hσlo hσhi hbound₀ ha ha₀ hb hb₀
  let fHigh := fun x => fcenter + Δ x
  let fHigh₀ := fcenter + Δ₀
  let w := fun x t => L (W x t)
  let w₀ := fun t => L (W₀ t)
  have hfHigh : Tendsto fHigh l (𝓝 fHigh₀) := tendsto_const_nhds.add hΔ
  have hfLow : Tendsto (fun x => (f x).val) l (𝓝 f₀.val) := by
    have h := (R.continuous.tendsto fHigh₀).comp hfHigh
    change Tendsto (fun x => R (fcenter + Δ x)) l (𝓝 (R (fcenter + Δ₀))) at h
    simpa only [hf, hf₀] using h
  have hw₀ : ContinuousOn w₀ (Icc 0 T) := L.continuous.comp_continuousOn hW₀
  have hw : TendstoUniformlyOn w w₀ l (Icc 0 T) :=
    L.uniformContinuous.comp_tendstoUniformlyOn hW
  let q₀ := fun t => scalarH1PiToContinuous g₀
    (scalarH1TimeCoordinate g₀ (σ₀ + t, P f₀.val + J (w₀ t)))
  have hmap₀ : ∀ t ∈ Icc 0 T, ∀ z, q₀ t z ∈ S := by
    intro t ht z
    have htt : σ₀ + t ∈ Icc (-ρ) ρ := by
      constructor <;> linarith [ht.1, ht.2]
    exact hcoeff.1 f₀ (σ₀ + t) htt (w₀ t) (hbound₀ t ht) (mem_range_self z)
  obtain ⟨K, hK, hKS, hlim, hfamily⟩ :=
    reference_shifted_firstJet_exists_compact_range g₀ T P J σ σ₀ hσ
      (fun x => (f x).val) f₀.val w w₀ hfLow hw₀ hw S hS hmap₀
  let PH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; rfl :
        ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
  let Hjet := PH.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
  let QH := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => AH)
  have hData := (hgood.and (ha.and hb)).mono fun x hx =>
    reference_high_coefficients_eval_timeShift_ae g₀ k T (σ x) fref (f x)
      (fHigh x) (V x) (W x) F G alpha reaction (a x) (b x)
      hcoeff (hf x) (hWV x) hx.1.1 hx.1.2.1 hx.1.2.2 hx.2.1 hx.2.2
  have hData₀ := reference_high_coefficients_eval_timeShift_ae g₀ k T σ₀ fref f₀
    fHigh₀ V₀ W₀ F G alpha reaction a₀ b₀ hcoeff hf₀ hWV₀ hσlo hσhi hbound₀ ha₀ hb₀
  have hrange : ∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (Hjet (σ x + t, fHigh x + V x t)))) ⊆ K := by
    filter_upwards [hfamily, hData] with x hx hdx
    filter_upwards [hdx.1, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [ht]
    rintro z ⟨y, rfl⟩
    exact hx t htt y
  have hrange₀ : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (QH (Hjet (σ₀ + t, fHigh₀ + V₀ t)))) ⊆ K := by
    filter_upwards [hData₀.1, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [ht]
    rintro z ⟨y, rfl⟩
    exact interior_subset (hlim t htt y)
  have haT := AddCircle.tendsto_timeL2_scalarHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    g₀ (k + 1) T σ σ₀ hσ F hF hS hK hKS fHigh fHigh₀ V V₀ a a₀ W W₀
    hfHigh hV hW₀ hW hWV hWV₀ hrange hrange₀
    (hData.mono fun _ hx => hx.2.mono fun _ ht => ht.1) (hData₀.2.mono fun _ ht => ht.1)
  have hbT := AddCircle.tendsto_timeL2_vectorHs_composition_firstJet_timeShift_of_tendstoUniformlyOn
    g₀ (k + 1) T σ σ₀ hσ G hG hS hK hKS fHigh fHigh₀ V V₀ b b₀ W W₀
    hfHigh hV hW₀ hW hWV hWV₀ hrange hrange₀
    (hData.mono fun _ hx => hx.2.mono fun _ ht => ht.2) (hData₀.2.mono fun _ ht => ht.2)
  exact haT.prodMk_nhds hbT

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_principalCoefficient_tendstoUniformlyOn
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ) (f₀ : Metric.closedBall fref δ)
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto (fun x => (f x).val) l (𝓝 f₀.val))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction)
    (hgood : ∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖w x t‖ ≤ ρ)
    (hσlo : -ρ ≤ σ₀) (hσhi : σ₀ + T ≤ ρ)
    (hbound₀ : ∀ t ∈ Icc 0 T, ‖w₀ t‖ ≤ ρ) :
    TendstoUniformlyOn (fun x t => alpha (f x) (σ x + t) (w x t))
      (fun t => alpha f₀ (σ₀ + t) (w₀ t)) l (Icc 0 T) := by
  let A := scalarH1TimeCoordinate (ι := Fin n ⊕ Fin n) g₀
  let Atime := A.comp (ContinuousLinearMap.inl ℝ ℝ _)
  let Astate := A.comp (ContinuousLinearMap.inr ℝ ℝ _)
  let q := fun x t => A (σ x + t, P (f x).val + J (w x t))
  let q₀ := fun t => A (σ₀ + t, P f₀.val + J (w₀ t))
  have hstate : TendstoUniformlyOn
      (fun x t => P (f x).val + J (w x t))
      (fun t => P f₀.val + J (w₀ t)) l (Icc 0 T) :=
    (((P.continuous.tendsto f₀.val).comp hf).tendstoUniformlyOn_const (Icc 0 T)).add
      (J.uniformContinuous.comp_tendstoUniformlyOn hw)
  have hshift := ((Atime.continuous.tendsto σ₀).comp hσ).tendstoUniformlyOn_const (Icc 0 T)
  have htime : TendstoUniformlyOn (fun (_ : X) t => Atime t)
      (fun t => Atime t) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε
  have heq (s t : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) :
      Atime s + Atime t + Astate v = A (s + t, v) := by
    change A (s, 0) + A (t, 0) + A (0, v) = A (s + t, v)
    rw [← map_add, ← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hq : TendstoUniformlyOn q q₀ l (Icc 0 T) := by
    have h := (hshift.add htime).add (Astate.uniformContinuous.comp_tendstoUniformlyOn hstate)
    change TendstoUniformlyOn
      (fun x t => Atime (σ x) + Atime t + Astate (P (f x).val + J (w x t)))
      (fun t => Atime σ₀ + Atime t + Astate (P f₀.val + J (w₀ t))) l (Icc 0 T) at h
    simpa only [heq] using h
  have hq₀ : ContinuousOn q₀ (Icc 0 T) :=
    A.continuous.comp_continuousOn
      ((continuousOn_const.add continuousOn_id).prodMk
        (continuousOn_const.add (J.continuous.comp_continuousOn hw₀)))
  have hcoords (s : ℝ) (v : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) (z : AddCircle (1 : ℝ)) :
      scalarH1PiToContinuous g₀ (A (s, v)) z =
        (fun i => match i with | none => s | some i => scalarH1ToContinuous g₀ (v i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  let E := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ (1 : ℝ))
  let R := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 1)
  let EP := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => E)
  let RP := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => R)
  have hRE (y : TensorHs g₀ 0 0 1) : R (E y) = y := by
    apply TensorHs.ext
    rfl
  have hREP (y : PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) => TensorHs g₀ 0 0 1)) :
      RP (EP y) = y := by
    apply PiLp.ext
    intro i
    exact hRE (y i)
  have hRaw : TendstoUniformlyOn (fun x t => E (alpha (f x) (σ x + t) (w x t)))
      (fun t => E (alpha f₀ (σ₀ + t) (w₀ t))) l (Icc 0 T) := by
    apply AddCircle.tendstoUniformlyOn_scalarHs_composition_of_isCompact_image
      g₀ 0 F hF hS (fun x t => EP (q x t)) (fun t => EP (q₀ t))
      (fun x t => E (alpha (f x) (σ x + t) (w x t)))
      (fun t => E (alpha f₀ (σ₀ + t) (w₀ t)))
      (isCompact_Icc.image_of_continuousOn (EP.continuous.comp_continuousOn hq₀))
      (EP.uniformContinuous.comp_tendstoUniformlyOn hq)
    · intro t ht
      change range (scalarH1PiToContinuous g₀ (RP (EP (q₀ t)))) ⊆ S
      rw [hREP]
      have htime₀ : σ₀ + t ∈ Icc (-ρ) ρ := by
        constructor <;> linarith [ht.1, ht.2]
      exact hcoeff.1 f₀ (σ₀ + t) htime₀ (w₀ t) (hbound₀ t ht)
    · filter_upwards [hgood] with x hx t ht z
      change scalarH1ToContinuous g₀ (R (E (alpha (f x) (σ x + t) (w x t)))) z =
        F (scalarH1PiToContinuous g₀ (RP (EP (q x t))) z)
      rw [hRE, hREP]
      have htimeₓ : σ x + t ∈ Icc (-ρ) ρ := by
        constructor <;> linarith [ht.1, ht.2, hx.1, hx.2.1]
      change scalarH1ToContinuous g₀ (alpha (f x) (σ x + t) (w x t)) z =
        F (scalarH1PiToContinuous g₀ (A (σ x + t, P (f x).val + J (w x t))) z)
      rw [hcoords]
      exact hcoeff.2.1 (f x) (σ x + t) htimeₓ (w x t) (hx.2.2 t ht) z
    · intro t ht z
      change scalarH1ToContinuous g₀ (R (E (alpha f₀ (σ₀ + t) (w₀ t)))) z =
        F (scalarH1PiToContinuous g₀ (RP (EP (q₀ t))) z)
      rw [hRE, hREP]
      have htime₀ : σ₀ + t ∈ Icc (-ρ) ρ := by
        constructor <;> linarith [ht.1, ht.2]
      change scalarH1ToContinuous g₀ (alpha f₀ (σ₀ + t) (w₀ t)) z =
        F (scalarH1PiToContinuous g₀ (A (σ₀ + t, P f₀.val + J (w₀ t))) z)
      rw [hcoords]
      exact hcoeff.2.1 f₀ (σ₀ + t) htime₀ (w₀ t) (hbound₀ t ht) z
  have h := R.uniformContinuous.comp_tendstoUniformlyOn hRaw
  change TendstoUniformlyOn (fun x t => R (E (alpha (f x) (σ x + t) (w x t))))
    (fun t => R (E (alpha f₀ (σ₀ + t) (w₀ t)))) l (Icc 0 T) at h
  simpa only [hRE] using h

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_principalCoefficient_tendsto_top
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ) (f₀ : Metric.closedBall fref δ)
    (w : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (w₀ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hf : Tendsto (fun x => (f x).val) l (𝓝 f₀.val))
    (hw₀ : ContinuousOn w₀ (Icc 0 T))
    (hw : TendstoUniformlyOn w w₀ l (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction)
    (hgood : ∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖w x t‖ ≤ ρ)
    (hσlo : -ρ ≤ σ₀) (hσhi : σ₀ + T ≤ ρ)
    (hbound₀ : ∀ t ∈ Icc 0 T, ‖w₀ t‖ ≤ ρ)
    (aTop : X → Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T))
    (aTop₀ : Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T))
    (haTop : ∀ x, aTop x =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (w x t)))
    (haTop₀ : aTop₀ =ᵐ[timeMeasure T] (fun t => alpha f₀ (σ₀ + t) (w₀ t))) :
    Tendsto aTop l (𝓝 aTop₀) := by
  exact Lp.tendsto_top_of_tendstoUniformlyOn (ae_restrict_mem measurableSet_Icc)
    aTop aTop₀ (fun x t => alpha (f x) (σ x + t) (w x t))
    (fun t => alpha f₀ (σ₀ + t) (w₀ t)) haTop haTop₀
    (reference_shifted_principalCoefficient_tendstoUniformlyOn g₀ T P J σ σ₀ hσ
      fref f f₀ w w₀ hf hw₀ hw F G hF hS alpha reaction hcoeff hgood hσlo hσhi hbound₀)

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_selected_driftCoefficient_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (σ : X → ℝ) (σ₀ : ℝ) (hσ : Tendsto σ l (𝓝 σ₀))
    (fcenter : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (Δ : X → CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (Δ₀ : CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1))
    (hΔ : Tendsto Δ l (𝓝 Δ₀))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ}
    (f : X → Metric.closedBall fref δ) (f₀ : Metric.closedBall fref δ)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (V : X → timeL2
      (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (V₀ : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 + 2 : ℕ) : ℝ) + 1)) T)
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (W₀ : ℝ → CircleHsPi g₀ (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (a : X → timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b : X → timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b₀ : timeL2 (CircleHsPi g₀ (Fin n) (((k + 1 : ℕ) : ℝ) + 2)) T)
    (hV : Tendsto V l (𝓝 V₀))
    (hW₀ : ContinuousOn W₀ (Icc 0 T))
    (hW : TendstoUniformlyOn W W₀ l (Icc 0 T)) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let B := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith :
        ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, R (fcenter + Δ x) = (f x).val) → R (fcenter + Δ₀) = f₀.val →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => B (V x t)) →
    W₀ =ᵐ[timeMeasure T] (fun t => B (V₀ t)) →
    (∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    -ρ ≤ σ₀ → σ₀ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖L (W₀ t)‖ ≤ ρ) →
    (∀ᶠ x in l, (fun t => AH (a x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (fun t => AH (a₀ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f₀ (σ₀ + t) (L (W₀ t))) →
    (∀ᶠ x in l, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (L (W x t)))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₀ t))
      =ᵐ[timeMeasure T] (fun t => reaction f₀ (σ₀ + t) (L (W₀ t))) →
    let N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let D := (((k + 2 : ℕ) : ℝ) • N).compLpL 2 (timeMeasure T)
    Tendsto (fun x => D (a x)) l (𝓝 (D a₀)) ∧
      (∀ x, D (a x) =ᵐ[timeMeasure T]
        (fun t => ((k + 2 : ℕ) : ℝ) • N (a x t))) ∧
      D a₀ =ᵐ[timeMeasure T] (fun t => ((k + 2 : ℕ) : ℝ) • N (a₀ t)) := by
  intro R L B K₀ P J AH hcoeff hf hf₀ hWV hWV₀ hgood hσlo hσhi hbound₀ ha ha₀ hb hb₀ N D
  have hPair := reference_selected_coefficients_tendsto_timeShift
    g₀ k T σ σ₀ hσ fcenter Δ Δ₀ hΔ fref f f₀ F G hF hG hS alpha reaction
    V V₀ W W₀ a a₀ b b₀ hV hW₀ hW
    hcoeff hf hf₀ hWV hWV₀ hgood hσlo hσhi hbound₀ ha ha₀ hb hb₀
  have haT : Tendsto a l (𝓝 a₀) :=
    (continuous_fst.tendsto (a₀, b₀)).comp hPair
  refine ⟨(D.continuous.tendsto a₀).comp haT, ?_, ?_⟩
  · intro x
    exact (((k + 2 : ℕ) : ℝ) • N).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (a x)
  · exact (((k + 2 : ℕ) : ℝ) • N).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) a₀

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_selected_initial_coefficients_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (hf : Tendsto (fun x => (f x).val) l (𝓝 (f x₀).val))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (V : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
    (hV : Tendsto V l (𝓝 (V x₀)))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW₀ : ContinuousOn (W x₀) (Icc 0 T))
    (hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) →
    (∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    -ρ ≤ σ x₀ → σ x₀ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖W x₀ t‖ ≤ ρ) →
    (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t)))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) →
    Tendsto (fun x => (a₂ x, b₂ x)) l (𝓝 (a₂ x₀, b₂ x₀)) := by
  intro K K₀ P J AH C Cpi hcoeff hWV hgood hσlo hσhi hbound₀ ha₂ hb₂
  let A1 := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hCA (v : TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) : C (A1 v) = AH v := by
    have h := tensorHsCongrL_incl (g := g₀) (r := 0) (s := 0)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (rfl : ((1 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    simpa only [C, A1, AH, ContinuousLinearMap.comp_apply,
      tensorHsCongrL_refl, ContinuousLinearMap.id_apply] using congrArg (fun L => L v) h
  have hCpiA (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
      Cpi (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A1) v) =
        ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) v := by
    apply PiLp.ext
    intro i
    change C (A1 (v i)) = AH (v i)
    exact hCA (v i)
  have ha₂real (x : X) : (fun t => A1 (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (W x t)) := by
    filter_upwards [ha₂ x] with t ht
    apply (tensorHsCongr g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).injective
    change C (A1 (a₂ x t)) = C (alpha (f x) (σ x + t) (W x t))
    rw [hCA]
    exact ht
  have hb₂real (x : X) :
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A1) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (W x t)) := by
    filter_upwards [hb₂ x] with t ht
    apply Cpi.injective
    rw [hCpiA]
    exact ht
  let R := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
  let L := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 + 1 : ℕ) : ℝ) + 1)
  let N₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 + 2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  let B₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 + 1 : ℕ) : ℝ) + 1 ≤ ((0 + 2 : ℕ) : ℝ) + 1)
  let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 1)
  let NP₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
  let A₀ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
  let AP₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₀)
  let AP₁ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A1)
  let VN := fun x => N₃.compLpL 2 (timeMeasure T) (V x)
  let aN := fun x => N₂.compLpL 2 (timeMeasure T) (a₂ x)
  let bN := fun x => NP₂.compLpL 2 (timeMeasure T) (b₂ x)
  have hRN (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) :
      R (N₃ v) = v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hL (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) : L v = v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hA₀N (v : TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) :
      A₀ (N₂ v) = A1 v := by
    apply TensorHs.ext
    rfl
  have hAP₀N (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
      AP₀ (NP₂ v) = AP₁ v := by
    apply PiLp.ext
    intro i
    exact hA₀N (v i)
  have hfN : Tendsto (fun x => N₃ (f x).val) l (𝓝 (N₃ (f x₀).val)) :=
    (N₃.continuous.tendsto (f x₀).val).comp hf
  have hVN : Tendsto VN l (𝓝 (VN x₀)) :=
    ((N₃.compLpL 2 (timeMeasure T)).continuous.tendsto (V x₀)).comp hV
  have hWN (x : X) : W x =ᵐ[timeMeasure T] fun t => B₃ (VN x t) := by
    filter_upwards [hWV x, N₃.coeFn_compLpL (V x)] with t hwt hnt
    change VN x t = N₃ (V x t) at hnt
    rw [hwt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have haN (x : X) : (fun t => A₀ (aN x t)) =ᵐ[timeMeasure T]
      fun t => alpha (f x) (σ x + t) (L (W x t)) := by
    filter_upwards [N₂.coeFn_compLpL (a₂ x), ha₂real x] with t hnt hat
    change aN x t = N₂ (a₂ x t) at hnt
    rw [hnt, hA₀N, hL]
    exact hat
  have hbN (x : X) : (fun t => AP₀ (bN x t)) =ᵐ[timeMeasure T]
      fun t => reaction (f x) (σ x + t) (L (W x t)) := by
    filter_upwards [NP₂.coeFn_compLpL (b₂ x), hb₂real x] with t hnt hbt
    change bN x t = NP₂ (b₂ x t) at hnt
    rw [hnt, hAP₀N, hL]
    exact hbt
  have hpairN := reference_selected_h2_coefficients_tendsto_timeShift
    g₀ T σ (σ x₀) hσ 0 (fun x => N₃ (f x).val) (N₃ (f x₀).val) hfN fref f (f x₀)
    F G hF hG hS alpha reaction VN (VN x₀) W (W x₀)
    aN (aN x₀) bN (bN x₀) hVN hW₀ hW hcoeff
    (by intro x; simpa only [zero_add] using hRN (f x).val)
    (by simpa only [zero_add] using hRN (f x₀).val) hWN (hWN x₀)
    (by
      change ∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ
      simpa only [hL] using hgood)
    hσlo hσhi (by
      change ∀ t ∈ Icc 0 T, ‖L (W x₀ t)‖ ≤ ρ
      simpa only [hL] using hbound₀)
    (Eventually.of_forall haN) (haN x₀) (Eventually.of_forall hbN) (hbN x₀)
  have haNlim : Tendsto aN l (𝓝 (aN x₀)) := (continuous_fst.tendsto _).comp hpairN
  have hbNlim : Tendsto bN l (𝓝 (bN x₀)) := (continuous_snd.tendsto _).comp hpairN
  let Q₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
  let QP₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q₂)
  have haReturn (x : X) : Q₂.compLpL 2 (timeMeasure T) (aN x) = a₂ x := by
    apply Lp.ext
    filter_upwards [Q₂.coeFn_compLpL (aN x), N₂.coeFn_compLpL (a₂ x)] with t hqt hnt
    change aN x t = N₂ (a₂ x t) at hnt
    rw [hqt, hnt]
    apply TensorHs.ext
    rfl
  have ha₂lim : Tendsto a₂ l (𝓝 (a₂ x₀)) := by
    have h := ((Q₂.compLpL 2 (timeMeasure T)).continuous.tendsto (aN x₀)).comp haNlim
    change Tendsto (fun x => Q₂.compLpL 2 (timeMeasure T) (aN x)) l
      (𝓝 (Q₂.compLpL 2 (timeMeasure T) (aN x₀))) at h
    simpa only [haReturn] using h
  have hbReturn (x : X) : QP₂.compLpL 2 (timeMeasure T) (bN x) = b₂ x := by
    apply Lp.ext
    filter_upwards [QP₂.coeFn_compLpL (bN x), NP₂.coeFn_compLpL (b₂ x)] with t hqt hnt
    change bN x t = NP₂ (b₂ x t) at hnt
    rw [hqt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)) := by
    have h := ((QP₂.compLpL 2 (timeMeasure T)).continuous.tendsto (bN x₀)).comp hbNlim
    change Tendsto (fun x => QP₂.compLpL 2 (timeMeasure T) (bN x)) l
      (𝓝 (QP₂.compLpL 2 (timeMeasure T) (bN x₀))) at h
    simpa only [hbReturn] using h
  exact ha₂lim.prodMk_nhds hb₂lim

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)
open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_high_principal_continuous_representative
    {n : ℕ}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T σ : ℝ)
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (fHigh : CircleHsPi g (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (W : ℝ → CircleHsPi g (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g).comp K₀
    let J := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ)))
    let q := fun t => E (AddCircle.scalarHsTimeFirstJet g (k + 1 + 1)
      (σ + t, fHigh + W t))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A)
    referenceCircleSymmetricCoefficientFacts g fref P J F G S δ ρ alpha reaction →
    R fHigh = f.val → -ρ ≤ σ → σ + T ≤ ρ →
    (∀ t ∈ Icc 0 T, ‖L (W t)‖ ≤ ρ) →
    ContinuousOn q (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (Q (q t))) ⊆ S) ∧
      ∃ a : ℝ → TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1),
        ContinuousOn a (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) = alpha f (σ + t) (L (W t))) ∧
        ∀ t ∈ Icc 0 T, ∀ z, scalarH1ToContinuous g (A (a t)) z =
          F (scalarH1PiToContinuous g (Q (q t)) z) := by
  intro R L K₀ P J E q A Q hcoeff hf hσlo hσhi hbound
  have hq : ContinuousOn q (Icc 0 T) :=
    E.continuous.comp_continuousOn
      ((AddCircle.scalarHsTimeFirstJet g (k + 1 + 1)).continuous.comp_continuousOn
        ((continuousOn_const.add continuousOn_id).prodMk (continuousOn_const.add hW)))
  have hproject (t : ℝ) : Q (q t) =
      scalarH1TimeCoordinate g (σ + t, P f.val + J (L (W t))) := by
    have h := reference_scalarHsTimeFirstJet_projection g (k + 1 + 1) (by omega)
      (σ + t) fHigh (W t) f.val (L (W t)) hf rfl
    refine Eq.trans ?_ h
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : σ + t ∈ Icc (-ρ) ρ := by
    constructor <;> linarith [ht.1, ht.2]
  have hRange : ∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (Q (q t))) ⊆ S := by
    intro t ht
    rw [hproject]
    exact hcoeff.1 f (σ + t) (htime t ht) (L (W t)) (hbound t ht)
  obtain ⟨ac, hac, heval⟩ := AddCircle.exists_continuousOn_scalarHs_composition
    g (k + 1) F hF hS q hq hRange
  refine ⟨hq, hRange, ac, hac, ?_, heval⟩
  intro t ht
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro z
  rw [heval t ht z, hproject]
  have hcoords : scalarH1PiToContinuous g
      (scalarH1TimeCoordinate g (σ + t, P f.val + J (L (W t)))) z =
      (fun i => match i with
        | none => σ + t
        | some i => scalarH1ToContinuous g ((P f.val) i + (J (L (W t))) i) z) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g _ _
    | some i => rfl
  rw [hcoords]
  exact (hcoeff.2.1 f (σ + t) (htime t ht) (L (W t)) (hbound t ht) z).symm

end DifferentialGeometry.Analysis.Parabolic
end


noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)
open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_shifted_high_principal_exists_tendsto_top
    {X : Type*} {n : ℕ} {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (fHigh : X → CircleHsPi g (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (W : X → ℝ → CircleHsPi g (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    {sA : ℝ} (hA : ((k + 1 : ℕ) : ℝ) + 1 ≤ sA)
    (aHigh : X → timeL2 (TensorHs g 0 0 sA) T)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g).comp K₀
    let J := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith : (1 : ℝ) ≤ sA)
    let C := tensorHsInclusion (g := g) (r := 0) (s := 0)
      hA
    referenceCircleSymmetricCoefficientFacts g fref P J F G S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    (∀ x, (fun t => AH (aHigh x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    ∃ aTop : X → Lp (TensorHs g 0 0 (((k + 1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T),
      (∀ x, aTop x =ᵐ[timeMeasure T] fun t => C (aHigh x t)) ∧
      Tendsto aTop l (𝓝 (aTop x₀)) := by
  classical
  intro R L K₀ P J AH C hcoeff hf hgood haHigh
  let E := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 : ℕ) : ℝ)))
  let q := fun x t => E (AddCircle.scalarHsTimeFirstJet g (k + 1 + 1)
    (σ x + t, fHigh x + W x t))
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A)
  have hrep (x : X) := reference_high_principal_continuous_representative
    g k T (σ x) fref (f x) (fHigh x) (W x) (hW x) F G hF hS
    alpha reaction hcoeff (hf x) (hgood x).1 (hgood x).2.1 (hgood x).2.2
  have hq (x : X) : ContinuousOn (q x) (Icc 0 T) := (hrep x).1
  have hRange (x : X) : ∀ t ∈ Icc 0 T,
      range (scalarH1PiToContinuous g (Q (q x t))) ⊆ S := (hrep x).2.1
  choose ac hac hactual heval using fun x => (hrep x).2.2
  let Hjet := E.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g (k + 1 + 1))
  let Atime := Hjet.comp (ContinuousLinearMap.inl ℝ ℝ _)
  let Astate := Hjet.comp (ContinuousLinearMap.inr ℝ ℝ _)
  have hstate : TendstoUniformlyOn (fun x t => fHigh x + W x t)
      (fun t => fHigh x₀ + W x₀ t) l (Icc 0 T) :=
    (hfHigh.tendstoUniformlyOn_const (Icc 0 T)).add hWlim
  have hshift := ((Atime.continuous.tendsto (σ x₀)).comp hσ).tendstoUniformlyOn_const (Icc 0 T)
  have htime : TendstoUniformlyOn (fun (_ : X) t => Atime t)
      (fun t => Atime t) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε
  have heq (s t : ℝ)
      (v : CircleHsPi g (Fin n) (((k + 1 + 1 : ℕ) : ℝ) + 1)) :
      Atime s + Atime t + Astate v = Hjet (s + t, v) := by
    change Hjet (s, 0) + Hjet (t, 0) + Hjet (0, v) = Hjet (s + t, v)
    rw [← map_add, ← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hqlim : TendstoUniformlyOn q (q x₀) l (Icc 0 T) := by
    have h := (hshift.add htime).add (Astate.uniformContinuous.comp_tendstoUniformlyOn hstate)
    change TendstoUniformlyOn
      (fun x t => Atime (σ x) + Atime t + Astate (fHigh x + W x t))
      (fun t => Atime (σ x₀) + Atime t + Astate (fHigh x₀ + W x₀ t)) l (Icc 0 T) at h
    simpa only [heq, Hjet, ContinuousLinearMap.comp_apply, q] using h
  have haclim : TendstoUniformlyOn ac (ac x₀) l (Icc 0 T) :=
    AddCircle.tendstoUniformlyOn_scalarHs_composition_of_isCompact_image
      g (k + 1) F hF hS q (q x₀) ac (ac x₀)
      (isCompact_Icc.image_of_continuousOn (hq x₀)) hqlim (hRange x₀)
      (Eventually.of_forall heval) (heval x₀)
  have hmem (x : X) : MemLp (ac x) ∞ (timeMeasure T) :=
    (hac x).memLp_top_of_isCompact isCompact_Icc measurableSet_Icc
  let aTop := fun x => (hmem x).toLp (ac x)
  have htop (x : X) : aTop x =ᵐ[timeMeasure T] ac x := (hmem x).coeFn_toLp
  refine ⟨aTop, ?_, ?_⟩
  · intro x
    filter_upwards [htop x, haHigh x, ae_restrict_mem measurableSet_Icc] with t hat ht htt
    rw [hat]
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    change A (ac x t) = A (C (aHigh x t))
    rw [hactual x t htt, ← ht]
    apply TensorHs.ext
    rfl
  · exact Lp.tendsto_top_of_tendstoUniformlyOn (ae_restrict_mem measurableSet_Icc)
      aTop (aTop x₀) ac (ac x₀) htop (htop x₀) haclim

end DifferentialGeometry.Analysis.Parabolic
end


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_successor_principal_exists_tendsto_top
    {X : Type*} {n : ℕ} {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (fHigh : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (W : X → ℝ → CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (aHigh : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g).comp K₀
    let J := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P J F G S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    (∀ x, (fun t => A (aHigh x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    ∃ aTop : X → Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) ∞ (timeMeasure T),
      (∀ x, aTop x =ᵐ[timeMeasure T] aHigh x) ∧
      Tendsto aTop l (𝓝 (aTop x₀)) := by
  intro R L K₀ P J A hcoeff hf hgood haHigh
  let E := circleHsPiInclusion g (Fin n)
    (by push_cast; linarith :
      ((k + 1 + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let B := circleHsPiInclusion g (Fin n)
    (by push_cast; linarith :
      ((k + 1 + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ) + 2)
  let Rg := circleHsPiInclusion g (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 1 + 1 : ℕ) : ℝ) + 1)
  let Lg := circleHsPiInclusion g (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 1 + 1 : ℕ) : ℝ) + 1)
  have hRB (v : CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2)) :
      Rg (B v) = R v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hLE (v : CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2)) :
      Lg (E v) = L v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hfg : Tendsto (fun x => B (fHigh x)) l (𝓝 (B (fHigh x₀))) :=
    (B.continuous.tendsto (fHigh x₀)).comp hfHigh
  have hWg : TendstoUniformlyOn (fun x t => E (W x t))
      (fun t => E (W x₀ t)) l (Icc 0 T) :=
    E.uniformContinuous.comp_tendstoUniformlyOn hWlim
  obtain ⟨aRaw, haRaw, hRawlim⟩ :=
    reference_shifted_high_principal_exists_tendsto_top
      g (k + 1) T x₀ σ hσ fref f (fun x => B (fHigh x)) (fun x t => E (W x t))
      (fun x => E.continuous.comp_continuousOn (hW x)) hfg hWg
      (by push_cast; linarith : ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
      aHigh F G hF hS alpha reaction hcoeff
      (fun x => (hRB (fHigh x)).trans (hf x))
      (fun x => ⟨(hgood x).1, (hgood x).2.1, fun t ht => by
        change ‖Lg (E (W x t))‖ ≤ ρ
        rw [hLE]
        exact (hgood x).2.2 t ht⟩)
      (fun x => by
        filter_upwards [haHigh x] with t ht
        change A (aHigh x t) = alpha (f x) (σ x + t) (Lg (E (W x t)))
        rw [hLE]
        exact ht)
  let C := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) + 1)
  let aTop := fun x => C.compLpL ∞ (timeMeasure T) (aRaw x)
  refine ⟨aTop, ?_, ?_⟩
  · intro x
    filter_upwards [C.coeFn_compLpL (aRaw x), haRaw x] with t hct hat
    change C.compLpL ∞ (timeMeasure T) (aRaw x) t = aHigh x t
    rw [hct, hat]
    apply TensorHs.ext
    rfl
  · exact ((C.compLpL ∞ (timeMeasure T)).continuous.tendsto (aRaw x₀)).comp hRawlim

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_successor_principal_from_projection
    {X : Type*} {n : ℕ} {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (fHigh : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ))
    (Wnext : X → ℝ → CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2))
    (hWnext : ∀ x, ContinuousOn (Wnext x) (Icc 0 T))
    (hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)))
    (hWnextlim : TendstoUniformlyOn Wnext (Wnext x₀) l (Icc 0 T))
    (aHigh : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let Aphys := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith [hk] :
        (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ F G S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    (∀ x, (fun t => Aphys (aHigh x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (∀ x t, t ∈ Icc 0 T →
      ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
        2 (fun _ : Fin n => K) (Wnext x t) = W x t) →
    ∃ aTop : X → Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) ∞ (timeMeasure T),
      (∀ x, aTop x =ᵐ[timeMeasure T] aHigh x) ∧
      Tendsto aTop l (𝓝 (aTop x₀)) := by
  intro K R L K₀ P₀ J₀ Aphys hcoeff hf hgood haPhysical hWproject
  let Ln := circleHsPiInclusion g (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 2)
  have hLn (x : X) (t : ℝ) (ht : t ∈ Icc 0 T) : Ln (Wnext x t) = L (W x t) := by
    rw [← hWproject x t ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact reference_successor_principal_exists_tendsto_top
    g k T x₀ σ hσ fref f fHigh Wnext hWnext hfHigh hWnextlim aHigh
    F G hF hS alpha reaction hcoeff hf
    (fun x => ⟨(hgood x).1, (hgood x).2.1, fun t ht => by
      change ‖Ln (Wnext x t)‖ ≤ ρ
      rw [hLn x t ht]
      exact (hgood x).2.2 t ht⟩)
    (fun x => by
      filter_upwards [haPhysical x, ae_restrict_mem measurableSet_Icc] with t ht htt
      change Aphys (aHigh x t) = alpha (f x) (σ x + t) (Ln (Wnext x t))
      rw [hLn x t htt]
      exact ht)

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev QuasiLinear


private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_coefficient_representatives_timeShift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) :
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    W =ᵐ[timeMeasure T] (fun t => B (field t)) →
    -ρ ≤ σ → σ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) →
    ∃ (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
      (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
      (aTop₁ : Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T)),
      (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T] (fun t => alpha f (σ + t) (W t)) ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t))
        =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (W t)) ∧
      aTop₁ =ᵐ[timeMeasure T] (fun t => alpha f (σ + t) (W t)) ∧
      (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T] aTop₁ := by
  intro B K₀ P J A₂ field hcoeff hWV hσlo hσhi hbound
  obtain ⟨aRaw, bRaw, haRaw, hbRaw⟩ := reference_exists_h2_coefficients_timeShift
    g₀ T σ fref f field W hW F G hF hG hS alpha reaction
    hcoeff hWV hσlo hσhi hbound
  let N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ))
  let NP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N)
  let a₂ := N.compLpL 2 (timeMeasure T) aRaw
  let b₂ := NP.compLpL 2 (timeMeasure T) bRaw
  have ha₂ : (fun t => A₂ (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => alpha f (σ + t) (W t)) := by
    filter_upwards [N.coeFn_compLpL aRaw, haRaw] with t ht hraw
    change a₂ t = N (aRaw t) at ht
    rw [ht]
    refine Eq.trans ?_ hraw
    apply TensorHs.ext
    rfl
  have hb₂ : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t))
      =ᵐ[timeMeasure T] (fun t => reaction f (σ + t) (W t)) := by
    filter_upwards [NP.coeFn_compLpL bRaw, hbRaw] with t ht hraw
    change b₂ t = NP (bRaw t) at ht
    rw [ht]
    refine Eq.trans ?_ hraw
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have ha := (reference_shifted_coefficients_continuousOn
    g₀ T σ fref f P J W hW F G hF hG hS alpha reaction
    hcoeff hσlo hσhi hbound).1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hmem : MemLp (fun t => alpha f (σ + t) (W t)) ∞ (timeMeasure T) := by
    apply memLp_top_of_bound (memLp_of_continuousOn ha).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    exact hC t ht
  let aTop₁ := hmem.toLp (fun t => alpha f (σ + t) (W t))
  have haTop₁ : aTop₁ =ᵐ[timeMeasure T] (fun t => alpha f (σ + t) (W t)) :=
    hmem.coeFn_toLp
  exact ⟨a₂, b₂, aTop₁, ha₂, hb₂, haTop₁, ha₂.trans haTop₁.symm⟩

end DifferentialGeometry.Analysis.Parabolic

end
