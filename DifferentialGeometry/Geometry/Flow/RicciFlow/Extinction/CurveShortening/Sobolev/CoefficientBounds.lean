import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private ScalarVectorTimeCoefficients.diffusion ScalarVectorTimeCoefficients.diffusionLipschitz ScalarVectorTimeCoefficients.diffusion_eval ScalarVectorTimeCoefficients.diffusion_lipschitz ScalarVectorTimeCoefficients.radius ScalarVectorTimeCoefficients.radius_pos ScalarVectorTimeCoefficients.range_mem ScalarVectorTimeCoefficients.reaction ScalarVectorTimeCoefficients.reaction_eval ScalarVectorTimeCoefficients.reaction_lipschitz from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private coordinateMultiplication CircleHsPi circleHsPiInclusion extendClosedBall extendClosedBall_apply circleHsPiCongr circleHsPiCongr_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private firstJetCoordinates geometric_coefficients_contDiffOn circleDerivativeH1 circleFirstJet ambientCoordinateCc ambientSobolev tensorHsCongrL_ccTensorToHs ambientFirstJet ambientFirstJet_range ScalarVectorTimeCoefficients ambientCoefficients initial_diffusion_coefficients from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circleFirstJet_eq_normalized_firstJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : CircleHsPi g ι (1 + 1)) :
    circleFirstJet g u =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
        (AddCircle.firstJetHs g 1
          (circleHsPiCongr g ι (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1) u)) := by
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    apply TensorHs.ext
    change (u i).coeff =
      (tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)
        (u i)).coeff
    rw [hcongr]
  | inr i =>
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
      ((AddCircle.parameterDerivativeHs g 1)
        (tensorHsCongrL g 0 0
          (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1) (u i)))).coeff = _
    rw [hcongr]
    rfl

private theorem circle_firstJetHs_normalized
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) :
    circleFirstJet g
      (circleHsPiCongr g ι (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) u) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) (AddCircle.firstJetHs g 1 u) := by
  have hc {a b : ℝ} (h : a = b) (v : CircleHsPi g ι a) :
      circleHsPiCongr g ι h.symm (circleHsPiCongr g ι h v) = v := by
    cases h
    rfl
  rw [circleFirstJet_eq_normalized_firstJetHs, hc]

private theorem circle_timeL2_h2_composition
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (u : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T)
    (w : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 1) (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let q := fun t => scalarH1TimeCoordinate g (t, J (K f₀ + w t))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
      (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a := by
  intro J K q hwu hRange hEval
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let u₂ := E.compLpL 2 (timeMeasure T) u
  let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hK₂ (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) : K₂ (E v) = K v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
    rw [hcongr]
  have hw₂ : w =ᵐ[timeMeasure T] (fun t => K₂ (u₂ t)) := by
    filter_upwards [hwu, E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht he
    change u₂ t = E (u t) at he
    rw [he, hK₂]
    exact ht
  have hq (t : ℝ) :
      scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))) = q t := by
    rw [hK₂, ← circle_firstJetHs_normalized]
    rfl
  apply AddCircle.exists_timeL2_scalarH2_composition_firstJet g T (E f₀) u₂ w hw
    F hF hS a ha hw₂
  · intro t ht
    change range (scalarH1PiToContinuous g
      (scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))))) ⊆ S
    rw [hq]
    exact hRange t ht
  · filter_upwards [hEval] with t ht
    change ∀ x, scalarH1ToContinuous g (a t) x = F (scalarH1PiToContinuous g
      (scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t)))) x)
    rw [hq]
    exact ht

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_diffusion_h2
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (T : ℝ) (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
      (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) := by
  classical
  intro J K hu₀ hwu hbound
  let a := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : a t = (ScalarVectorTimeCoefficients.diffusion C) t (z t) :=
    extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)) (z t).2
  have ha : ContinuousOn a (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((ScalarVectorTimeCoefficients.diffusion_lipschitz C).continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  apply circle_timeL2_h2_composition g₀ T f₀ field w hw F hF hS a
    (memLp_of_continuousOn ha).aestronglyMeasurable hwu
  · intro t ht
    have h := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    intro x
    change scalarH1ToContinuous g₀ (a t) x = F
      (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [map_add, ← hu₀, he ⟨t, htt⟩, (ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨htt.1, htt.2.trans hT⟩]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
      rfl

private theorem scalarVectorTimeCoefficients_diffusion_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (k : ℕ)
    (T : ℝ) (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (field : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
    (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) →
    ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
        (aHigh t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K L J A hu₀ hwu hbound hactual
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  apply AddCircle.exists_timeL2_scalarHs_composition_firstJet g₀ k T f₀ field w hw
    F hF hS a ha hwu
  · intro t ht
    have h := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht, hactual] with t htt hat
    intro x
    change scalarH1ToContinuous g₀ (A (a t)) x =
      F (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [hat, extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))
      (z ⟨t, htt⟩).2, (ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨htt.1, htt.2.trans hT⟩]
    rw [map_add, ← hu₀]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]

private theorem scalarVectorTimeCoefficients_reaction_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (j : Fin n)
    (hF : ContDiffOn ℝ ∞ (fun z => G z j) S) (hS : IsOpen S) (k : ℕ)
    (T : ℝ) (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (field : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
    (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)) j) →
    ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
        (aHigh t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K L J A hu₀ hwu hbound hactual
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  apply AddCircle.exists_timeL2_scalarHs_composition_firstJet g₀ k T f₀ field w hw
    (fun z => G z j) hF hS a ha hwu
  · intro t ht
    have h := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht, hactual] with t htt hat
    intro x
    change scalarH1ToContinuous g₀ (A (a t)) x =
      (fun z => G z j) (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [hat, extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t))
      (z ⟨t, htt⟩).2, (ScalarVectorTimeCoefficients.reaction_eval C) t ⟨htt.1, htt.2.trans hT⟩]
    rw [map_add, ← hu₀]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambientFirstJet_eq_initialJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ambientFirstJet c₀ g e he = J (K f₀) := by
  intro g₀ f₀ J K
  change circleFirstJet g₀ _ = circleFirstJet g₀ _
  congr 1
  apply PiLp.ext
  intro i
  change ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i) =
    tensorHsCongrL g₀ 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
      (tensorHsInclusion
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (ccTensorToHs g₀ 0 (((1 : ℕ) : ℝ) + 2) (ambientCoordinateCc c₀ g e he i)))
  rw [tensorHsInclusion_ccTensorToHs, tensorHsCongrL_ccTensorToHs]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambientFirstJet_eq_higher_initialJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (k : ℕ) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((k + 2 : ℕ) : ℝ) + 1)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    ambientFirstJet c₀ g e he = J (K f₀) := by
  intro g₀ f₀ K L J
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1)
      (ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i)) =
      tensorHsInclusion
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
        (tensorHsInclusion (by linarith : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
          (tensorHsInclusion
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1)
        (ccTensorToHs g₀ 0 (((k + 2 : ℕ) : ℝ) + 1) (ambientCoordinateCc c₀ g e he i))))
    simp only [tensorHsInclusion_ccTensorToHs]
  | inr i =>
    change circleDerivativeH1 g₀
      (ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i)) =
      tensorHsInclusion
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
        (AddCircle.parameterDerivativeHs g₀ (k + 1)
          (tensorHsInclusion
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1)
            (ccTensorToHs g₀ 0 (((k + 2 : ℕ) : ℝ) + 1)
          (ambientCoordinateCc c₀ g e he i))))
    simp only [circleDerivativeH1, ContinuousLinearMap.comp_apply,
      tensorHsInclusion_ccTensorToHs, tensorHsCongrL_ccTensorToHs,
      AddCircle.parameterDerivativeHs_apply_ccTensorToHs]

private theorem ambient_diffusion_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (k : ℕ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn w (Icc 0 T) →
      ∀ a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1),
      AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (fun t => A (a t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) →
      ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
        (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
          (aHigh t)) =ᵐ[timeMeasure T] a := by
  intro C g₀ K L J A T hT field w hw a ha hwu hbound hactual
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_diffusion_higher_order g₀ _ _ _ _ C
    hF hS k T hT f₀ field w hw a ha
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k) hwu hbound hactual

private theorem ambient_reaction_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (j : Fin n) (k : ℕ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn w (Icc 0 T) →
      ∀ a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1),
      AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (fun t => A (a t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)) j) →
      ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
        (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
          (aHigh t)) =ᵐ[timeMeasure T] a := by
  intro C g₀ K L J A T hT field w hw a ha hwu hbound hactual
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, _, hG'⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_reaction_higher_order g₀ _ _ _ _ C j
    (contDiffOn_pi.mp hG' j) hS k T hT f₀ field w hw a ha
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k) hwu hbound hactual

private theorem ambient_diffusion_h2
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))) := by
  intro C g₀ J K T hT field w hw hwu hbound
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨a₂, ha₂⟩ := scalarVectorTimeCoefficients_diffusion_h2 g₀ _ _ _ _ C
    hF hS T hT f₀ field w hw (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound
  refine ⟨a₂, ?_⟩
  filter_upwards [ha₂] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hc : tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =
      tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) := by
    apply TensorHs.ext
    rw [hcongr]
    rfl
  rw [← hc, htt]

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
open DifferentialGeometry.Geometry.Curvature
variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_timeCoordinate_firstJet_h3_projection
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (t : ℝ) (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) :
    let E := (circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 2))
      (AddCircle.scalarHsTimeCoordinate g 2 (t, AddCircle.firstJetHs g 2 (E v))) =
      scalarH1TimeCoordinate g (t, J (K v)) := by
  intro E J K
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  rw [AddCircle.tensorHsInclusion_scalarHsTimeCoordinate]
  congr 1
  apply Prod.ext
  · rfl
  · let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    have hK₂ : K₂ (E v) = K v := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      change (tensorHsCongrL g 0 0
        (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
      rw [hcongr]
    have hjet := congrArg (fun A => A (E v))
      (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := ι) g (by decide : 1 ≤ 2))
    change AddCircle.firstJetHs g 1 (K₂ (E v)) = _ at hjet
    rw [hK₂] at hjet
    have hnormalized : J (K v) = L (AddCircle.firstJetHs g 1 (K v)) :=
      circle_firstJetHs_normalized g (K v)
    rw [hnormalized, hjet]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl

private theorem continuousOn_circle_timeCoordinate_firstJet_h3
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let E := (circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ContinuousOn (fun t => AddCircle.scalarHsTimeCoordinate g 2
      (t, AddCircle.firstJetHs g 2 (E (f₀ + W t)))) (Icc 0 T) := by
  intro E
  exact (AddCircle.scalarHsTimeCoordinate g 2).continuous.comp_continuousOn
    (continuousOn_id.prodMk ((AddCircle.firstJetHs g 2).continuous.comp_continuousOn
      (E.continuous.comp_continuousOn (continuousOn_const.add hW))))

private theorem circle_exists_continuousOn_h2_composition_of_h3
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 1) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let q := fun t => scalarH1TimeCoordinate g (t, J (K (f₀ + W t)))
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ t ∈ Icc 0 T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ a₂ : ℝ → TensorHs g 0 0 2, ContinuousOn a₂ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) = a t := by
  intro J K q hRange hEval
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let V := fun t => AddCircle.scalarHsTimeCoordinate g 2
    (t, AddCircle.firstJetHs g 2 (E (f₀ + W t)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))
  have hV : ContinuousOn V (Icc 0 T) :=
    continuousOn_circle_timeCoordinate_firstJet_h3 g f₀ W hW
  have hq (t : ℝ) : P (V t) = q t :=
    circle_timeCoordinate_firstJet_h3_projection g t (f₀ + W t)
  have hRangeV (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g (P (V t))) ⊆ S := by
    rw [hq]
    exact hRange t ht
  obtain ⟨a₂, ha₂, hEval₂⟩ :=
    AddCircle.exists_continuousOn_scalarH2_composition g F hF hS V hV hRangeV
  refine ⟨a₂, ha₂, ?_⟩
  intro t ht
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro x
  exact (hEval₂ t ht x).trans (by rw [hq]; exact (hEval t ht x).symm)

private theorem scalarVectorTimeCoefficients_continuousOn_h2
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {T : ℝ} (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    u₀ = J (K f₀) →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
      (∀ t ∈ Icc 0 T, (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖a₂ t‖ + ‖b₂ t‖ ≤ B := by
  classical
  intro J K hu₀ hbound
  let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K (f₀ + W t)))
  let a := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))
  let b := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (K (W t)), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hRange (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g₀ (q t)) ⊆ S := by
    have h := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩ (J (K (W t))) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K (f₀ + W t))))) ⊆ S
    rw [map_add, map_add, ← hu₀]
    simpa only [zero_add] using h
  have hcoord (t : ℝ) (x : AddCircle (1 : ℝ)) :
      (fun i : Option (Fin n ⊕ Fin n) => match i with
        | none => 0 + t
        | some j => scalarH1ToContinuous g₀ (u₀ j + J (K (W t)) j) x) =
      scalarH1PiToContinuous g₀ (q t) x := by
    funext i
    cases i with
    | none => simp only [q, scalarH1TimeCoordinate_eval_none, zero_add]
    | some j =>
      simp only [q, map_add, ← hu₀, scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
  have haEval (t : ℝ) (ht : t ∈ Icc 0 T) (x : AddCircle (1 : ℝ)) :
      scalarH1ToContinuous g₀ (a t) x = F (scalarH1PiToContinuous g₀ (q t) x) := by
    rw [show a t = (ScalarVectorTimeCoefficients.diffusion C) t (z ⟨t, ht⟩) from
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))) (z ⟨t, ht⟩).2]
    rw [(ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    congr 1
    funext i
    exact congrFun (hcoord t x) i
  have hbEval (j : Fin n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : AddCircle (1 : ℝ)) :
      scalarH1ToContinuous g₀ (b t j) x = G (scalarH1PiToContinuous g₀ (q t) x) j := by
    rw [show b t = (ScalarVectorTimeCoefficients.reaction C) t (z ⟨t, ht⟩) from
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))) (z ⟨t, ht⟩).2]
    rw [(ScalarVectorTimeCoefficients.reaction_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    congr 2
    funext i
    exact congrFun (hcoord t x) i
  obtain ⟨a₂, ha₂, ha₂eq⟩ := circle_exists_continuousOn_h2_composition_of_h3
    g₀ f₀ W hW F hF hS a hRange haEval
  choose b₂j hb₂j hb₂jeq using fun j : Fin n =>
    circle_exists_continuousOn_h2_composition_of_h3 g₀ f₀ W hW
      (fun y => G y j) (contDiffOn_pi.mp hG j) hS (fun t => b t j) hRange (hbEval j)
  let b₂ := fun t => WithLp.toLp 2 (fun j => b₂j j t)
  have hb₂ : ContinuousOn b₂ (Icc 0 T) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hb₂j)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha₂
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hb₂
  refine ⟨a₂, b₂, ha₂, hb₂, ha₂eq, ?_, max 0 (A + B), le_max_left _ _, ?_⟩
  · intro t ht
    apply PiLp.ext
    intro j
    exact hb₂jeq j t ht
  · intro t ht
    exact (add_le_add (hA t ht) (hB t ht)).trans (le_max_right _ _)

private theorem ambient_coefficients_continuousOn_h2
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {T : ℝ}
    (W : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    T ≤ ScalarVectorTimeCoefficients.radius C →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    let alpha := fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) = alpha t) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (b₂ t) = reaction t) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖a₂ t‖ + ‖b₂ t‖ ≤ B := by
  intro C g₀ J K hT hbound alpha reaction
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq, B, hB, hbound₂⟩ :=
    scalarVectorTimeCoefficients_continuousOn_h2 g₀ _ _ _ _ C
      hF hReaction hS hT f₀ W hW
      (ambientFirstJet_eq_initialJet c₀ (g 0) he) hbound
  refine ⟨a₂, b₂, ha₂, hb₂, ?_, ?_, B, hB, hbound₂⟩
  · intro t htt
    have h := congrArg (tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (haeq t htt)
    refine Eq.trans ?_ h
    apply TensorHs.ext
    rw [hcongr]
    rfl
  · intro t htt
    have h := congrArg (circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (hbeq t htt)
    refine Eq.trans ?_ h
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simp only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, hcongr, tensorHsInclusion_coeff]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_timeL2_h2_composition_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S Krange : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T ≤ 1 →
      ∀ u : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g (t, J (K f₀ + w t))
      ∀ a : ℝ → TensorHs g 0 0 1, AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (u t)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
        F (scalarH1PiToContinuous g (q t) x)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  intro J K
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  obtain ⟨C, hC, hc⟩ := AddCircle.exists_timeL2_scalarH2_composition_firstJet_norm_le
    g (E f₀) F hF hS hK hKS R
  refine ⟨C, hC, ?_⟩
  intro T hT u w q a ha hwu hRange hBound hEval
  let u₂ := E.compLpL 2 (timeMeasure T) u
  let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
  let V := fun t z => P (AddCircle.scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
    (t, AddCircle.firstJetHs g 2 z))
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hK₂ (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) : K₂ (E v) = K v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
    rw [hcongr]
  have hw₂ : w =ᵐ[timeMeasure T] (fun t => K₂ (u₂ t)) := by
    filter_upwards [hwu, E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht he
    change u₂ t = E (u t) at he
    rw [he, hK₂]
    exact ht
  have hq (t : ℝ) :
      scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))) = q t := by
    rw [hK₂, ← circle_firstJetHs_normalized]
    rfl
  have hproject := AddCircle.scalarHsTimeCoordinate_firstJetHs_ae_eq
    g (by decide : 1 ≤ 2) T (E f₀) u₂ w hw₂
  have hqv : (fun t => Q (V t (E f₀ + u₂ t))) =ᵐ[timeMeasure T] q := by
    filter_upwards [hproject] with t ht
    rw [← hq]
    refine Eq.trans ?_ ht
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hrange : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (V t (E f₀ + u₂ t)))) ⊆ Krange := by
    filter_upwards [hRange, hqv] with t ht he
    rwa [he]
  have hbound : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (E f₀ + u₂ t)) i‖) ≤ R := by
    filter_upwards [hBound, hqv] with t ht he
    rwa [he]
  have heval : ∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (Q (V t (E f₀ + u₂ t))) x) := by
    filter_upwards [hEval, hqv] with t ht he
    rwa [he]
  obtain ⟨a₂, ha₂, hnorm⟩ := hc T hT u₂ a ha hrange hbound heval
  refine ⟨a₂, ha₂, hnorm.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add le_rfl
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht
  change u₂ t = E (u t) at ht
  rw [ht]
  exact (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).norm_map (u t) |>.le

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_diffusion_h2_norm_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      u₀ = J (K f₀) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  classical
  intro J K
  obtain ⟨A, hA, ha₂⟩ := circle_timeL2_h2_composition_norm_le g₀ f₀ F hF hS hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hu₀ hwu hbound hRange hBound
  let a := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : a t = (ScalarVectorTimeCoefficients.diffusion C) t (z t) :=
    extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)) (z t).2
  have ha : ContinuousOn a (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((ScalarVectorTimeCoefficients.diffusion_lipschitz C).continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  apply ha₂ T hT1 field w a (memLp_of_continuousOn ha).aestronglyMeasurable
    hwu hRange hBound
  have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ht] with t htt
  intro x
  change scalarH1ToContinuous g₀ (a t) x = F
    (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
  rw [map_add, ← hu₀, he ⟨t, htt⟩, (ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨htt.1, htt.2.trans hT⟩]
  congr 1
  funext i
  cases i with
  | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
  | some i =>
    simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
    rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem ambient_diffusion_h2_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange)
    (hKS : Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β) (R : ℝ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ f₀ J K
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨A, hA, ha₂⟩ := scalarVectorTimeCoefficients_diffusion_h2_norm_le g₀ _ _ _ _ C
    hF hS f₀ hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hwu hbound hRange hBound
  obtain ⟨a₂, hproject, hnorm⟩ := ha₂ T hT1 hT field w hw
    (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound hRange hBound
  refine ⟨a₂, ?_, hnorm⟩
  filter_upwards [hproject] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hc : tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =
      tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) := by
    apply TensorHs.ext
    rw [hcongr]
    rfl
  rw [← hc, htt]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_firstJet_bounds_on_closedBall
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let q := fun t v => scalarH1TimeCoordinate g₀ (t, J (K f₀ + v))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧ ‖J‖ * δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧
      ∃ Krange : Set (Option (Fin n ⊕ Fin n) → ℝ), IsCompact Krange ∧
        Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
        ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) δ,
          ∀ v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1), ‖v‖ ≤ δ →
            range (scalarH1PiToContinuous g₀ (q t v)) ⊆ Krange ∧
              (∑ i, ‖q t v i‖) ≤ R := by
  intro C g₀ f₀ J K q
  let q₀ := scalarH1TimeCoordinate g₀ (0, J (K f₀))
  have hbase := ambientFirstJet_range c₀ g ht he hr hEU hleft β
  rw [ambientFirstJet_eq_initialJet c₀ (g 0) he] at hbase
  obtain ⟨hS, _, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨η, hη, Krange, hK, hKS, hrange⟩ :=
    exists_scalarH1Pi_ball_range_subset g₀ q₀ hS hbase
  let X := CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)
  let B : ℝ × X →L[ℝ] PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) => TensorHs g₀ 0 0 1) :=
    (scalarH1TimeCoordinate g₀).comp
      ((ContinuousLinearMap.fst ℝ ℝ X).prod (J.comp (ContinuousLinearMap.snd ℝ ℝ X)))
  obtain ⟨δJ, hδJ, hδJC, hJ⟩ := J.exists_pos_norm_mul_le (ScalarVectorTimeCoefficients.radius_pos C)
  obtain ⟨δB, hδB, _, hB⟩ := B.exists_pos_norm_mul_le (half_pos hη)
  let δ := min δJ (min δB 1)
  have hδ : 0 < δ := lt_min hδJ (lt_min hδB zero_lt_one)
  have hδJle : δ ≤ δJ := min_le_left _ _
  have hδBle : δ ≤ δB := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let R := (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * (‖q₀‖ + η)
  have hR : 0 ≤ R := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  refine ⟨δ, hδ, hδJle.trans hδJC, hδ1,
    (mul_le_mul_of_nonneg_left hδJle (norm_nonneg J)).trans hJ,
    Krange, hK, hKS, R, hR, ?_⟩
  intro t ht v hv
  have hp : ‖(t, v)‖ ≤ δ := by
    rw [Prod.norm_def]
    apply max_le
    · simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    · exact hv
  have hpert : ‖B (t, v)‖ < η := by
    calc
      _ ≤ ‖B‖ * ‖(t, v)‖ := B.le_opNorm _
      _ ≤ ‖B‖ * δB := mul_le_mul_of_nonneg_left (hp.trans hδBle) (norm_nonneg B)
      _ ≤ η / 2 := hB
      _ < η := half_lt_self hη
  have hq : q t v = q₀ + B (t, v) := by
    change scalarH1TimeCoordinate g₀ (t, J (K f₀ + v)) =
      scalarH1TimeCoordinate g₀ (0, J (K f₀)) + scalarH1TimeCoordinate g₀ (t, J v)
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, zero_add, map_add]
  have hmem : q t v ∈ Metric.ball q₀ η := by
    rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left]
    exact hpert
  refine ⟨hrange _ hmem, ?_⟩
  have hnorm : ‖q t v‖ ≤ ‖q₀‖ + η := by
    rw [hq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hpert.le)
  calc
    _ ≤ ∑ _i : Option (Fin n ⊕ Fin n), ‖q t v‖ :=
      Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
    _ = (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖q t v‖ := by simp
    _ ≤ R := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_diffusion_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K
  obtain ⟨δ, hδ, hδC, hδ1, hJδ, Krange, hK, hKS, R, _, hb⟩ :=
    ambient_firstJet_bounds_on_closedBall c₀ g ht he hr hEU hleft β hG
  obtain ⟨A, hA, ha₂⟩ := ambient_diffusion_h2_norm_le c₀ g ht he hr hEU hleft β hG
    hK hKS R
  refine ⟨δ, hδ, hδC, hδ1, A, hA, ?_⟩
  intro T hT field w hw hwu hbound
  change ‖J‖ * δ ≤ (ScalarVectorTimeCoefficients.radius C) at hJδ
  have hJw : ∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    intro t htt
    calc
      ‖J (w t)‖ ≤ ‖J‖ * ‖w t‖ := J.le_opNorm _
      _ ≤ ‖J‖ * δ := mul_le_mul_of_nonneg_left (hbound t htt) (norm_nonneg J)
      _ ≤ (ScalarVectorTimeCoefficients.radius C) := hJδ
  apply ha₂ T (hT.trans hδ1) (hT.trans hδC) field w hw hwu hJw
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).1
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_reaction_h2_norm_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      u₀ = J (K f₀) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (ContinuousLinearMap.piLpMap 2 fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  classical
  intro J K
  choose A hA hc using fun j : Fin n =>
    circle_timeL2_h2_composition_norm_le g₀ f₀ (fun z => G z j)
      (contDiffOn_pi.mp hG j) hS hK hKS R
  refine ⟨∑ j, A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  intro T hT1 hT field w q hw hu₀ hwu hbound hRange hBound
  let b := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : b t = (ScalarVectorTimeCoefficients.reaction C) t (z t) :=
    extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)) (z t).2
  have hb : ContinuousOn b (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((ScalarVectorTimeCoefficients.reaction_lipschitz C).continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  have heval (j : Fin n) : ∀ᵐ t ∂timeMeasure T, ∀ x,
      scalarH1ToContinuous g₀ (b t j) x = G (scalarH1PiToContinuous g₀ (q t) x) j := by
    have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    intro x
    change scalarH1ToContinuous g₀ (b t j) x = G
      (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x) j
    rw [map_add, ← hu₀, he ⟨t, htt⟩, (ScalarVectorTimeCoefficients.reaction_eval C) t ⟨htt.1, htt.2.trans hT⟩]
    congr 2
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
      rfl
  have hj (j : Fin n) := hc j T hT1 field w (fun t => b t j)
    (memLp_of_continuousOn ((PiLp.continuous_apply 2 (fun _ : Fin n => TensorHs g₀ 0 0 1) j).comp_continuousOn hb)).aestronglyMeasurable
    hwu hRange hBound (heval j)
  choose v hv hvnorm using hj
  let e₂ := Lp.piLpEquiv (𝕜 := ℝ)
    (X := fun _ : Fin n => TensorHs g₀ 0 0 2) (timeMeasure T)
  let vpi : PiLp 2 (fun _ : Fin n => timeL2 (TensorHs g₀ 0 0 2) T) := WithLp.toLp 2 v
  let b₂ := e₂.symm vpi
  have hb₂ : ∀ᵐ t ∂timeMeasure T, ∀ j, b₂ t j = v j t := by
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) vpi] with t ht
    intro j
    exact congrArg (fun z : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2) => z j) ht
  have hb₂norm : ‖b₂‖ ≤ ∑ j, ‖v j‖ := by
    change ‖e₂.symm vpi‖ ≤ _
    rw [e₂.symm.norm_map]
    have hs : vpi = ∑ j, PiLp.single 2 j (v j) := by
      apply PiLp.ext
      intro j
      simp [vpi]
    rw [hs]
    simpa only [PiLp.norm_single] using norm_sum_le Finset.univ
      (fun j : Fin n => (PiLp.single 2 j (v j) :
        PiLp 2 (fun _ : Fin n => timeL2 (TensorHs g₀ 0 0 2) T)))
  refine ⟨b₂, ?_, hb₂norm.trans ?_⟩
  · filter_upwards [hb₂, Filter.eventually_all.mpr hv] with t ht hvt
    apply PiLp.ext
    intro j
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (b₂ t j) = b t j
    rw [ht j]
    exact hvt j
  · calc
      ∑ j, ‖v j‖ ≤ ∑ j, A j * (Real.sqrt T + ‖field‖) :=
        Finset.sum_le_sum (fun j _ => hvnorm j)
      _ = (∑ j, A j) * (Real.sqrt T + ‖field‖) := (Finset.sum_mul _ _ _).symm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem ambient_reaction_h2_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange)
    (hKS : Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β) (R : ℝ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ f₀ J K
  obtain ⟨hS, _, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨A, hA, hb₂⟩ := scalarVectorTimeCoefficients_reaction_h2_norm_le g₀ _ _ _ _ C
    hReaction hS f₀ hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hwu hbound hRange hBound
  obtain ⟨b₂, hproject, hnorm⟩ := hb₂ T hT1 hT field w hw
    (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound hRange hBound
  refine ⟨b₂, ?_, hnorm⟩
  filter_upwards [hproject] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  apply PiLp.ext
  intro j
  have hp := congrArg (fun v : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1) => v j) htt
  change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (b₂ t j) =
    extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)) j at hp
  change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (b₂ t j) =
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)) j)
  apply TensorHs.ext
  rw [hcongr, ← hp]
  rfl

private theorem ambient_reaction_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K
  obtain ⟨δ, hδ, hδC, hδ1, hJδ, Krange, hK, hKS, R, _, hb⟩ :=
    ambient_firstJet_bounds_on_closedBall c₀ g ht he hr hEU hleft β hG
  obtain ⟨A, hA, hb₂⟩ := ambient_reaction_h2_norm_le c₀ g ht he hr hEU hleft β hG
    hK hKS R
  refine ⟨δ, hδ, hδC, hδ1, A, hA, ?_⟩
  intro T hT field w hw hwu hbound
  change ‖J‖ * δ ≤ (ScalarVectorTimeCoefficients.radius C) at hJδ
  have hJw : ∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    intro t htt
    calc
      ‖J (w t)‖ ≤ ‖J‖ * ‖w t‖ := J.le_opNorm _
      _ ≤ ‖J‖ * δ := mul_le_mul_of_nonneg_left (hbound t htt) (norm_nonneg J)
      _ ≤ (ScalarVectorTimeCoefficients.radius C) := hJδ
  apply hb₂ T (hT.trans hδ1) (hT.trans hδC) field w hw hwu hJw
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).1
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_coefficients_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K H P
  obtain ⟨δa, hδa, hδaC, hδa1, A, hA, ha⟩ :=
    ambient_diffusion_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  obtain ⟨δb, hδb, _, _, B, hB, hb⟩ :=
    ambient_reaction_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδaC,
    (min_le_left _ _).trans hδa1, A, B, hA, hB, ?_⟩
  intro T hTδ field w hw hwu hbound
  have hwa : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ δa := fun t ht =>
    (hbound t ht).trans (min_le_left _ _)
  have hwb : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ δb := fun t ht =>
    (hbound t ht).trans (min_le_right _ _)
  obtain ⟨a₂, ha₂, hanorm⟩ := ha T (hTδ.trans (min_le_left _ _)) field w hw hwu hwa
  obtain ⟨b₂, hb₂, hbnorm⟩ := hb T (hTδ.trans (min_le_right _ _)) field w hw hwu hwb
  exact ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩

private theorem ambient_parameterDerivative_duhamel_equation
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      let Gforce := parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce
      let V := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((0 : ℕ) : ℝ)) hT 0 Gforce
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ)) (Gforce t i) =
            AddCircle.parameterDerivativeParabolicForcing g₀
              (alpha t) (reaction t i) (f₀ i) (V t i) := by
  intro C g₀ f₀ J T hT gforce field w alpha reaction L Q m heq Gforce V
  apply parameterDerivativeDuhamelForcing_ae_eq g₀ hT gforce f₀ alpha reaction
  filter_upwards [heq] with t ht
  intro i
  exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev (scalarCc)
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_diffusion_sub_baseline_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ Cα : ℝ≥0, ∀ {ρ T : ℝ}, 0 ≤ ρ → T ≤ ρ →
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ t ∈ Icc 0 T,
        ‖tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) - q‖ ≤ Cα * ρ := by
  intro C g₀ J q
  refine ⟨(ScalarVectorTimeCoefficients.diffusionLipschitz C) * max 1 ‖J‖₊, ?_⟩
  intro ρ T hρ hTρ w hw hJ t ht
  let z₀ : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) :=
    ⟨0, Metric.mem_closedBall_self (ScalarVectorTimeCoefficients.radius_pos C).le⟩
  have hz : J (w t) ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJ t ht
  have hbase : (ScalarVectorTimeCoefficients.diffusion C) 0 z₀ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) :=
    initial_diffusion_coefficients c₀ g he hr hEU hleft β C
  have hmax : max t ‖J (w t)‖ ≤ max 1 ‖J‖ * ρ := by
    apply max_le
    · exact (ht.2.trans hTρ).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 ‖J‖) hρ)
    · exact (J.le_opNorm (w t)).trans
        ((mul_le_mul_of_nonneg_left (hw t ht) (norm_nonneg J)).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 ‖J‖) hρ))
  have hbound : ‖extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)) -
      (ScalarVectorTimeCoefficients.diffusion C) 0 z₀‖ ≤ (ScalarVectorTimeCoefficients.diffusionLipschitz C) * (max 1 ‖J‖ * ρ) := by
    rw [extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)) hz]
    have h := (ScalarVectorTimeCoefficients.diffusion_lipschitz C).dist_le_mul (t, ⟨J (w t), hz⟩) (0, z₀)
    simp only [Prod.dist_eq, Subtype.dist_eq, z₀, dist_eq_norm, sub_zero,
      Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hmax (ScalarVectorTimeCoefficients.diffusionLipschitz C).coe_nonneg)
  change ‖tensorHsCongrL g₀ 0 0 _ _ -
    ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤ _
  rw [← tensorHsCongrL_ccTensorToHs g₀
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)), ← hbase,
    ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
  simpa only [NNReal.coe_mul, NNReal.coe_max, NNReal.coe_one, coe_nnnorm, mul_assoc]
    using hbound

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
