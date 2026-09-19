import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

open private ScalarVectorTimeCoefficients.diffusion ScalarVectorTimeCoefficients.diffusion_eval ScalarVectorTimeCoefficients.radius ScalarVectorTimeCoefficients.radius_pos ScalarVectorTimeCoefficients.range_mem ScalarVectorTimeCoefficients.reaction ScalarVectorTimeCoefficients.reaction_eval from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private coordinateMultiplication CircleHsPi circleHsPiInclusion extendClosedBall extendClosedBall_apply circleHsPiCongr circleHsPiCongr_apply circleHsPiCongr_inclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private geometric_coefficients_contDiffOn circleFirstJet ambientCoordinateCc ambientSobolev ScalarVectorTimeCoefficients ambientCoefficients from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private circle_firstJetHs_normalized scalarVectorTimeCoefficients_diffusion_higher_order scalarVectorTimeCoefficients_reaction_higher_order ambientFirstJet_eq_initialJet ambientFirstJet_eq_higher_initialJet scalarVectorTimeCoefficients_continuousOn_h2 from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
open private parameterNormalizeZero parameterPrincipalLow ambientParameterDerivativeControl ambientDiffusionProjection ambientParameterDerivativeLiftAtRadius ambient_h2_coefficient_contraction ambientH2CoefficientsAtState ambient_parameterDerivative_forcing_lift_at_small_state ambientCappedSobolevSolutionSpec parameterDerivativeForcingFieldLift ambientSobolevSolutionFacts ambient_parameterDerivative_lift_of_solution_facts ambient_fourth_order_lift_of_parameterDerivative_lift scalarVectorClassicalTimeEquation ambient_firstJet_mem_of_sobolev_solution_facts ambient_classical_time_equation_of_parameterDerivative_lift ambient_chart_equation_of_parameterDerivative_lift ambient_original_forcing_higher_equation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJetHs_eq_of_projection
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (v : CircleHsPi g ι ((k : ℝ) + 3)) (w : CircleHsPi g ι 3)
    (hp : circleHsPiInclusion g ι
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3) v = w) :
    let Em := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let Lm := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    Lm (AddCircle.firstJetHs g (k + 2) (Em v)) =
      circleFirstJet g
        (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) := by
  intro Em Lm
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
  let z := K (Em v)
  let L₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hcoeff {a b : ℝ} (h : a = b) (u : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h u).coeff = u.coeff := by
    cases h
    rfl
  have hz : circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) z =
        circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w := by
    rw [← hp]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rw [circleHsPiCongr_apply, hcoeff]
    rfl
  let L₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show ((1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ k + 2 by omega)))
  have hjet := congrArg (fun A => A (Em v))
    (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := ι) g
      (show 1 ≤ k + 2 by omega))
  change AddCircle.firstJetHs g 1 z = L₁ (AddCircle.firstJetHs g (k + 2) (Em v)) at hjet
  have hnormalized := circle_firstJetHs_normalized g z
  rw [hz, hjet] at hnormalized
  change circleFirstJet g
      (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) =
        L₀ (L₁ (AddCircle.firstJetHs g (k + 2) (Em v))) at hnormalized
  calc
    Lm (AddCircle.firstJetHs g (k + 2) (Em v)) =
        L₀ (L₁ (AddCircle.firstJetHs g (k + 2) (Em v))) := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    _ = circleFirstJet g
        (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) := hnormalized.symm

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

private theorem ambient_spatial_jets_of_sobolev_representative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (k : ℕ) {T : ℝ}
    (u : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ))
    (W : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((k : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T))
    (hWu : ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u t) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ)))
    (∀ t ∈ Icc 0 T, ContDiff ℝ (k + 1) (F t)) ∧
      ∀ j ≤ k + 1, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro g₀ f₀ P S F
  let f := fun t (x : ℝ) =>
    scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ))
  let f₀H := ambientSobolev c₀ g e he ((k : ℝ) + 2)
  have hlow (t : ℝ) (ht : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ (k : ℝ) + 2) (f₀H + W t) = P f₀ + S (u t) := by
    apply PiLp.ext
    intro i
    simp only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
    apply congrArg₂ (· + ·)
    · change tensorHsInclusion (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ (k : ℝ) + 2) (ccTensorToHs g₀ 0 ((k : ℝ) + 2)
          (ambientCoordinateCc c₀ g e he i)) =
        tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
          (ccTensorToHs g₀ 0 (((1 : ℕ) : ℝ) + 2)
          (ambientCoordinateCc c₀ g e he i))
      rw [tensorHsInclusion_ccTensorToHs, tensorHsInclusion_ccTensorToHs]
    · have hi := congrArg (fun z => z i) (hWu t ht)
      have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
      simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply] using hi'
  have hjet (j : ℕ) (hj : j ≤ k + 1) :
      (∀ t ∈ Icc 0 T, ContDiff ℝ j (f t)) ∧
        ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (f p.1) p.2)
          (Icc 0 T ×ˢ univ) := by
    have hjk : (j : ℝ) + 1 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hj 1
    let K := circleHsPiInclusion g₀ (Fin n) hjk
    exact AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
      g₀ j (fun t => P f₀ + S (u t)) (fun t => K (f₀H + W t))
      (K.continuous.comp_continuousOn (continuousOn_const.add hW)) (fun t ht => by
        refine Eq.trans ?_ (hlow t ht)
        apply PiLp.ext
        intro i
        exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ (j : ℝ) + 1) hjk ((f₀H + W t) i)).symm)
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hder (j : ℕ) (t x : ℝ) :
      iteratedDeriv j (F t) x = L (iteratedDeriv j (f t) x) := by
    change iteratedDeriv j (L ∘ f t) x = _
    rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_left]
    rfl
  constructor
  · intro t ht
    exact L.contDiff.comp ((hjet (k + 1) le_rfl).1 t ht)
  · intro j hj
    have hc := L.continuous.comp_continuousOn (hjet j hj).2
    apply hc.congr
    intro p _
    exact hder j p.1 p.2

private theorem ambient_spatial_jets_of_sobolev_tower
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {T : ℝ}
    (u : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ))
    (htower : ∀ k : ℕ,
      ∃ W : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((k : ℝ) + 2),
        ContinuousOn W (Icc 0 T) ∧
          ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
            (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u t) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ)))
    (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (F t)) ∧
      ∀ j : ℕ, ContinuousOn
        (fun p : ℝ × ℝ => iteratedFDeriv ℝ j (F p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro g₀ f₀ P S F
  have hfinite (k : ℕ) :
      (∀ t ∈ Icc 0 T, ContDiff ℝ (k + 1) (F t)) ∧
        ∀ j ≤ k + 1, ContinuousOn
          (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2)
          (Icc 0 T ×ˢ univ) := by
    obtain ⟨W, hW, hWu⟩ := htower k
    exact ambient_spatial_jets_of_sobolev_representative c₀ g he k u W hW hWu
  constructor
  · intro t ht
    rw [contDiff_infty]
    intro k
    exact ((hfinite k).1 t ht).of_le (by exact_mod_cast Nat.le_succ k)
  · intro j
    have h := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j)
      (EuclideanSpace ℝ (Fin n))).continuous.comp_continuousOn
        ((hfinite j).2 j (Nat.le_succ j))
    simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
    convert! h using 1

private theorem ambient_contDiffOn_of_sobolev_tower
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {n : ℕ} (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce)
    (htower : ∀ k : ℕ,
      ∃ W : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((k : ℝ) + 2),
        ContinuousOn W (Icc 0 T) ∧
          ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
            (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u.toFun t) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro g₀ f₀ P S F
  have hspatial := ambient_spatial_jets_of_sobolev_tower c₀ (g 0) he u.toFun htower
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  exact contDiffOn_of_parametric_chart_equation_spatial_jets hG β hT isOpen_univ
    (fun t ht => (hspatial.1 t ht).contDiffOn) hspatial.2
    (fun t ht x _ => hjet t ht x)
    (fun t ht x _ => (hchart t ⟨ht.1.le, ht.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem scalarVectorTimeCoefficients_continuousOn_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (k : ℕ) {T : ℝ} (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hW : ContinuousOn W (Icc 0 T)) :
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
    (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
      (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1))),
      ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, A (a t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
      ∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) := by
  classical
  intro K L J A hu₀ hbound
  let B := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; rfl : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ)))
  let qLow := fun t => B (AddCircle.scalarHsTimeCoordinate g₀ ((k + 1 : ℕ) : ℝ)
    (t, AddCircle.firstJetHs g₀ (k + 1) (K f₀ + W t)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A)
  let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + W t))
  have hqLow : ContinuousOn qLow (Icc 0 T) :=
    B.continuous.comp_continuousOn
      ((AddCircle.scalarHsTimeCoordinate g₀ _).continuous.comp_continuousOn
        (continuousOn_id.prodMk ((AddCircle.firstJetHs g₀ (k + 1)).continuous.comp_continuousOn
          (continuousOn_const.add hW))))
  have hq (t : ℝ) : P (qLow t) = q t := by
    have hh := AddCircle.tensorHsInclusion_scalarHsTimeCoordinate g₀
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      (t, AddCircle.firstJetHs g₀ (k + 1) (K f₀ + W t))
    refine Eq.trans ?_ hh
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
        (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (W t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hRange (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g₀ (P (qLow t))) ⊆ S := by
    rw [hq]
    have hh := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩
      (J (W t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + W t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using hh
  have hcoord (t : ℝ) (x : AddCircle (1 : ℝ)) :
      (fun i : Option (Fin n ⊕ Fin n) => match i with
        | none => 0 + t
        | some j => scalarH1ToContinuous g₀ (u₀ j + J (W t) j) x) =
      scalarH1PiToContinuous g₀ (q t) x := by
    funext i
    cases i with
    | none => simp only [q, scalarH1TimeCoordinate_eval_none, zero_add]
    | some j =>
      simp only [q, map_add, ← hu₀, scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
  obtain ⟨a, ha, hae⟩ := AddCircle.exists_continuousOn_scalarHs_composition
    g₀ k F hF hS qLow hqLow hRange
  have hFi (j : Fin n) : ContDiffOn ℝ ∞ (fun q => G q j) S :=
    contDiffOn_pi.mp hG j
  choose bᵢ hbᵢ hbe using fun j : Fin n =>
    AddCircle.exists_continuousOn_scalarHs_composition
      g₀ k (fun q => G q j) (hFi j) hS qLow hqLow hRange
  let b := fun t => WithLp.toLp 2 (fun j => bᵢ j t)
  have hb : ContinuousOn b (Icc 0 T) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hbᵢ)
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · intro t ht
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    rw [extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t (J (W t)) (z ⟨t, ht⟩).2,
      (ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    exact (hae t ht x).trans ((congrArg
      (fun v => F (scalarH1PiToContinuous g₀ v x)) (hq t)).trans
        (congrArg F (hcoord t x).symm))
  · intro t ht
    apply PiLp.ext
    intro j
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    change scalarH1ToContinuous g₀ (A (bᵢ j t)) x = _
    rw [extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) (z ⟨t, ht⟩).2,
      (ScalarVectorTimeCoefficients.reaction_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    exact (hbe j t ht x).trans ((congrArg
      (fun v => G (scalarH1PiToContinuous g₀ v x) j) (hq t)).trans
        (congrArg (fun v => G v j) (hcoord t x).symm))

private theorem scalarVectorTimeCoefficients_timeL2_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {k : ℕ}
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) :
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
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    u₀ = J (K f₀) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1))),
      ContinuousOn a (Icc 0 T) → ContinuousOn b (Icc 0 T) →
      (∀ t ∈ Icc 0 T, A (a t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b := by
  classical
  intro K L J A Q hu₀ T hT Z W hW hWZ hbound a b ha hb hae hbe
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have haactual : (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) := by
    filter_upwards [htime] with t htt
    exact hae t htt
  obtain ⟨aHigh, haHigh⟩ := scalarVectorTimeCoefficients_diffusion_higher_order g₀ F G S u₀ C hF hS
    k T hT f₀ Z W hW a (memLp_of_continuousOn ha).aestronglyMeasurable
      hu₀ hWZ hbound haactual
  have hbcoord (j : Fin n) : AEStronglyMeasurable (fun t => b t j) (timeMeasure T) :=
    (memLp_of_continuousOn
      ((PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)) j).continuous.comp_continuousOn
          hb)).aestronglyMeasurable
  have hbactual (j : Fin n) : (fun t => A (b t j)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) j) := by
    filter_upwards [htime] with t htt
    exact congrArg (fun z => z j) (hbe t htt)
  have hblift (j : Fin n) : ∃ z : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => Q (z t)) =ᵐ[timeMeasure T] (fun t => b t j) :=
    scalarVectorTimeCoefficients_reaction_higher_order g₀ F G S u₀ C j
      (contDiffOn_pi.mp hG j) hS k T hT f₀ Z W hW
      (fun t => b t j) (hbcoord j) hu₀ hWZ hbound (hbactual j)
  choose B hB using hblift
  let bHigh := (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm (WithLp.toLp 2 B)
  have hbHigh : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q)
      (bHigh t)) =ᵐ[timeMeasure T] b := by
    have hBall : ∀ᵐ t ∂timeMeasure T, ∀ j, Q (B j t) = b t j := ae_all_iff.mpr hB
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) (WithLp.toLp 2 B),
      hBall] with t hbₜ hBₜ
    change bHigh t = WithLp.toLp 2 (fun j => B j t) at hbₜ
    rw [hbₜ]
    apply PiLp.ext
    exact hBₜ
  exact ⟨aHigh, bHigh, haHigh, hbHigh⟩

private theorem scalarVectorTimeCoefficients_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {k : ℕ} (hk : 1 ≤ k)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) :
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
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith : (2 : ℝ) ≤ (k : ℝ) + 1)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    u₀ = J (K f₀) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t =>
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)) =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  classical
  intro K L J A P Q hu₀ T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  obtain ⟨a, b, ha, hb, hae, hbe⟩ := scalarVectorTimeCoefficients_continuousOn_higher_order
    g₀ F G S u₀ C hF hG hS k hT f₀ W hW hu₀ hbound
  obtain ⟨aHigh, bHigh, haHigh, hbHigh⟩ :=
    scalarVectorTimeCoefficients_timeL2_higher_order g₀ F G S u₀ C hF hG hS f₀
      hu₀ T hT Z W hW hWZ hbound a b ha hb hae hbe
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have hap (t : ℝ) (htt : t ∈ Icc 0 T) : P (a t) = a₂ t := by
    apply tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)
    have hh : tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (a t)) = A (a t) := by
      apply TensorHs.ext
      rfl
    rw [hh, hae t htt, ha₂ t htt]
  have hbp (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t := by
    apply PiLp.ext
    intro j
    apply tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)
    have hh : tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (b t j)) = A (b t j) := by
      apply TensorHs.ext
      rfl
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (b t j)) = _
    rw [hh]
    exact (congrArg (fun z => z j) (hbe t htt)).trans
      (congrArg (fun z => z j) (hb₂ t htt)).symm
  refine ⟨a, b, aHigh, bHigh, ha, hb, hae, hbe, hap, hbp, haHigh, hbHigh, ?_, ?_⟩
  · filter_upwards [htime, haHigh] with t htt hat
    rw [hat]
    exact hap t htt
  · filter_upwards [htime, hbHigh] with t htt hbt
    rw [hbt]
    exact hbp t htt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private theorem ambient_coefficients_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {k : ℕ} (hk : 1 ≤ k) :
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
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith : (2 : ℝ) ≤ (k : ℝ) + 1)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t =>
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)) =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro C g₀ K L J A P Q T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_higher_order g₀ _ _ _ _ C hF hReaction hS hk f₀
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k)
    T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem firstJetHs_successor_normalization
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ)
    (x : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) :
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Lraw := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ)))
    (Lraw.comp (AddCircle.firstJetHs g₀ (k + 1 + 1))) (E x) =
      (L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)) x := by
  intro E L Lraw
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation (TensorHs tensorHsInclusion)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circleHsPi_successor_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (Z : timeL2 (PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T)
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 ((k : ℝ) + 3))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let EZ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith only : ((k + 1 + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 4))
    let Kraw := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
    ContinuousOn (fun t => E (W t)) (Icc 0 T) ∧
      (fun t => E (W t)) =ᵐ[timeMeasure T]
        (fun t => Kraw ((EZ.compLpL 2 (timeMeasure T) Z) t)) := by
  intro K E EZ Kraw hW hWZ
  refine ⟨E.continuous.comp_continuousOn hW, ?_⟩
  filter_upwards [hWZ, EZ.coeFn_compLpL Z] with t hwt hzt
  rw [hzt, hwt]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private def mapTimeL2Real {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (T : ℝ) (L : X →L[ℝ] Y) (z : timeL2 X T) : timeL2 Y T :=
  L.compLpL 2 (timeMeasure T) z

private theorem mapTimeL2Real_ae {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (T : ℝ) (L : X →L[ℝ] Y) (z : timeL2 X T) :
    mapTimeL2Real T L z =ᵐ[timeMeasure T] (fun t => L (z t)) :=
  L.coeFn_compLpL z

private theorem exists_four_elim
    {A B C D : Sort*} {P : A → B → C → D → Prop} {Q : Prop}
    (h : ∃ a b c d, P a b c d)
    (hQ : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, hp⟩ := h
  exact hQ a b c d hp

private theorem scalarVectorTimeCoefficients_reindex
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (f₁ : ℝ → TensorHs g₀ 0 0 1)
    (g₁ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2))
    (ar : ℝ → TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1))
    (br : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (aHr : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (bHr : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2))) T) :
    let Araw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          push_cast
          linarith only [hk] : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let Praw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          push_cast
          linarith only [hk] : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let Qraw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    ContinuousOn ar (Icc 0 T) → ContinuousOn br (Icc 0 T) →
    (∀ t ∈ Icc 0 T, Araw (ar t) = f₁ t) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Araw) (br t) =
      g₁ t) →
    (∀ t ∈ Icc 0 T, Praw (ar t) = a₂ t) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Praw) (br t) =
      b₂ t) →
    (fun t => Qraw (aHr t)) =ᵐ[timeMeasure T] ar →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Qraw) (bHr t))
      =ᵐ[timeMeasure T] br →
    ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
      (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
      (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
      (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
      ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, A (a t) = f₁ t) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        g₁ t) ∧
      (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
      (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
        =ᵐ[timeMeasure T] b ∧
      (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)))
          =ᵐ[timeMeasure T] b₂ := by
  intro Araw Praw Qraw A P Q har hbr hae hbe hap hbp haH hbH
  let O := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : (k : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 1)
  let OH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : (k : ℝ) + 3 ≤ ((k + 1 : ℕ) : ℝ) + 2)
  let OP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => O)
  let OHP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => OH)
  let a := fun t => O (ar t)
  let b := fun t => OP (br t)
  let aHigh := mapTimeL2Real T OH aHr
  let bHigh := mapTimeL2Real T OHP bHr
  have ha : ContinuousOn a (Icc 0 T) := O.continuous.comp_continuousOn har
  have hb : ContinuousOn b (Icc 0 T) := OP.continuous.comp_continuousOn hbr
  have haeval (t : ℝ) (ht : t ∈ Icc 0 T) : A (a t) =
      f₁ t := by
    refine Eq.trans ?_ (hae t ht)
    apply TensorHs.ext
    rfl
  have hbeval (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
      g₁ t := by
    refine Eq.trans ?_ (hbe t ht)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have ha₂proj (t : ℝ) (ht : t ∈ Icc 0 T) : P (a t) = a₂ t := by
    refine Eq.trans ?_ (hap t ht)
    apply TensorHs.ext
    rfl
  have hb₂proj (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t := by
    refine Eq.trans ?_ (hbp t ht)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have haHigh : (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a := by
    filter_upwards [mapTimeL2Real_ae T OH aHr, haH] with t hot hht
    change Q (aHigh t) = O (ar t)
    rw [hot, ← hht]
    apply TensorHs.ext
    rfl
  have hab : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2 := by
    linarith only
  have hcd : (k : ℝ) + 2 ≤ (k : ℝ) + 3 := by
    linarith only
  have hca : (k : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith only
  have hdb : (k : ℝ) + 3 ≤ ((k + 1 : ℕ) : ℝ) + 2 := by
    push_cast
    linarith only
  have hvector := tensorHsPi_ae_eq_of_inclusion
    (ι := Fin n) (Ω := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    g₀ 0 0 hab hcd hca hdb (p := 2) (μ := timeMeasure T) bHr br
  whnf at hvector
  have hvectorAE := hvector hbH
  have hbHigh : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q)
      (bHigh t)) =ᵐ[timeMeasure T] b := by
    dsimp only [bHigh, b, mapTimeL2Real, OP, OHP, O, OH, Q]
    with_reducible exact hvectorAE
  refine ⟨a, b, aHigh, bHigh, ha, hb, haeval, hbeval, ha₂proj, hb₂proj,
    haHigh, hbHigh, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc, haHigh] with t htt hat
    rw [hat]
    exact ha₂proj t htt
  · filter_upwards [ae_restrict_mem measurableSet_Icc, hbHigh] with t htt hbt
    rw [hbt]
    exact hb₂proj t htt


private theorem scalarVectorTimeCoefficients_successor_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (k : ℕ)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k
          linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Kraw := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    u₀ = L (AddCircle.firstJetHs g₀ (k + 2) (Kraw f₀)) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro K E L J A P Q Kraw hu₀ T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let EZ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 1 + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 4))
  let Zraw := EZ.compLpL 2 (timeMeasure T) Z
  let Wraw := fun t => E (W t)
  have hnormalize := circleHsPi_successor_normalization g₀ k T Z W hW hWZ
  have hWraw : ContinuousOn Wraw (Icc 0 T) := hnormalize.1
  have hWZraw : Wraw =ᵐ[timeMeasure T] (fun t => Kraw (Zraw t)) := hnormalize.2
  have hraw := scalarVectorTimeCoefficients_higher_order g₀ F G S u₀ C hF hG hS
    (k := k + 1) (by omega) f₀
  whnf at hraw
  have hs0 := hraw hu₀ T hT
  have hs1 := hs0 Zraw Wraw hWraw hWZraw
  have hsBound := hs1 (fun t ht => by
    refine le_trans ?_ (hbound t ht)
    exact le_of_eq (congrArg norm (firstJetHs_successor_normalization g₀ k (W t))))
  have hs2 := hsBound a₂ b₂
  have hsA := hs2 (fun t ht => by
    refine (ha₂ t ht).trans ?_
    exact congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t)
      (firstJetHs_successor_normalization g₀ k (W t)).symm)
  have hreactionJet (t : ℝ) := congrArg
    (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t)
    (firstJetHs_successor_normalization g₀ k (W t))
  have hs3 := hsA (fun t ht => by
    with_reducible exact ((hb₂ t ht).trans (hreactionJet t).symm))
  refine exists_four_elim hs3 ?_
  intro ar br aHr bHr hrawFacts
  have har := hrawFacts.1
  have hbr := hrawFacts.2.1
  have hae := hrawFacts.2.2.1
  have hbe := hrawFacts.2.2.2.1
  have hap := hrawFacts.2.2.2.2.1
  have hbp := hrawFacts.2.2.2.2.2.1
  have haH := hrawFacts.2.2.2.2.2.2.1
  have hbH := hrawFacts.2.2.2.2.2.2.2.1
  exact scalarVectorTimeCoefficients_reindex g₀ k T
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t (J (W t)))
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t (J (W t)))
    a₂ b₂ ar br aHr bHr har hbr
    (fun t ht => (hae t ht).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t)
      (firstJetHs_successor_normalization g₀ k (W t))))
    (fun t ht => (hbe t ht).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t)
      (firstJetHs_successor_normalization g₀ k (W t))))
    hap hbp haH hbH

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private theorem ambient_coefficients_successor_order
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
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k
          linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro C g₀ K E L J A P Q T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 1 + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_successor_order g₀ _ _ _ _ C hF hReaction hS k f₀
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he (k + 1))
    T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJetHs_coefficients_of_projection
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T ρ : ℝ)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (diffusion : ℝ → CircleHsPi g₀ (Fin n ⊕ Fin n) 1 → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n ⊕ Fin n) 1 → CircleHsPi g₀ (Fin n) 1) :
    let P := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (3 : ℝ) ≤ (k : ℝ) + 3)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have hk := Nat.cast_nonneg (α := ℝ) k
            push_cast
            linarith only [hk] : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    (∀ t ∈ Icc 0 T, P (W t) = W₃ t) →
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) = diffusion t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      reaction t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ ρ) ∧
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) = diffusion t (J (W t))) ∧
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      reaction t (J (W t))) := by
  intro P J₃ A₂ E L J hWP hbound hdiffusion hreaction
  have hjet (t : ℝ) (htt : t ∈ Icc 0 T) : J (W t) = J₃ (W₃ t) :=
    circle_firstJetHs_eq_of_projection g₀ k (W t) (W₃ t) (hWP t htt)
  refine ⟨?_, ?_, ?_⟩
  · intro t htt
    exact (le_of_eq (congrArg norm (hjet t htt))).trans (hbound t htt)
  · intro t htt
    exact (hdiffusion t htt).trans (congrArg (diffusion t) (hjet t htt).symm)
  · intro t htt
    exact (hreaction t htt).trans (congrArg (reaction t) (hjet t htt).symm)

private theorem circle_sobolev_boost_data_reindex
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
    (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let Ih := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Ia := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let N₃ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 3 : ℕ) : ℝ) ≤ (k : ℝ) + 3)
    let N₃V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₃)
    let WN := fun t => N₃V (W t)
    let aHN := N₃.compLpL 2 (timeMeasure T) aHigh
    let bHN := N₃V.compLpL 2 (timeMeasure T) bHigh
    let IhN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let I₁N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let KW := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only :
        ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    (fun t => Ih (aHigh t)) =ᵐ[timeMeasure T] a →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Ih) (bHigh t))
      =ᵐ[timeMeasure T] b →
    (fun t => Ia (Ih (aHigh t))) =ᵐ[timeMeasure T] a₂ →
    ContinuousOn WN (Icc 0 T) ∧
    (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, WN t i = KW (VN t i)) ∧
    (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T] (fun t => E₁ (A₂ (a₂ t))) := by
  intro R Ih Ia A₂ E₁ N₂ N₂V N₄ VN aN bN N₃ N₃V WN aHN bHN IhN I₁N KW
    hW hWV haHigh hbHigh haHigh₂
  have hWN : ContinuousOn WN (Icc 0 T) := N₃V.continuous.comp_continuousOn hW
  have haHN : (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN := by
    filter_upwards [N₃.coeFn_compLpL aHigh, haHigh] with t hnt hht
    change IhN (aHN t) = N₂ (a t)
    rw [hnt, ← hht]
    apply TensorHs.ext
    rfl
  have hbHN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i := by
    filter_upwards [N₃V.coeFn_compLpL bHigh, hbHigh] with t hnt hht
    intro i
    rw [hnt]
    change IhN (N₃ (bHigh t i)) = N₂ (b t i)
    rw [← hht]
    apply TensorHs.ext
    rfl
  have hWNVN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, WN t i = KW (VN t i) := by
    filter_upwards [hWV, N₄.coeFn_compLpL V] with t hwt hnt
    intro i
    change N₃ (W t i) = KW (VN t i)
    rw [hwt, hnt]
    apply TensorHs.ext
    rfl
  have hprincipal : (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T]
      (fun t => E₁ (A₂ (a₂ t))) := by
    filter_upwards [N₃.coeFn_compLpL aHigh, haHigh₂] with t hnt ht
    rw [hnt]
    have hh := congrArg (E₁.comp A₂) ht
    refine Eq.trans ?_ hh
    apply TensorHs.ext
    rfl
  exact ⟨hWN, haHN, hbHN, hWNVN, hprincipal⟩

private theorem circle_sobolev_successor_of_forcing_lift
    {n : ℕ} (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) {T : ℝ} (hT : 0 < T)
    (Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (FH : timeL2 (CircleHsPi g₀ (Fin n) 1) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T) :
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    VN = maximalRegularityDuhamelVectorField hT 0 Fm →
    iteratedParameterDerivativeDuhamelForcing g₀ 0 (k + 2) hT Fm =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)))).compLpL
            2 (timeMeasure T) FH →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      S.compLpL 2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
  intro N₄ VN R S hW hWV hVF hFH
  have hVN : VN =ᵐ[timeMeasure T] (fun t => N₄ (V t)) := N₄.coeFn_compLpL V
  obtain ⟨Wraw, hWraw, _, hWrawF⟩ :=
    exists_continuousOn_representative_of_iteratedParameterDerivative_forcing_lift
      g₀ (k + 2) hT Fm FH hFH
  obtain ⟨Vraw, hVrawF⟩ :=
    exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_forcing_lift
      g₀ (k + 2) hT Fm FH hFH
  let B₄ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : (k : ℝ) + 4 ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let B₅ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : (k : ℝ) + 5 ≤ ((k + 2 : ℕ) : ℝ) + 3)
  let Wnew := fun t => B₄ (Wraw t)
  let Vnew := B₅.compLpL 2 (timeMeasure T) Vraw
  have hWnew : ContinuousOn Wnew (Icc 0 T) := B₄.continuous.comp_continuousOn hWraw
  have hWrawVN : Wraw =ᵐ[timeMeasure T] VN := by
    rw [hVF]
    exact hWrawF
  have hWnewV : Wnew =ᵐ[timeMeasure T] V := by
    filter_upwards [hWrawVN, hVN] with t hwt hnt
    change B₄ (Wraw t) = V t
    rw [hwt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  let Sraw := circleHsPiInclusion g₀ (Fin n)
    (by linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 3)
  have hVrawVN : Sraw.compLpL 2 (timeMeasure T) Vraw = VN := hVrawF.trans hVF.symm
  have hVnewV : S.compLpL 2 (timeMeasure T) Vnew = V := by
    apply Lp.ext
    have hraw := Sraw.coeFn_compLpL Vraw
    rw [hVrawVN] at hraw
    filter_upwards [S.coeFn_compLpL Vnew, B₅.coeFn_compLpL Vraw, hraw, hVN]
      with t hst hbt hrt hnt
    rw [hst, hbt]
    have hc : S (B₅ (Vraw t)) = B₄ (Sraw (Vraw t)) := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    rw [hc, ← hrt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hWnewW : ∀ t ∈ Icc 0 T, R (Wnew t) = W t := by
    apply Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) (ne_of_lt hT)
      _ (R.continuous.comp_continuousOn hWnew) hW
    filter_upwards [hWnewV, hWV] with t ht hwt
    change R (Wnew t) = W t
    rw [ht]
    exact hwt.symm
  have hWnewVnew : Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
    have hh := S.coeFn_compLpL Vnew
    rw [hVnewV] at hh
    exact hWnewV.trans hh
  exact ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew⟩

private theorem circle_sobolev_forcing_data_reindex
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (U₂ : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℝ) + 2)) T) :
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let JN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let KN := circleHsPiInclusion g₀ (Fin n)
      (by exact_mod_cast (show 2 + 2 ≤ (k + 2) + 2 by omega) :
        ((2 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2)
    ContinuousOn a (Icc 0 T) → ContinuousOn b (Icc 0 T) →
    (∀ t ∈ Icc 0 T, P (a t) = a₂ t) →
    (∀ t ∈ Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    ContinuousOn aN (Icc 0 T) ∧ ContinuousOn bN (Icc 0 T) ∧
    (fun t => JN (aN t)) =ᵐ[timeMeasure T] a₂ ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, JN (bN t i) = b₂ t i) ∧
    KN.compLpL 2 (timeMeasure T) VN = U₂ := by
  intro P Q N₂ N₂V N₄ VN aN bN JN KN ha hb ha₂proj hb₂proj hVQ
  have haN : ContinuousOn aN (Icc 0 T) := N₂.continuous.comp_continuousOn ha
  have hbN : ContinuousOn bN (Icc 0 T) := N₂V.continuous.comp_continuousOn hb
  have hapN : (fun t => JN (aN t)) =ᵐ[timeMeasure T] a₂ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    refine Eq.trans ?_ (ha₂proj t htt)
    apply TensorHs.ext
    rfl
  have hbpN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, JN (bN t i) = b₂ t i := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    intro i
    refine Eq.trans ?_ (congrArg (fun z => z i) (hb₂proj t htt))
    apply TensorHs.ext
    rfl
  have hVN : VN =ᵐ[timeMeasure T] (fun t => N₄ (V t)) := N₄.coeFn_compLpL V
  have hVNQ : KN.compLpL 2 (timeMeasure T) VN = U₂ := by
    apply Lp.ext
    have hQ := Q.coeFn_compLpL V
    rw [hVQ] at hQ
    filter_upwards [KN.coeFn_compLpL VN, hVN, hQ] with t hkt hnt hqt
    rw [hkt, hnt, hqt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact ⟨haN, hbN, hapN, hbpN, hVNQ⟩

private theorem circle_sobolev_successor_of_principal_norm_lt_one
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) {T : ℝ} (hT : 0 < T)
    (Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
    (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) (C2h C2l : ℝ≥0) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
    let Ih := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Ia := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let Pb := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    (fun t => Ih (aHigh t)) =ᵐ[timeMeasure T] a →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Ih) (bHigh t))
      =ᵐ[timeMeasure T] b →
    (fun t => Ia (Ih (aHigh t))) =ᵐ[timeMeasure T] a₂ →
    VN = maximalRegularityDuhamelVectorField hT 0 Fm →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
          (VN t i) + Fm t i =
        scalarHsMul g₀ (k + 2) (by simp) (aN t)
          (AddCircle.parameterSecondDerivativeHs g₀ (k + 2)
            (Pb (fHigh i) + VN t i)) + bN t i) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      S.compLpL 2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
  intro R S Ih Ia A₂ E₁ N₂ N₂V N₄ VN aN bN Pb hW hWV haHigh hbHigh haHigh₂ hVF hPDE
    hC2h hC2l hC2hlt hC2llt
  let N₃ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : ((k + 3 : ℕ) : ℝ) ≤ (k : ℝ) + 3)
  let N₃V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₃)
  let WN := fun t => N₃V (W t)
  let aHN := N₃.compLpL 2 (timeMeasure T) aHigh
  let bHN := N₃V.compLpL 2 (timeMeasure T) bHigh
  let IhN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
      ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let I₁N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
      ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let KW := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only :
      ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
  have hnatural := circle_sobolev_boost_data_reindex g₀ k T W V a b aHigh bHigh a₂
  have hnaturalFacts := hnatural hW hWV haHigh hbHigh haHigh₂
  have hWN : ContinuousOn WN (Icc 0 T) := hnaturalFacts.1
  have haHN : (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN := hnaturalFacts.2.1
  have hbHN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i :=
    hnaturalFacts.2.2.1
  have hWNVN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      WN t i = KW (maximalRegularityDuhamelVectorField hT 0 Fm t i) := by
    rw [← hVF]
    exact hnaturalFacts.2.2.2.1
  have hprincipal : (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T]
      (fun t => E₁ (A₂ (a₂ t))) := hnaturalFacts.2.2.2.2
  have hAh : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (I₁N (aHN t))‖ ≤ C2h :=
    (hprincipal.fun_comp (fun z =>
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ z‖)).trans_le hC2h
  have hAl : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (I₁N (aHN t))‖ ≤ C2l :=
    (hprincipal.fun_comp (fun z =>
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ z‖)).trans_le hC2l
  have hboost := exists_iteratedParameterDerivative_forcing_lift_of_principal_norm_lt_one
    (ι := Fin n) g₀ k hT
  obtain ⟨FH, hFH⟩ := hboost Fm fHigh WN hWN aHN bHN bN C2h C2l
    hbHN hWNVN (by
      filter_upwards [hPDE, haHN] with t ht hat
      intro i
      rw [hat, ← hVF]
      exact ht i) hAh hAl hC2hlt hC2llt
  let E := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  let FH₁ := E.compLpL 2 (timeMeasure T) FH
  let Z := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
  let Z₁ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ))
  have hFH₁ : iteratedParameterDerivativeDuhamelForcing g₀ 0 (k + 2) hT Fm =
      Z₁.compLpL 2 (timeMeasure T) FH₁ := by
    rw [hFH]
    change Z.compLpL 2 (timeMeasure T) FH = _
    apply Lp.ext
    filter_upwards [Z.coeFn_compLpL FH, Z₁.coeFn_compLpL FH₁, E.coeFn_compLpL FH]
      with t hzt hz₁t het
    rw [hzt, hz₁t, het]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact circle_sobolev_successor_of_forcing_lift g₀ k hT Fm FH₁ W V hW hWV hVF hFH₁

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_original_forcing_successor_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (gM : SmoothRiemannianMetric I M) (k : ℕ) {T : ℝ} (hT : 0 < T)
    (F₂ : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) 2) T)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 2)
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) 2)
    (V : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((k : ℝ) + 2))
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    let g₀ := c₀.pullbackMetric gM
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let JN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    (∀ t ∈ Icc 0 T, P (a t) = a₂ t) →
    (∀ t ∈ Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ gM e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    ∃ Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => JN)).compLpL
        2 (timeMeasure T) Fm = F₂ ∧
      VN = maximalRegularityDuhamelVectorField hT 0 Fm ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
            (VN t i) + Fm t i =
          scalarHsMul g₀ (k + 2) (by simp) (aN t)
            (AddCircle.parameterSecondDerivativeHs g₀ (k + 2)
              (ambientSobolev c₀ gM e he (((k + 2 : ℕ) : ℝ) + 2) i + VN t i)) +
                bN t i := by
  intro g₀ U₂ P Q N₂ N₂V N₄ VN aN bN JN ha₂proj hb₂proj hVQ hPDE₂
  have hinput := circle_sobolev_forcing_data_reindex g₀ k T V a b a₂ b₂ U₂
  have hinputFacts := hinput ha hb ha₂proj hb₂proj hVQ
  dsimp only [g₀] at hinputFacts
  have hproducer := ambient_original_forcing_higher_equation c₀ he gM (m := k + 2)
    (by omega) hT F₂ a₂ b₂ VN aN bN hinputFacts.1 hinputFacts.2.1
  have hresult := hproducer hinputFacts.2.2.1 hinputFacts.2.2.2.1
    hinputFacts.2.2.2.2 hPDE₂
  dsimp only [g₀, VN, aN, bN, N₂, N₂V, N₄, JN]
  exact hresult

private theorem ambient_sobolev_regularity_successor
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {Udom : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r Udom)
    (hEU : Set.range e ⊆ Udom) (hleft : ∀ p, r (e p) = p) (β : Udom)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (k : ℕ) {T : ℝ} (hT : 0 < T) (C2h C2l : ℝ≥0) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let P := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    T ≤ (ScalarVectorTimeCoefficients.radius C) →
    ∀ (F₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T)
      (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
      (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2),
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t))) →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∀ (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T),
    ContinuousOn W (Icc 0 T) →
    (∀ t ∈ Icc 0 T, P (W t) = W₃ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5)).compLpL
          2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
        (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5) (Vnew t)) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 4)
          (Wnew t) = W₃ t) ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)).compLpL
          2 (timeMeasure T) Vnew = U₂ := by
  intro C g₀ J₃ A₂ E₁ P Q R hTC F₂ W₃ a₂ b₂ U₂ hJ₃ ha₂ hb₂ hPDE₂
    hC2h hC2l hC2hlt hC2llt W V hW hWP hVQ hWV
  have hjetTransfer := circle_firstJetHs_coefficients_of_projection g₀ k T
    (ScalarVectorTimeCoefficients.radius C) W W₃ a₂ b₂
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t)
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t)
  have hjetFacts := hjetTransfer hWP hJ₃ ha₂ hb₂
  dsimp only [C, g₀] at hjetFacts
  have hcoeff := ambient_coefficients_successor_order c₀ g ht he hr hEU hleft β hG k
  whnf at hcoeff
  have hcoeffT := hcoeff T hTC
  have hcoeffW := hcoeffT V W hW hWV
  have hcoeffBound := hcoeffW hjetFacts.1
  have hcoeffBase := hcoeffBound a₂ b₂
  have hcoeffDiffusion := hcoeffBase hjetFacts.2.1
  have hcoeffAll := hcoeffDiffusion hjetFacts.2.2
  refine exists_four_elim hcoeffAll ?_
  intro a b aHigh bHigh hcoeffFacts
  have ha := hcoeffFacts.1
  have hb := hcoeffFacts.2.1
  have hae := hcoeffFacts.2.2.1
  have hbe := hcoeffFacts.2.2.2.1
  have ha₂proj := hcoeffFacts.2.2.2.2.1
  have hb₂proj := hcoeffFacts.2.2.2.2.2.1
  have haHigh := hcoeffFacts.2.2.2.2.2.2.1
  have hbHigh := hcoeffFacts.2.2.2.2.2.2.2.1
  have haHigh₂ := hcoeffFacts.2.2.2.2.2.2.2.2.1
  have hbHigh₂ := hcoeffFacts.2.2.2.2.2.2.2.2.2
  let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
  let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
  let N₄ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
  let VN := N₄.compLpL 2 (timeMeasure T) V
  let aN := fun t => N₂ (a t)
  let bN := fun t => N₂V (b t)
  have hforcing := ambient_original_forcing_successor_order c₀ he (g 0) k hT
    F₂ a₂ b₂ V a b ha hb
  obtain ⟨Fm, hFm₂, hVF, hPDE⟩ := hforcing ha₂proj hb₂proj hVQ hPDE₂
  let fHigh := ambientSobolev c₀ (g 0) e he (((k + 3 : ℕ) : ℝ) + 2)
  let Pb := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only :
      ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
  have hbaseline (i : Fin n) : Pb (fHigh i) =
      ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 2) i := by
    change tensorHsInclusion _ (ccTensorToHs g₀ 0 (((k + 3 : ℕ) : ℝ) + 2) _) = _
    rw [tensorHsInclusion_ccTensorToHs]
    rfl
  obtain ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew⟩ :=
    circle_sobolev_successor_of_principal_norm_lt_one g₀ k hT Fm fHigh W V
      a b aHigh bHigh a₂ C2h C2l hW hWV haHigh hbHigh haHigh₂ hVF (by
        filter_upwards [hPDE] with t ht
        intro i
        rw [hbaseline]
        exact ht i) hC2h hC2l hC2hlt hC2llt
  let S := circleHsPiInclusion g₀ (Fin n)
    (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
  refine ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew, ?_, ?_⟩
  · intro t htt
    have hh := (congrArg P (hWnewW t htt)).trans (hWP t htt)
    refine Eq.trans ?_ hh
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  · apply Lp.ext
    have hS := S.coeFn_compLpL Vnew
    rw [hVnewV] at hS
    have hQ := Q.coeFn_compLpL V
    rw [hVQ] at hQ
    let Rbase := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)
    filter_upwards [Rbase.coeFn_compLpL Vnew, hS, hQ] with t hr hs hq
    rw [hr, hq, hs]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem scalarVectorTimeCoefficients_continuousOn_h2_weak_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    T ≤ ScalarVectorTimeCoefficients.radius C →
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    W =ᵐ[timeMeasure T] field →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))
          (Q (f₀ + field t)) +
          circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) →
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro J K H₂ field L Q m hTC hu₀ hwfield hWfield hJW heq
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  have hcoeffReal :
      ∃ (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)),
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, tensorHsInclusion
          (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) (a₂ t) = tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) (b₂ t) =
            circleHsPiCongr g₀ (Fin n)
              (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) := by
    obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq, _⟩ :=
      scalarVectorTimeCoefficients_continuousOn_h2 g₀ F G S u₀ C
        hF hG hS hTC f₀ W hW hu₀ hJW
    refine ⟨a₂, b₂, ha₂, hb₂, ?_, ?_⟩
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
  have hcoeff :
      ∃ (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
            circleHsPiCongr g₀ (Fin n)
              (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) := by
    norm_num only [H₂, CircleHsPi] at hcoeffReal ⊢
    exact hcoeffReal
  obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq⟩ := hcoeff
  refine ⟨a₂, b₂, hW, hWfield, hJW, ha₂, hb₂, haeq, hbeq, ?_⟩
  filter_upwards [heq, hwfield, hWfield,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t heqₜ hwₜ hWₜ htt
  have hwW : w t = K (W t) := by rw [hwₜ, hWₜ]
  have hA : H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) := by
    rw [hwW]
    exact haeq t htt
  have hB : circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
    circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (w t))) := by
    rw [hwW]
    exact hbeq t htt
  intro i
  rw [hA]
  have hb := congrArg (fun z => z i) hB
  change H₂ (b₂ t i) = _ at hb
  rw [hb]
  exact congrArg (fun z => z i) heqₜ

private theorem scalarVectorTimeCoefficients_h2_weak_equation_of_classical_time_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    T ≤ ScalarVectorTimeCoefficients.radius C →
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))
          (Q (f₀ + field t)) +
          circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) →
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ F G S u₀ C hT f₀ J u gforce →
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro J K H₂ field L Q m hTC hu₀ hwfield heq hclass
  rcases hclass with ⟨W, hW, _, hWfield, _, hJW, _⟩
  change ∀ t ∈ Icc 0 T,
    ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C at hJW
  refine Exists.intro W ?_
  exact scalarVectorTimeCoefficients_continuousOn_h2_weak_equation
    g₀ F G S u₀ C hF hG hS hT f₀ gforce w W hW
    hTC hu₀ hwfield hWfield hJW heq

private theorem circle_exists_forcing_h2_of_weak_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : ∀ i : Fin n, tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₄ i) = f₀ i)
    (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ))
    (ha₂ : ContinuousOn a₂ (Icc 0 T)) (hb₂ : ContinuousOn b₂ (Icc 0 T)) :
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (field t i) + gforce t i =
        scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) FH = gforce ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) = field ∧
      let UH := maximalRegularityDuhamelVectorField hT 0 FH
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
            (UH t i) + FH t i =
          scalarHsMul g₀ 2 (by norm_num) (a₂ t)
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ i + UH t i)) + b₂ t i := by
  intro H₂ field heq
  let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
  let P₄ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K₄)
  obtain ⟨field₄, hfield₄⟩ := ambient_fourth_order_lift_of_parameterDerivative_lift
    g₀ hT gforce hlift
  have hfield₄ae : ∀ᵐ t ∂timeMeasure T, P₄ (field₄ t) = field t := by
    have hh := P₄.coeFn_compLpL field₄
    rw [hfield₄] at hh
    exact hh.symm
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (K₄ (field₄ t i)) + gforce t i =
        scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i + field₄ t i))) + H₂ (b₂ t i) := by
    filter_upwards [heq, hfield₄ae] with t heqₜ hfieldₜ
    intro i
    have hfi : K₄ (field₄ t i) = field t i := congrArg (fun z => z i) hfieldₜ
    rw [K₄.map_add, hf₄, hfi]
    exact heqₜ i
  obtain ⟨FH, hFH, hU, hhigh⟩ := AddCircle.exists_timeL2_parabolic_forcing_lift_of_continuousOn
    g₀ (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) hT f₄ field₄ gforce a₂ b₂ ha₂ hb₂ hfield₄ hweak
  refine ⟨FH, hFH, ?_, ?_⟩
  · rw [← hU]
    exact hfield₄
  · rw [← hU]
    exact hhigh

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))


omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem tensorHsInclusion_ambientSobolev
    (gM : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a ≤ b) (i : Fin n) :
    tensorHsInclusion (g := c₀.pullbackMetric gM) (r := 0) (s := 0) hab
      (ambientSobolev c₀ gM e he b i) = ambientSobolev c₀ gM e he a i := by
  change tensorHsInclusion hab (ccTensorToHs (c₀.pullbackMetric gM) 0 b _) = _
  rw [tensorHsInclusion_ccTensorToHs]
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_exists_forcing_h2_of_weak_equation
    (gM : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric gM) hT gforce)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ))
    (ha₂ : ContinuousOn a₂ (Icc 0 T)) (hb₂ : ContinuousOn b₂ (Icc 0 T)) :
    let H₂ := tensorHsInclusion (g := c₀.pullbackMetric gM) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := c₀.pullbackMetric gM) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (field t i) + gforce t i =
        scalarHsMul (c₀.pullbackMetric gM) 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs (c₀.pullbackMetric gM) 1
            (ambientSobolev c₀ gM e he (((1 : ℕ) : ℝ) + 2) i + field t i)) + H₂ (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ)) T,
      (circleHsPiInclusion (c₀.pullbackMetric gM) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) FH = gforce ∧
      (circleHsPiInclusion (c₀.pullbackMetric gM) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) = field ∧
      let UH := maximalRegularityDuhamelVectorField hT 0 FH
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := c₀.pullbackMetric gM) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
            (UH t i) + FH t i =
          scalarHsMul (c₀.pullbackMetric gM) 2 (by norm_num) (a₂ t)
            (AddCircle.parameterSecondDerivativeHs (c₀.pullbackMetric gM) 2
              (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i + UH t i)) + b₂ t i := by
  intro H₂ field hweak
  exact circle_exists_forcing_h2_of_weak_equation
    (c₀.pullbackMetric gM) hT gforce hlift
    (ambientSobolev c₀ gM e he (((1 : ℕ) : ℝ) + 2))
    (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2))
    (fun i => tensorHsInclusion_ambientSobolev
      (c₀ := c₀) (he := he) (gM := gM) (by norm_num) i)
    a₂ b₂ ha₂ hb₂ hweak

private theorem ambient_original_coefficients_h2_weak_equation
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro C g₀ J K H₂ f₀ field
  have hclass := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, _, _, hwfield, _, _, _, heq, _⟩
  exact scalarVectorTimeCoefficients_h2_weak_equation_of_classical_time_equation
    g₀ _ _ _ _ C hF hReaction hS hT f₀ u gforce w
    (hTρ.trans hρC) (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwfield heq hclass

private theorem ambient_original_forcing_h2_equation
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) FH = gforce ∧
        (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
            2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) =
              maximalRegularityDuhamelVectorField hT 0 gforce ∧
        let UH := maximalRegularityDuhamelVectorField hT 0 FH
        ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
          tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
              (UH t i) + FH t i =
            scalarHsMul g₀ 2 (by norm_num) (a₂ t)
              (AddCircle.parameterSecondDerivativeHs g₀ 2
                (ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2) i + UH t i)) + b₂ t i := by
  whnf
  have hsource := ambient_original_coefficients_h2_weak_equation
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  whnf at hsource
  refine Exists.imp (fun W => ?_) hsource
  refine Exists.imp (fun a₂ => ?_)
  refine Exists.imp (fun b₂ => ?_)
  refine And.imp (fun h => h) ?_
  refine And.imp (fun h => h) ?_
  refine And.imp (fun h => h) ?_
  rintro ⟨ha₂, hb₂, hcoeff⟩
  refine ⟨ha₂, hb₂, ?_⟩
  refine ⟨hcoeff.1, hcoeff.2.1, ?_⟩
  exact ambient_exists_forcing_h2_of_weak_equation
    (c₀ := c₀) (he := he) (gM := g 0)
    hT gforce hlift a₂ b₂ ha₂ hb₂ hcoeff.2.2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open private CircleHsPi circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJet_h3_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (x : CircleHsPi g₀ ι 3) :
    let J := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiCongr g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ ι (by norm_num : (2 : ℝ) ≤ 3)
    let J₃ := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiInclusion g₀ ι (by norm_num : (1 : ℝ) + 1 ≤ 3))
    J (K x) = J₃ x := by
  intro J K J₃
  have hK : circleHsPiCongr g₀ ι
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (K x) =
      circleHsPiInclusion g₀ ι (by norm_num : (1 : ℝ) + 1 ≤ 3) x := by
    simpa only [K, circleHsPiInclusion, circleHsPiCongr, tensorHsCongr_refl,
      LinearIsometryEquiv.piLpCongrRight_refl, LinearIsometryEquiv.coe_refl, id_eq] using
      circleHsPiCongr_inclusion g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (rfl : (3 : ℝ) = 3)
        (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (1 : ℝ) + 1 ≤ 3) x
  exact congrArg (circleFirstJet (ι := ι) g₀) hK

private theorem circle_firstJet_seed_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (x : CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) :
    let J := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiCongr g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ ι (by norm_num : (2 : ℝ) ≤ 3)
    let L₃ := circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Jraw := fun z => circleFirstJet g₀ (circleHsPiCongr g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) z)
    let Kraw := circleHsPiInclusion g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    J (K (L₃ x)) = Jraw (Kraw x) := by
  intro J K L₃ Jraw Kraw
  have hcoeff {a b : ℝ} (hab : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab v).coeff = v.coeff := by
    cases hab
    rfl
  have hin : circleHsPiCongr g₀ ι
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (K (L₃ x)) =
      circleHsPiCongr g₀ ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (Kraw x) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simpa only [circleHsPiCongr_apply, hcoeff] using
      (show (K (L₃ x) i).coeff = (Kraw x i).coeff from rfl)
  exact congrArg (circleFirstJet (ι := ι) g₀) hin

private theorem circleHsPi_ae_eq_of_projection
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ) (U : timeL2 (CircleHsPi g₀ ι ((2 : ℝ) + 2)) T)
    (V : timeL2 (CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) T)
    (W : ℝ → CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) :
    let L₃ := circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Praw := circleHsPiInclusion g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) + 2)
    let P := circleHsPiInclusion g₀ ι (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
    W =ᵐ[timeMeasure T] V → Praw.compLpL 2 (timeMeasure T) U = V →
      (fun t => L₃ (W t)) =ᵐ[timeMeasure T] (fun t => P (U t)) := by
  intro L₃ Praw P hW hU
  have hp := Praw.coeFn_compLpL U
  rw [hU] at hp
  filter_upwards [hW, hp] with t hWt hpt
  rw [hWt, hpt]
  apply PiLp.ext
  intro i
  exact (tensorHsInclusion_trans_apply
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) + 2) (U t i)).symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open private CircleHsPi circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem parameterPrincipalLow_norm_eq
    {n : ℕ} (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) (t : ℝ) :
    ‖parameterPrincipalLow (n := n) g₀ a t‖ =
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t))‖ := by
  let R := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  have hR : ‖R‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hN : ‖parameterNormalizeZero (n := n) g₀‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hrecover : R.comp (parameterPrincipalLow (n := n) g₀ a t) =
      AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t)) := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    change tensorHsInclusion (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
        (AddCircle.parameterPrincipalOperatorH0Pi g₀
          (tensorHsInclusion
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
            (a t)) x i)) = _
    rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  · rw [← hrecover]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (norm_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
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
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_parameter_principal_bounds_of_sobolev_solution
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let Jraw := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let Kraw := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∀ (Wraw : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ)),
      Wraw =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce →
      (∀ t ∈ Icc 0 T,
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (a₂ t) =
          tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (Jraw (Kraw (Wraw t))))) →
      ∃ C2h C2l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
        (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ Jraw Kraw H₂ E₁ Wraw a₂ hWrawfield haRaw
  have hfacts' := hfacts
  rcases hfacts' with ⟨_, _, _, _, _, hforce, _, w, hw, _, hwu,
    hbound, _, hJ, _, _⟩
  obtain ⟨aControl, _, haControl, _, haNorm, _⟩ :=
    ambientH2CoefficientsAtState c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ gforce w hw hwu hbound hforce
  have hpa : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w aControl :=
    haControl
  obtain ⟨C2h, C2l, hC2h, hC2l, hsmallh, hsmalll⟩ :=
    ambient_h2_coefficient_contraction c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ w aControl hpa haNorm hbound hJ
  have hcoefficient : ∀ᵐ t ∂timeMeasure T,
      E₁ (H₂ (a₂ t)) = tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (aControl t) := by
    dsimp only [ambientDiffusionProjection] at hpa
    filter_upwards [hpa, hwu, hWrawfield, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t hat hwt hWt htt
    have hstate : w t = Kraw (Wraw t) := by rw [hwt, hWt]
    rw [hat, hstate, ← haRaw t htt]
    apply TensorHs.ext
    rfl
  have hhigh : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h := by
    filter_upwards [hC2h, hcoefficient] with t ht hct
    rw [hct]
    exact ht
  have hlow : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l := by
    filter_upwards [hC2l, hcoefficient] with t ht hct
    rw [hct, ← parameterPrincipalLow_norm_eq (n := n) g₀ aControl t]
    exact ht
  have hC2hlt : (C2h : ℝ) < 1 :=
    (le_mul_of_one_le_right C2h.coe_nonneg
      (le_add_of_nonneg_right hT.le)).trans_lt
      ((le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg (1 + T)) ENNReal.toReal_nonneg)).trans_lt hsmallh)
  have hC2llt : (C2l : ℝ) < 1 :=
    (le_mul_of_one_le_right C2l.coe_nonneg
      (le_add_of_nonneg_right hT.le)).trans_lt
      ((le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg (1 + T)) ENNReal.toReal_nonneg)).trans_lt hsmalll)
  exact ⟨C2h, C2l, hhigh, hlow, hC2hlt, hC2llt⟩

private theorem ambient_sobolev_solution_h2_forcing
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∃ F₂ : timeL2 (CircleHsPi g₀ (Fin n) (2 : ℝ)) T,
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)).compLpL
        2 (timeMeasure T) F₂ = gforce ∧
      ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (3 : ℝ))
        (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)) (C2h C2l : ℝ≥0),
        ContinuousOn W (Icc 0 T) ∧
        W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
          (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
            (maximalRegularityDuhamelVectorField hT 0 gforce t)) ∧
        W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
          (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
            (maximalRegularityDuhamelVectorField hT 0 F₂ t)) ∧
        (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, H₂ (a₂ t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
        (∀ t ∈ Icc 0 T,
          circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
            extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
          tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (2 : ℝ)
              (maximalRegularityDuhamelVectorField hT 0 F₂ t i) + F₂ t i =
            scalarHsMul g₀ 2 (by norm_num) (a₂ t)
              (AddCircle.parameterSecondDerivativeHs g₀ 2
                (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i +
                  maximalRegularityDuhamelVectorField hT 0 F₂ t i)) + b₂ t i) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
        (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ J K H₂ E₁
  have hrich := ambient_original_forcing_h2_equation
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  whnf at hrich
  rcases hrich with ⟨Wraw, a₂, b₂, hWraw, hWrawfield, hJWraw, ha₂, hb₂, haRaw, hbRaw,
    F₂, hF₂, hU₂, hPDE⟩
  let L₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let W := fun t => L₃ (Wraw t)
  let Jraw : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)) :=
    fun x => circleFirstJet g₀ (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) x)
  let Kraw := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  have hcongr {a b : ℝ} (hab : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab v).coeff = v.coeff := by
    cases hab
    rfl
  have hjet (x : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) :
      J (K (L₃ x)) = Jraw (Kraw x) := by
    exact circle_firstJet_seed_normalization g₀ x
  have hW : ContinuousOn W (Icc 0 T) := L₃.continuous.comp_continuousOn hWraw
  have hWfield : W =ᵐ[timeMeasure T] (fun t => L₃
      (maximalRegularityDuhamelVectorField hT 0 gforce t)) := by
    filter_upwards [hWrawfield] with t ht
    exact congrArg L₃ ht
  let Z := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := (2 : ℝ)) hT 0 F₂
  let P := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
  have hWU₂ : W =ᵐ[timeMeasure T] (fun t => P (Z t)) := by
    have htransport := circleHsPi_ae_eq_of_projection g₀ T Z _ Wraw hWrawfield
    exact htransport hU₂
  have hJW (t : ℝ) (htt : t ∈ Icc 0 T) :
      ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    change ‖J (K (L₃ (Wraw t)))‖ ≤ (ScalarVectorTimeCoefficients.radius C)
    rw [hjet]
    simpa only [C, g₀, Jraw, Kraw, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      using hJWraw t htt
  have haactual (t : ℝ) (htt : t ∈ Icc 0 T) : H₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))) := by
    apply TensorHs.ext
    have hh := congrArg TensorHs.coeff (haRaw t htt)
    rw [hcongr] at hh
    change (a₂ t).coeff =
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (L₃ (Wraw t))))).coeff
    rw [hjet]
    exact hh
  have hbactual (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    have hh := congrArg (fun z => (z i).coeff) (hbRaw t htt)
    rw [circleHsPiCongr_apply, hcongr] at hh
    change (b₂ t i).coeff =
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (K (L₃ (Wraw t)))) i).coeff
    rw [hjet]
    simpa only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      tensorHsInclusion_coeff, C, g₀, Jraw, Kraw, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      using hh
  have hprincipal := ambient_parameter_principal_bounds_of_sobolev_solution
    c₀ g ht he hr hEU hleft β hG hT hTρ hρδ u gforce hfacts
  whnf at hprincipal
  obtain ⟨C2h, C2l, hhigh, hlow, hC2hlt, hC2llt⟩ :=
    hprincipal Wraw a₂ hWrawfield haRaw
  exact ⟨F₂, hF₂, W, a₂, b₂, C2h, C2l, hW, hWfield, hWU₂,
    hJW, ha₂, hb₂, haactual, hbactual, hPDE, hhigh, hlow, hC2hlt, hC2llt⟩


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
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
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem exists_solution_with_property
    {A : Sort*} {B : A → Sort*} {D : ∀ a, B a → Sort*}
    {X : ∀ a b, D a b → Sort*} {Y : ∀ a b d, X a b d → Sort*}
    {P₀ P₁ P₂ P₃ : A → Prop}
    {R : ∀ a b, D a b → Prop}
    {F H Q : ∀ a b d x, Y a b d x → Prop}
    (hsource : ∃ a, P₀ a ∧ P₁ a ∧ P₂ a ∧ P₃ a ∧
      ∃ b d, R a b d ∧ ∃ x y, F a b d x y ∧ H a b d x y)
    (hproperty : ∀ a b d, R a b d → P₁ a → P₃ a →
      ∀ x y, F a b d x y → H a b d x y → Q a b d x y) :
    ∃ a, P₀ a ∧ P₁ a ∧ P₂ a ∧ P₃ a ∧
      ∃ b d, R a b d ∧ ∃ x y, F a b d x y ∧ H a b d x y ∧ Q a b d x y := by
  rcases hsource with ⟨a, hp₀, hp₁, hp₂, hp₃, b, d, hr, x, y, hf, hh⟩
  exact ⟨a, hp₀, hp₁, hp₂, hp₃, b, d, hr, x, y, hf, hh,
    hproperty a b d hr hp₁ hp₃ x y hf hh⟩

private theorem ambient_capped_sobolev_solution_exists_with_parameterDerivative_lift
    {δ : ℝ} (hδ : 0 < δ)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧ ρ ≤ δ ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce := by
  whnf
  obtain ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hfacts⟩ :=
    ambientCappedSobolevSolutionSpec c₀ g ht he hr hEU hleft β hG hδ
  have hlift' := ambient_parameterDerivative_lift_of_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρδ u gforce hfacts hlift
  exact ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hfacts, hlift'⟩

private theorem ambient_sobolev_solution_exists_with_h2_forcing :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ∃ F₂ : timeL2 (CircleHsPi g₀ (Fin n) (2 : ℝ)) T,
            (circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)).compLpL
              2 (timeMeasure T) F₂ = gforce ∧
            ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (3 : ℝ))
              (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
              (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)) (C2h C2l : ℝ≥0),
              ContinuousOn W (Icc 0 T) ∧
              W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
                (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
                  (maximalRegularityDuhamelVectorField hT 0 gforce t)) ∧
              W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
                (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
                  (maximalRegularityDuhamelVectorField hT 0 F₂ t)) ∧
              (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
              ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, H₂ (a₂ t) =
                extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
              (∀ t ∈ Icc 0 T,
                circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
                  extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                    (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
              (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
                tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (2 : ℝ)
                    (maximalRegularityDuhamelVectorField hT 0 F₂ t i) + F₂ t i =
                  scalarHsMul g₀ 2 (by norm_num) (a₂ t)
                    (AddCircle.parameterSecondDerivativeHs g₀ 2
                      (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i +
                        maximalRegularityDuhamelVectorField hT 0 F₂ t i)) + b₂ t i) ∧
              (∀ᵐ t ∂timeMeasure T,
                ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
              (∀ᵐ t ∂timeMeasure T,
                ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
              (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ J K H₂ E₁
  let control := ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG
  have hsource := ambient_capped_sobolev_solution_exists_with_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG control.property.1
    (ambient_parameterDerivative_forcing_lift_at_small_state c₀ g ht he hr hEU hleft β hG)
  whnf at hsource
  refine exists_solution_with_property hsource ?_
  intro ρ T hT hTρ hρC hρδ u gforce hfacts hlift
  with_reducible exact (ambient_sobolev_solution_h2_forcing
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC hρδ u gforce hfacts hlift)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open private CircleHsPi circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_sobolev_tower_of_successor
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ)
    (U₂ : timeL2 (CircleHsPi g₀ ι ((2 : ℝ) + 2)) T)
    (W₃ : ℝ → CircleHsPi g₀ ι 3)
    (hW₃ : ContinuousOn W₃ (Icc 0 T))
    (hW₃U₂ : W₃ =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2) (U₂ t)))
    (hstep : ∀ (k : ℕ)
      (W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 4)) T),
      ContinuousOn W (Icc 0 T) →
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t) →
      (circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)).compLpL
          2 (timeMeasure T) V = U₂ →
      W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4) (V t)) →
      ∃ (Wnew : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 4))
        (Vnew : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 5)) T),
        ContinuousOn Wnew (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 4)
            (Wnew t) = W₃ t) ∧
        (circleHsPiInclusion g₀ ι
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)).compLpL
            2 (timeMeasure T) Vnew = U₂ ∧
        Wnew =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
          (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5) (Vnew t))) :
    ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3),
      ContinuousOn W (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t := by
  let regular (k : ℕ) : Prop :=
    ∃ (W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 4)) T),
      ContinuousOn W (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t) ∧
      (circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)).compLpL
          2 (timeMeasure T) V = U₂ ∧
      W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4) (V t))
  have hall : ∀ k : ℕ, regular k := by
    intro k
    induction k with
    | zero =>
      dsimp only [regular]
      let P₀ := circleHsPiInclusion g₀ ι
        (by norm_num : ((0 : ℕ) : ℝ) + 3 ≤ 3)
      let W₀ := fun t => P₀ (W₃ t)
      let B := circleHsPiInclusion g₀ ι
        (by norm_num : ((0 : ℕ) : ℝ) + 4 ≤ (2 : ℝ) + 2)
      let Q := circleHsPiInclusion g₀ ι
        (by norm_num : (2 : ℝ) + 2 ≤ ((0 : ℕ) : ℝ) + 4)
      let V₀ := B.compLpL 2 (timeMeasure T) U₂
      have hQB (z : CircleHsPi g₀ ι ((2 : ℝ) + 2)) : Q (B z) = z := by
        apply PiLp.ext
        intro i
        change tensorHsInclusion (by norm_num : (2 : ℝ) + 2 ≤ ((0 : ℕ) : ℝ) + 4)
          (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 4 ≤ (2 : ℝ) + 2) (z i)) = z i
        rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
      refine ⟨W₀, V₀, P₀.continuous.comp_continuousOn hW₃, ?_, ?_, ?_⟩
      · intro t ht
        apply PiLp.ext
        intro i
        change tensorHsInclusion (by norm_num : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + 3)
          (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 3 ≤ 3) (W₃ t i)) = W₃ t i
        rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
      · apply Lp.ext
        filter_upwards [Q.coeFn_compLpL V₀, B.coeFn_compLpL U₂] with t hQ hB
        exact hQ.trans ((congrArg Q hB).trans (hQB (U₂ t)))
      · filter_upwards [hW₃U₂, B.coeFn_compLpL U₂] with t hW₃t hB
        change P₀ (W₃ t) = _
        rw [hB]
        refine (congrArg P₀ hW₃t).trans ?_
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
    | succ k hk =>
      obtain ⟨W, V, hW, hWW₃, hVU₂, hWV⟩ := hk
      obtain ⟨Wnew, Vnew, hWnew, hWnewW₃, hVnewU₂, hWnewVnew⟩ :=
        hstep k W V hW hWW₃ hVU₂ hWV
      dsimp only [regular]
      let P := circleHsPiInclusion g₀ ι
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 3 ≤ (k : ℝ) + 4)
      let B := circleHsPiInclusion g₀ ι
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 4 ≤ (k : ℝ) + 5)
      let Q := circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) (k + 1)
            linarith : (2 : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 4)
      let A := circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k
            linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)
      let Vlift := B.compLpL 2 (timeMeasure T) Vnew
      refine ⟨fun t => P (Wnew t), Vlift, P.continuous.comp_continuousOn hWnew,
        ?_, ?_, ?_⟩
      · intro t ht
        refine Eq.trans ?_ (hWnewW₃ t ht)
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
      · refine Eq.trans ?_ hVnewU₂
        apply Lp.ext
        filter_upwards [Q.coeFn_compLpL Vlift, B.coeFn_compLpL Vnew,
          A.coeFn_compLpL Vnew] with t hQ hB hA
        rw [hQ, hB, hA]
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
      · filter_upwards [hWnewVnew, B.coeFn_compLpL Vnew] with t hWt hB
        rw [hB]
        refine (congrArg P hWt).trans ?_
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
  intro k
  obtain ⟨W, _, hW, hWW₃, _, _⟩ := hall k
  exact ⟨W, hW, hWW₃⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_sobolev_regularity_all_orders
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {Udom : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r Udom)
    (hEU : Set.range e ⊆ Udom) (hleft : ∀ p, r (e p) = p) (β : Udom)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {T : ℝ} (hT : 0 < T) (C2h C2l : ℝ≥0) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    T ≤ (ScalarVectorTimeCoefficients.radius C) →
    ∀ (F₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T)
      (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
      (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2),
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    ContinuousOn W₃ (Icc 0 T) →
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t))) →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    W₃ =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2) (U₂ t)) →
    ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3),
      ContinuousOn W (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t := by
  intro C g₀ J₃ A₂ E₁ hTC F₂ W₃ a₂ b₂ U₂ hW₃ hJ₃ ha₂ hb₂ hPDE hC2h hC2l hsmallh hsmalll hW₃U₂
  apply circle_sobolev_tower_of_successor g₀ T U₂ W₃ hW₃ hW₃U₂
  intro k W V hW hWW₃ hVU₂ hWV
  have hstep := ambient_sobolev_regularity_successor
    c₀ g ht he hr hEU hleft β hG k hT C2h C2l
  whnf at hstep
  have hdata := hstep hTC F₂ W₃ a₂ b₂
  whnf at hdata
  dsimp only [C, g₀, J₃] at hJ₃
  have hjet := hdata hJ₃
  dsimp only [C, g₀, J₃, A₂] at ha₂
  have hdiffusion := hjet ha₂
  dsimp only [C, g₀, J₃, A₂] at hb₂
  have hreaction := hdiffusion hb₂
  dsimp only [g₀, U₂] at hPDE
  have hequation := hreaction hPDE
  have hsmall := hequation hC2h hC2l hsmallh hsmalll
  obtain ⟨Wnew, Vnew, hWnew, _, _, hWnewVnew, hWnewW₃, hVnewU₂⟩ :=
    hsmall W V hW hWW₃ hVU₂ hWV
  exact ⟨Wnew, Vnew, hWnew, hWnewW₃, hVnewU₂, hWnewVnew⟩

private theorem ambient_sobolev_solution_exists_with_sobolev_tower :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2),
            ContinuousOn W (Icc 0 T) ∧
            ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
              (by
                have hk := Nat.cast_nonneg (α := ℝ) k;
                norm_num only [Nat.cast_one];
                linarith only [hk] : ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u.toFun t := by
  intro C g₀
  have hseed := ambient_sobolev_solution_exists_with_h2_forcing
    c₀ g ht he hr hEU hleft β hG
  whnf at hseed
  obtain ⟨ρ, hρ, hρC, hρ1, _, T, hT, hTρ, u, gforce, hfacts, hlift,
    F₂, _, W₃, a₂, b₂, C2h, C2l, hW₃, hW₃field, hW₃U₂, hJW₃,
    _, _, ha₂, hb₂, hPDE, hC2h, hC2l, hsmallh, hsmalll⟩ := hseed
  let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
  let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
  have hJ (x : CircleHsPi g₀ (Fin n) 3) : J (K x) = J₃ x := by
    exact circle_firstJet_h3_normalization g₀ x
  have hJbound (t : ℝ) (htt : t ∈ Icc 0 T) :
      ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    calc
      ‖J₃ (W₃ t)‖ = ‖J (K (W₃ t))‖ := congrArg norm (hJ (W₃ t)).symm
      _ ≤ (ScalarVectorTimeCoefficients.radius C) := by
        dsimp only [C, g₀, J, K, J₃] at hJW₃ ⊢
        exact hJW₃ t htt
  have hae (t : ℝ) (htt : t ∈ Icc 0 T) : A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t)) := by
    apply TensorHs.ext
    have hphysical := congrArg TensorHs.coeff (ha₂ t htt)
    have hjetTransport := congrArg
      (fun z => (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t z).coeff) (hJ (W₃ t))
    dsimp only [C, g₀, J₃, J, K, A₂] at hphysical hjetTransport ⊢
    with_reducible exact hphysical.trans hjetTransport
  have hbe (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t)) := by
    exact (hb₂ t htt).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t) (hJ (W₃ t)))
  have hallProvider := ambient_sobolev_regularity_all_orders
    c₀ g ht he hr hEU hleft β hG hT C2h C2l
  whnf at hallProvider
  have hallData := hallProvider (hTρ.trans hρC) F₂ W₃ a₂ b₂
  whnf at hallData
  have hallContinuous := hallData hW₃
  dsimp only [C, g₀, J₃] at hJbound
  have hallBound := hallContinuous hJbound
  dsimp only [C, g₀, J₃, A₂] at hae
  have hallDiffusion := hallBound hae
  have hallReaction := hallDiffusion hbe
  have hallEquation := hallReaction hPDE
  have hallHigh := hallEquation hC2h
  have hallLow := hallHigh hC2l
  have hallHighSmall := hallLow hsmallh
  have hallLowSmall := hallHighSmall hsmalll
  have hall := hallLowSmall hW₃U₂
  have hclassical := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨W₀, hW₀, hW₀u, hW₀field, _, _, _⟩ := hclassical
  let L₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  have hWW₀ae : W₃ =ᵐ[timeMeasure T] (fun t => L₃ (W₀ t)) := by
    filter_upwards [hW₃field, hW₀field] with t h₃ h₀
    exact h₃.trans (congrArg L₃ h₀.symm)
  have hWW₀ : EqOn W₃ (fun t => L₃ (W₀ t)) (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT)
      hWW₀ae hW₃ (L₃.continuous.comp_continuousOn hW₀)
  have hW₃u (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 3) (W₃ t) = u.toFun t := by
    rw [hWW₀ htt]
    refine Eq.trans ?_ (hW₀u t htt)
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (W₀ t i)).symm
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  intro k
  obtain ⟨W, hW, hWW₃⟩ := hall k
  let P := circleHsPiInclusion g₀ (Fin n)
    (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
  refine ⟨fun t => P (W t), P.continuous.comp_continuousOn hW, ?_⟩
  intro t htt
  have hlink : circleHsPiInclusion g₀ (Fin n)
      (by
        have hk := Nat.cast_nonneg (α := ℝ) k;
        norm_num only [Nat.cast_one];
        linarith : ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
        (P (W t)) = circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 3)
          (circleHsPiInclusion g₀ (Fin n)
            (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
              (W t)) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  rw [hlink, hWW₃ t htt]
  exact hW₃u t htt

private theorem ambient_sobolev_solution_exists_with_smooth_chart :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
          let P := circleHsPiInclusion g₀ (Fin n)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
          let S := circleHsPiInclusion g₀ (Fin n)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
          let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
            (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
          ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro C g₀
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, htower⟩ :=
    ambient_sobolev_solution_exists_with_sobolev_tower c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  exact ambient_contDiffOn_of_sobolev_tower c₀ g ht he hr hEU hleft β hG
    hT hTρ hρC u gforce hfacts hlift htower

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
