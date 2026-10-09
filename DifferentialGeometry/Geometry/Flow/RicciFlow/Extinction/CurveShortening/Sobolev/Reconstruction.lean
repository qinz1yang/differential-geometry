import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Uniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialJetEvolution
import DifferentialGeometry.Analysis.Calculus.TimeJet.MixedJets
import DifferentialGeometry.Geometry.Metric.Family.Retraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction
import DifferentialGeometry.Geometry.Metric.Family.TimeShift

noncomputable section

open Set
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open private
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions


private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem continuousOn_scalar_jet_slice
    {P F : Type*} [TopologicalSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} {a b : ℝ} {G : P → ℝ → ℝ → F} {j : ℕ}
    (hjets : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (G q.1 q.2.1) q.2.2)
      (S ×ˢ Icc a b ×ˢ univ)) {p : P} (hp : p ∈ S) :
    ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv j (G p q.1) q.2)
      (Icc a b ×ˢ univ) :=
  hjets.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hq => ⟨hp, hq⟩)

private theorem reference_ambient_mixed_full_jets
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {P : Type*} [TopologicalSpace P] {S : Set P} {N : ℕ} {T : ℝ}
    (hT : 0 < T) {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ S)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    {r : EuclideanSpace ℝ (Fin N) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U) (β : U) :
    let f := fun p => fixedAmbientSobolev e g₀ (initial p)
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B (f p) + L ((u p).toFun t)) z)
    let G : P → ℝ → ℝ → EuclideanSpace ℝ (Fin N) := fun p t x => (d p).lift x t
    let gambient := fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (G p t)) →
    (∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (G q.1 q.2.1) q.2.2)
      (S ×ˢ Icc 0 T ×ˢ univ)) →
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      (σ p + t, G p t x, deriv (G p t) x) ∈
        curveShorteningChartFirstJetDomain D gambient β) →
    (∀ p ∈ S, ∀ t ∈ Ioo 0 T, ∀ x : ℝ,
      HasDerivAt (fun s => G p s x)
        (curveShorteningParametricChartRhs gambient β
          (σ p + t, G p t x, deriv (G p t) x, deriv (deriv (G p t)) x)) t) →
    (∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (G p)) (Icc 0 T ×ˢ univ)) ∧
      (∀ k j : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedDerivWithin k
          (fun t => iteratedDeriv j (G q.1 t) q.2.2) (Icc 0 T) q.2.1)
        (S ×ˢ Icc 0 T ×ˢ univ)) ∧
      ∀ n : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
          (Function.uncurry (G q.1)) (Icc 0 T ×ˢ univ) q.2)
        (S ×ˢ Icc 0 T ×ˢ univ) := by
  intro f B L d G gambient hspace hjets hjet hpde
  have hgambient : MetricFamilySmoothOn D gambient :=
    metricFamilySmoothOn_retractionMetric g hg e.smooth hr
  let first : (ℝ × ℝ × (Fin 3 → EuclideanSpace ℝ (Fin N))) →
      ℝ × EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) :=
    fun q => (q.1, q.2.2 0, q.2.2 1)
  let second : (ℝ × ℝ × (Fin 3 → EuclideanSpace ℝ (Fin N))) →
      EuclideanSpace ℝ (Fin N) := fun q => q.2.2 2
  let Ω := first ⁻¹' curveShorteningChartFirstJetDomain D gambient β
  let Φ : (ℝ × ℝ × (Fin 3 → EuclideanSpace ℝ (Fin N))) →
      EuclideanSpace ℝ (Fin N) := fun q =>
    curveShorteningParametricChartRhs gambient β (q.1, q.2.2 0, q.2.2 1, q.2.2 2)
  have hfirst : ContDiff ℝ ∞ first := by fun_prop
  have hsecond : ContDiff ℝ ∞ second := by fun_prop
  have hΩ : IsOpen Ω :=
    (isOpen_curveShorteningChartFirstJetDomain hgambient β).preimage hfirst.continuous
  have hΦ : ContDiffOn ℝ ∞ Φ Ω :=
    (((contDiffOn_curveShorteningChartDiffusionCoefficient hgambient β).comp
      hfirst.contDiffOn (fun _ h => h)).smul hsecond.contDiffOn).add
        ((contDiffOn_curveShorteningParametricChartReaction hgambient β).comp
          hfirst.contDiffOn (fun _ h => h))
  have hGs (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContDiffOn ℝ ∞ (G p t) (univ : Set ℝ) := (hspace p hp t ht).contDiffOn
  have hmap (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T)
      (x : ℝ) :
      (σ p + t, x, fun i : Fin 3 => iteratedDeriv i.val (G p t) x) ∈ Ω := by
    change (σ p + t, iteratedDeriv 0 (G p t) x, iteratedDeriv 1 (G p t) x) ∈
      curveShorteningChartFirstJetDomain D gambient β
    simpa only [iteratedDeriv_zero, iteratedDeriv_one] using hjet p hp t ht x
  have hpde' (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Ioo 0 T)
      (x : ℝ) :
      HasDerivAt (fun s => G p s x)
        (Φ (σ p + t, x, fun i : Fin 3 => iteratedDeriv i.val (G p t) x)) t := by
    change HasDerivAt (fun s => G p s x)
      (curveShorteningParametricChartRhs gambient β
        (σ p + t, iteratedDeriv 0 (G p t) x, iteratedDeriv 1 (G p t) x,
          iteratedDeriv 2 (G p t) x)) t
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hpde p hp t ht x
  have hG (p : P) (hp : p ∈ S) :
      ContDiffOn ℝ ∞ (Function.uncurry (G p)) (Icc 0 T ×ˢ univ) := by
    apply Analysis.contDiffOn_of_scalar_jet_equation
      (G := G p) (σ := σ p) (Φ := Φ) hT isOpen_univ hΩ hΦ (hGs p hp)
    · intro j
      exact continuousOn_scalar_jet_slice (hjets j) hp
    · exact fun t ht x _ => hmap p hp t ht x
    · exact fun t ht x _ => hpde' p hp t ht x
  have hmixed (k j : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (G q.1 t) q.2.2) (Icc 0 T) q.2.1)
      (S ×ˢ Icc 0 T ×ˢ univ) :=
    Analysis.continuousOn_iteratedDerivWithin_iteratedDeriv_of_jet_equation
      hT isOpen_univ hσ Φ hΩ hΦ
      (fun p hp t ht x _ => hmap p hp t ht x) hGs hjets
      (fun p hp t ht x _ => hpde' p hp t ht x) k j
  refine ⟨hG, hmixed, ?_⟩
  intro n
  apply Analysis.continuousOn_iteratedFDerivWithin_of_mixed_derivatives
    (uniqueDiffOn_Icc hT) ?_ isOpen_univ hG hmixed n
  rw [interior_Icc, closure_Ioo hT.ne]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end


noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open private
  coordinateMultiplication
  DifferentialGeometry.Analysis.Parabolic.coordinateMultiplication
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr
  circleHsPiCongr_apply
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  firstJetCoordinates
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.firstJetCoordinates
  geometric_coefficients_contDiffOn
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_coefficients_contDiffOn
  circleFirstJet
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  parameterDerivativeForcingFieldLift
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.parameterDerivativeForcingFieldLift
  circleHsPi_eq_of_inclusion_eq
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.circleHsPi_eq_of_inclusion_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private
  referenceCircleSolutionFacts
  DifferentialGeometry.Analysis.Parabolic.referenceCircleSolutionFacts
  reference_solution_exists_continuousOn_representative
  DifferentialGeometry.Analysis.Parabolic.reference_solution_exists_continuousOn_representative
  DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  scalarH1PiToContinuous_parameter_rhs
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.scalarH1PiToContinuous_parameter_rhs from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Uniqueness
open private
  firstJetCoordinates_circleFirstJet_deriv
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.firstJetCoordinates_circleFirstJet_deriv
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  reference_shifted_coefficients_continuousOn
  DifferentialGeometry.Analysis.Parabolic.reference_shifted_coefficients_continuousOn from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_hasDerivWithinAt_of_parameterDerivative_lift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {Ω : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F Ω) (hG : ContDiffOn ℝ ∞ G Ω) (hΩ : IsOpen Ω)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleSymmetricCoefficientFacts g₀ fref P J F G Ω δ ρ alpha reaction)
    (hσlo : -ρ ≤ σ) (hσhi : σ + T ≤ ρ)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : referenceCircleSolutionFacts g₀ f.val
      (fun t => alpha f (σ + t)) (fun t => reaction f (σ + t)) ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let C := tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ContinuousOn W (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖K (W t)‖ ≤ ρ) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u.toFun
        (m (C (alpha f (σ + t) (K (W t)))) (Q (f.val + W t)) +
          Cpi (reaction f (σ + t) (K (W t)))) (Icc 0 T) t := by
  intro K K₀ C Cpi Q m
  obtain ⟨w, _, hwlow, _, hwbound, _, heq⟩ :=
    reference_solution_exists_continuousOn_representative g₀ f.val
      (fun t => alpha f (σ + t)) (fun t => reaction f (σ + t)) hT u gforce hfacts
  rcases hlift with ⟨FH, hFH, _⟩
  obtain ⟨W, hW, hWlow, hWfield⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift
      g₀ 0 hT gforce FH hFH
  have hWlow' : ∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t := by
    intro t ht
    rw [hfacts.1]
    exact hWlow t ht
  have hwW (t : ℝ) (ht : t ∈ Icc 0 T) : w t = K (W t) :=
    circleHsPi_eq_of_inclusion_eq g₀ (w t) (W t)
      ((hwlow t ht).trans (hWlow' t ht).symm)
  have hbound : ∀ t ∈ Icc 0 T, ‖K (W t)‖ ≤ ρ := by
    intro t ht
    rw [← hwW t ht]
    exact hwbound t ht
  have hKW : ContinuousOn (fun t => K (W t)) (Icc 0 T) :=
    K.continuous.comp_continuousOn hW
  obtain ⟨ha, hb⟩ := reference_shifted_coefficients_continuousOn
    g₀ T σ fref f P J (fun t => K (W t)) hKW F G hF hG hΩ
    alpha reaction hcoeff hσlo hσhi hbound
  let rhs := fun t => m (C (alpha f (σ + t) (K (W t)))) (Q (f.val + W t)) +
    Cpi (reaction f (σ + t) (K (W t)))
  have hRHS : ContinuousOn rhs (Icc 0 T) :=
    ((m.continuous.comp_continuousOn (C.continuous.comp_continuousOn ha)).clm_apply
      (Q.continuous.comp_continuousOn (continuousOn_const.add hW))).add
        (Cpi.continuous.comp_continuousOn hb)
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    MaximalRegularity.tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
  let field := maximalRegularityDuhamelVectorField hT 0 gforce
  have hder : u.deriv = L.compLpL 2 (timeMeasure T) field + gforce :=
    hfacts.2.2.2.2.1
  have hrep : u.deriv =ᵐ[timeMeasure T] rhs := by
    rw [hder]
    filter_upwards [Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) gforce,
      L.coeFn_compLpL field, heq, hWfield, ae_restrict_mem measurableSet_Icc]
      with t hadd hL htEq htW htmem
    rw [hadd, Pi.add_apply, hL, htEq, ← htW]
    change m _ (Q (f.val + W t)) + _ = m _ (Q (f.val + W t)) + _
    rw [hwW t htmem]
  refine ⟨W, hW, hWlow', hWfield, hbound, ?_⟩
  intro t ht
  exact u.hasDerivWithinAt_toFun_of_continuousOn hRHS hrep ht

private theorem reference_shifted_coefficients_eval_of_sobolev_representative
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (A : (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ)
    (R : (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n))
    (Ω : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    {δ ρ T σ : ℝ} (hσlo : -ρ ≤ σ) (hσhi : σ + T ≤ ρ)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) :
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    referenceCircleSymmetricCoefficientFacts g₀ fref P J
      (A ∘ firstJetCoordinates n) (fun z i => R (firstJetCoordinates n z) i)
      (firstJetCoordinates n ⁻¹' Ω) δ ρ alpha reaction →
    ∀ (f : Metric.closedBall fref δ)
      (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
      (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)),
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (w t) = u.toFun t) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      let B := circleHsPiInclusion g₀ (Fin n)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
      let S := circleHsPiInclusion g₀ (Fin n)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (B f.val + S (u.toFun t)) z)
      ∀ t ∈ Icc 0 T, ∀ x : ℝ,
        let q := (σ + t, d.lift x t, deriv (fun y => d.lift y t) x)
        q ∈ Ω ∧
        scalarH1ToContinuous g₀ (alpha f (σ + t) (w t))
          (x : AddCircle (1 : ℝ)) = A q ∧
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (reaction f (σ + t) (w t))
          (x : AddCircle (1 : ℝ))) = R q := by
  intro K₀ P J hcoeff f u w hwu hbound B S d t ht x q
  let E := circleHsPiCongr g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
  let v : CircleHsPi g₀ (Fin n) ((1 : ℝ) + 1) := K₀ f.val + E (w t)
  let V := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (1 : ℝ) ≤ (1 : ℝ) + 1)
  have hcast {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  have hbase : V (K₀ f.val) = B f.val := by
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : (1 : ℝ) ≤ (1 : ℝ) + 1)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f.val i)).symm
  have hstate : V (E (w t)) = S (u.toFun t) := by
    rw [← hwu t ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simp only [V, E, S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, tensorHsInclusion_coeff, hcast]
  have hproject : V v = B f.val + S (u.toFun t) := by
    change V (K₀ f.val + E (w t)) = _
    rw [map_add, hbase, hstate]
  have hjet : P f.val + J (w t) = circleFirstJet g₀ v := by
    change circleFirstJet g₀ (K₀ f.val) + circleFirstJet g₀ (E (w t)) =
      circleFirstJet g₀ (K₀ f.val + E (w t))
    exact (map_add _ _ _).symm
  have hcurve : (fun y : ℝ => d.lift y t) = fun y : ℝ => WithLp.toLp 2
      (fun i => scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (v i))
          (y : AddCircle (1 : ℝ))) := by
    funext y
    change WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B f.val + S (u.toFun t))
        (y : AddCircle (1 : ℝ))) = _
    rw [← hproject]
    rfl
  have hcoordinates : firstJetCoordinates n (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (w t)))
        (x : AddCircle (1 : ℝ))) = q := by
    rw [hjet, firstJetCoordinates_circleFirstJet_deriv]
    change (σ + t, _, _) =
      (σ + t, (fun y => d.lift y t) x, deriv (fun y => d.lift y t) x)
    rw [hcurve]
  have hraw : scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (w t)))
        (x : AddCircle (1 : ℝ)) =
      (fun i => match i with
        | none => σ + t
        | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (w t)) i)
            (x : AddCircle (1 : ℝ))) := by
    funext i
    cases i with
    | none => exact scalarH1TimeCoordinate_eval_none g₀ _ _
    | some i => rfl
  have htime : σ + t ∈ Icc (-ρ) ρ := by
    constructor <;> linarith [ht.1, ht.2]
  have hrawcoordinates : firstJetCoordinates n (fun i => match i with
      | none => σ + t
      | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J (w t)) i)
          (x : AddCircle (1 : ℝ))) = q :=
    (congrArg (firstJetCoordinates n) hraw).symm.trans hcoordinates
  refine ⟨?_, ?_, ?_⟩
  · have hmem := hcoeff.1 f (σ + t) htime (w t) (hbound t ht)
      (mem_range_self (x : AddCircle (1 : ℝ)))
    change firstJetCoordinates n (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (σ + t, P f.val + J (w t)))
        (x : AddCircle (1 : ℝ))) ∈ Ω at hmem
    rwa [hcoordinates] at hmem
  · rw [hcoeff.2.1 f (σ + t) htime (w t) (hbound t ht)]
    change A (firstJetCoordinates n _) = A q
    exact congrArg A hrawcoordinates
  · apply PiLp.ext
    intro i
    change scalarH1ToContinuous g₀ (reaction f (σ + t) (w t) i)
      (x : AddCircle (1 : ℝ)) = R q i
    rw [hcoeff.2.2 f (σ + t) htime (w t) (hbound t ht)]
    exact congrArg (fun z => R z i) hrawcoordinates

private theorem reference_ambient_equation_of_parameterDerivative_lift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (A : (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ)
    (R : (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n))
    {Ω : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hA : ContDiffOn ℝ ∞ (A ∘ firstJetCoordinates n) (firstJetCoordinates n ⁻¹' Ω))
    (hR : ContDiffOn ℝ ∞ (fun z i => R (firstJetCoordinates n z) i)
      (firstJetCoordinates n ⁻¹' Ω))
    (hΩ : IsOpen (firstJetCoordinates n ⁻¹' Ω))
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hσlo : -ρ ≤ σ) (hσhi : σ + T ≤ ρ)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
    let K₂ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₂
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    referenceCircleSymmetricCoefficientFacts g₀ fref P J
      (A ∘ firstJetCoordinates n) (fun z i => R (firstJetCoordinates n z) i)
      (firstJetCoordinates n ⁻¹' Ω) δ ρ alpha reaction →
    referenceCircleSolutionFacts g₀ f.val
      (fun t => alpha f (σ + t)) (fun t => reaction f (σ + t)) ρ hT u gforce →
    parameterDerivativeForcingFieldLift g₀ hT gforce →
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B f.val + S (u.toFun t)) z)
    ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      let q := (σ + t, d.lift x t, deriv (fun y => d.lift y t) x)
      q ∈ Ω ∧ HasDerivWithinAt (fun τ => d.lift x τ)
        (A q • deriv (deriv (fun y => d.lift y t)) x + R q) (Icc 0 T) t := by
  intro K₂ P J hcoeff hfacts hlift B S d
  let K := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  let K₀ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let C := tensorHsCongrL g₀ 0 0
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let Cpi := circleHsPiCongr g₀ (Fin n)
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
  let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
  obtain ⟨W, _, hWlow, _, hbound, htime⟩ :=
    reference_hasDerivWithinAt_of_parameterDerivative_lift g₀ hT σ fref f P J
      (A ∘ firstJetCoordinates n) (fun z i => R (firstJetCoordinates n z) i)
      hA hR hΩ alpha reaction hcoeff hσlo hσhi u gforce hfacts hlift
  have hwlow (t : ℝ) (ht : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
          (K (W t)) = u.toFun t := by
    rw [← hWlow t ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (W t i)).symm
  have heval := reference_shifted_coefficients_eval_of_sobolev_representative
    g₀ fref A R Ω hσlo hσhi alpha reaction hcoeff f u (fun t => K (W t)) hwlow hbound
  have hcast {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  intro t ht x q
  have hfull : B (f.val + W t) = B f.val + S (u.toFun t) := by
    rw [map_add, ← hWlow t ht]
    congr 1
  let a := C (alpha f (σ + t) (K (W t)))
  let b := Cpi (reaction f (σ + t) (K (W t)))
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  let O := L.comp ((ContinuousMap.evalCLM ℝ (x : AddCircle (1 : ℝ))).comp
    (scalarH1PiToContinuous (ι := Fin n) g₀))
  have hd := O.hasFDerivAt.comp_hasDerivWithinAt t
    ((S.hasFDerivAt.comp_hasDerivWithinAt t (htime t ht)).const_add (B f.val))
  have hd' : HasDerivWithinAt (fun τ => d.lift x τ)
      (WithLp.toLp 2 (scalarH1PiToContinuous g₀
        (S (m a (Q (f.val + W t)) + b)) (x : AddCircle (1 : ℝ)))) (Icc 0 T) t := by
    exact hd
  have hrhs := scalarH1PiToContinuous_parameter_rhs g₀ (f.val + W t) a b x
  change WithLp.toLp 2 (scalarH1PiToContinuous g₀
      (S (m a (Q (f.val + W t)) + b)) (x : AddCircle (1 : ℝ))) =
      scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) a)
          (x : AddCircle (1 : ℝ)) •
        deriv (deriv (fun y : ℝ => WithLp.toLp 2
          (scalarH1PiToContinuous g₀ (B (f.val + W t))
            (y : AddCircle (1 : ℝ))))) x +
      WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S b)
        (x : AddCircle (1 : ℝ))) at hrhs
  rw [hfull] at hrhs
  have ha : tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) a =
      alpha f (σ + t) (K (W t)) := by
    apply TensorHs.ext
    simp only [a, C, tensorHsInclusion_coeff, hcast]
  have hb : S b = reaction f (σ + t) (K (W t)) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simp only [S, b, Cpi, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, tensorHsInclusion_coeff, hcast]
  rw [hrhs, ha, hb] at hd'
  have he := heval t ht x
  refine ⟨he.1, ?_⟩
  rw [he.2.1, he.2.2] at hd'
  exact hd'

private theorem reference_chart_equation_of_parameterDerivative_lift
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    (hg : MetricFamilySmoothOn D g) (β : M)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hσlo : -ρ ≤ σ) (hσhi : σ + T ≤ ρ)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
    let K₂ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₂
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    referenceCircleSymmetricCoefficientFacts g₀ fref P J
      (curveShorteningChartDiffusionCoefficient g β ∘ firstJetCoordinates n)
      (fun z i => curveShorteningParametricChartReaction g β (firstJetCoordinates n z) i)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D g β)
      δ ρ alpha reaction →
    referenceCircleSolutionFacts g₀ f.val
      (fun t => alpha f (σ + t)) (fun t => reaction f (σ + t)) ρ hT u gforce →
    parameterDerivativeForcingFieldLift g₀ hT gforce →
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B f.val + S (u.toFun t)) z)
    (∀ t ∈ Icc 0 T, ∀ x : ℝ,
      (σ + t, d.lift x t, deriv (fun y => d.lift y t) x) ∈
        curveShorteningChartFirstJetDomain D g β ∧
      HasDerivWithinAt (fun τ => d.lift x τ)
        (curveShorteningParametricChartRhs g β
          (σ + t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) (Icc 0 T) t) ∧
    ∀ t ∈ Ioo 0 T, ∀ x : ℝ,
      HasDerivAt (fun τ => d.lift x τ)
        (curveShorteningParametricChartRhs g β
          (σ + t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) t := by
  intro K₂ P J hcoeff hfacts hlift B S d
  obtain ⟨hΩ, hA, hR⟩ := geometric_coefficients_contDiffOn hg β
  have heq := reference_ambient_equation_of_parameterDerivative_lift
    g₀ hT σ fref f (curveShorteningChartDiffusionCoefficient g β)
      (curveShorteningParametricChartReaction g β) hA hR hΩ alpha reaction
      hσlo hσhi u gforce hcoeff hfacts hlift
  refine ⟨heq, ?_⟩
  intro t ht x
  exact ((heq t ⟨ht.1.le, ht.2.le⟩ x).2).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end


noncomputable section

open Set Filter
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open private
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  firstJetCoordinates
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.firstJetCoordinates
  circleFirstJet
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  parameterDerivativeForcingFieldLift
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.parameterDerivativeForcingFieldLift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private
  referenceCircleSolutionFacts
  DifferentialGeometry.Analysis.Parabolic.referenceCircleSolutionFacts
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  reference_sobolev_spatial_jets
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_sobolev_spatial_jets
  reference_joint_total_sobolev_representatives
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_joint_total_sobolev_representatives from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialJets


private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_selected_ambient_jets
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {P : Type*} [TopologicalSpace P] {S : Set P} {N : ℕ} {T : ℝ}
    (hT : 0 < T) {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ S)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinitial : @ContinuousOn P (SmoothImmersion (I := I) (M := M))
      inferInstance (smoothImmersionTopology e) initial S)
    (fref : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : P → Metric.closedBall fref δ)
    (hf : ∀ p ∈ S, (f p).val = fixedAmbientSobolev e g₀ (initial p))
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin N) 1)
    (hσlo : ∀ p ∈ S, -ρ ≤ σ p) (hσhi : ∀ p ∈ S, σ p + T ≤ ρ)
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (gforce : P → timeL2 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (W : ∀ k : ℕ, P → ℝ → CircleHsPi g₀ (Fin N) ((k : ℝ) + 3))
    (hW : ∀ k p, p ∈ S → ContinuousOn (W k p) (Icc 0 T))
    (hWlim : ∀ k p, p ∈ S →
      TendstoUniformlyOn (W k) (W k p) (𝓝[S] p) (Icc 0 T))
    {r : EuclideanSpace ℝ (Fin N) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U) (β : U) :
    let K₂ := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let Q := (circleFirstJet (ι := Fin N) g₀).comp K₂
    let J := (circleFirstJet (ι := Fin N) g₀).comp
      (circleHsPiCongr g₀ (Fin N)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let gambient := fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr
    referenceCircleSymmetricCoefficientFacts g₀ fref Q J
      (curveShorteningChartDiffusionCoefficient gambient β ∘ firstJetCoordinates N)
      (fun z i => curveShorteningParametricChartReaction gambient β (firstJetCoordinates N z) i)
      (firstJetCoordinates N ⁻¹' curveShorteningChartFirstJetDomain D gambient β)
      δ ρ alpha reaction →
    (∀ p ∈ S, referenceCircleSolutionFacts g₀ (f p).val
      (fun t => alpha (f p) (σ p + t)) (fun t => reaction (f p) (σ p + t))
      ρ hT (u p) (gforce p)) →
    (∀ p ∈ S, parameterDerivativeForcingFieldLift g₀ hT (gforce p)) →
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀
        (B (fixedAmbientSobolev e g₀ (initial p)) + L ((u p).toFun t)) z)
    let G : P → ℝ → ℝ → EuclideanSpace ℝ (Fin N) := fun p t x => (d p).lift x t
    (∀ (k : ℕ) p, p ∈ S → ∀ t, t ∈ Icc 0 T →
      circleHsPiInclusion g₀ (Fin N)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
          (1 : ℝ) ≤ (k : ℝ) + 3) (W k p t) = L ((u p).toFun t)) →
    (∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (G p)) (Icc 0 T ×ˢ univ)) ∧
      (∀ k j : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedDerivWithin k
          (fun t => iteratedDeriv j (G q.1 t) q.2.2) (Icc 0 T) q.2.1)
        (S ×ˢ Icc 0 T ×ˢ univ)) ∧
      ∀ n : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
          (Function.uncurry (G q.1)) (Icc 0 T ×ˢ univ) q.2)
        (S ×ˢ Icc 0 T ×ˢ univ) := by
  intro K₂ Q J gambient hcoeff hfacts hlift B L d G hWpin
  have htower := reference_joint_total_sobolev_representatives
    e g₀ initial hinitial u W hW hWlim hWpin
  obtain ⟨hspace, hjets⟩ := reference_sobolev_spatial_jets e g₀ initial u htower
  have hgambient : MetricFamilySmoothOn D gambient :=
    metricFamilySmoothOn_retractionMetric g hg e.smooth hr
  have heq (p : P) (hp : p ∈ S) :
      (∀ t ∈ Icc 0 T, ∀ x : ℝ,
        (σ p + t, G p t x, deriv (G p t) x) ∈
          curveShorteningChartFirstJetDomain D gambient β ∧
        HasDerivWithinAt (fun τ => G p τ x)
          (curveShorteningParametricChartRhs gambient β
            (σ p + t, G p t x, deriv (G p t) x, deriv (deriv (G p t)) x))
          (Icc 0 T) t) ∧
      ∀ t ∈ Ioo 0 T, ∀ x : ℝ,
        HasDerivAt (fun τ => G p τ x)
          (curveShorteningParametricChartRhs gambient β
            (σ p + t, G p t x, deriv (G p t) x, deriv (deriv (G p t)) x)) t := by
    have hh := reference_chart_equation_of_parameterDerivative_lift
      gambient hgambient β g₀ hT (σ p) fref (f p) alpha reaction
      (hσlo p hp) (hσhi p hp) (u p) (gforce p) hcoeff (hfacts p hp) (hlift p hp)
    simpa only [hf p hp, G, d] using hh
  exact reference_ambient_mixed_full_jets hT g hg σ hσ e g₀ initial u hr β
    hspace hjets (fun p hp t ht x => ((heq p hp).1 t ht x).1)
    (fun p hp t ht x => (heq p hp).2 t ht x)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end


noncomputable section

open Set Filter
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open private
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  firstJetCoordinates
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.firstJetCoordinates
  circleFirstJet
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  parameterDerivativeForcingFieldLift
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.parameterDerivativeForcingFieldLift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private
  referenceCircleSolutionFacts
  DifferentialGeometry.Analysis.Parabolic.referenceCircleSolutionFacts
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  reference_curve_initial_eq
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_curve_initial_eq
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions


private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem retraction_of_shifted_classical_equation
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] {T : ℝ} (hT : 0 < T) {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M) (hg : MetricFamilySmoothOn D g) (σ : ℝ)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (d : CurveMap F) (initial : AddCircle (1 : ℝ) → M)
    (hsmooth : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => d.lift q.2 q.1)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ z, d z 0 = e (initial z))
    (hjet : ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      (σ + t, d.lift x t, deriv (fun y => d.lift y t) x) ∈
        curveShorteningChartFirstJetDomain D
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      HasDerivWithinAt (d.lift x)
        (curveShorteningParametricChartRhs
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (σ + t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) (Icc 0 T) t) :
    let c : CurveMap M := fun z t => r (d z t)
    c.SmoothOn (I := I) (Icc 0 T) ∧
      (∀ z, c z 0 = initial z) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
      c.ImmersedOn (I := I) (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed (fun s => g (σ + s)) x t ^ (-2 : ℤ) •
          c.Dx (fun s => g (σ + s)) c.X x t := by
  intro c
  let gshift := fun s => g (σ + s)
  have hgshift : MetricFamilySmoothOn (D.timeShift σ) gshift := by
    simpa only [gshift, add_comm] using hg.timeShift σ
  have hd : d.SmoothOn (I := 𝓘(ℝ, F)) (Icc 0 T) := by
    have hswap : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (q.2, q.1))
        (univ ×ˢ Icc 0 T) := contDiffOn_snd.prodMk contDiffOn_fst
    have hmap : MapsTo (fun q : ℝ × ℝ => (q.2, q.1))
        (univ ×ˢ Icc 0 T) (Icc 0 T ×ˢ univ) := fun _ hq => ⟨hq.2, hq.1⟩
    exact (hsmooth.comp hswap hmap).contMDiffOn
  have hjetshift (x t : ℝ) (ht : t ∈ Icc 0 T) :
      (t, d.lift x t, deriv (fun y => d.lift y t) x) ∈
        curveShorteningChartFirstJetDomain (D.timeShift σ)
          (fun s => Geometry.Riemannian.retractionMetric (gshift s) he hr) β := by
    have hj := hjet t ht x
    refine ⟨?_, hj.2⟩
    change t + σ ∈ D.regular
    simpa only [add_comm] using hj.1
  have hpdeshift (x t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (d.lift x)
        (curveShorteningParametricChartRhs
          (fun s => Geometry.Riemannian.retractionMetric (gshift s) he hr) β
          (t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) (Icc 0 T) t := by
    exact hpde t ht x
  obtain ⟨b, hb, hbe, hbPDE⟩ :=
    CurveMap.exists_parabolic_curve_of_classical_retraction_equation_of_firstJet_mem
      gshift hgshift he hr hEU hleft β d hT hd
      (fun z => ⟨initial z, (hinit z).symm⟩) hjetshift hpdeshift
  have hcb (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      c z t = b z t := by
    change r (d z t) = b z t
    rw [← hbe z t ht, hleft]
  have hc : c.SmoothOn (I := I) (Icc 0 T) :=
    hb.congr (fun q hq => hcb (q.1 : AddCircle (1 : ℝ)) q.2 hq.2)
  have hce (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      e (c z t) = d z t := by
    rw [hcb z t ht]
    exact hbe z t ht
  refine ⟨hc, ?_, hce, ?_, ?_⟩
  · intro z
    change r (d z 0) = initial z
    rw [hinit z, hleft]
  · intro x t ht hzero
    have hpos := (hjet t ht x).2.2
    have hdne : deriv (fun y => d.lift y t) x ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hpos
      exact lt_irrefl _ hpos
    have hslice : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
      contMDiffOn_univ.mp (c.space_slice_contMDiffOn (Icc 0 T) hc t ht)
    have hcomp := mfderiv_comp_apply x (he.mdifferentiableAt (by simp))
      (hslice.mdifferentiableAt (by simp)) (1 : ℝ)
    have heq : e ∘ (fun y : ℝ => c.lift y t) = (fun y => d.lift y t) :=
      funext (fun y => hce (y : AddCircle (1 : ℝ)) t ht)
    rw [heq, mfderiv_eq_fderiv] at hcomp
    change deriv (fun y => d.lift y t) x =
      mfderiv I 𝓘(ℝ, F) e (c.lift x t) (c.X (I := I) x t) at hcomp
    rw [hzero, map_zero] at hcomp
    exact hdne hcomp
  · intro x t ht
    exact CurveMap.velocity_eq_parametric_acceleration_of_eqOn hcb ht (hbPDE x t ht)

private theorem reference_selected_retraction
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {P : Type*} [TopologicalSpace P] {S : Set P} {N : ℕ} {T : ℝ}
    (hT : 0 < T) {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ S)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinitial : @ContinuousOn P (SmoothImmersion (I := I) (M := M))
      inferInstance (smoothImmersionTopology e) initial S)
    (fref : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : P → Metric.closedBall fref δ)
    (hf : ∀ p ∈ S, (f p).val = fixedAmbientSobolev e g₀ (initial p))
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin N) 1)
    (hσlo : ∀ p ∈ S, -ρ ≤ σ p) (hσhi : ∀ p ∈ S, σ p + T ≤ ρ)
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (gforce : P → timeL2 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (W : ∀ k : ℕ, P → ℝ → CircleHsPi g₀ (Fin N) ((k : ℝ) + 3))
    (hW : ∀ k p, p ∈ S → ContinuousOn (W k p) (Icc 0 T))
    (hWlim : ∀ k p, p ∈ S →
      TendstoUniformlyOn (W k) (W k p) (𝓝[S] p) (Icc 0 T))
    {r : EuclideanSpace ℝ (Fin N) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U) :
    let K₂ := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let Q := (circleFirstJet (ι := Fin N) g₀).comp K₂
    let J := (circleFirstJet (ι := Fin N) g₀).comp
      (circleHsPiCongr g₀ (Fin N)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let gambient := fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr
    referenceCircleSymmetricCoefficientFacts g₀ fref Q J
      (curveShorteningChartDiffusionCoefficient gambient β ∘ firstJetCoordinates N)
      (fun z i => curveShorteningParametricChartReaction gambient β (firstJetCoordinates N z) i)
      (firstJetCoordinates N ⁻¹' curveShorteningChartFirstJetDomain D gambient β)
      δ ρ alpha reaction →
    (∀ p ∈ S, referenceCircleSolutionFacts g₀ (f p).val
      (fun t => alpha (f p) (σ p + t)) (fun t => reaction (f p) (σ p + t))
      ρ hT (u p) (gforce p)) →
    (∀ p ∈ S, parameterDerivativeForcingFieldLift g₀ hT (gforce p)) →
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀
        (B (fixedAmbientSobolev e g₀ (initial p)) + L ((u p).toFun t)) z)
    (∀ (k : ℕ) p, p ∈ S → ∀ t, t ∈ Icc 0 T →
      circleHsPiInclusion g₀ (Fin N)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
          (1 : ℝ) ≤ (k : ℝ) + 3) (W k p t) = L ((u p).toFun t)) →
    let c : P → CurveMap M := fun p z t => r (d p z t)
    ∀ p ∈ S,
      (c p).SmoothOn (I := I) (Icc 0 T) ∧
      (∀ z, c p z 0 = (initial p).map z) ∧
      (∀ z t, t ∈ Icc 0 T → e.map (c p z t) = d p z t) ∧
      (c p).ImmersedOn (I := I) (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T → (c p).velocity (I := I) (Icc 0 T) x t =
        (c p).speed (fun s => g (σ p + s)) x t ^ (-2 : ℤ) •
          (c p).Dx (fun s => g (σ p + s)) (c p).X x t := by
  intro K₂ Q J gambient hcoeff hfacts hlift B L d hWpin c p hp
  have hambient := reference_selected_ambient_jets
    hT g hg σ hσ e g₀ initial hinitial fref f hf alpha reaction hσlo hσhi
    u gforce W hW hWlim hr β hcoeff hfacts hlift hWpin
  have hgambient : MetricFamilySmoothOn D gambient :=
    metricFamilySmoothOn_retractionMetric g hg e.smooth hr
  have heq := reference_chart_equation_of_parameterDerivative_lift
    gambient hgambient β g₀ hT (σ p) fref (f p) alpha reaction
    (hσlo p hp) (hσhi p hp) (u p) (gforce p) hcoeff (hfacts p hp) (hlift p hp)
  have hinit := reference_curve_initial_eq e g₀ (initial p) (u p)
    (hfacts p hp).2.2.2.1
  apply retraction_of_shifted_classical_equation hT g hg (σ p) e.smooth hr
    hEU hleft β (d p) (initial p).map (hambient.1 p hp) hinit
  · intro t ht x
    simpa only [hf p hp, d] using ((heq.1 t ht x).1)
  · intro t ht x
    simpa only [hf p hp, d] using ((heq.1 t ht x).2)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
