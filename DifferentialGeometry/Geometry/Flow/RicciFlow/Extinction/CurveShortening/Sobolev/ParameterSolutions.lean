import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CurveRepresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

open private
  coordinateMultiplication
  CircleHsPi
  circleHsPiInclusion
  shiftedRemainder
  extendClosedBall
  extendClosedBall_apply
  circleHsPiCongr
  circleHsPiCongr_apply
  DifferentialGeometry.Analysis.Parabolic.coordinateMultiplication
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.shiftedRemainder
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall_apply
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  firstJetCoordinates
  geometric_coefficients_contDiffOn
  circleFirstJet
  ambientCoordinate
  ambientSobolev
  tensorHsCongrL_ccTensorToHs
  ambientFirstJet
  ambientFirstJet_range
  hasDerivAt_circleH2Pi
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.firstJetCoordinates
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_coefficients_contDiffOn
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientCoordinate
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.tensorHsCongrL_ccTensorToHs
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientFirstJet
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientFirstJet_range
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.hasDerivAt_circleH2Pi from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  exists_pos_parameterPrincipal_norm_le
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_pos_parameterPrincipal_norm_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private
  scaled_coefficient_radius_bounds
  circle_shifted_equation_ae
  referenceCircleSolutionFacts
  referenceCircleCoefficientFacts
  circle_coefficient_threshold_pos
  reference_jet_add_correction_eq
  reference_diffusion_at_sobolev_jet
  reference_solution_exists_continuousOn_representative
  continuous_of_ambient_derivative_bound
  fixedAmbientSobolev
  continuous_fixedAmbientSobolev
  exists_isOpen_fixedAmbientSobolev_mem_closedBall
  DifferentialGeometry.Analysis.Parabolic.scaled_coefficient_radius_bounds
  DifferentialGeometry.Analysis.Parabolic.circle_shifted_equation_ae
  DifferentialGeometry.Analysis.Parabolic.referenceCircleSolutionFacts
  DifferentialGeometry.Analysis.Parabolic.referenceCircleCoefficientFacts
  DifferentialGeometry.Analysis.Parabolic.circle_coefficient_threshold_pos
  DifferentialGeometry.Analysis.Parabolic.reference_jet_add_correction_eq
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_diffusion_at_sobolev_jet
  DifferentialGeometry.Analysis.Parabolic.reference_solution_exists_continuousOn_representative
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_of_ambient_derivative_bound
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.continuous_fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_isOpen_fixedAmbientSobolev_mem_closedBall
  DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  scalarH1PiToContinuous_fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.scalarH1PiToContinuous_fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CurveRepresentation

noncomputable section

open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def fixedAmbientSobolevExponent
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (σ : ℝ)
    (d : SmoothImmersion (I := I) (M := M)) :
    PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 σ) :=
  WithLp.toLp 2 (fun i =>
    ccTensorToHs g₀ 0 σ (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)))

private theorem continuous_fixedAmbientSobolevExponent
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (σ : ℝ) :
    @Continuous _ _ (smoothImmersionTopology e) inferInstance
      (fixedAmbientSobolevExponent e g₀ σ) := by
  let := smoothImmersionTopology e
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 σ)).comp
  apply continuous_pi
  intro i
  obtain ⟨m, C, hC, hbound⟩ :=
    AddCircle.exists_norm_sub_ccTensorToHs_le_iteratedDeriv g₀ σ
  apply continuous_of_ambient_derivative_bound e _ m C hC
  intro c d ε hε hcd
  apply hbound _ _ ε hε.le
  intro j hj x hx
  simp only [scalar0_scalarCc]
  change |iteratedDeriv j (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ))) i) x -
    iteratedDeriv j (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ))) i) x| ≤ ε
  have hd : ContDiff ℝ ∞ (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) :=
    contMDiff_iff_contDiff.mp (e.smooth.comp d.smooth)
  have hc : ContDiff ℝ ∞ (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) :=
    contMDiff_iff_contDiff.mp (e.smooth.comp c.smooth)
  exact (PiLp.norm_iteratedDeriv_apply_sub_le
    (hd.of_le (by exact_mod_cast le_top)).contDiffAt
    (hc.of_le (by exact_mod_cast le_top)).contDiffAt i).trans (hcd j hj x hx)

private theorem fixedAmbientSobolevExponent_inclusion
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) (d : SmoothImmersion (I := I) (M := M)) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0) hab))
        (fixedAmbientSobolevExponent e g₀ b d) =
      fixedAmbientSobolevExponent e g₀ a d := by
  apply PiLp.ext
  intro i
  change tensorHsInclusion hab
    (ccTensorToHs g₀ 0 b (scalarCc g₀ (ambientCoordinate d e.map e.smooth i))) = _
  exact tensorHsInclusion_ccTensorToHs g₀ 0 hab _

private theorem fixedAmbientSobolevExponent_three
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) :
    fixedAmbientSobolevExponent e g₀ (((1 : ℕ) : ℝ) + 2) d =
      fixedAmbientSobolev e g₀ d := by
  apply PiLp.ext
  intro i
  change ccTensorToHs g₀ 0 (((1 : ℕ) : ℝ) + 2)
      (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)) =
    tensorHsCongrL g₀ 0 0 (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
      (ccTensorToHs g₀ 0 3 (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)))
  exact (tensorHsCongrL_ccTensorToHs g₀ _ _).symm

private theorem fixedAmbientSobolevExponent_inclusion_three
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {σ : ℝ} (hσ : ((1 : ℕ) : ℝ) + 2 ≤ σ)
    (d : SmoothImmersion (I := I) (M := M)) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0) hσ))
      (fixedAmbientSobolevExponent e g₀ σ d) = fixedAmbientSobolev e g₀ d := by
  rw [fixedAmbientSobolevExponent_inclusion, fixedAmbientSobolevExponent_three]

private theorem scalarH1PiToContinuous_fixedAmbientSobolevExponent
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {σ : ℝ} (hσ : 1 ≤ σ) (d : SmoothImmersion (I := I) (M := M))
    (z : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous g₀
      ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0) hσ))
        (fixedAmbientSobolevExponent e g₀ σ d)) z = fun i => e.map (d.map z) i := by
  funext i
  change scalarH1ToContinuous g₀
    (tensorHsInclusion hσ
      (ccTensorToHs g₀ 0 σ (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)))) z = _
  rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs,
    scalar0_scalarCc]
  rfl

variable [IsManifold I ∞ M]

private theorem fixedAmbientSobolevExponent_pullbackMetric_eq
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    fixedAmbientSobolevExponent e (c₀.pullbackMetric g) σ c₀ =
      ambientSobolev c₀ g e.map e.smooth σ := rfl

private theorem exists_isOpen_fixedAmbientSobolevExponent_mem_closedBall
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M)
    (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    let := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ c₀ ∈ U ∧ ∀ d ∈ U,
        fixedAmbientSobolevExponent e (c₀.pullbackMetric g) σ d ∈
          Metric.closedBall (ambientSobolev c₀ g e.map e.smooth σ) r := by
  let := smoothImmersionTopology e
  let f₀ := ambientSobolev c₀ g e.map e.smooth σ
  refine ⟨(fixedAmbientSobolevExponent e (c₀.pullbackMetric g) σ) ⁻¹'
    Metric.ball f₀ r, ?_, ?_, ?_⟩
  · exact (continuous_fixedAmbientSobolevExponent e (c₀.pullbackMetric g) σ).isOpen_preimage
      _ Metric.isOpen_ball
  · change fixedAmbientSobolevExponent e (c₀.pullbackMetric g) σ c₀ ∈ Metric.ball f₀ r
    rw [fixedAmbientSobolevExponent_pullbackMetric_eq]
    exact Metric.mem_ball_self hr
  · intro d hd
    exact Metric.ball_subset_closedBall hd

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem firstJetCoordinates_circleFirstJet_deriv
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : CircleHsPi g₀ (Fin n) ((1 : ℝ) + 1)) (t x : ℝ) :
    let f := fun y : ℝ => WithLp.toLp 2 (fun i => scalarH1ToContinuous g₀
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (v i))
        (y : AddCircle (1 : ℝ)))
    firstJetCoordinates n (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, circleFirstJet g₀ v))
        (x : AddCircle (1 : ℝ))) = (t, f x, deriv f x) := by
  intro f
  apply Prod.ext
  · exact scalarH1TimeCoordinate_eval_none _ _ _
  apply Prod.ext
  · rfl
  · exact (hasDerivAt_circleH2Pi g₀ v x).deriv.symm

private theorem reference_firstJet_mem_of_sobolev_solution_facts
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (Ω : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    {δ ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) :
    let K₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    referenceCircleCoefficientFacts g₀ f₀ P J F G
      (firstJetCoordinates n ⁻¹' Ω) δ ρ alpha reaction →
    ∀ (f : Metric.closedBall f₀ δ)
      (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
      (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts g₀ f.val (alpha f) (reaction f) ρ hT u gforce →
      let B := circleHsPiInclusion g₀ (Fin n)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
      let S := circleHsPiInclusion g₀ (Fin n)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (B f.val + S (u.toFun t)) z)
      ∀ t ∈ Icc 0 T, ∀ x : ℝ,
        (t, d.lift x t, deriv (fun y => d.lift y t) x) ∈ Ω := by
  intro K₀ P J hcoeff f u gforce hfacts B S d
  obtain ⟨w, _, hwu, _, hbound, _, _⟩ :=
    reference_solution_exists_continuousOn_representative
      g₀ f.val (alpha f) (reaction f) hT u gforce hfacts
  intro t ht x
  let E := circleHsPiCongr g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
  let v : CircleHsPi g₀ (Fin n) ((1 : ℝ) + 1) := K₀ f.val + E (w t)
  let R := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (1 : ℝ) ≤ (1 : ℝ) + 1)
  have hcast {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  have hbase : R (K₀ f.val) = B f.val := by
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : (1 : ℝ) ≤ (1 : ℝ) + 1)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f.val i)).symm
  have hstate : R (E (w t)) = S (u.toFun t) := by
    rw [← hwu t ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simp only [R, E, S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, tensorHsInclusion_coeff, hcast]
  have hproject : R v = B f.val + S (u.toFun t) := by
    change R (K₀ f.val + E (w t)) = _
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
      (scalarH1TimeCoordinate g₀ (t, P f.val + J (w t)))
        (x : AddCircle (1 : ℝ))) =
      (t, d.lift x t, deriv (fun y => d.lift y t) x) := by
    rw [hjet, firstJetCoordinates_circleFirstJet_deriv]
    change (t, _, _) = (t, (fun y => d.lift y t) x, deriv (fun y => d.lift y t) x)
    rw [hcurve]
  have hmem := hcoeff.1 f t ⟨ht.1, ht.2.trans hTρ⟩ (w t) (hbound t ht)
    (mem_range_self (x : AddCircle (1 : ℝ)))
  change firstJetCoordinates n (scalarH1PiToContinuous g₀
    (scalarH1TimeCoordinate g₀ (t, P f.val + J (w t)))
      (x : AddCircle (1 : ℝ))) ∈ Ω at hmem
  rwa [hcoordinates] at hmem

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_curve_initial_eq
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : SmoothImmersion (I := I) (M := M)) {T : ℝ}
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (htrace : timeH1.trace0 _ T u = 0) :
    let f := fixedAmbientSobolev e g₀ initial
    let B := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B f + S (u.toFun t)) z)
    ∀ z, d z 0 = e.map (initial.map z) := by
  intro f B S d z
  have hu : u.toFun 0 = 0 := by
    simpa only [timeH1.toFun_zero, timeH1.trace0_apply] using htrace
  change WithLp.toLp 2
    (scalarH1PiToContinuous g₀ (B f + S (u.toFun 0)) z) = _
  rw [hu, map_zero, add_zero]
  have hbase := scalarH1PiToContinuous_fixedAmbientSobolev e g₀ initial z
  change scalarH1PiToContinuous g₀ (B f) z = fun i => e.map (initial.map z) i at hbase
  rw [hbase]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_successor_coefficients_tendsto
    {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ} {l : Filter X}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (d : X → SmoothImmersion (I := I) (M := M))
    (d₀ : SmoothImmersion (I := I) (M := M))
    (hd : Tendsto d l (@nhds _ (smoothImmersionTopology e) d₀))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {U K : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (V : X → timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 2 : ℕ) : ℝ) + 1))) T)
    (V₀ : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 2 : ℕ) : ℝ) + 1))) T)
    (W : X → ℝ →
      PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 1 : ℕ) : ℝ) + 1)))
    (W₀ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 1 : ℕ) : ℝ) + 1)))
    (a : X → timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (a₀ : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (b : X → timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2))) T)
    (b₀ : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2))) T)
    (hV : Tendsto V l (𝓝 V₀)) (hW₀ : ContinuousOn W₀ (Icc 0 T))
    (hW : TendstoUniformlyOn W W₀ l (Icc 0 T)) :
    let f := fun x =>
      fixedAmbientSobolevExponent e g₀ (((k + 1 + 2 : ℕ) : ℝ) + 1) (d x)
    let f₀ := fixedAmbientSobolevExponent e g₀ (((k + 1 + 2 : ℕ) : ℝ) + 1) d₀
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; rfl :
          ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 1 + 2 : ℕ) : ℝ)))
    let Hjet := P.comp (AddCircle.scalarHsTimeFirstJet (ι := Fin n) g₀ (k + 1 + 2))
    let J := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => J)
    let B := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    (∀ x, W x =ᵐ[timeMeasure T] fun t => B (V x t)) →
    W₀ =ᵐ[timeMeasure T] (fun t => B (V₀ t)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (Q (Hjet (t, f x + V x t)))) ⊆ K) →
    (∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g₀ (Q (Hjet (t, f₀ + V₀ t)))) ⊆ K) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g₀ (J (a x t)) z =
      F (scalarH1PiToContinuous g₀ (Q (Hjet (t, f x + V x t))) z)) →
    (∀ᵐ t ∂timeMeasure T, ∀ z, scalarH1ToContinuous g₀ (J (a₀ t)) z =
      F (scalarH1PiToContinuous g₀ (Q (Hjet (t, f₀ + V₀ t))) z)) →
    (∀ᶠ x in l, ∀ᵐ t ∂timeMeasure T, ∀ z j,
      scalarH1ToContinuous g₀ (J (b x t j)) z =
        G (scalarH1PiToContinuous g₀ (Q (Hjet (t, f x + V x t))) z) j) →
    (∀ᵐ t ∂timeMeasure T, ∀ z j, scalarH1ToContinuous g₀ (J (b₀ t j)) z =
      G (scalarH1PiToContinuous g₀ (Q (Hjet (t, f₀ + V₀ t))) z) j) →
    Tendsto (fun x => (a x, b x)) l (𝓝 (a₀, b₀)) := by
  intro f f₀ P Hjet J Q B hWV hWV₀ hRange hRange₀ ha ha₀ hb hb₀
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  have hf : Tendsto f l (𝓝 f₀) := by
    exact (continuous_fixedAmbientSobolevExponent e g₀
      (((k + 1 + 2 : ℕ) : ℝ) + 1)).continuousAt.tendsto.comp hd
  have haT := AddCircle.tendsto_timeL2_scalarHs_composition_firstJet_of_tendstoUniformlyOn
    g₀ (k + 1) T F hF hU hK hKU f f₀ V V₀ a a₀ W W₀ hf hV hW₀ hW
    hWV hWV₀ hRange hRange₀ ha ha₀
  have hbT := AddCircle.tendsto_timeL2_vectorHs_composition_firstJet_of_tendstoUniformlyOn
    g₀ (k + 1) T G hG hU hK hKU f f₀ V V₀ b b₀ W W₀ hf hV hW₀ hW
    hWV hWV₀ hRange hRange₀ hb hb₀
  exact haT.prodMk_nhds hbT

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic (circleFirstJet)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}

attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem ambient_reference_symmetric_composition
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ε : ℝ} (hε : 0 < ε) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) :=
      ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (1 + 1)) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := circleFirstJet (ι := Fin n) g₀
    let K : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (1 + 1)) :=
        ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := J.comp K
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ), ‖P‖ * δ ≤ R ∧
      ∃ Ca Cb : ℝ≥0,
      R ≤ ε ∧ (Ca : ℝ) * R ≤ ε ∧ (Cb : ℝ) * R ≤ ε ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R →
          TensorHs g₀ 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R →
          PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1),
      (∀ f, LipschitzWith Ca (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R => alpha f p.1 p.2)) ∧
      (∀ f, LipschitzWith Cb (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R => reaction f p.1 p.2)) ∧
      (∀ f t, t ∈ Set.Icc (-R) R → ∀ v,
        ‖alpha f t v - alpha ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R)) ∧
      (∀ f t, t ∈ Set.Icc (-R) R → ∀ v,
        ‖reaction f t v - reaction ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R)) ∧
      (∀ f k t s v, ‖alpha f t v - alpha k s v‖ ≤
        (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖) ∧
      (∀ f k t s v, ‖reaction f t v - reaction k s v‖ ≤
        (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖) ∧
      (∀ (f : Metric.closedBall f₀ δ) t
        (v : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R),
        t ∈ Set.Icc (-R) R →
        Set.range (scalarH1PiToContinuous g₀
          (scalarH1TimeCoordinate g₀ (0 + t, P f.val + v.val))) ⊆ S) ∧
      (∀ f t, t ∈ Set.Icc (-R) R → ∀ v x,
        scalarH1ToContinuous g₀ (alpha f t v) x =
          F (fun i => match i with
            | none => 0 + t
            | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x)) ∧
      (∀ f t, t ∈ Set.Icc (-R) R → ∀ v x j,
        scalarH1ToContinuous g₀ (reaction f t v j) x =
          G (fun i => match i with
            | none => 0 + t
            | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) := by
  intro g₀ f₀ J K P F G S
  obtain ⟨hS, hF, hG'⟩ := geometric_coefficients_contDiffOn hG β
  have hjet : ambientFirstJet c₀ (g 0) e he = P f₀ := by
    change circleFirstJet g₀ _ = circleFirstJet g₀ _
    congr 1
  have hreference : Set.range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (0, P f₀))) ⊆ S := by
    rw [← hjet]
    exact ambientFirstJet_range c₀ g ht he hr hEU hleft β
  exact exists_scalar_vectorH1_time_composition_on_symmetric_translated_closedBall
    g₀ n P 0 f₀ F G hF hG' hS hreference hε

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private theorem precomposed_symmetric_reference_coefficient_bounds
    {P X V A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A]
    (J : X →L[ℝ] V) {R : ℝ} (hR : 0 < R)
    (a : P → ℝ → Metric.closedBall (0 : V) R → A) (q : A) (Ca : ℝ≥0)
    (ha : ∀ p, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a p z.1 z.2))
    (hclose : ∀ p t, t ∈ Set.Icc (-R) R → ∀ z, ‖a p t z - q‖ ≤ (Ca : ℝ) * (2 * R)) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun p => extendClosedBall hρ.le
        (fun t z => a p t (J.closedBallMap hJρ z))
      (∀ p t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ w, ‖w‖ ≤ ρ →
        ‖alpha p t z - alpha p t w‖ ≤ ((Ca : ℝ) * ‖J‖) * ‖z - w‖) ∧
      (∀ p t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
        ‖alpha p t z - q‖ ≤ (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ) ∧
      (∀ p, Continuous (fun z : Set.Icc (-ρ) ρ × Metric.closedBall (0 : X) ρ =>
        alpha p z.1 z.2)) ∧
      (∀ p t (z : Metric.closedBall (0 : X) ρ), alpha p t z = a p t (J.closedBallMap hJρ z)) := by
  let ρ := R / (1 + ‖J‖)
  have hden : 0 < 1 + ‖J‖ := by positivity
  have hρ : 0 < ρ := div_pos hR hden
  have hρeq : (1 + ‖J‖) * ρ = R := by
    dsimp only [ρ]
    field_simp
  have hρR : ρ ≤ R := by nlinarith [norm_nonneg J]
  have hJρ : ‖J‖ * ρ ≤ R := by nlinarith
  refine ⟨ρ, hρ, hJρ, rfl, hρR, ?_, ?_, ?_, ?_⟩
  · intro p t _ z hz w hw
    dsimp only
    have hz' : z ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hw' : w ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    rw [extendClosedBall_apply hρ.le _ t z hz', extendClosedBall_apply hρ.le _ t w hw']
    exact ((ha p).norm_sub_time_precomp_closedBall J hJρ t ⟨z, hz'⟩ ⟨w, hw'⟩).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (J.le_opNorm (z - w)) Ca.coe_nonneg)
  · intro p t htt z hz
    dsimp only
    have hz' : z ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [extendClosedBall_apply hρ.le _ t z hz']
    calc
      _ ≤ (Ca : ℝ) * (2 * R) := hclose p t ⟨(neg_le_neg hρR).trans htt.1, htt.2.trans hρR⟩ _
      _ = (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρeq]; ring
  · intro p
    have hc : Continuous (fun z : Set.Icc (-ρ) ρ × Metric.closedBall (0 : X) ρ =>
        a p z.1 (J.closedBallMap hJρ z.2)) :=
      ((ha p).prod_precomp_closedBall J hJρ).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    apply hc.congr
    intro z
    exact (extendClosedBall_apply hρ.le
      (fun t v => a p t (J.closedBallMap hJρ v)) z.1 z.2.val z.2.property).symm
  · intro p t z
    exact extendClosedBall_apply hρ.le _ t z.val z.property

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open MeasureTheory Filter
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem precomposed_translated_uniform_time_lipschitz
    {ι A V : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (m : A →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (Q : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (D : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (d : CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (P : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ] V)
    (J : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    (q : A) (b₀ : CircleHsPi g ι ((1 : ℕ) : ℝ)) (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → A)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → CircleHsPi g ι ((1 : ℕ) : ℝ))
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : V) R => b f z.1 z.2))
    (haclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖a f t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖b f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (haparam : ∀ f k t s z, ‖a f t z - a k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hbparam : ∀ f k t s z, ‖b f t z - b k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun f => extendClosedBall hρ.le
        (fun t z => a f t (J.closedBallMap hJρ z))
      let reaction := fun f => extendClosedBall hρ.le
        (fun t z => b f t (J.closedBallMap hJρ z))
      let K := circleHsPiInclusion g ι
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      let Params := Set.Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
      let N := fun (p : Params) t
        (v : {v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) | ‖K v‖ ≤ ρ}) =>
        shiftedRemainder m Q K D d q
          (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
          (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) p.2 t v
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
        ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (Lip : ℝ≥0) (u : Params → timeH1 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T)
          (gforce : Params → timeL2 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T),
          LipschitzWith Lip gforce ∧ LipschitzWith (2 * Lip) u ∧
          ∀ f,
          let field := maximalRegularityDuhamelVectorField
            (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
            (a := ((1 : ℕ) : ℝ)) (ι := ι) hT
            (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) (gforce f)
          u f = maximalRegularityDuhamelVectorMap
            (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
            (a := ((1 : ℕ) : ℝ)) (ι := ι) hT (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) (gforce f) ∧
            (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
            gforce f =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
              (show (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
            (u f).toFunL2 =
              (circleHsPiInclusion g ι
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                  2 (timeMeasure T) field ∧
            timeH1.trace0 _ T (u f) = 0 ∧
            timeH1.timeDeriv _ T (u f) =
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s
                  := 0) ((1 : ℕ) : ℝ))).compLpL
                  2 (timeMeasure T) field + gforce f ∧
            ‖gforce f‖ ≤ ρ / 4 := by
  obtain ⟨ρ, hρ, hJρ, hρeq, hρR, halip, haclose', hacont, _⟩ :=
    precomposed_symmetric_reference_coefficient_bounds
      (P := Metric.closedBall f₀ δ) (X := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
      (V := V) (A := A) J hR a q Ca ha haclose
  obtain ⟨ρb, hρb, hJρb, hρbeq, _, hblip, hbclose', hbcont, _⟩ :=
    precomposed_symmetric_reference_coefficient_bounds
      (P := Metric.closedBall f₀ δ) (X := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
      (V := V) (A := CircleHsPi g ι ((1 : ℕ) : ℝ)) J hR b b₀ Cb hb hbclose
  have hρbρ : ρb = ρ := hρbeq.trans hρeq.symm
  clear hρbeq
  subst ρb
  refine ⟨ρ, hρ, hJρ, hρeq, hρR, ?_⟩
  intro alpha reaction K Params N
  have hsmall := scaled_coefficient_radius_bounds ‖m‖₊ ‖Q‖₊ ‖J‖₊ Ca hR hCa
  simp only [coe_nnnorm] at hsmall
  rw [← hρeq] at hsmall
  have halip' : ∀ f t, t ∈ Set.Icc (-ρ) ρ →
      LipschitzOnWith (Ca * ‖J‖₊) (alpha f t) (Metric.closedBall 0 ρ) := by
    intro f t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm] using
      halip f t ht z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
        w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
  have hblip' : ∀ f t, t ∈ Set.Icc (-ρ) ρ →
      LipschitzOnWith (Cb * ‖J‖₊) (reaction f t) (Metric.closedBall 0 ρ) := by
    intro f t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm] using
      hblip f t ht z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
        w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
  have haparam' : ∀ f k t, t ∈ Set.Icc (-ρ) ρ →
      ∀ t', t' ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖alpha f t z - alpha k t' z‖ ≤
        (Ca : ℝ) * max |t - t'| ‖P (f.val - k.val)‖ := by
    intro f k t _ t' _ z hz
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    change ‖extendClosedBall hρ.le _ t z - extendClosedBall hρ.le _ t' z‖ ≤ _
    rw [extendClosedBall_apply hρ.le _ t z hz', extendClosedBall_apply hρ.le _ t' z hz']
    exact haparam f k t t' _
  have hbparam' : ∀ f k t, t ∈ Set.Icc (-ρ) ρ →
      ∀ t', t' ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖reaction f t z - reaction k t' z‖ ≤
        (Cb : ℝ) * max |t - t'| ‖P (f.val - k.val)‖ := by
    intro f k t _ t' _ z hz
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    change ‖extendClosedBall hρ.le _ t z - extendClosedBall hρ.le _ t' z‖ ≤ _
    rw [extendClosedBall_apply hρ.le _ t z hz', extendClosedBall_apply hρ.le _ t' z hz']
    exact hbparam f k t t' _
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    exists_uniform_time_translated_vector_lipschitz (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
      ((1 : ℕ) : ℝ) m Q D d q b₀ f₀ hδ hρ hρ
      alpha reaction P (2 * Ca * (1 + ‖J‖₊)) (Ca * ‖J‖₊) (Cb * ‖J‖₊)
      (2 * Cb * (1 + ‖J‖₊)) Ca Cb halip'
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using haclose') hblip'
      (fun f t ht => by
        simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
          coe_nnnorm] using hbclose' f t ht 0 (by simpa using hρ.le))
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hsmall.2.2.2.1)
      (by simpa only [NNReal.coe_mul, coe_nnnorm] using hsmall.2.2.2.2) hacont hbcont haparam'
        hbparam'
  refine ⟨T₀, hT₀, ?_, ?_⟩
  · rw [hT₀eq]
    exact min_le_left _ _
  intro T hT hTT₀
  obtain ⟨u, gforce, hFLip, huLip, hfacts⟩ := hsol hT hTT₀
  refine ⟨_, u, gforce, hFLip, huLip, ?_⟩
  exact hfacts

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
  (CircleHsPi maximalRegularityDuhamelVectorField)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable {n : ℕ}

private theorem precomposed_circle_translated_lipschitz_solutions
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] V)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → CircleHsPi g₀ (Fin n) 1)
    (Ca Cb : ℝ≥0)
    (halip : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a f z.1 z.2))
    (hblip : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : V) R => b f z.1 z.2))
    (hbaseline : a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)))
    (haclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖a f t z - a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖b f t z - b ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R))
    (haparam : ∀ f k t s z, ‖a f t z - a k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hbparam : ∀ f k t s z, ‖b f t z - b k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hCa : let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun f => extendClosedBall hρ.le
        (fun t z => a f t (J.closedBallMap hJρ z))
      let reaction := fun f => extendClosedBall hρ.le
        (fun t z => b f t (J.closedBallMap hJρ z))
      let Params := Set.Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
        ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (Lip : ℝ≥0) (u : Params → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : Params → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          LipschitzWith Lip gforce ∧ LipschitzWith (2 * Lip) u ∧
          ∀ p, referenceCircleSolutionFacts g₀ p.2.val
            (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
            (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) ρ hT (u p) (gforce p) := by
  let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := coordinateMultiplication (ι := Fin n) (scalarHsMul
          g₀ 1 (by norm_num))
  let q := ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
  let d : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      appHs g₀ 0 0 1 (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
  let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
  let D₁ := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ 1
  let fref : Metric.closedBall f₀ δ := ⟨f₀, Metric.mem_closedBall_self hδ⟩
  let zref : Metric.closedBall (0 : V) R := ⟨0, Metric.mem_closedBall_self hR.le⟩
  change a fref 0 zref = q at hbaseline
  have haclose' : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖a f t z - q‖ ≤ (Ca : ℝ) * (2 * R) := by
    intro f t htt z
    rw [← hbaseline]
    exact haclose f t htt z
  let a' := fun f t z => C (a f t z)
  let b' := fun f t z => Cpi (b f t z)
  have halip' : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall
        (0 : V) R => a' f z.1 z.2) := by
    intro f
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [a', dist_eq_norm, ← map_sub, C, tensorHsCongrL_apply, norm_tensorHsCongr]
      using (halip f).dist_le_mul z w
  have hblip' : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall
        (0 : V) R => b' f z.1 z.2) := by
    intro f
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [b', dist_eq_norm, ← map_sub, Cpi.norm_map]
      using (hblip f).dist_le_mul z w
  have haclose'' : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖a' f t z - C q‖ ≤ (Ca : ℝ) * (2 * R) := by
    intro f t htt z
    simpa only [a', ← map_sub, C, tensorHsCongrL_apply, norm_tensorHsCongr] using haclose' f t htt z
  have hbclose' : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖b' f t z - Cpi (b fref 0 zref)‖ ≤ (Cb : ℝ) * (2 * R) := by
    intro f t htt z
    simpa only [b', ← map_sub, Cpi.norm_map] using hbclose f t htt z
  have haparam' : ∀ f k t s z, ‖a' f t z - a' k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖ := by
    intro f k t s z
    simpa only [a', ← map_sub, C, tensorHsCongrL_apply, norm_tensorHsCongr]
      using haparam f k t s z
  have hbparam' : ∀ f k t s z, ‖b' f t z - b' k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖ := by
    intro f k t s z
    simpa only [b', ← map_sub, Cpi.norm_map] using hbparam f k t s z
  obtain ⟨ρ, hρ, hJρ, hρeq, hρR, T₀, hT₀, hT₀ρ, hsol⟩ :=
    precomposed_translated_uniform_time_lipschitz g₀ m Q D₁ d P J (C q) (Cpi (b fref 0 zref)) f₀
      hδ hR a' b' Ca Cb halip' hblip' haclose'' hbclose' haparam' hbparam' hCa
  let alpha := fun f => extendClosedBall hρ.le (fun t z => a f t (J.closedBallMap hJρ z))
  let reaction := fun f => extendClosedBall hρ.le (fun t z => b f t (J.closedBallMap hJρ z))
  have halpha : (fun f => extendClosedBall hρ.le (fun t z => a' f t (J.closedBallMap hJρ z))) =
      fun f t z => C (alpha f t z) := by
    funext f t z
    simp only [a', alpha, extendClosedBall]
    split_ifs <;> rfl
  have hreaction : (fun f => extendClosedBall hρ.le (fun t z => b' f t (J.closedBallMap hJρ z))) =
      fun f t z => Cpi (reaction f t z) := by
    funext f t z
    simp only [b', reaction, extendClosedBall]
    split_ifs <;> rfl
  refine ⟨ρ, hρ, hJρ, hρeq, hρR, T₀, hT₀, hT₀ρ, ?_⟩
  intro T hT hTT₀
  obtain ⟨Lip, u, gforce, hFLip, huLip, hfacts⟩ := hsol hT hTT₀
  refine ⟨Lip, u, gforce, hFLip, huLip, ?_⟩
  intro p
  obtain ⟨hu, hstate, hforce, hreal, htrace, hderiv, hnorm⟩ := hfacts p
  unfold referenceCircleSolutionFacts
  refine ⟨hu, hstate, hreal, htrace, hderiv, hnorm, ?_⟩
  apply circle_shifted_equation_ae g₀ p.2.val
    (fun t z => C (alpha p.2 ((p.1 : ℝ) + t) z))
    (fun t z => Cpi (reaction p.2 ((p.1 : ℝ) + t) z)) hρ.le
    (maximalRegularityDuhamelVectorField
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n)
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 (gforce p)) (gforce p) hstate
  have hq : C q = ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) := by
    exact
      tensorHsCongrL_ccTensorToHs
      g₀ _ _
  rw [halpha, hreaction, hq] at hforce
  exact hforce

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable {n : ℕ}

private def referenceCircleSymmetricCoefficientFacts
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (δ ρ : ℝ)
    (alpha : Metric.closedBall f₀ δ → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀
      0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →
      CircleHsPi g₀ (Fin n) 1) : Prop :=
  (∀ (f : Metric.closedBall f₀ δ) t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
    Set.range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P f.val + J z))) ⊆ S) ∧
  (∀ f t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ x,
    scalarH1ToContinuous g₀ (alpha f t z) x =
      F (fun i => match i with
        | none => t
        | some i => scalarH1ToContinuous g₀ ((P f) i + (J z) i) x)) ∧
  (∀ f t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ x j,
    scalarH1ToContinuous g₀ (reaction f t z j) x =
      G (fun i => match i with
        | none => t
        | some i => scalarH1ToContinuous g₀ ((P f) i + (J z) i) x) j)

private theorem referenceCircleSymmetricCoefficientFacts_precomposed
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    {δ R ρ : ℝ} (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R) (hρR : ρ ≤ R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R →
      TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R →
      CircleHsPi g₀ (Fin n) 1)
    (hrange : ∀ (f : Metric.closedBall f₀ δ) t
      (v : Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R),
      t ∈ Set.Icc (-R) R →
      Set.range (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, P f.val + v.val))) ⊆ S)
    (haeval : ∀ f t, t ∈ Set.Icc (-R) R → ∀ v x,
      scalarH1ToContinuous g₀ (a f t v) x =
        F (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x))
    (hbeval : ∀ f t, t ∈ Set.Icc (-R) R → ∀ v x j,
      scalarH1ToContinuous g₀ (b f t v j) x =
        G (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) :
    let alpha := fun f => extendClosedBall hρ.le
      (fun t z => a f t (J.closedBallMap hJρ z))
    let reaction := fun f => extendClosedBall hρ.le
      (fun t z => b f t (J.closedBallMap hJρ z))
    referenceCircleSymmetricCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction := by
  intro alpha reaction
  refine ⟨?_, ?_, ?_⟩
  · intro f t htt z hz
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact hrange f t (J.closedBallMap hJρ ⟨z, hz'⟩) ⟨(neg_le_neg hρR).trans htt.1, htt.2.trans hρR⟩
  · intro f t htt z hz x
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [alpha]
    rw [extendClosedBall_apply hρ.le _ t z hz']
    exact haeval f t ⟨(neg_le_neg hρR).trans htt.1, htt.2.trans hρR⟩ (J.closedBallMap hJρ ⟨z,
      hz'⟩) x
  · intro f t htt z hz x j
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [reaction]
    rw [extendClosedBall_apply hρ.le _ t z hz']
    exact hbeval f t ⟨(neg_le_neg hρR).trans htt.1, htt.2.trans hρR⟩ (J.closedBallMap hJρ ⟨z,
      hz'⟩) x j

private def referenceCirclePrincipalNormBounds
    {P X : Type*} [NormedAddCommGroup X]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (ρ : ℝ)
    (alpha : P → ℝ → X → TensorHs g₀ 0 0 1) : Prop :=
  ∀ f t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
    let E₁ := tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (alpha f t z))‖ ≤ (1 / 4 : ℝ) ∧
    ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (alpha f t z))‖ ≤ (1 / 4 : ℝ)

private theorem parameter_principal_bounds_of_norm_sub_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {ε : ℝ}
    (hprincipal : ∀ a : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ),
      ‖a - ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
        (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤ ε →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ) ∧
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ))
    (a : TensorHs g₀ 0 0 1)
    (ha : ‖a - ccTensorToHs g₀ 0 1
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤ ε) :
    let E₁ := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ a)‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ a)‖ ≤ (1 / 4 : ℝ) := by
  intro E₁
  apply hprincipal
  rw [← tensorHsCongrL_ccTensorToHs g₀
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)), ← map_sub]
  change ‖tensorHsCongr g₀ 0 0
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) _‖ ≤ ε
  rw [norm_tensorHsCongr]
  exact ha

private theorem reference_circle_translated_lipschitz_solutions_of_coefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R →
      TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R →
      CircleHsPi g₀ (Fin n) 1)
    (Ca Cb : ℝ≥0)
    (halip : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin
      n) 1) R => a f z.1 z.2))
    (hblip : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin
      n) 1) R => b f z.1 z.2))
    (hbaseline : a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)))
    (haclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖a f t z - a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (-R) R → ∀ z,
      ‖b f t z - b ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R))
    (haparam : ∀ f k t s z, ‖a f t z - a k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hbparam : ∀ f k t s z, ‖b f t z - b k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hCa : let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1)))
    (hrange : ∀ (f : Metric.closedBall f₀ δ) t
      (v : Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R),
      t ∈ Set.Icc (-R) R →
      Set.range (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, P f.val + v.val))) ⊆ S)
    (haeval : ∀ f t, t ∈ Set.Icc (-R) R → ∀ v x,
      scalarH1ToContinuous g₀ (a f t v) x =
        F (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x))
    (hbeval : ∀ f t, t ∈ Set.Icc (-R) R → ∀ v x j,
      scalarH1ToContinuous g₀ (b f t v j) x =
        G (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) :
    ∃ (ρ : ℝ), 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1,
      referenceCircleSymmetricCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction ∧
      (∀ f t, t ∈ Set.Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
        ‖alpha f t z - ccTensorToHs g₀ 0 1
          (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤ (Ca : ℝ) * (2 * R)) ∧
      let Params := Set.Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
        ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (Lip : ℝ≥0) (u : Params → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : Params → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          LipschitzWith Lip gforce ∧ LipschitzWith (2 * Lip) u ∧
          ∀ p, referenceCircleSolutionFacts g₀ p.2.val
            (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
            (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) ρ hT (u p) (gforce p) := by
  obtain ⟨ρ, hρ, hJρ, _, hρR, hsol⟩ :=
    precomposed_circle_translated_lipschitz_solutions (n := n)
      (V := CircleHsPi g₀ (Fin n ⊕ Fin n) 1) g₀ f₀ P J hδ hR a b Ca Cb halip hblip
      hbaseline haclose hbclose haparam hbparam hCa
  let alpha := fun f => extendClosedBall hρ.le (fun t z => a f t (J.closedBallMap hJρ z))
  let reaction := fun f => extendClosedBall hρ.le (fun t z => b f t (J.closedBallMap hJρ z))
  refine ⟨ρ, hρ, alpha, reaction, ?_, ?_, hsol⟩
  · exact referenceCircleSymmetricCoefficientFacts_precomposed g₀ f₀ P J F G S hρ hJρ hρR
      a b hrange haeval hbeval
  · intro f t ht z hz
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [alpha]
    rw [extendClosedBall_apply hρ.le _ t z hz', ← hbaseline]
    exact haclose f t ⟨(neg_le_neg hρR).trans ht.1, ht.2.trans hρR⟩ _


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal
open MeasureTheory Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_translated_lipschitz_solutions
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀
      (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n)
        (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2 (fun _
        : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs
          (c₀.pullbackMetric (g 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1,
      referenceCircleSymmetricCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha
        reaction ∧
      referenceCirclePrincipalNormBounds (n := n) (c₀.pullbackMetric (g 0)) ρ alpha ∧
      let Params := Set.Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
        ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (Lip : ℝ≥0)
          (u : Params → timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : Params → timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
          LipschitzWith Lip gforce ∧ LipschitzWith (2 * Lip) u ∧
          ∀ p, referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) p.2.val
            (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
            (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) ρ hT (u p) (gforce p) := by
  intro f₀ J₀ K₀ P J K F G S
  refine ⟨fun f v => reference_jet_add_correction_eq (c₀.pullbackMetric (g 0)) f v, ?_⟩
  obtain ⟨ε, hε, hprincipal⟩ := exists_pos_parameterPrincipal_norm_le (n := n)
    (c₀.pullbackMetric (g 0))
  have hthreshold := circle_coefficient_threshold_pos (n := n) (c₀.pullbackMetric (g 0))
  let εComp := min (1 / (32 *
    (‖coordinateMultiplication (ι := Fin n)
      (scalarHsMul (c₀.pullbackMetric (g 0)) 1 (by norm_num))‖ *
      ‖AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) (c₀.pullbackMetric (g 0)) 1‖ + 1)))
    (ε / 2)
  have hεComp : 0 < εComp := lt_min hthreshold (half_pos hε)
  obtain ⟨R, δ, hR, hδ, _, Ca, Cb, _, hCaRaw, _,
      a, b, halip, hblip, haclose, hbclose, haparam, hbparam, hrange, haeval, hbeval⟩ :=
    ambient_reference_symmetric_composition c₀ g ht he hr hEU hleft β hG hεComp
  have hCa := hCaRaw.trans (min_le_left _ _)
  have hCaHalf : (Ca : ℝ) * R ≤ ε / 2 := hCaRaw.trans (min_le_right _ _)
  let fref := (⟨ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2),
    Metric.mem_closedBall_self hδ.le⟩ :
      Metric.closedBall (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)) δ)
  let zref := (⟨0, Metric.mem_closedBall_self hR.le⟩ :
    Metric.closedBall (0 : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1) R)
  have ha0 := haeval fref 0 ⟨neg_nonpos.mpr hR.le, hR.le⟩ zref
  have hbaseline :=
    reference_diffusion_at_sobolev_jet
      (E := E) (H := H) (M := M) (I := I) (n := n)
      c₀ g (e := e) he (r := r) (U := U) hr hEU hleft β
      (a fref 0 zref) (by
        intro x
        rw [ha0 x]
        congr 2
        funext i
        cases i <;> simp only [fref, zref, WithLp.ofLp_zero, Pi.zero_apply, zero_add])
  have hs0 := reference_circle_translated_lipschitz_solutions_of_coefficients (n := n)
    (c₀.pullbackMetric (g 0)) (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
  have hs1 := hs0 J P F G S hδ.le hR
  have hs2 := hs1 a b Ca Cb
  have hs3 := hs2 halip hblip hbaseline
  have hs4 := hs3 haclose hbclose haparam hbparam hCa
  dsimp only [P, J₀, K₀, F, G, S] at hs4
  have hs5a := hs4 (by simpa only [zero_add] using hrange)
  have hs5b := hs5a (by
    intro f t ht' v x
    rw [haeval f t ht' v x]
    congr 1
    funext i
    cases i <;> simp only [zero_add])
  have hs5 := hs5b (by
    intro f t ht' v x j
    rw [hbeval f t ht' v x j]
    congr 2
    funext i
    cases i <;> simp only [zero_add])
  obtain ⟨ρ, hρ, alpha, reaction, hcoeff, halphaClose, hsol⟩ := hs5
  refine ⟨δ, ρ, hδ, hρ, alpha, reaction, hcoeff, ?_, hsol⟩
  intro f t ht' z hz E₁
  have hraw := halphaClose f t ht' z hz
  have hsmall : ‖alpha f t z - ccTensorToHs (c₀.pullbackMetric (g 0)) 0 1
      (scalarCc (c₀.pullbackMetric (g 0))
        (AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric (g 0))))‖ ≤ ε :=
    hraw.trans (by nlinarith [hCaHalf])
  exact parameter_principal_bounds_of_norm_sub_le (c₀.pullbackMetric (g 0))
    hprincipal (alpha f t z) hsmall


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal
open MeasureTheory Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_translated_solutions_on_smooth_neighborhood
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth
      hr)) :
    let _ := smoothImmersionTopology e
    let f₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀
      (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n)
        (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2 (fun _
        : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β (firstJetCoordinates n
        z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs
          (c₀.pullbackMetric (g 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1,
      referenceCircleSymmetricCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha
        reaction ∧
      referenceCirclePrincipalNormBounds (n := n) (c₀.pullbackMetric (g 0)) ρ alpha ∧
      ∃ V : Set (SmoothImmersion (I := I) (M := M)),
        IsOpen V ∧ c₀ ∈ V ∧
        ∃ hV : ∀ d ∈ V,
          fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d ∈ Metric.closedBall f₀ δ,
        let Params := Set.Ioo (-ρ / 4) (ρ / 4) × V
        ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
          ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
          ∃ (u : Params →
              timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
            (gforce : Params →
              timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
            Continuous u ∧ Continuous gforce ∧
            ∀ (p : Params), referenceCircleSolutionFacts (c₀.pullbackMetric (g 0))
              (fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) p.2.val)
              (fun t z => alpha
                (⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) p.2.val,
                  hV p.2.val p.2.property⟩)
                ((p.1 : ℝ) + t) z)
              (fun t z => reaction
                (⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) p.2.val,
                  hV p.2.val p.2.property⟩)
                ((p.1 : ℝ) + t) z) ρ hT (u p) (gforce p) := by
  let _ := smoothImmersionTopology e
  intro _ f₀ J₀ K₀ P J K F G S
  obtain ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff, hmargin, T₀, hT₀, hT₀ρ, hfamily⟩ :=
    ambient_reference_translated_lipschitz_solutions c₀ g ht e.smooth hr hEU hleft β hG
  obtain ⟨V, hVopen, hc₀, hV⟩ :=
    exists_isOpen_fixedAmbientSobolev_mem_closedBall e c₀ (g 0) hδ
  refine ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff, hmargin,
    V, hVopen, hc₀, hV, T₀, hT₀, hT₀ρ, ?_⟩
  intro T hT hTT₀
  obtain ⟨Lip, u, gforce, hFLip, huLip, hfacts⟩ := hfamily hT hTT₀
  let pull : Set.Ioo (-ρ / 4) (ρ / 4) × V →
      Set.Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ := fun p =>
    (⟨p.1.val, p.1.property.1.le, p.1.property.2.le⟩,
      ⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) p.2.val, hV p.2.val p.2.property⟩)
  have hpull : Continuous pull := by
    apply Continuous.prodMk
    · exact (continuous_subtype_val.comp continuous_fst).subtype_mk _
    · exact ((continuous_fixedAmbientSobolev e (c₀.pullbackMetric (g 0))).comp
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  exact ⟨u ∘ pull, gforce ∘ pull, huLip.continuous.comp hpull,
    hFLip.continuous.comp hpull, fun p => hfacts (pull p)⟩


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open private
  vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal
open MeasureTheory Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_joint_start_time_solutions
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (t₀ : ℝ) (ht : t₀ ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth
      hr)) :
    let gshift : ℝ → SmoothRiemannianMetric I M := fun s => g (t₀ + s)
    let _ := smoothImmersionTopology e
    let f₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) :=
      ambientSobolev c₀ (gshift 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n)
        (c₀.pullbackMetric (gshift 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2
        (fun _ : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (gshift 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (gshift 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (gshift 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β ∘
        firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β
        (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain (D.timeShift t₀)
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs
          (c₀.pullbackMetric (gshift 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) 1,
      referenceCircleSymmetricCoefficientFacts (c₀.pullbackMetric (gshift 0)) f₀ P J F G S δ ρ
        alpha reaction ∧
      referenceCirclePrincipalNormBounds (n := n) (c₀.pullbackMetric (gshift 0)) ρ alpha ∧
      ∃ V : Set (SmoothImmersion (I := I) (M := M)),
        IsOpen V ∧ c₀ ∈ V ∧
        ∃ hV : ∀ d ∈ V,
          fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) d ∈ Metric.closedBall f₀ δ,
        let Params := Set.Ioo (-ρ / 4) (ρ / 4) × V
        ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ / 4 ∧
          ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
          ∃ (u : Params →
              timeH1 (CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
            (gforce : Params →
              timeL2 (CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
            Continuous u ∧ Continuous gforce ∧
            ∀ (p : Params), referenceCircleSolutionFacts (c₀.pullbackMetric (gshift 0))
              (fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) p.2.val)
              (fun t z => alpha
                ⟨fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) p.2.val,
                  hV p.2.val p.2.property⟩ ((p.1 : ℝ) + t) z)
              (fun t z => reaction
                ⟨fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) p.2.val,
                  hV p.2.val p.2.property⟩ ((p.1 : ℝ) + t) z) ρ hT (u p) (gforce p) := by
  intro gshift
  have hzero : (0 : ℝ) ∈ (D.timeShift t₀).regular := by
    change 0 + t₀ ∈ D.regular
    simpa only [zero_add] using ht
  have hshift : MetricFamilySmoothOn (D.timeShift t₀)
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) := by
    simpa only [gshift, add_comm] using hG.timeShift t₀
  exact ambient_reference_translated_solutions_on_smooth_neighborhood
    c₀ gshift hzero e hr hEU hleft β hshift


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
