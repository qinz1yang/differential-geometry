import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCurveHarnack
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M]

section CurveTools

variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curve_scalar_hasDerivAt (hS : IsSolutionOn S)
    (hregular : D.regular = Set.Iio 0) {t : ℝ} (ht : t < 0) (gamma : ℝ → M)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    HasDerivAt (fun s : ℝ => S.scalar s (gamma s))
      (deriv (fun s : ℝ => S.scalar s (gamma t)) t +
        (S.base.metric t).inner (gamma t)
          (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) t := by
  have htreg : t ∈ D.regular := by
    rw [hregular]
    exact ht
  have hscalar : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => S.scalar p.1 p.2) (t, gamma t) :=
    ((scalar_joint (I := I) S hS).contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨htreg, mem_univ _⟩)).mdifferentiableAt
        (by norm_num)
  have htime : HasDerivAt (fun s : ℝ => S.scalar s (gamma t))
      (deriv (fun s : ℝ => S.scalar s (gamma t)) t) t :=
    ((hS.scalarTime (K := D.carrier) (D.regular_subset htreg) subset_rfl
      (gamma t)).differentiableAt (D.regular_mem_nhds htreg)).hasDerivAt
  exact hasDerivAt_along_curve (I := I) (S.base.metric t) hscalar hgamma htime

private theorem curve_harnack_nonneg (hS : IsSolutionOn S)
    (hregular : D.regular = Set.Iio 0)
    (hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ D.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : M,
        Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.carrier, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (gamma : ℝ → M) {t : ℝ} (ht : t < 0) :
    0 ≤ deriv (fun s : ℝ => S.scalar s (gamma t)) t +
      (S.base.metric t).inner (gamma t)
        (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) +
      (1 / 2 : ℝ) * smoothCurveRicciEnergy S gamma (t, t) := by
  have hpast : Set.Iic t ⊆ D.regular := by
    intro s hs
    rw [hregular]
    exact lt_of_le_of_lt hs ht
  have htrace := hamilton_ancient_trace_harnack (I := I) S hS
    (fun s hs => hcomplete s (D.regular_subset hs))
    (fun a b hab => hcurv a b (hab.trans D.regular_subset))
    (fun s hs y => hR s (D.regular_subset hs) y) hpast (gamma t)
    ((1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
  change 0 ≤ deriv (fun s : ℝ => S.scalar s (gamma t)) t +
    2 * (S.base.metric t).inner (gamma t)
      (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
      ((1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) +
    2 * metricRicciAt (I := I) (S.base.metric t) (gamma t)
      (vec2 ((1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
        ((1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) at htrace
  rw [metricRicciAt_apply_eq_ricciTensor] at htrace
  simp only [map_smul, smul_apply, smul_eq_mul] at htrace
  change 0 ≤ deriv (fun s : ℝ => S.scalar s (gamma t)) t +
    (S.base.metric t).inner (gamma t)
      (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
      (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) +
    (1 / 2 : ℝ) * ricciTensor (I := I) (S.base.metric t) (gamma t)
      (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
  linarith

private theorem curve_compensated_monotone {a b : ℝ}
    {scalar energy derivative : ℝ → ℝ} (hab : a ≤ b)
    (hs : ContinuousOn scalar (Set.Icc a b)) (he : ContinuousOn energy (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt scalar (derivative t) t)
    (hnonneg : ∀ t ∈ Set.Ioo a b, 0 ≤ derivative t + (1 / 2 : ℝ) * energy t) :
    MonotoneOn (fun t => scalar t + (1 / 2 : ℝ) * ∫ s in a..t, energy s)
      (Set.Icc a b) := by
  have hi : ContinuousOn (fun t => ∫ s in a..t, energy s) (Set.Icc a b) := by
    have hint : IntervalIntegrable energy volume a b := he.intervalIntegrable_of_Icc hab
    have h := intervalIntegral.continuousOn_primitive_interval' hint
      (a := a) left_mem_uIcc
    simpa only [uIcc_of_le hab] using h
  have htotal (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun q => scalar q + (1 / 2 : ℝ) * ∫ s in a..q, energy s)
        (derivative t + (1 / 2 : ℝ) * energy t) t := by
    have htcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    let _ : Fact (t ∈ Set.Icc a b) := ⟨htcc⟩
    have hint : IntervalIntegrable energy volume a t :=
      (he.mono (uIcc_subset_Icc ⟨le_rfl, hab⟩ htcc)).intervalIntegrable
    have hFTC : HasDerivWithinAt (fun q => ∫ s in a..q, energy s)
        (energy t) (Set.Icc a b) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hint
        (he.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (he t htcc)
    exact (hd t ht).add ((hFTC.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).const_mul (1 / 2 : ℝ))
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (hs.add (hi.const_mul (1 / 2 : ℝ)))
  · intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa only [interior_Icc] using ht
    exact (htotal t ht').differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa only [interior_Icc] using ht
    change 0 ≤ deriv (fun q => scalar q + (1 / 2 : ℝ) * ∫ s in a..q, energy s) t
    rw [(htotal t ht').deriv]
    exact hnonneg t ht'

private theorem curve_scalar_le_add_ricci_integral (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Set.Iic 0) (hregular : D.regular = Set.Iio 0)
    (hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ D.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : M,
        Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.carrier, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma) {a : ℝ} (ha : a ≤ 0) :
    S.scalar a (gamma a) ≤ S.scalar 0 (gamma 0) +
      (1 / 2 : ℝ) * ∫ s in a..0, smoothCurveRicciEnergy S gamma (s, s) := by
  have hcar : Set.Icc a 0 ⊆ D.carrier := by
    rw [hcarrier]
    intro t ht
    exact ht.2
  have he : ContinuousOn (fun t => smoothCurveRicciEnergy S gamma (t, t)) (Set.Icc a 0) :=
    (smoothCurveRicciEnergy_continuousOn S hS gamma hgamma).comp
      (continuous_id.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hcar ⟨ht.1, ht.2⟩, mem_univ _⟩)
  have hs : ContinuousOn (fun t => S.scalar t (gamma t)) (Set.Icc a 0) := by
    have hmap : ContinuousOn (fun t : ℝ => (t, gamma t)) (Set.Icc a 0) :=
      continuousOn_id.prodMk hgamma.continuous.continuousOn
    have hmaps : MapsTo (fun t : ℝ => (t, gamma t)) (Set.Icc a 0)
        (D.carrier ×ˢ (Set.univ : Set M)) :=
      fun t ht => ⟨hcar ⟨ht.1, ht.2⟩, mem_univ _⟩
    simpa only [Function.comp_def] using hS.scalarCont.comp hmap hmaps
  have hmono := curve_compensated_monotone (a := a) (b := 0) ha hs he
    (derivative := fun t => deriv (fun s : ℝ => S.scalar s (gamma t)) t +
      (S.base.metric t).inner (gamma t)
        (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)))
    (fun t ht => curve_scalar_hasDerivAt (S := S) hS hregular ht.2 gamma
      (hgamma.mdifferentiableAt (x := t) (by norm_num)))
    (fun t ht => curve_harnack_nonneg (S := S) hS hregular hcomplete hcurv hR gamma ht.2)
  have h := hmono ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  simpa only [intervalIntegral.integral_same, mul_zero, add_zero] using h

end CurveTools

theorem hamilton_ancient_trace_harnack_at_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Set.Iic 0) (hregular : D.regular = Set.Iio 0)
    (hcomplete : ∀ t ∈ D.carrier,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ D.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : M,
        Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.carrier, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) (V : TangentSpace I x) :
    0 ≤ derivWithin (fun s : ℝ => S.scalar s x) D.carrier 0 +
      2 * (S.base.metric 0).inner x
        (gradientAt (I := I) (flowG (I := I) S) 0 (S.scalar 0) x) V +
      2 * metricRicci (I := I) (M := M) (S.base.metric 0) x (vec2 V V) := by
  let g := S.base.metric 0
  have hzero : (0 : ℝ) ∈ D.carrier := by
    rw [hcarrier]
    simp only [Set.mem_Iic]
    exact le_rfl
  have hg : RiemannianMetricComplete (I := I) g := hcomplete 0 hzero
  let cg := g.toContinuousRiemannianMetric
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun q v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g q v
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x ((2 : ℝ) • V)
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma :=
    contMDiffOn_univ.mp (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x ((2 : ℝ) • V))
  have hgamma0 : gamma 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x ((2 : ℝ) • V)
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) = (2 : ℝ) • (V : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x ((2 : ℝ) • V)
  have hspatial : HasDerivAt (fun h : ℝ => S.scalar 0 (gamma h))
      (g.inner (gamma 0) (gradientFun (I := I) g (S.scalar 0) (gamma 0))
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ))) 0 := by
    have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (S.scalar 0) (gamma 0) :=
      (metricScalar_smooth (I := I) g).mdifferentiableAt (by simp)
    have hgc := (hgamma.mdifferentiableAt (x := (0 : ℝ)) (by norm_num)).mdifferentiableWithinAt
      (s := (Set.univ : Set ℝ))
    have h := hasDerivWithinAt_comp_mfderivWithin I (S.scalar 0) gamma Set.univ 0 hf hgc
    simp only [hasDerivWithinAt_univ, mfderivWithin_univ] at h
    exact h.congr_deriv
      (inner_gradientFun (I := I) g (S.scalar 0) (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ))).symm
  have htime : HasDerivWithinAt (fun s : ℝ => S.scalar s (gamma 0))
      (derivWithin (fun s : ℝ => S.scalar s (gamma 0)) (Set.Iic 0) 0) (Set.Iic 0) 0 := by
    simpa only [hcarrier] using
      (hS.scalarTime (K := D.carrier) hzero (fun _ hs => hs) (gamma 0)).hasDerivWithinAt
  have henergy : Tendsto (fun h => (∫ s in 0 - h..0,
      smoothCurveRicciEnergy S gamma (s, s - (0 - h))) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (smoothCurveRicciEnergy S gamma (0, 0))) :=
    smoothCurveRicciEnergy_short_average_tendsto S hS gamma hgamma (by rw [hcarrier])
  have hmain := terminal_harnack_of_endpoint_differences
    (spatial := fun h => S.scalar 0 (gamma h))
    (temporal := fun s => S.scalar s (gamma 0))
    (energy := fun h => (∫ s in 0 - h..0,
      smoothCurveRicciEnergy S gamma (s, s - (0 - h))) / h)
    hspatial htime henergy ?_
  · change 0 ≤ derivWithin (fun s : ℝ => S.scalar s (gamma 0)) (Set.Iic 0) 0 +
      g.inner (gamma 0) (gradientFun (I := I) g (S.scalar 0) (gamma 0))
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) +
      (1 / 2 : ℝ) * ricciTensor (I := I) g (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) at hmain
    rw [hvelocity, hgamma0] at hmain
    simp only [map_smul, smul_apply, smul_eq_mul] at hmain
    rw [← hcarrier] at hmain
    change 0 ≤ derivWithin (fun s : ℝ => S.scalar s x) D.carrier 0 +
      2 * g.inner x (gradientFun (I := I) g (S.scalar 0) x) V +
      2 * metricRicciAt (I := I) g x (vec2 V V)
    rw [metricRicciAt_apply_eq_ricciTensor]
    linarith
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    let shift : ℝ → ℝ := fun s => s - (0 - h)
    have hshift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 shift :=
      contMDiff_id.sub contMDiff_const
    have hgammaShift : ContMDiff 𝓘(ℝ, ℝ) I 1 (gamma ∘ shift) :=
      hgamma.comp hshift
    have hint := curve_scalar_le_add_ricci_integral (S := S) hS hcarrier hregular hcomplete
      hcurv hR (gamma ∘ shift) hgammaShift (a := 0 - h) (by linarith)
    have hvelocity' (s : ℝ) :
        mfderiv 𝓘(ℝ, ℝ) I (gamma ∘ shift) s (1 : ℝ) =
          mfderiv 𝓘(ℝ, ℝ) I gamma (s - (0 - h)) (1 : ℝ) := by
      rw [mfderiv_comp s (hgamma.mdifferentiableAt (x := shift s) (by norm_num))
        (hshift.mdifferentiableAt (x := s) (by norm_num))]
      change mfderiv 𝓘(ℝ, ℝ) I gamma (shift s)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) shift s (1 : ℝ)) = _
      simp only [shift, mfderiv_eq_fderiv, fderiv_sub_const]
      change mfderiv 𝓘(ℝ, ℝ) I gamma (s - (0 - h))
        ((fderiv ℝ (id : ℝ → ℝ) s) (1 : ℝ)) = _
      simp only [fderiv_id, ContinuousLinearMap.id_apply]
    have henergy' : (fun s => smoothCurveRicciEnergy S (gamma ∘ shift) (s, s)) =
        (fun s => smoothCurveRicciEnergy S gamma (s, s - (0 - h))) := by
      funext s
      unfold smoothCurveRicciEnergy
      rw [hvelocity']
      rfl
    rw [henergy'] at hint
    simp only [Function.comp_apply, shift, sub_self, sub_sub_cancel] at hint
    have hmul : h * ((∫ s in 0 - h..0,
        smoothCurveRicciEnergy S gamma (s, s - (0 - h))) / h) =
        ∫ s in 0 - h..0, smoothCurveRicciEnergy S gamma (s, s - (0 - h)) := by
      field_simp [ne_of_gt hh]
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
