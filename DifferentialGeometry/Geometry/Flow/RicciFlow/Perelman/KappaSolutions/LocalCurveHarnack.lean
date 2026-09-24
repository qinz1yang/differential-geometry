import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShortCurveRicciEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology Interval

universe u uE uH

private theorem local_curve_compensated_monotone {a b : ℝ}
    {scalar energy derivative : ℝ → ℝ} (hab : a ≤ b)
    (hs : ContinuousOn scalar (Icc a b)) (he : ContinuousOn energy (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt scalar (derivative t) t)
    (hnonneg : ∀ t ∈ Ioo a b, 0 ≤ derivative t + (1 / 2 : ℝ) * energy t) :
    MonotoneOn (fun t => scalar t + (1 / 2 : ℝ) * ∫ s in a..t, energy s) (Icc a b) := by
  have hi : ContinuousOn (fun t => ∫ s in a..t, energy s) (Icc a b) := by
    have hint : IntervalIntegrable energy volume a b := he.intervalIntegrable_of_Icc hab
    have h := intervalIntegral.continuousOn_primitive_interval' hint
      (a := a) left_mem_uIcc
    simpa only [uIcc_of_le hab] using h
  have htotal (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun q => scalar q + (1 / 2 : ℝ) * ∫ s in a..q, energy s)
        (derivative t + (1 / 2 : ℝ) * energy t) t := by
    have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    let _ : Fact (t ∈ Icc a b) := ⟨htcc⟩
    have hint : IntervalIntegrable energy volume a t :=
      (he.mono (uIcc_subset_Icc ⟨le_rfl, hab⟩ htcc)).intervalIntegrable
    have hFTC : HasDerivWithinAt (fun q => ∫ s in a..q, energy s)
        (energy t) (Icc a b) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hint
        (he.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (he t htcc)
    exact (hd t ht).add ((hFTC.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).const_mul (1 / 2 : ℝ))
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hs.add (hi.const_mul (1 / 2 : ℝ)))
  · intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    exact (htotal t ht').differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    change 0 ≤ deriv (fun q => scalar q + (1 / 2 : ℝ) * ∫ s in a..q, energy s) t
    rw [(htotal t ht').deriv]
    exact hnonneg t ht'

section LocalEnergy

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {D : RealTimeInterval}

theorem locallySmoothCurveRicciEnergy_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gamma : ℝ → M) {U : Set ℝ} (hU : IsOpen U)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U) :
    ContinuousOn (smoothCurveRicciEnergy S gamma) (D.carrier ×ˢ U) := by
  classical
  let K : Set (ℝ × ℝ) := D.carrier ×ˢ U
  let v : (t : ℝ) → TangentSpace I (gamma t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
  have hlift : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvWithin : ContinuousOn (fun t : ℝ =>
      tangentMapWithin 𝓘(ℝ, ℝ) I gamma U
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) U :=
    (hgamma.continuousOn_tangentMapWithin (by norm_num) hU.uniqueMDiffOn).comp
      hlift.continuousOn (fun _ ht => ht)
  have hv : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (gamma t) (v t)) U := by
    refine hvWithin.congr (fun t ht => ?_)
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
      (hgamma.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by norm_num)
    exact (tangentMapWithin_eq_tangentMap
      (p := (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (hU.uniqueMDiffOn t ht) hdiff).symm
  rw [continuousOn_iff_continuous_domRestrict]
  have ht : Continuous (fun q : ↥K => (q : ℝ × ℝ).1) :=
    continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun q : ↥K => (q : ℝ × ℝ).2) :=
    continuous_snd.comp continuous_subtype_val
  have hx : Continuous (fun q : ↥K => gamma (q : ℝ × ℝ).2) :=
    hgamma.continuousOn.comp_continuous hu (fun q => q.2.2)
  have heval := hS.ricciCont.eval_continuous
    (P := ↥K) (τ := fun q => (q : ℝ × ℝ).1)
    (b := fun q => gamma (q : ℝ × ℝ).2)
    ht (fun q => q.2.1) hx (v := fun _i q => v (q : ℝ × ℝ).2)
    (fun _i => hv.comp_continuous hu (fun q => q.2.2))
  have hRicAt : Continuous (fun q : ↥K =>
      S.ricciAt (q : ℝ × ℝ).1 (gamma (q : ℝ × ℝ).2)
        (vec2 (I := I) (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2))) := by
    refine heval.congr (fun q => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    change metricRicciAt (I := I) (S.base.metric (q : ℝ × ℝ).1)
        (gamma (q : ℝ × ℝ).2) (fun _i : Fin 2 => v (q : ℝ × ℝ).2) =
      metricRicciAt (I := I) (S.base.metric (q : ℝ × ℝ).1)
        (gamma (q : ℝ × ℝ).2)
        (vec2 (I := I) (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2))
    congr 1
    funext i
    fin_cases i <;> rfl
  refine hRicAt.congr (fun q => ?_)
  exact metricRicciAt_apply_eq_ricciTensor (I := I)
    (S.base.metric (q : ℝ × ℝ).1) (gamma (q : ℝ × ℝ).2)
    (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2)

end LocalEnergy

section PointedFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {D : RealTimeInterval}

private local instance localCurveTopology (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    TopologicalSpace F.M := F.topology
private local instance localCurveCharted (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    ChartedSpace H F.M := F.charted
private local instance localCurveSmooth (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    IsManifold I ∞ F.M := F.smooth
private local instance localCurveC1 (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
private local instance localCurveT2 (F : PointedFlowData.{u, uE, uH} (I := I) D) :
    T2Space F.M := F.t2

private theorem klimit_curve_energy_continuousOn
    {F : PointedFlowData.{u, uE, uH} (I := I) D} (gamma : ℝ → F.M)
    {U J : Set ℝ} (hU : IsOpen U) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U)
    (hcar : J ⊆ D.carrier) (hcurve : J ⊆ U) :
    ContinuousOn (fun t => smoothCurveRicciEnergy F.S gamma (t, t)) J :=
  (locallySmoothCurveRicciEnergy_continuousOn F.S F.isSolution gamma hU hgamma).comp
    (continuous_id.prodMk continuous_id).continuousOn
    (fun _ ht => ⟨hcar ht, hcurve ht⟩)

omit [I.Boundaryless] in
private theorem klimit_curve_scalar_continuousOn
    {F : PointedFlowData.{u, uE, uH} (I := I) D} (gamma : ℝ → F.M)
    {U J : Set ℝ} (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U)
    (hcar : J ⊆ D.carrier) (hcurve : J ⊆ U) :
    ContinuousOn (fun t => F.S.scalar t (gamma t)) J := by
  have hmap : ContinuousOn (fun t : ℝ => (t, gamma t)) J :=
    continuousOn_id.prodMk (hgamma.continuousOn.mono hcurve)
  have hmaps : MapsTo (fun t : ℝ => (t, gamma t)) J (D.carrier ×ˢ (univ : Set F.M)) :=
    fun _ ht => ⟨hcar ht, mem_univ _⟩
  simpa only [Function.comp_def] using F.isSolution.scalarCont.comp hmap hmaps

omit [I.Boundaryless] in
private theorem klimit_curve_scalar_hasDerivAt
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa t : ℝ}
    (hK : KLim kappa F) (gamma : ℝ → F.M) {U : Set ℝ}
    (hU : IsOpen U) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U)
    (ht : t < 0) (htU : t ∈ U) :
    HasDerivAt (fun s => F.S.scalar s (gamma s))
      (deriv (fun s => F.S.scalar s (gamma t)) t +
        (F.S.base.metric t).inner (gamma t)
          (gradientFun (I := I) (F.S.base.metric t) (F.S.scalar t) (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) t := by
  have htreg : t ∈ D.regular := by simpa only [hK.regular_eq, mem_Iio] using ht
  have hscalar : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × F.M => F.S.scalar p.1 p.2) (t, gamma t) :=
    ((scalar_joint F.S F.isSolution).contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨htreg, mem_univ _⟩)).mdifferentiableAt
        (by norm_num)
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
    (hgamma.contMDiffAt (hU.mem_nhds htU)).mdifferentiableAt (by norm_num)
  have htime : HasDerivAt (fun s => F.S.scalar s (gamma t))
      (deriv (fun s => F.S.scalar s (gamma t)) t) t :=
    ((F.isSolution.scalarTime (K := D.carrier) (D.regular_subset htreg)
      subset_rfl (gamma t)).differentiableAt (D.regular_mem_nhds htreg)).hasDerivAt
  exact hasDerivAt_along_curve (F.S.base.metric t) hscalar hg htime

private theorem klimit_curve_harnack_nonnegative
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa t : ℝ}
    (hK : KLim kappa F) (gamma : ℝ → F.M) (ht : t < 0) :
    0 ≤ deriv (fun s => F.S.scalar s (gamma t)) t +
      (F.S.base.metric t).inner (gamma t)
        (gradientFun (I := I) (F.S.base.metric t) (F.S.scalar t) (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) +
      (1 / 2 : ℝ) * smoothCurveRicciEnergy F.S gamma (t, t) := by
  have htreg : t ∈ D.regular := by simpa only [hK.regular_eq, mem_Iio] using ht
  let v : TangentSpace I (gamma t) := mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
  have htrace := hK.traceHarnack t (D.regular_subset htreg) (gamma t) ((1 / 2 : ℝ) • v)
  rw [derivWithin_of_mem_nhds (D.regular_mem_nhds htreg)] at htrace
  change 0 ≤ deriv (fun s => F.S.scalar s (gamma t)) t +
    2 * (F.S.base.metric t).inner (gamma t)
      (gradientFun (I := I) (F.S.base.metric t) (F.S.scalar t) (gamma t))
      ((1 / 2 : ℝ) • v) +
    2 * metricRicciAt (I := I) (F.S.base.metric t) (gamma t)
      (vec2 ((1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) at htrace
  rw [metricRicciAt_apply_eq_ricciTensor] at htrace
  simp only [map_smul, smul_apply, smul_eq_mul] at htrace
  change 0 ≤ deriv (fun s => F.S.scalar s (gamma t)) t +
    (F.S.base.metric t).inner (gamma t)
      (gradientFun (I := I) (F.S.base.metric t) (F.S.scalar t) (gamma t)) v +
    (1 / 2 : ℝ) * ricciTensor (I := I) (F.S.base.metric t) (gamma t) v v
  linarith

theorem KLim.compensated_scalar_monotoneOn
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa a b : ℝ}
    (hK : KLim kappa F) (gamma : ℝ → F.M) {U : Set ℝ}
    (hU : IsOpen U) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U)
    (hab : a ≤ b) (hb : b ≤ 0) (hcurve : Icc a b ⊆ U) :
    MonotoneOn (fun t => F.S.scalar t (gamma t) +
      (1 / 2 : ℝ) * ∫ s in a..t, smoothCurveRicciEnergy F.S gamma (s, s))
      (Icc a b) := by
  classical
  let energy : ℝ → ℝ := fun s => smoothCurveRicciEnergy F.S gamma (s, s)
  have hcar : Icc a b ⊆ D.carrier := by
    intro t ht
    rw [hK.carrier_eq]
    exact ht.2.trans hb
  have he : ContinuousOn energy (Icc a b) :=
    klimit_curve_energy_continuousOn (F := F) gamma hU hgamma hcar hcurve
  have hs : ContinuousOn (fun t => F.S.scalar t (gamma t)) (Icc a b) :=
    klimit_curve_scalar_continuousOn (F := F) gamma hgamma hcar hcurve
  apply local_curve_compensated_monotone hab hs he
    (derivative := fun t => deriv (fun s => F.S.scalar s (gamma t)) t +
      (F.S.base.metric t).inner (gamma t)
        (gradientFun (I := I) (F.S.base.metric t) (F.S.scalar t) (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)))
  · intro t ht
    exact klimit_curve_scalar_hasDerivAt hK gamma hU hgamma
      (ht.2.trans_le hb) (hcurve ⟨ht.1.le, ht.2.le⟩)
  · intro t ht
    exact klimit_curve_harnack_nonnegative hK gamma (ht.2.trans_le hb)

theorem KLim.scalar_le_add_curve_ricci_integral
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa a b : ℝ}
    (hK : KLim kappa F) (gamma : ℝ → F.M) {U : Set ℝ}
    (hU : IsOpen U) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma U)
    (hab : a ≤ b) (hb : b ≤ 0) (hcurve : Icc a b ⊆ U) :
    F.S.scalar a (gamma a) ≤ F.S.scalar b (gamma b) +
      (1 / 2 : ℝ) * ∫ s in a..b, smoothCurveRicciEnergy F.S gamma (s, s) := by
  have h := hK.compensated_scalar_monotoneOn gamma hU hgamma hab hb hcurve
    ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simpa only [intervalIntegral.integral_same, mul_zero, add_zero] using h

end PointedFlow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
