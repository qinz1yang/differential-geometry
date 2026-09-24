import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedIntegratedHarnack
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Manifold ContDiff _root_.Topology Interval

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance traceLimitTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance traceLimitCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance traceLimitSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance traceLimitC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance traceLimitT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

private local instance traceLimitSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

theorem pointed_limit_traceHarnack_along_curve
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hconvergence : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    (gamma : ℝ → L.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {tau : ℝ} (htau : tau ≤ 0) :
    0 ≤ derivWithin (fun s => L.S.scalar s (gamma 0)) X.D.carrier tau +
      (L.S.base.metric tau).inner (gamma 0)
        (gradientFun (I := I) (L.S.base.metric tau) (L.S.scalar tau) (gamma 0))
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ)) +
      (1 / 2 : ℝ) * smoothCurveRicciEnergy L.S gamma (tau, 0) := by
  classical
  have hcar : Iic tau ⊆ X.D.carrier := by
    intro t ht
    rw [(hsource 0).carrier_eq]
    exact ht.trans htau
  have hspace :
      HasDerivAt (fun h => L.S.scalar tau (gamma h))
        ((L.S.base.metric tau).inner (gamma 0)
          (gradientFun (I := I) (L.S.base.metric tau) (L.S.scalar tau) (gamma 0))
          (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ))) 0 := by
    have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (L.S.scalar tau) (gamma 0) :=
      (metricScalar_smooth (I := I) (L.S.base.metric tau)).mdifferentiableAt (by simp)
    have hg := (hgamma.mdifferentiableAt (x := (0 : ℝ)) (by norm_num)).mdifferentiableWithinAt
      (s := (univ : Set ℝ))
    have h := hasDerivWithinAt_comp_mfderivWithin I (L.S.scalar tau) gamma univ 0 hf hg
    simp only [hasDerivWithinAt_univ, mfderivWithin_univ] at h
    exact h.congr_deriv
      (inner_gradientFun (I := I) (L.S.base.metric tau) (L.S.scalar tau) (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ))).symm
  have htime : HasDerivWithinAt (fun s => L.S.scalar s (gamma 0))
      (derivWithin (fun s => L.S.scalar s (gamma 0)) X.D.carrier tau) (Iic tau) tau :=
    (L.isSolution.scalarTime (K := X.D.carrier) (hcar (le_rfl : tau ≤ tau))
      subset_rfl (gamma 0)).hasDerivWithinAt.mono hcar
  have haverage := smoothCurveRicciEnergy_short_average_tendsto
    L.S L.isSolution gamma hgamma hcar
  apply terminal_harnack_of_endpoint_differences
    (spatial := fun h => L.S.scalar tau (gamma h))
    (temporal := fun s => L.S.scalar s (gamma 0))
    (energy := fun h => (∫ s in tau - h..tau,
      smoothCurveRicciEnergy L.S gamma (s, s - (tau - h))) / h)
    hspace htime haverage
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  let shift : ℝ → ℝ := fun s => s - (tau - h)
  have hshift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 shift :=
    contMDiff_id.sub contMDiff_const
  have hgammaShift : ContMDiff 𝓘(ℝ, ℝ) I 1 (gamma ∘ shift) :=
    hgamma.comp hshift
  have hint := pointed_limit_scalar_le_add_curve_ricci_integral
    Phi hsource hconvergence (gamma ∘ shift) hgammaShift
    (a := tau - h) (b := tau) (by linarith) htau
  have hvelocity (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) I (gamma ∘ shift) s (1 : ℝ) =
        mfderiv 𝓘(ℝ, ℝ) I gamma (s - (tau - h)) (1 : ℝ) := by
    rw [mfderiv_comp s (hgamma.mdifferentiableAt (x := shift s) (by norm_num))
      (hshift.mdifferentiableAt (x := s) (by norm_num))]
    change mfderiv 𝓘(ℝ, ℝ) I gamma (shift s)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) shift s (1 : ℝ)) = _
    simp only [shift, mfderiv_eq_fderiv, fderiv_sub_const]
    change mfderiv 𝓘(ℝ, ℝ) I gamma (s - (tau - h))
      ((fderiv ℝ (id : ℝ → ℝ) s) (1 : ℝ)) = _
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
  have henergy :
      (fun s => smoothCurveRicciEnergy L.S (gamma ∘ shift) (s, s)) =
        (fun s => smoothCurveRicciEnergy L.S gamma (s, s - (tau - h))) := by
    funext s
    unfold smoothCurveRicciEnergy
    rw [hvelocity]
    rfl
  rw [henergy] at hint
  simp only [Function.comp_apply, shift, sub_self, sub_sub_cancel] at hint
  have hmul : h * ((∫ s in tau - h..tau,
      smoothCurveRicciEnergy L.S gamma (s, s - (tau - h))) / h) =
      ∫ s in tau - h..tau, smoothCurveRicciEnergy L.S gamma (s, s - (tau - h)) := by
    field_simp [ne_of_gt hh]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pointed_limit_traceHarnack
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hconvergence : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    {tau : ℝ} (htau : tau ∈ X.D.carrier)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) tau))
    (x : L.M) (V : TangentSpace I x) :
    0 ≤ derivWithin (fun s => L.S.scalar s x) X.D.carrier tau +
      2 * (L.S.base.metric tau).inner x
        (gradientAt (I := I) (flowG (I := I) L.S) tau (L.S.scalar tau) x) V +
      2 * metricRicci (I := I) (L.S.base.metric tau) x (vec2 V V) := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hdim := (hsource 0).dimension_ge_two
    omega⟩
  let g := L.S.base.metric tau
  have hg : RiemannianMetricComplete (I := I) g :=
    ⟨MetricComplete.complete (I := I) (L.atTime (I := I) tau) hcomplete⟩
  let _ : TopologicalSpace.MetrizableSpace L.M := Manifold.metrizableSpace I L.M
  let _ : T3Space L.M := inferInstance
  let _ : RiemannianBundle (fun q : L.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun q : L.M => TangentSpace I q) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace L.M := EMetricSpace.ofRiemannianMetric I L.M
  let _ : CompleteSpace L.M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := L.M) g := fun q v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g q v
  let gamma : ℝ → L.M := intrinsicGeodesic (I := I) g hEnorm x ((2 : ℝ) • V)
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma :=
    contMDiffOn_univ.mp (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x ((2 : ℝ) • V))
  have hgamma0 : gamma 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x ((2 : ℝ) • V)
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) = (2 : ℝ) • (V : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x ((2 : ℝ) • V)
  have htau0 : tau ≤ 0 := by simpa only [(hsource 0).carrier_eq, mem_Iic] using htau
  have h := pointed_limit_traceHarnack_along_curve Phi hsource hconvergence gamma hgamma htau0
  change 0 ≤ derivWithin (fun s => L.S.scalar s (gamma 0)) X.D.carrier tau +
    g.inner (gamma 0) (gradientFun (I := I) g (L.S.scalar tau) (gamma 0))
      (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) +
    (1 / 2 : ℝ) * ricciTensor (I := I) g (gamma 0)
      (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E)
      (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) at h
  rw [hvelocity, hgamma0] at h
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  change 0 ≤ derivWithin (fun s => L.S.scalar s x) X.D.carrier tau +
    2 * g.inner x (gradientFun (I := I) g (L.S.scalar tau) x) V +
    2 * metricRicciAt (I := I) g x (vec2 V V)
  rw [metricRicciAt_apply_eq_ricciTensor]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
