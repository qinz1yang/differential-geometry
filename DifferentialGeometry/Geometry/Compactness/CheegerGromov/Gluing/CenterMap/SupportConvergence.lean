import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.SupportSelection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

private noncomputable local instance supportConvergenceModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance supportConvergenceModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance supportConvergenceModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance supportConvergenceModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def HasCompactCover {Y J : Type*} [TopologicalSpace Y]
    (sourceBall : Set Y) (sourcePatch : J → Set Y) : Prop :=
  ∃ K : J → Set Y, (∀ j, IsCompact (K j)) ∧
    (∀ j, K j ⊆ sourcePatch j) ∧ sourceBall = ⋃ j, K j

def HasSuppConvData
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E) : Prop :=
  let Lphi := L.subseq hphi
  (∀ alpha, IsOpen (U alpha)) ∧
  (∀ alpha, U alpha ⊆
    Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
  (∀ alpha, IsCompact (C0 alpha)) ∧
  (∀ alpha, IsCompact (C1 alpha)) ∧
  (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
  (∀ alpha, C1 alpha ⊆ U alpha) ∧
  (∀ alpha, Convex Real (C0 alpha)) ∧
  (∀ alpha, (0 : E) ∈ C0 alpha) ∧
  (∃ eta : LiveSlot L inp.pack r → Real,
    (∀ alpha, 0 < eta alpha) ∧
    ∀ k,
      let Y := X.obj (L.φ (phi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
      ∀ y ∈ L.hatSourceBall inp.decay P r (phi k),
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    L.hatSourceBall inp.decay P r (phi k) ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) ''
            interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    (∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0
          (inp.normalBounds.radius (L.φ (phi k))
            (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      U alpha ⊆ Metric.ball 0
          ((c2RadiusNormalChartFamily (I := I) X).radius (L.φ (phi k))
            (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      Set.MapsTo
        ((c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
        (U alpha)
        (L.hatBall inp.decay inp.D P inp.pack r (phi k) alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma)) ∧
    L.hatSourceBall inp.decay P r (phi k) ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) '' U alpha) ∧
  (∀ alpha,
    HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
      (U alpha) (aInf alpha)) ∧
  (∀ alpha,
    centerAverage.WeightDataOn (U alpha)
      (fun _ : Fin (inp.pack.A r) => Set.univ)
      (fun z gamma =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma)) ∧
  (∀ alpha target,
    ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    ContinuousOn (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContinuousOn (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => (c2RadiusNormalChartFamily (I := I) X).transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Jinf alpha target) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => (c2RadiusNormalChartFamily (I := I) X).transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
      (Jbarinf alpha target) ∧
    (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      Jinf alpha target z ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
        Jbarinf alpha target (Jinf alpha target z) = z) ∧
    ∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbarinf alpha target w ∈
          Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
        Jinf alpha target (Jbarinf alpha target w) = w) ∧
  ∀ (alpha : LiveSlot L inp.pack r)
      (target : InterSlot L inp.pack r alpha) (k : Nat),
    ContDiffOn Real (⊤ : ℕ∞)
      ((c2RadiusNormalChartFamily (I := I) X).transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞)
      ((c2RadiusNormalChartFamily (I := I) X).transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))

theorem HasSuppConvData.weight_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf : E → Fin (inp.pack.A r) → Real := fun z gamma =>
      rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
    ContDiffOn Real (∞ : WithTop ℕ∞) weightInf (U alpha) ∧
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ) weightInf := by
  dsimp only
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      hlim, hweight, _htrans, _hsmooth⟩
  have hlim0 := hlim alpha
  dsimp only [HasAtomWeightLim] at hlim0
  rcases hlim0 with
    ⟨_hdead, _hatomC, _hatomInfC, _hatomConv, _hweightC,
      hweightInfC, _hweightConv⟩
  exact ⟨hweightInfC, hweight alpha⟩

theorem HasSuppConvData.core_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    IsOpen (U alpha) ∧ IsCompact (C0 alpha) ∧ IsCompact (C1 alpha) ∧
      C0 alpha ⊆ interior (C1 alpha) ∧ C1 alpha ⊆ U alpha := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨hU, _hU8, hC0, hC1, hC01, hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact ⟨hU alpha, hC0 alpha, hC1 alpha, hC01 alpha, hC1U alpha⟩

theorem HasSuppConvData.core_shape
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    Convex Real (C0 alpha) ∧ (0 : E) ∈ C0 alpha := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, hconvex, hzero,
      _hbuffer, _hcore, _hcover, _hlim, _hweight, _htrans, _hsmooth⟩
  exact ⟨hconvex alpha, hzero alpha⟩

theorem HasSuppConvData.buffer_cover
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    let Lphi := L.subseq hphi
    ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            expMapDiffeo (I := I) Y.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z = y ∧
              Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      hbuffer, _hcore, _hcover, _hlim, _hweight, _htrans, _hsmooth⟩
  exact hbuffer

theorem HasSuppConvData.source_cover
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (k : Nat) :
    let Lphi := L.subseq hphi
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
            interior (C0 alpha) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, hcore, _hcover,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact hcore k

theorem HasSuppConvData.geom_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (k : Nat) (alpha : LiveSlot L inp.pack r) :
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    U alpha ⊆ Metric.ball 0
        (inp.normalBounds.radius (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      U alpha ⊆ Metric.ball 0
        ((c2RadiusNormalChartFamily (I := I) X).radius (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      Set.MapsTo
        ((c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
        (U alpha)
        (L.hatBall inp.decay inp.D P inp.pack r (phi k) alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact (hgeom k).1 alpha

theorem HasSuppConvData.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasSuppConvData (I := I) inp P L r hr (phi ∘ ψ) (hphi.comp hψ)
      U C0 C1 aInf Jinf Jbarinf := by
  dsimp only [HasSuppConvData] at h ⊢
  rcases h with
    ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero,
      hbuffer, hcore, hcover, hweight,
      hweightData, htrans, hsmooth⟩
  refine ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero, ?_, ?_, ?_, ?_,
    hweightData, ?_, ?_⟩
  · rcases hbuffer with ⟨eta, heta, hbuf⟩
    refine ⟨eta, heta, ?_⟩
    intro k
    simpa only [Function.comp_apply] using hbuf (ψ k)
  · intro k
    simpa only [Function.comp_apply] using hcore (ψ k)
  · intro k
    simpa only [Function.comp_apply] using hcover (ψ k)
  · intro alpha
    have hsub := (hweight alpha).subseq hψ
    change HasAtomWeightLim (I := I) inp.decay inp.hD P
      ((L.subseq hphi).subseq hψ) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P L (phi (ψ k)) (alpha.1 : Nat))
      (U alpha) (aInf alpha)
    exact hsub
  · intro alpha target
    rcases htrans alpha target with
      ⟨hJ, hJbar, hJcont, hJbarcont, hJconv, hJbarconv, hleft, hright⟩
    refine ⟨hJ, hJbar, hJcont, hJbarcont, ?_, ?_, hleft, hright⟩
    · have hsub := hJconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [Function.comp_apply] using hsub
    · have hsub := hJbarconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [Function.comp_apply] using hsub
  · intro alpha target k
    simpa only [Function.comp_apply] using hsmooth alpha target (ψ k)

theorem MetricCompactnessInputs.exists_supp_pts_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.metricCoerciveRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
        aInf Jinf Jbarinf ∧
      ∀ᶠ n in Filter.atTop,
        let Y := X.obj (Lphi.φ n)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : SigmaCompactSpace Y.M := Y.sigmaCompact
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
        letI : TopologicalSpace.MetrizableSpace Y.M :=
          Manifold.metrizableSpace I Y.M
        letI : T3Space Y.M := inferInstance
        letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.toRiemannianMetric⟩
        letI : IsContinuousRiemannianBundle E
            (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
        letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        let chi := fun (alpha : LiveSlot L inp.pack r) =>
          NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
        let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
          Lphi.hatSourceBall inp.decay P r n ∩
            (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
        let localWeight := fun (alpha : LiveSlot L inp.pack r)
            (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
          weightInf alpha (chi alpha x) gamma
        let pairPts : (alpha : LiveSlot L inp.pack r) →
            InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
          fun alpha target a b x =>
            (chi alpha).symm
              (normalTransition (I := I) (X.obj (Lphi.φ b))
                (beta b target.1) (beta b alpha)
                (normalTransition (I := I) (X.obj (Lphi.φ a))
                  (beta a alpha) (beta a target.1) (chi alpha x)))
        let pts := fun (alpha : LiveSlot L inp.pack r) =>
          totalPts (X := X) pairPts alpha
        HasCompactCover (Lphi.hatSourceBall inp.decay P r n) sourcePatch ∧
          Lphi.hatSourceBall inp.decay P r n ⊆
            ⋃ alpha : LiveSlot L inp.pack r, sourcePatch alpha ∧
          (∀ alpha,
            sourcePatch alpha ⊆
              Lphi.hatBall inp.decay inp.D P inp.pack r n alpha.1) ∧
          (∀ alpha,
            centerAverage.WeightDataOn (sourcePatch alpha)
              (fun _ : Fin (inp.pack.A r) => Set.univ)
              (localWeight alpha)) ∧
          ∀ alpha gamma epsilon, 0 < epsilon →
            ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
              ∀ x ∈ sourcePatch alpha,
                localWeight alpha x gamma ≠ 0 →
                  dist x (pts alpha a b x gamma) < epsilon := by
  classical
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
      hbuffer, hcore, hgeom, hlim, htrans, hstage,
      hsupp⟩ :=
    inp.exists_atom_supp_fin h8 hradRatio P L hstable r hr
  obtain ⟨hgp0, _hrad⟩ := inp.exponential_scale_tails h8 hradRatio P L r
  have hgpPhi : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P
      (L.subseq hphi) inp.pack r :=
    hgp0.subseq inp.decay inp.D P L inp.pack r hphi
  have hweightData : ∀ alpha : LiveSlot L inp.pack r,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (fun z gamma =>
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma) := by
    intro alpha
    have hcoverU : ∀ᶠ k in Filter.atTop,
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj ((L.subseq hphi).φ k)).M) :=
          (X.obj ((L.subseq hphi).φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I)
            (X.obj ((L.subseq hphi).φ k)).metric
            (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat)) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r k gamma) :=
      Filter.Eventually.of_forall fun k z hz => ((hgeom k).1 alpha).2.2 hz |>.2
    exact (hlim alpha).weight_data_of_innerCover hcoverU
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨⟨hUopen, hU8, hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
    hbuffer, hcore, ?_, hlim, hweightData, htrans, hstage⟩, ?_⟩
  · intro k
    have hgeomK := hgeom k
    simp only [NormalChartFamily.hom, NormalChartFamily.radius, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_apply, c2_radius_normal_ball_chart_radius] at ⊢
    convert hgeomK using 1
    all_goals
      simp only [NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.hatBall_subseq, NetLimitData.innerBall_subseq,
        NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  have hcenters : ∀ᶠ n in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      seqCenter inp.decay inp.D P ((L.subseq hphi).φ n) (alpha.1 : Nat) =
        some (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
    Filter.eventually_all.mpr fun alpha =>
      seqCenterD_live inp.decay P (L.subseq hphi) (alpha.1 : Nat) (by
        simpa only [NetLimitData.subseq] using alpha.2)
  filter_upwards [hgpPhi, hcenters] with n hgpN hcenterN
  let Y := X.obj ((L.subseq hphi).φ n)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : ConnectedSpace Y.M := hconn ((L.subseq hphi).φ n)
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  have hcover : (L.subseq hphi).hatSourceBall inp.decay P r n ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (L.subseq hphi).hatSourceBall inp.decay P r n ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))).source ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) ⁻¹' U alpha := by
    intro x hx
    rcases Set.mem_iUnion.mp ((hgeom n).2 hx) with ⟨alpha, z, hzU, rfl⟩
    refine Set.mem_iUnion.mpr ⟨alpha, ⟨hx, ?_⟩, ?_⟩
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hxtarget :=
        (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).map_source hzsrc
      simpa only [normalChartAt_source_eq] using hxtarget
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hchart :
          NormalCoordinates.normalChartAt (I := I)
              (X.obj ((L.subseq hphi).φ n)).metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
              (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
                (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) = z := by
        change (expMapDiffeo (I := I)
            (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).symm
          ((expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))) z) = z
        exact (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).left_inv hzsrc
      change NormalCoordinates.normalChartAt (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) ∈ U alpha
      rw [hchart]
      exact hzU
  refine ⟨?_, hcover, ?_, ?_, ?_⟩
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourceBall := (L.subseq hphi).hatSourceBall inp.decay P r n
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let patchOpen : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    change HasCompactCover sourceBall sourcePatch
    have hopen : ∀ alpha, IsOpen (patchOpen alpha) := fun alpha =>
      (chi alpha).toOpenPartialHomeomorph.isOpen_inter_preimage (hUopen alpha)
    have hcoverOpen : sourceBall ⊆ ⋃ alpha, patchOpen alpha := by
      intro x hx
      rcases Set.mem_iUnion.mp (hcover hx) with ⟨alpha, hxalpha⟩
      exact Set.mem_iUnion.mpr ⟨alpha, ⟨hxalpha.1.2, hxalpha.2⟩⟩
    obtain ⟨K, hKcompact, hKsub, hKeq⟩ :=
      ((L.subseq hphi).hatSourceCompact inp.decay P r n).finite_compact_cover
        Finset.univ patchOpen (fun alpha _ => hopen alpha)
          (by simpa only [Finset.mem_univ, iUnion_true] using hcoverOpen)
    refine ⟨K, hKcompact, ?_, ?_⟩
    · intro alpha x hxK
      have hxSource : x ∈ sourceBall := by
        change x ∈ (L.subseq hphi).hatSourceBall inp.decay P r n
        rw [hKeq]
        exact Set.mem_iUnion.mpr ⟨alpha,
          Set.mem_iUnion.mpr ⟨Finset.mem_univ alpha, hxK⟩⟩
      have hxOpen : x ∈ patchOpen alpha := hKsub alpha hxK
      exact ⟨⟨hxSource, hxOpen.1⟩, hxOpen.2⟩
    · simpa only [Finset.mem_univ, iUnion_true] using hKeq
  · intro alpha x hx
    have hmap := ((hgeom n).1 alpha).2.2 hx.2
    have hexp : expMapDiffeo (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (NormalCoordinates.normalChartAt (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) = x := by
      change (expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        ((expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).symm x) = x
      exact (expMapDiffeo (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).right_inv
          (by simpa only [normalChartAt_source_eq] using hx.1.2)
    change expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) ∈
        (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
      at hmap
    rw [hexp] at hmap
    exact hmap.1
  · intro alpha
    simpa only [Set.preimage_univ] using
      (hweightData alpha).comp (fun _ hx => hx.2)
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (L.subseq hphi).hatSourceBall inp.decay P r n ∩
        (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let localWeight := fun (alpha : LiveSlot L inp.pack r) (x : Y.M)
        (gamma : Fin (inp.pack.A r)) =>
      rawWeights
        (cutRaw
          (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
          (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
        (chi alpha x) gamma
    let pairPts : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
      fun alpha target a b x =>
        (chi alpha).symm
          (normalTransition (I := I) (X.obj ((L.subseq hphi).φ b))
            (seqCenterD inp.decay P (L.subseq hphi) b
              (target.1.1 : Nat))
            (seqCenterD inp.decay P (L.subseq hphi) b (alpha.1 : Nat))
            (normalTransition (I := I) (X.obj ((L.subseq hphi).φ a))
              (seqCenterD inp.decay P (L.subseq hphi) a (alpha.1 : Nat))
              (seqCenterD inp.decay P (L.subseq hphi) a
                (target.1.1 : Nat))
              (chi alpha x)))
    let pts := fun (alpha : LiveSlot L inp.pack r) =>
      totalPts (X := X) pairPts alpha
    change ∀ alpha gamma epsilon, 0 < epsilon →
      ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ sourcePatch alpha,
        localWeight alpha x gamma ≠ 0 →
          dist x (pts alpha a b x gamma) < epsilon
    have hpair (alpha : LiveSlot L inp.pack r) :
        ∀ target : InterSlot L inp.pack r alpha, ∀ epsilon : Real,
          0 < epsilon → ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
            ∀ x ∈ sourcePatch alpha,
              localWeight alpha x target.1.1 ≠ 0 →
                dist x (pairPts alpha target a b x) < epsilon := by
      let centerAll : Fin (inp.pack.A r) → Y.M := fun gamma =>
        seqCenterD inp.decay P (L.subseq hphi) n (gamma : Nat)
      let pairWeight : Y.M → InterSlot L inp.pack r alpha → Real :=
        fun x target => localWeight alpha x target.1.1
      let centerPair : InterSlot L inp.pack r alpha → Y.M := fun _ =>
        seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)
      let sourceCage : InterSlot L inp.pack r alpha → Set Y.M := fun _ =>
        (L.subseq hphi).hatSourceCage inp.decay P inp.pack r n alpha.1
      let U8 : InterSlot L inp.pack r alpha → Set E := fun _ =>
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))
      let V6 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat))
      let V8 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
      let B : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
      let A : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
      have hCageCompact : ∀ target : InterSlot L inp.pack r alpha,
          IsCompact (sourceCage target) := by
        intro target
        simpa only [sourceCage] using
          NetLimitData.hatCageCompact (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n alpha.1
      have hSuppCage : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            x ∈ sourceCage target := by
        intro target x hx _hne
        have hmap := ((hgeom n).1 alpha).2.2 hx.2
        have hexp : expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) = x := by
          change (expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
            ((expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).symm x) = x
          exact (expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).right_inv
              (by simpa only [chi, normalChartAt_source_eq] using hx.1.2)
        change expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) ∈
          (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
          at hmap
        rw [hexp] at hmap
        exact NetLimitData.hatCageSub (I := I) (X := X) inp.decay P
          (L.subseq hphi) inp.pack r n alpha.1 ⟨hx.1.1, hmap.1⟩
      have hR : 4 * L.lamInf (alpha.1 : Nat) <
          metricCoerciveExpRadius (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
        hgpN alpha.1 _ (hcenterN alpha)
      have hsrc : ∀ target : InterSlot L inp.pack r alpha,
          sourceCage target ⊆ (chi alpha).source := by
        intro target
        simpa only [sourceCage, chi, centerAll] using
          NetLimitData.hatCageSrcOfRad (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n centerAll alpha.1
            (hcenterN alpha) hR
      have hBcont : ∀ target : InterSlot L inp.pack r alpha,
          ContinuousOn (Jinf alpha target) (U8 target) := by
        intro target
        simpa only [U8] using (htrans alpha target).2.2.1
      have hsigma : 4 * L.lamInf (alpha.1 : Nat) /
            Real.sqrt (metricCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) <
          8 * L.lamInf (alpha.1 : Nat) := by
        have hhalf : (1 / 2 : Real) ≤ metricCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
          inp.normalBounds.half_le_metricCoerciveConst ((L.subseq hphi).φ n)
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        have hsqrtHalf : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
          have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
          have hn := Real.sqrt_nonneg (1 / 2 : Real)
          nlinarith
        have hsqrt : (1 / 2 : Real) < Real.sqrt
            (metricCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) :=
          hsqrtHalf.trans_le (Real.sqrt_le_sqrt hhalf)
        have hsc : 0 < Real.sqrt (metricCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) :=
          Real.sqrt_pos.mpr (metricCoerciveConst_pos (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
        apply (div_lt_iff₀ hsc).2
        have hfour : (4 : Real) < 8 * Real.sqrt
            (metricCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) := by
          nlinarith
        calc
          4 * L.lamInf (alpha.1 : Nat) <
              (8 * Real.sqrt (metricCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat)))) * L.lamInf (alpha.1 : Nat) :=
            mul_lt_mul_of_pos_right hfour hlam
          _ = (8 * L.lamInf (alpha.1 : Nat)) *
              Real.sqrt (metricCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat))) := by ring
      have hKU : ∀ target : InterSlot L inp.pack r alpha,
          (chi alpha) '' sourceCage target ⊆ U8 target := by
        intro target
        simpa only [chi, sourceCage, U8, centerAll] using
          hatCageImg' (I := I) (X := X) inp.decay P (L.subseq hphi)
            inp.pack r n centerAll alpha.1
            (fun gamma => 8 * L.lamInf (gamma : Nat))
            (hcenterN alpha) hR hsigma
      have hSuppV : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            Jinf alpha target (chi alpha x) ∈ V6 target := by
        intro target x hx hne
        obtain ⟨target', hslot, hmem⟩ :=
          hsupp alpha (chi alpha x) hx.2 target.1.1 (by
            simpa only [pairWeight] using hne)
        have htarget : target' = target := by
          apply Subtype.ext
          apply Subtype.ext
          exact hslot
        simpa only [V6, htarget] using hmem
      obtain ⟨sourceK, hK, hSuppK, hsrcK, hKU_K, hKV6⟩ :=
        NetLimitData.hatSuppCageData (I := I) (X := X) inp.decay P
          (L.subseq hphi) n (s := sourcePatch alpha)
          pairWeight centerPair sourceCage U8 V6 (Jinf alpha)
          hCageCompact hSuppCage (by
            intro target
            simpa only [centerPair] using hsrc target)
          hBcont (by
            intro target
            simpa only [centerPair] using hKU target)
          (fun _ => Metric.isClosed_closedBall) (by
            intro target x hx hne
            simpa only [centerPair] using hSuppV target x hx hne)
      have hKV8 : ∀ target : InterSlot L inp.pack r alpha, ∀ v : E,
          v ∈ (chi alpha) '' sourceK target →
            Jinf alpha target v ∈ V8 target := by
        intro target v hv
        have hv6 := hKV6 target v (by
          simpa only [centerPair] using hv)
        change Jinf alpha target v ∈ Metric.closedBall 0
          (6 * L.lamInf (target.1.1 : Nat)) at hv6
        rw [Metric.mem_closedBall, dist_zero_right] at hv6
        change Jinf alpha target v ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
        rw [Metric.mem_ball, dist_zero_right]
        have hlam : 0 < L.lamInf (target.1.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat))
        nlinarith
      have hpoints := NetLimitData.hatSuppPtsOfComp (I := I) (X := X)
        inp.decay P (L.subseq hphi) n (s := sourcePatch alpha)
        pairWeight centerPair sourceK U8 V8 B (Jinf alpha) A (Jbarinf alpha)
        (hconn ((L.subseq hphi).φ n)) hK hSuppK hsrcK
        (fun _ => Metric.isOpen_ball)
        (fun target => by simpa only [B, U8] using
          (htrans alpha target).2.2.2.2.1)
        (fun target => by simpa only [A, V8] using
          (htrans alpha target).2.2.2.2.2.1)
        hBcont
        (fun target => by simpa only [V8] using
          (htrans alpha target).2.2.2.1)
        (fun target => by simpa only [U8, V8] using
          (htrans alpha target).2.2.2.2.2.2.1)
        hKU_K (by
          intro target v hv
          simpa only [centerPair] using hKV8 target v (by
            simpa only [centerPair] using hv))
      intro target epsilon hepsilon
      simpa only [pairWeight, centerPair, B, A, pairPts, chi] using
        hpoints target epsilon hepsilon
    intro alpha gamma epsilon hepsilon
    by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma
    · let target := Classical.choose htarget
      have hslot : target.1.1 = gamma := Classical.choose_spec htarget
      obtain ⟨N, hN⟩ := hpair alpha target epsilon hepsilon
      refine ⟨N, ?_⟩
      intro a ha b hb x hx hne
      have hp := hN a ha b hb x hx (by simpa only [hslot] using hne)
      have hlookup : interSlot? alpha gamma = some target := by
        unfold interSlot?
        split
        next h =>
          congr 1
        next h =>
          exact (h htarget).elim
      simpa only [pts, totalPts, hlookup] using hp
    · refine ⟨0, ?_⟩
      intro a _ha b _hb x hx hne
      exfalso
      obtain ⟨target, hslot, _hmem⟩ := hsupp alpha (chi alpha x) hx.2 gamma hne
      exact htarget ⟨target, hslot⟩

def HasSuppConvDataOn
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E) : Prop :=
  let Lphi := L.subseq hphi
  (∀ alpha, IsOpen (U alpha)) ∧
  (∀ alpha, U alpha ⊆
    Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
  (∀ alpha, IsCompact (C0 alpha)) ∧
  (∀ alpha, IsCompact (C1 alpha)) ∧
  (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
  (∀ alpha, C1 alpha ⊆ U alpha) ∧
  (∀ alpha, Convex Real (C0 alpha)) ∧
  (∀ alpha, (0 : E) ∈ C0 alpha) ∧
  (∃ eta : LiveSlot L inp.pack r → Real,
    (∀ alpha, 0 < eta alpha) ∧
    ∀ k,
      let Y := X.obj (L.φ (phi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
      ∀ y ∈ L.hatSourceBall inp.decay P r (phi k),
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          chart.hom (L.φ (phi k))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    L.hatSourceBall inp.decay P r (phi k) ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        chart.hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) ''
            interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    (∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0
          (chart.radius (L.φ (phi k))
            (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      Set.MapsTo
        (chart.hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
        (U alpha)
        (L.hatBall inp.decay inp.D P inp.pack r (phi k) alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma)) ∧
    L.hatSourceBall inp.decay P r (phi k) ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        chart.hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) '' U alpha) ∧
  (∀ alpha,
    HasAtomWeightLimOn (I := I) chart
      inp.decay inp.hD P Lphi inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
      (U alpha) (aInf alpha)) ∧
  (∀ alpha,
    centerAverage.WeightDataOn (U alpha)
      (fun _ : Fin (inp.pack.A r) => Set.univ)
      (fun z gamma =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma)) ∧
  (∀ alpha target,
    ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    ContinuousOn (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContinuousOn (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k =>
        chart.transition (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Jinf alpha target) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k =>
        chart.transition (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
      (Jbarinf alpha target) ∧
    (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      Jinf alpha target z ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
        Jbarinf alpha target (Jinf alpha target z) = z) ∧
    ∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbarinf alpha target w ∈
          Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
        Jinf alpha target (Jbarinf alpha target w) = w) ∧
  ∀ (alpha : LiveSlot L inp.pack r)
      (target : InterSlot L inp.pack r alpha) (k : Nat),
    ContDiffOn Real (⊤ : ℕ∞)
      (chart.transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞)
      (chart.transition (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))

theorem HasSuppConvData.to_on_c2_radius_normal_chart_family
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    HasSuppConvDataOn (I := I) inp P L r hr phi hphi
      (c2RadiusNormalChartFamily (I := I) X) U C0 C1 aInf Jinf Jbarinf := by
  dsimp only [HasSuppConvData] at h
  dsimp only [HasSuppConvDataOn, MetricCompactnessInputs.toCore]
  rcases h with
    ⟨hUopen, hUball, hC0, hC1, hC01, hC1U, hconv, hzero,
      heta, hcover, hsource, hatom, hweight, htrans, hsmooth⟩
  refine ⟨hUopen, hUball, hC0, hC1, hC01, hC1U, hconv, hzero,
    ?_, ?_, ?_, ?_, hweight, ?_, ?_⟩
  · rcases heta with ⟨eta, hetaPos, heta⟩
    refine ⟨eta, hetaPos, ?_⟩
    intro k
    let Y := X.obj ((L.subseq hphi).φ k)
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : T2Space Y.M := Y.t2
    let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let : MetricSpace Y.M := (P ((L.subseq hphi).φ k)).ms
    simpa only [NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply,
      NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NetLimitData.hatSourceBall_subseq] using heta k
  · intro k
    let Y := X.obj ((L.subseq hphi).φ k)
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : T2Space Y.M := Y.t2
    let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let : MetricSpace Y.M := (P ((L.subseq hphi).φ k)).ms
    simpa only [NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply,
      NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NetLimitData.hatSourceBall_subseq] using hcover k
  · intro k
    let Y := X.obj ((L.subseq hphi).φ k)
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : T2Space Y.M := Y.t2
    let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let : MetricSpace Y.M := (P ((L.subseq hphi).φ k)).ms
    rcases hsource k with ⟨hsource, hcoverU⟩
    refine ⟨?_, ?_⟩
    · intro alpha
      rcases hsource alpha with ⟨_hmetric, hradius, hmaps⟩
      exact ⟨by
        simpa only [NormalChartFamily.radius, c2RadiusNormalChartFamily,
          c2_radius_normal_ball_chart_radius, NetLimitData.subseq_phi, Function.comp_apply,
          seqCenterD_subseq] using hradius,
        by
          intro z hz
          simpa only [NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply,
            NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
            NetLimitData.hatBall_subseq, NetLimitData.innerBall_subseq] using hmaps hz⟩
    · simpa only [NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply,
        NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.hatSourceBall_subseq] using hcoverU
  · intro alpha
    exact hatom alpha
  · intro alpha target
    rcases htrans alpha target with
      ⟨hJ, hJbar, hJcont, hJbarCont, hJlim, hJbarLim, hleft, hright⟩
    refine ⟨hJ, hJbar, hJcont, hJbarCont, ?_, ?_, hleft, hright⟩
    · simpa only [NormalChartFamily.transition, c2RadiusNormalChartFamily,
        c2_radius_normal_ball_chart_transition, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using hJlim
    · simpa only [NormalChartFamily.transition, c2RadiusNormalChartFamily,
        c2_radius_normal_ball_chart_transition, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using hJbarLim
  · intro alpha target k
    let Y := X.obj ((L.subseq hphi).φ k)
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    simpa only [NormalChartFamily.transition, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_transition, NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq] using hsmooth alpha target k

omit [CompleteSpace E] in
theorem HasSuppConvDataOn.weight_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (chart : NormalChartFamily (I := I) X)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf : E → Fin (inp.pack.A r) → Real := fun z gamma =>
      rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
    ContDiffOn Real (∞ : WithTop ℕ∞) weightInf (U alpha) ∧
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ) weightInf := by
  dsimp only
  dsimp only [HasSuppConvDataOn] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      hlim, hweight, _htrans, _hsmooth⟩
  have hlim0 := hlim alpha
  dsimp only [HasAtomWeightLimOn] at hlim0
  rcases hlim0 with
    ⟨_hdead, _hatomC, _hatomInfC, _hatomConv, _hweightC,
      hweightInfC, _hweightConv⟩
  exact ⟨hweightInfC, hweight alpha⟩

omit [CompleteSpace E] in
theorem HasSuppConvDataOn.core_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (chart : NormalChartFamily (I := I) X)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    IsOpen (U alpha) ∧ IsCompact (C0 alpha) ∧ IsCompact (C1 alpha) ∧
      C0 alpha ⊆ interior (C1 alpha) ∧ C1 alpha ⊆ U alpha := by
  dsimp only [HasSuppConvDataOn] at h
  rcases h with
    ⟨hU, _hU8, hC0, hC1, hC01, hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact ⟨hU alpha, hC0 alpha, hC1 alpha, hC01 alpha, hC1U alpha⟩

omit [CompleteSpace E] in
theorem HasSuppConvDataOn.geom_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (chart : NormalChartFamily (I := I) X)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (k : Nat) (alpha : LiveSlot L inp.pack r) :
    let Y := X.obj (L.φ (phi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
    U alpha ⊆ Metric.ball 0
        (chart.radius (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))) ∧
      Set.MapsTo
        (chart.hom (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
        (U alpha)
        (L.hatBall inp.decay inp.D P inp.pack r (phi k) alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma) := by
  dsimp only [HasSuppConvDataOn] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact (hgeom k).1 alpha

omit [CompleteSpace E] in
theorem HasSuppConvDataOn.subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasSuppConvDataOn (I := I) inp P L r hr
      (phi ∘ ψ) (hphi.comp hψ) chart U C0 C1 aInf Jinf Jbarinf := by
  dsimp only [HasSuppConvDataOn] at h ⊢
  rcases h with
    ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero,
      hbuffer, hcore, hcover, hweight,
      hweightData, htrans, hsmooth⟩
  refine ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero, ?_, ?_, ?_, ?_,
    hweightData, ?_, ?_⟩
  · rcases hbuffer with ⟨eta, heta, hbuf⟩
    refine ⟨eta, heta, ?_⟩
    intro k
    simpa only [Function.comp_apply] using hbuf (ψ k)
  · intro k
    simpa only [Function.comp_apply] using hcore (ψ k)
  · intro k
    simpa only [Function.comp_apply] using hcover (ψ k)
  · intro alpha
    have hsub := (hweight alpha).subseq hψ
    change HasAtomWeightLimOn (I := I) chart inp.decay inp.hD P
      ((L.subseq hphi).subseq hψ) inp.realizes inp.pack r hr
      (fun k => seqCenterD inp.decay P L (phi (ψ k))
        (alpha.1 : Nat)) (U alpha) (aInf alpha)
    exact hsub
  · intro alpha target
    rcases htrans alpha target with
      ⟨hJ, hJbar, hJcont, hJbarcont, hJconv, hJbarconv, hleft, hright⟩
    refine ⟨hJ, hJbar, hJcont, hJbarcont, ?_, ?_, hleft, hright⟩
    · have hsub := hJconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [Function.comp_apply] using hsub
    · have hsub := hJbarconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [Function.comp_apply] using hsub
  · intro alpha target k
    simpa only [Function.comp_apply] using hsmooth alpha target (ψ k)

end HCGCompactness
end DifferentialGeometry
