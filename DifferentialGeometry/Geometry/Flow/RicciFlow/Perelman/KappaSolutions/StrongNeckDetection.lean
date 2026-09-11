import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenTensorJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ComparisonTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedDomainEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle CanonicalNeighborhood
open CanonicalNeighborhood DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance strongDetectionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance strongDetectionC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

private def cylindricalJet {D : RealTimeInterval}
    {L : PointedFlowData.{u, 0, 0} (I := I3) D}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (U : TopologicalSpace.Opens SpatialNeckCylinder)
    (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2) :
    Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) 2 :=
  restrictOpen0S (I := SpatialNeckCylinderModel) 2 (V := U)
    (pullbackTensor02FieldCross e A)

private theorem cylindricalJet_apply {D : RealTimeInterval}
    {L : PointedFlowData.{u, 0, 0} (I := I3) D}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (U : TopologicalSpace.Opens SpatialNeckCylinder)
    (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2) (x : U)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    cylindricalJet (L := L) e U A x v = A (e x)
      (fun j => mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v j)) :=
  (restrictOpenTensor02Field_apply U (pullbackTensor02FieldCross e A) x v).trans
    (pullbackTensor02FieldCross_apply e A (x : SpatialNeckCylinder) v)

private theorem cylindricalJet_norm {D : RealTimeInterval}
    {L : PointedFlowData.{u, 0, 0} (I := I3) D}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (U : TopologicalSpace.Opens SpatialNeckCylinder)
    (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2)
    (gcov gnorm : SmoothRiemannianMetric I3 L.M) (a : ℕ) (x : U) :
    tensor02CovDerivNormWith a (cylindricalJet (L := L) e U A)
        ((DifferentialGeometry.Diffeomorph.pullbackMetricCross gcov e).restrictOpen U)
        ((DifferentialGeometry.Diffeomorph.pullbackMetricCross gnorm e).restrictOpen U) x =
      tensor02CovDerivNormWith a A gcov gnorm (e x) := by
  unfold cylindricalJet
  rw [tensor02CovDerivNormWith_restrictOpen0S,
    tensor02CovDerivNormWith_pullbackTensor02FieldCross]

private theorem cylindricalEmbedding_deriv
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (U : TopologicalSpace.Opens SpatialNeckCylinder) (i : ℕ)
    (hU : e '' (U : Set SpatialNeckCylinder) ⊆ (Phi.atTime (L := L) 0).source i)
    (x : U) (v : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel I3
        (pointedDomainEmbedding (Phi.atTime (L := L) 0) e U i hU) x v =
      mfderiv I3 I3 (Phi.map i) (e x)
        (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) v) := by
  have he := e.mdifferentiable (by decide) (x : SpatialNeckCylinder)
  have hval : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : U → SpatialNeckCylinder) x :=
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (U := U) (n := ∞)).mdifferentiable
      (by decide) x
  have hmap : MDifferentiableAt I3 I3 (Phi.map i) (e x) :=
    ((Phi.atTime (L := L) 0).partialDiffeomorph i).mdifferentiableAt
      (by decide) (hU ⟨x, x.property, rfl⟩)
  have hcomp := mfderiv_comp x hmap (he.comp x hval)
  rw [mfderiv_comp x he hval, mfderiv_subtype_val] at hcomp
  exact DFunLike.congr_fun hcomp v

private theorem cylindricalNormalizedMetric_inner
    {D : RealTimeInterval} (F : PointedFlowData.{u, 0, 0} (I := I3) D)
    (hscalar : F.S.scalar 0 F.basepoint = 1)
    {epsilon : ℝ} {f : C(spatialNeckBuffer epsilon, F.M)}
    (hf : IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (hQ : 0 < F.S.scalar 0 F.basepoint) (s : ℝ)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (strongNeckNormalizedMetric F.S F.basepoint 0 hQ hf s).inner x v w =
      (F.S.base.metric s).inner (f x) (mfderiv SpatialNeckCylinderModel I3 f x v)
        (mfderiv SpatialNeckCylinderModel I3 f x w) := by
  rw [strongNeckNormalizedMetric_inner, hscalar, zero_add, div_one, one_mul]

private theorem cylindricalComparison_jet_zero
    {D : RealTimeInterval} {F L : PointedFlowData.{u, 0, 0} (I := I3) D}
    {phi : L.M → F.M} {K : Set L.M} {epsilon eta : ℝ} {order : ℕ}
    (C : MetricComparisonOn L.S.base.metric F.S.base.metric phi K
      (Icc (-1 : ℝ) 0) order eta)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hscalar : F.S.scalar 0 F.basepoint = 1) (hQ : 0 < F.S.scalar 0 F.basepoint)
    (f : C(spatialNeckBuffer epsilon, F.M))
    (hf : IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (s : ℝ) (x : spatialNeckBuffer epsilon) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x)
    (hx : e (x : SpatialNeckCylinder) ∈ K) (hfmap : f x = phi (e (x : SpatialNeckCylinder)))
    (hd : ∀ w : TangentSpace SpatialNeckCylinderModel x,
      mfderiv SpatialNeckCylinderModel I3 f x w =
        mfderiv I3 I3 phi (e x) (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) w))
    (hmetric : strongNeckBackgroundMetric epsilon s =
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e).restrictOpen
        (spatialNeckBuffer epsilon)) :
    cylindricalJet (L := L) e (spatialNeckBuffer epsilon) (C.jet 0 s) x v =
      (strongNeckNormalizedMetric F.S F.basepoint 0 hQ hf s).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1) := by
  apply (cylindricalJet_apply (L := L) e (spatialNeckBuffer epsilon) (C.jet 0 s) x v).trans
  apply (C.jet_zero s (e x) _).trans
  rw [C.pullback_eq s (e x) hx]
  have hpair :
      ((mfderiv SpatialNeckCylinderModel I3 f x (v 0),
        mfderiv SpatialNeckCylinderModel I3 f x (v 1)) : ThreeSpace × ThreeSpace) =
      (mfderiv I3 I3 phi (e x) (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v 0)),
        mfderiv I3 I3 phi (e x) (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v 1))) :=
    Prod.ext (hd (v 0)) (hd (v 1))
  have hsource := (cylindricalNormalizedMetric_inner F hscalar hf hQ s x (v 0) (v 1)).trans
    (congrArg₂ (fun (y : F.M) (vw : ThreeSpace × ThreeSpace) =>
      (F.S.base.metric s).inner y vw.1 vw.2) hfmap hpair)
  have hreference := (congrArg (fun g : SmoothRiemannianMetric SpatialNeckCylinderModel
      (spatialNeckBuffer epsilon) => g.inner x (v 0) (v 1)) hmetric).trans
    ((SmoothRiemannianMetric.restrictOpen_inner
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e)
      (spatialNeckBuffer epsilon) x (v 0) (v 1)).trans
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
          (L.S.base.metric s) e (x : SpatialNeckCylinder) (v 0) (v 1)))
  exact congrArg₂ (fun a b : ℝ => a - b) hsource.symm hreference.symm

private theorem cylindricalComparison_witness
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (hD : X.D = ancientTimeInterval)
    (hscalar : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ s : ℝ, ∀ hs : s ≤ 0,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
        scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (K : Set SpatialNeckCylinder) (hUK : (spatialNeckBuffer epsilon : Set SpatialNeckCylinder) ⊆ K)
    (i : ℕ)
    (C : MetricComparisonOn L.S.base.metric (X.term (phi i)).S.base.metric
      (Phi.map i) (e '' K) (Icc (-1 : ℝ) 0) (Nat.ceil epsilon⁻¹) (epsilon / 2))
    (hU : e '' (spatialNeckBuffer epsilon : Set SpatialNeckCylinder) ⊆
      (Phi.atTime (L := L) 0).source i) :
    ∃ W : StrongNeckWitness (X.term (phi i)).S yStar
        (X.term (phi i)).basepoint 0 epsilon,
      ∀ x : spatialNeckBuffer epsilon, W.embedding x = Phi.map i (e (x : SpatialNeckCylinder)) := by
  let U := spatialNeckBuffer epsilon
  have hcarrier : X.D.carrier = Iic (0 : ℝ) := by rw [hD]; rfl
  have hregular : X.D.regular = Iio (0 : ℝ) := by rw [hD]; rfl
  let PhiR := Phi.atTime (L := L) 0
  let f : C(U, (X.term (phi i)).M) := pointedDomainEmbedding PhiR e U i hU
  have hf : IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f :=
    pointedMaps_restrict_isSmoothEmbedding PhiR e U i hU
  have hfmap (x : U) : f x = Phi.map i (e (x : SpatialNeckCylinder)) := rfl
  have hpoint (x : U) : e (x : SpatialNeckCylinder) ∈ e '' K :=
    ⟨x, hUK x.property, rfl⟩
  have hd (x : U) (v : TangentSpace SpatialNeckCylinderModel x) :
      mfderiv SpatialNeckCylinderModel I3 f x v =
        mfderiv I3 I3 (Phi.map i) (e x)
          (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) v) :=
    cylindricalEmbedding_deriv Phi e U i hU x v
  have hQ : 0 < (X.term (phi i)).S.scalar 0 (X.term (phi i)).basepoint := by
    rw [hscalar]; norm_num
  have hfmarked : f (spatialNeckCentralPoint epsilon hepsilon yStar) =
      (X.term (phi i)).basepoint := by
    rw [hfmap]
    change Phi.map i (e (yStar, 0)) = _
    rw [hmarked]
    exact Phi.basepoint_map i
  let jet : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) 2 :=
    fun b s => cylindricalJet (L := L) e U (C.jet b s)
  have hjet (b : ℕ) (s : ℝ) (x : U) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
      jet b s x v = C.jet b s (e x)
        (fun j => mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v j)) :=
    cylindricalJet_apply (L := L) e U (C.jet b s) x v
  have hreference (s : ℝ) (hs : s ≤ 0) :
      strongNeckBackgroundMetric epsilon s =
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e).restrictOpen U := by
    rw [strongNeckBackgroundMetric_of_nonpos epsilon s hs, hmetric s hs]
  let W : StrongNeckWitness (X.term (phi i)).S yStar (X.term (phi i)).basepoint 0 epsilon := {
    dimension_three := by simp [ThreeSpace]
    isSolution := (X.term (phi i)).isSolution
    epsilon_pos := hepsilon
    epsilon_lt_one := hepsilon_one
    scalar_pos := hQ
    time_window := by
      rw [hscalar, hcarrier]
      exact fun _ ht => ht.2
    embedding := f
    smooth_embedding := hf
    marked := hfmarked
    jet := jet
    jet_zero := by
      intro s hs x v
      exact cylindricalComparison_jet_zero C e (hscalar (phi i)) hQ f hf
        s x v (hpoint x) (hfmap x) (hd x) (hreference s hs.2)
    jet_succ := by
      intro b s hs x v
      have ht := metricComparison_hasDerivWithinAt (X.term (phi i)).S
        (X.term (phi i)).isSolution L.S L.isSolution hcarrier hregular C (by norm_num)
        le_rfl b s hs (e x) (hpoint x)
        (fun j => mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v j))
      simpa only [hjet] using ht
    closeness := by
      refine ⟨epsilon / 2, by positivity, by linarith, ?_⟩
      intro a b hab s hs x _hx
      rw [hreference s hs.2]
      exact (cylindricalJet_norm (L := L) e U (C.jet b s)
        (L.S.base.metric s) (L.S.base.metric s) a x).le.trans
          (C.close a b hab s hs (e x) (hpoint x)) }
  exact ⟨W, hfmap⟩


theorem pointedCylinderFlowLimit_eventually_strongNeckWitness
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (hD : X.D = ancientTimeInterval)
    (hscalar : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn L.S.base.metric
        (X.term (phi i)).S.base.metric (Phi.map i) K (Icc (-1 : ℝ) 0) order eta))
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ s : ℝ, ∀ hs : s ≤ 0,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
        scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    ∀ᶠ i in atTop, ∃ W : StrongNeckWitness (X.term (phi i)).S yStar
        (X.term (phi i)).basepoint 0 epsilon,
      ∀ x : spatialNeckBuffer epsilon, W.embedding x = Phi.map i (e (x : SpatialNeckCylinder)) := by
  let U := spatialNeckBuffer epsilon
  let Kbuffer : Set SpatialNeckCylinder :=
    (univ : Set SpatialNeckSphere) ×ˢ Icc (-epsilon⁻¹ - 1) (epsilon⁻¹ + 1)
  have hbuffer : IsCompact Kbuffer := isCompact_univ.prod isCompact_Icc
  have hUbuffer : (U : Set SpatialNeckCylinder) ⊆ Kbuffer := by
    intro x hx
    exact ⟨mem_univ _, hx.1.le, hx.2.le⟩
  have himage : IsCompact (e '' Kbuffer) := hbuffer.image e.continuous
  let PhiR := Phi.atTime (L := L) 0
  obtain ⟨i0, hi0⟩ := PhiR.source_subset himage
  have hsource : ∀ᶠ i in atTop, e '' Kbuffer ⊆ PhiR.source i :=
    eventually_atTop.2 ⟨i0, hi0⟩
  have hcomparison := hconvergence (e '' Kbuffer) himage
    (Nat.ceil epsilon⁻¹) (epsilon / 2) (by positivity)
  filter_upwards [hsource, hcomparison] with i hsource_i hcomparison_i
  obtain ⟨C⟩ := hcomparison_i
  have hU : e '' (U : Set SpatialNeckCylinder) ⊆ PhiR.source i :=
    (image_mono hUbuffer).trans hsource_i
  exact cylindricalComparison_witness Phi hD hscalar yStar e hmarked hmetric
    epsilon hepsilon hepsilon_one Kbuffer hUbuffer i C hU


theorem pointedCylinderFlowLimit_eventually_isStrongNeckCenter
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (hD : X.D = ancientTimeInterval)
    (hscalar : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn L.S.base.metric
        (X.term (phi i)).S.base.metric (Phi.map i) K (Icc (-1 : ℝ) 0) order eta))
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ s : ℝ, ∀ hs : s ≤ 0,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
        scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    ∀ᶠ i in atTop, IsStrongNeckCenter (X.term (phi i)).S yStar
      (X.term (phi i)).basepoint 0 epsilon := by
  filter_upwards [pointedCylinderFlowLimit_eventually_strongNeckWitness Phi hD hscalar
    hconvergence yStar e hmarked hmetric epsilon hepsilon hepsilon_one] with i hi
  exact ⟨hi.choose⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
