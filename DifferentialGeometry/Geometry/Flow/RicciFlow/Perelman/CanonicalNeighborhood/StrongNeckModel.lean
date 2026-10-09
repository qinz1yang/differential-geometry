import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeckPartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Construction.TensorOpenExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Locality
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance strongNeckConversionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem strongNeckBackgroundMetric_eq_reference (epsilon s : ℝ) (hs : s ≤ 0) :
    strongNeckBackgroundMetric epsilon s =
      (cylinderReferenceMetric s).restrictOpen (spatialNeckBuffer epsilon) := by
  rw [strongNeckBackgroundMetric_of_nonpos epsilon s hs]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num))).inner x.val v w =
    (cylinderReferenceMetric s).inner x.val v w
  exact (scalarOneShrinkingCylinderMetric_inner s (hs.trans_lt (by norm_num))
    x.val.1 x.val.2 v.1 w.1 v.2 w.2).trans
      (cylinderReferenceMetric_inner s hs x.val v w).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {yStar : SpatialNeckSphere} {p : M} {t epsilon : ℝ}

theorem KappaSolutions.StrongNeckWitness.exists_strongNeck
    (W : StrongNeckWitness S yStar p t epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ N : StrongNeck S epsilon p t,
      N.map.source = spatialNeckBuffer epsilon ∧
      N.map.target = range W.embedding ∧
      N.center = yStar ∧
      (∀ z : spatialNeckBuffer epsilon, N.map z.val = W.embedding z) ∧
      N.map '' (univ ×ˢ ({0} : Set ℝ)) = W.embedding '' spatialNeckCentralDomain epsilon := by
  classical
  obtain ⟨F, hsource, htarget, hmap, hcentral⟩ := W.exists_partialDiffeomorph
  let K : Set Cylinder := univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  let U : Set Cylinder := univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hKU : K ⊆ spatialNeckBuffer epsilon := by
    intro x hx
    change -epsilon⁻¹ - 1 < x.2 ∧ x.2 < epsilon⁻¹ + 1
    have h := hx.2
    constructor <;> linarith [h.1, h.2]
  have hUK : U ⊆ K := fun _ hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  let P : ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 := fun s =>
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (metricTensorField (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s))).choose
  have hP (s : ℝ) (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) :
      P s x.val v =
        (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s).inner x (v 0) (v 1) :=
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (metricTensorField (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s))).choose_spec
        x hx v
  let J : ℕ → ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 := fun b s =>
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU (W.jet b s)).choose
  have hJ (b : ℕ) (s : ℝ) (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) : J b s x.val v = W.jet b s x v :=
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (W.jet b s)).choose_spec x hx v
  let jet : ℕ → ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2
    | 0, s => P s - metricTensorField (cylinderReferenceMetric s)
    | b + 1, s => J (b + 1) s
  have hjet (b : ℕ) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0)
      (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) : jet b s x.val v = W.jet b s x v := by
    cases b with
    | zero =>
      change P s x.val v - (cylinderReferenceMetric s).inner x.val (v 0) (v 1) = _
      rw [hP s x hx v, W.jet_zero s hs x v,
        strongNeckBackgroundMetric_eq_reference epsilon s hs.2,
        SmoothRiemannianMetric.restrictOpen_inner]
    | succ b => exact hJ (b + 1) s x hx v
  have hderiv (x : spatialNeckBuffer epsilon) (v : TangentSpace IC x) :
      mfderiv IC I3 W.embedding x v = mfderiv IC I3 F x.val v := by
    have hfun : (F ∘ (Subtype.val : spatialNeckBuffer epsilon → Cylinder)) =
        W.embedding := funext hmap
    have hF := F.mdifferentiableAt (by simp)
      (by rw [hsource]; exact x.property)
    have hval : MDifferentiableAt IC IC
        (Subtype.val : spatialNeckBuffer epsilon → Cylinder) x :=
      (contMDiff_subtype_val (I := IC) (U := spatialNeckBuffer epsilon)
        (n := ∞)).mdifferentiableAt (by decide)
    have h := mfderiv_comp x hF hval
    rw [hfun, mfderiv_subtype_val] at h
    exact DFunLike.congr_fun h v
  have hclose (a b : ℕ) (hab : a + 2 * b ≤ Nat.ceil epsilon⁻¹)
      (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (y : Cylinder) (hy : y ∈ U) :
      tensor02CovDerivNormWith a (jet b s)
        (cylinderReferenceMetric s) (cylinderReferenceMetric s) y ≤ epsilon := by
    let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
    have hnear : {z : spatialNeckBuffer epsilon | z.val ∈ U} ∈ 𝓝 x :=
      ((isOpen_univ.prod isOpen_Ioo).preimage continuous_subtype_val).mem_nhds hy
    have heq : ∀ᶠ z : spatialNeckBuffer epsilon in 𝓝 x,
        restrictOpen0S (I := IC) 2 (V := spatialNeckBuffer epsilon) (jet b s) z =
          W.jet b s z := by
      filter_upwards [hnear] with z hz
      ext v
      exact hjet b s hs z (hUK hz) v
    obtain ⟨delta, _, hdelta, hc⟩ := W.closeness
    calc
      tensor02CovDerivNormWith a (jet b s)
          (cylinderReferenceMetric s) (cylinderReferenceMetric s) y =
        tensor02CovDerivNormWith a
          (restrictOpen0S (I := IC) 2 (V := spatialNeckBuffer epsilon) (jet b s))
          (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x := by
            rw [strongNeckBackgroundMetric_eq_reference epsilon s hs.2,
              tensor02CovDerivNormWith_restrictOpen0S]
      _ = tensor02CovDerivNormWith a (W.jet b s)
          (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x :=
        tensor02CovDerivNormWith_eq_of_eventuallyEq _ _ _ _ a x heq
      _ ≤ delta := hc a b hab s hs x ⟨hy.2.1.le, hy.2.2.le⟩
      _ ≤ epsilon := hdelta.le
  let cmp : MetricComparisonOn cylinderReference.metric
      (rescaledMetric S t (S.scalar t p) W.scalar_pos) F U (Icc (-1 : ℝ) 0)
      (Nat.ceil epsilon⁻¹) epsilon :=
    { pullback := P
      pullback_eq := by
        intro s y hy v
        let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
        rw [hP s x (hUK hy) v]
        erw [strongNeckNormalizedMetric_inner, ← hmap x,
          hderiv x (v 0), hderiv x (v 1)]
        rfl
      jet := jet
      jet_zero := fun _ _ _ => rfl
      jet_succ := by
        intro b s hs y hy v
        let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
        rw [hjet (b + 1) s hs x (hUK hy) v]
        apply ((W.jet_succ b s hs x v).derivWithin
          (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) s hs)).symm.trans
        exact derivWithin_congr (fun r hr => (hjet b r hr x (hUK hy) v).symm)
          (hjet b s hs x (hUK hy) v).symm
      equivalence := by
        intro s hs y hy v
        apply tensor_apply_bounds_of_metricTensorErrorNorm_le (P s) (cylinderReferenceMetric s) _ v
        exact hclose 0 0 (by simp) s hs y hy
      close := hclose }
  refine ⟨{
    eps_pos := W.epsilon_pos
    eps_small := hsmall
    Q_pos := W.scalar_pos
    cylinder := cylinderReference
    map := F
    center := yStar
    center_eq := (hmap (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)).trans W.marked
    domain := fun y hy => hsource.symm ▸ hKU (hUK hy)
    time_domain := W.time_window
    comparison := cmp }, hsource, htarget, rfl, hmap, hcentral⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
