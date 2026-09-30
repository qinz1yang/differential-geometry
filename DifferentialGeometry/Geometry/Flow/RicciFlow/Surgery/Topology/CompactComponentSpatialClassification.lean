import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSpatialCanonicalAlternatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
import DifferentialGeometry.Geometry.Neck.CompactCapClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCanonicalCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

open private positive_component_restrictOpen from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
open private diffeomorphOfPartialDiffeomorphUniv from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Metric (riemannianEDistOf_ball_subset_of_le_frontier_distance)
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M}

theorem SpatialCanonicalWitness.exists_capCore_with_neck_frontier
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hchart : W.capTubeHasNeckChart eps)
    (cap : SpatialLocalCap g eps x W.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x z)
    (htag : W.alternative = SpatialCanonicalAlternative.cap cap hdepth) :
    ∃ (V : CompactDomain M) (v : M) (nk : SpatialNeck g eps v),
      Nonempty (CapCore V.carrier) ∧
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior V.carrier ∧ V.carrier ⊆ W.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      (∀ z, nk.map z = cap.tubeMap z) ∧
      riemannianBallOf g x (1000 / Real.sqrt (metricScalarAt g x)) ⊆ interior V.carrier := by
  obtain ⟨v, nk, hmap⟩ := hchart cap hdepth htag
  obtain ⟨V, hV, hxV, hVU, hVfront⟩ :=
    cap.exists_truncated_compactDomain (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  have hmodel : Nonempty (CapCore V.carrier) := by
    rw [hV]
    exact cap.nonempty_capCore_truncated_core (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  refine ⟨V, v, nk, hmodel, hV, hxV, hVU, ?_, fun z => (hmap z).symm, ?_⟩
  · rw [hVfront]
    congr 1
    funext q
    exact hmap _
  · have hcore : cap.core.carrier ⊆ V.carrier := by rw [hV]; exact subset_union_left
    have hball := riemannianEDistOf_ball_subset_of_le_frontier_distance g cap.center_inside
      (r := ENNReal.ofReal (10000 / Real.sqrt (metricScalarAt g x))) (by
        intro z hz
        have hztube : z ∈ cap.tube := (cap.overlap_eq.symm ▸ hz).2
        exact (ENNReal.ofReal_le_ofReal (hdepth z hztube)).trans ENNReal.ofReal_toReal_le)
    intro z hz
    apply interior_mono hcore (hball ?_)
    exact hz.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)))

theorem SpatialCanonicalWitness.exists_capCore_on_connectedComponent
    (U : TopologicalSpace.Opens M) (xU : U)
    (hU : (U : Set M) = connectedComponent (xU : M))
    (W : SpatialCanonicalWitness g eps C1 C2 (xU : M)) (hchart : W.capTubeHasNeckChart eps)
    (cap : SpatialLocalCap g eps (xU : M) W.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (metricScalarAt g (xU : M)) ≤ metricDistance g (xU : M) z)
    (htag : W.alternative = SpatialCanonicalAlternative.cap cap hdepth) :
    ∃ (K : CompactDomain U) (v : U) (nk : SpatialNeck (g.restrictOpen U) eps v),
      Nonempty (CapCore K.carrier) ∧
      frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      riemannianBallOf (g.restrictOpen U) xU
        (1000 / Real.sqrt (metricScalarAt (g.restrictOpen U) xU)) ⊆ interior K.carrier := by
  obtain ⟨K, v, nk, hmodel, hK, hxK, _, hfront, hmap, hballM⟩ :=
    W.exists_capCore_with_neck_frontier hchart cap hdepth htag
  have hKU : K.carrier ⊆ U := by
    rw [hU]
    exact K.connected.subset_connectedComponent (interior_subset hxK)
  have hvK : v ∈ K.carrier := by
    rw [← nk.center_eq, hmap, hK]
    exact Or.inr ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hcapture : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
    rw [hU]
    have hvc : v ∈ connectedComponent (xU : M) := by
      have hvU : v ∈ (U : Set M) := hKU hvK
      rwa [hU] at hvU
    rw [connectedComponent_eq hvc]
    exact nk.controlled_range_subset_connectedComponent
  obtain ⟨hvU', nkU, _, hmapU, _, _, hscalarU⟩ := nk.exists_restrict_target U hcapture
  have hhalf (q : Sphere 2) : (q, (1 / 2 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hinv : (1 : ℝ) < eps⁻¹ := (one_lt_inv₀ W.eps_pos).mpr W.eps_lt_one
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  refine ⟨K.restrictOpen U hKU, ⟨v, hvU'⟩, nkU, hmodel.some.nonempty_preimage_open U hKU,
    ?_, ?_⟩
  · rw [K.frontier_restrictOpen_carrier U hKU, hfront]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext ((hmapU (q, 1 / 2) (hhalf q)).trans hq)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, (hmapU (q, 1 / 2) (hhalf q)).symm⟩
  · intro z hz
    rw [K.interior_restrictOpen_carrier U hKU]
    apply hballM
    change riemannianEDistOf (g.restrictOpen U) xU z <
      ENNReal.ofReal (1000 / Real.sqrt (metricScalarAt (g.restrictOpen U) xU)) at hz
    rw [hscalarU] at hz
    exact (riemannianEDistOf_le_restrictOpen g U xU z).trans_lt hz

def SpatialRoundComponent.restrictOpen (U : TopologicalSpace.Opens M) (x : U)
    (R : SpatialRoundComponent g eps (x : M) (U : Set M)) :
    SpatialRoundComponent (g.restrictOpen U) eps x univ := by
  letI := R.topology
  letI := R.charted
  letI := R.smooth
  letI := R.t2
  letI := R.compact
  letI := R.connected
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩
  have hitarget : i.target = (U : Set M) := U.openPartialHomeomorphSubtypeCoe_target ⟨x⟩
  have hmap (z : R.Z) : R.map z ∈ U := by
    change (R.map z : M) ∈ (U : Set M)
    have hz : R.map z ∈ R.map.target :=
      R.map.map_source (by rw [R.source_eq]; exact mem_univ z)
    simpa only [R.target_eq] using hz
  let F := R.map.trans i.symm
  have hsource : F.source = univ := by
    ext z
    rw [show F.source = R.map.source ∩ R.map ⁻¹' i.target from rfl, R.source_eq]
    simp only [hitarget, mem_inter_iff, mem_univ, true_and, mem_preimage]
    exact iff_true_intro (hmap z)
  have htarget : F.target = univ := by
    ext z
    change (z ∈ i.source ∧ i z ∈ R.map.target) ↔ z ∈ (univ : Set U)
    rw [R.target_eq]
    exact iff_true_intro ⟨mem_univ z, z.property⟩
  have hval (z : R.Z) : (F z : M) = R.map z := by
    change (i.symm (R.map z) : M) = R.map z
    apply i.right_inv'
    rw [hitarget]
    exact hmap z
  have hdf (z : R.Z) : mfderiv I3 I3 F z = mfderiv I3 I3 R.map z := by
    have heq : (fun y => (F y : M)) = (R.map : R.Z → M) := funext hval
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp, heq]
  have hscalar : metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) :=
    metricScalarAt_restrictOpen g U x
  have hQ : 0 < metricScalarAt (g.restrictOpen U) x := hscalar.symm ▸ R.Q_pos
  have hinner (z : R.Z) (v w : TangentSpace I3 (F z)) :
      (g.restrictOpen U).inner (F z) v w = g.inner (R.map z) v w := by
    rw [SmoothRiemannianMetric.restrictOpen_inner, hval]
  refine {
    Z := R.Z
    topology := R.topology
    charted := R.charted
    smooth := R.smooth
    t2 := R.t2
    compact := R.compact
    connected := R.connected
    metric := R.metric
    p := R.p
    scalar_one := R.scalar_one
    constant_curvature := R.constant_curvature
    map := F
    source_eq := hsource
    target_eq := htarget
    center_eq := ?_
    Q_pos := hQ
    comparison := ?_
    metric_bounds := ?_ }
  · apply Subtype.ext
    exact (hval R.p).trans R.center_eq
  · refine {
      pullback := R.comparison.pullback
      pullback_eq := ?_
      jet := R.comparison.jet
      jet_zero := R.comparison.jet_zero
      jet_succ := R.comparison.jet_succ
      equivalence := R.comparison.equivalence
      close := R.comparison.close }
    intro s z hz v
    rw [R.comparison.pullback_eq s z hz v]
    simp only [scaleMetric_inner, hscalar, hinner, hdf]
    rfl
  · intro z v
    rw [hscalar, hinner, hdf]
    exact R.metric_bounds z v

theorem SpatialCanonicalWitness.spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
    (U : TopologicalSpace.Opens M) (xU : U)
    (hU : (U : Set M) = connectedComponent (xU : M))
    (W : SpatialCanonicalWitness g eps C1 C2 (xU : M)) (hchart : W.capTubeHasNeckChart eps)
    (hx : ¬ Nonempty (SpatialNeck (g.restrictOpen U) eps xU)) :
    Nonempty (PositiveComponent (M := U) univ) ∨
      Nonempty (SpatialRoundComponent (g.restrictOpen U) eps xU univ) ∨
      ∃ (K : CompactDomain U) (v : U) (nk : SpatialNeck (g.restrictOpen U) eps v) (a : ℝ),
        0 < metricScalarAt (g.restrictOpen U) xU ∧ Nonempty (CapCore K.carrier) ∧
        |a| ≤ 4 ∧ frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
        riemannianBallOf (g.restrictOpen U) xU
          (1000 / Real.sqrt (metricScalarAt (g.restrictOpen U) xU)) ⊆ interior K.carrier := by
  cases htag : W.alternative with
  | neck data =>
    have hcapture : data.neck.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
      rw [hU]
      exact data.neck.controlled_range_subset_connectedComponent
    exact (hx ⟨data.neck.restrictOpen hcapture⟩).elim
  | positive whole data sec =>
    have hdom : W.domain.carrier = (U : Set M) := whole.trans hU.symm
    exact Or.inl (positive_component_restrictOpen (hdom ▸ data))
  | round whole data =>
    have hdom : W.domain.carrier = (U : Set M) := whole.trans hU.symm
    exact Or.inr (Or.inl ⟨SpatialRoundComponent.restrictOpen U xU (hdom ▸ data)⟩)
  | cap data depth =>
    obtain ⟨K, v, nk, hmodel, hfront, hball⟩ :=
      W.exists_capCore_on_connectedComponent U xU hU hchart data depth htag
    refine Or.inr (Or.inr ⟨K, v, nk, 1 / 2, ?_, hmodel, by norm_num, hfront, hball⟩)
    rw [metricScalarAt_restrictOpen]
    exact W.Q_pos

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem admitsConstantPositiveSectionalCurvature_of_spatialRoundComponent
    (M : ConnectedClosedOrientedManifold.{u} 3) {g : SmoothRiemannianMetric I3 M.Carrier}
    {eps : ℝ} {x : M.Carrier} (R : SpatialRoundComponent g eps x univ) :
    admitsConstantPositiveSectionalCurvature (I := I3) (M := M.Carrier) := by
  let _ : TopologicalSpace R.Z := R.topology
  let _ : ChartedSpace ThreeSpace R.Z := R.charted
  let _ : IsManifold I3 ∞ R.Z := R.smooth
  let _ : T2Space R.Z := R.t2
  let _ : CompactSpace R.Z := R.compact
  let _ : ConnectedSpace R.Z := R.connected
  have hZ : constantPositiveSectionalCurvatureMetric R.metric := by
    apply (constantPositiveSectionalCurvatureMetric_iff (I := I3) R.metric).2
    refine ⟨1 / 6, by norm_num, fun z v w hLI => ?_⟩
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
      funext i
      fin_cases i <;> rfl
    rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
      metricRm04StandardAt_apply, ← hvec, R.constant_curvature z v w]
    have hden : 0 < R.metric.inner z v v * R.metric.inner z w w - (R.metric.inner z v w) ^ 2 := by
      simpa only [Riemannian.sectionalCurvatureDenominator_def]
        using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := I3) (M := R.Z) R.metric z v w hLI
    field_simp [ne_of_gt hden]
  exact ⟨Diffeomorph.pullbackMetric R.metric
      (diffeomorphOfPartialDiffeomorphUniv R.map R.source_eq R.target_eq).symm,
    constantPositiveSectionalCurvatureMetric_pullback R.metric hZ
      (diffeomorphOfPartialDiffeomorphUniv R.map R.source_eq R.target_eq).symm⟩

theorem exists_compact_component_spatial_poincareStandard_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : ClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric I3 M.Carrier)
        (c : ConnectedComponents M.Carrier) (C1 C2 : ℝ)
        (W : ∀ x : (M.component c).Carrier, SpatialCanonicalWitness g eps C1 C2 x.val),
        (∀ x, (W x).capTubeHasNeckChart eps) →
          isPoincareStandard (M.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M g c C1 C2 W hchart
  let U := M.componentOpen c
  apply hclass eps heps (M.component c) (g.restrictOpen U)
  intro x hx
  let xU : U := ⟨x.val, x.property⟩
  let _ : CompactSpace U := (M.component c).compact
  have hU : (U : Set M.Carrier) = connectedComponent (xU : M.Carrier) := by
    change M.componentSet c = connectedComponent (xU : M.Carrier)
    rw [← xU.property, ClosedOrientedManifold.componentSet_mk]
  rcases (W x).spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
      U xU hU (hchart x) hx with hp | hr | hc
  · exact Or.inl hp
  · exact Or.inr (Or.inl
      (admitsConstantPositiveSectionalCurvature_of_spatialRoundComponent (M.component c) hr.some))
  · exact Or.inr (Or.inr hc)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology

universe u

theorem exists_component_poincareStandard_tolerance_of_spatiallyCanonical :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (g : G.TerminalLimitMetric) (C1 C2 q R : ℝ),
      0 < q → q < R →
      G.SpatiallyCanonicalBefore eps C1 C2 q s →
      ∀ Ctime : ℝ≥0, G.DerivativeBoundBefore Ctime q s →
      ∀ c : ConnectedComponents P.Carrier,
        (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
          R < metricScalarAt g.metric x) →
        isPoincareStandard (P.toClosedOrientedManifold.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_component_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P a s G g C1 C2 q R hq hqR hcanonical Ctime hbound c hterminal
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨d, hd, hhigh⟩ := g.eventually_scalar_gt_on_closed_set hq hbound hPhi hpinch
    (P.componentOpen_isClosed c) hqR hterminal
  obtain ⟨t, ht⟩ := exists_between hd.2
  have htime : t ∈ Ioo a s := ⟨hd.1.trans_lt ht.1, ht.2⟩
  choose W hchart using fun x : (P.toClosedOrientedManifold.component c).Carrier =>
    hcanonical x.val t htime (hhigh t ht x.val x.property)
  exact hclass eps heps P.toClosedOrientedManifold (G.flow.base.metric t) c C1 C2 W hchart

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
