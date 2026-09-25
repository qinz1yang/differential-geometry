import DifferentialGeometry.Geometry.Neck.CapSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBufferedChartTransfer
import DifferentialGeometry.Topology.RelativeOpenInterior

noncomputable section
open Set Manifold Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

theorem GeometricCutoffRecord.scalar_sublevel_mem_interior_core
    (R : GeometricCutoffRecord H i p) {L : ℝ}
    (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : metricScalarAt (H.event i).terminal.metric x ≤ L) :
    x.val ∈ interior (H.event i).transition.trace.tubes.core := by
  let T := (H.event i).transition.trace.tubes
  have hopen : IsOpen ((⋃ j : T.Index, range (T.tube j))ᶜ) :=
    (isCompact_iUnion (fun j => isCompact_range (T.tube j).continuous)).isClosed.isOpen_compl
  have hsub : (⋃ j : T.Index, range (T.tube j))ᶜ ⊆ T.core := by
    intro y hy
    change y ∉ ⋃ j, T.removedBand j
    intro hm
    obtain ⟨j, q, hq, heq⟩ := mem_iUnion.mp hm
    exact hy (mem_iUnion.mpr ⟨j, q, heq⟩)
  apply interior_maximal hsub hopen
  intro hm
  obtain ⟨j, q, heq⟩ := mem_iUnion.mp hm
  let z : neckBuffer (R.delta j) := ⟨(q.1, q.2.val), R.tube_in_buffer j q⟩
  have hwide : 2 ≤ (R.delta j)⁻¹ := by
    have hh := inv_anti₀ (R.delta_pos j) (hδ j)
    norm_num at hh
    exact hh
  have hz : z ∈ neckClosedTest (R.delta j) := by
    change -(R.delta j)⁻¹ ≤ q.2.val ∧ q.2.val ≤ (R.delta j)⁻¹
    constructor <;> linarith [q.2.property.1, q.2.property.2]
  have hk : 2 ≤ R.order j := by
    have hh := R.order_lower j
    have hl := le_max_right (p.modelOrder + 6) (2 * ⌊(R.delta j)⁻¹⌋₊ + 4)
    omega
  have hmark : (R.neck j).chart z = x :=
    Subtype.ext ((R.tube_eq j q z.property).symm.trans heq)
  have hr := (abs_le.mp ((R.neck j).abs_scalar_ratio_sub_one_le hk (hδ j) z hz)).1
  rw [hmark] at hr
  have hlow : (1 - 4323 * R.delta j) * (R.neck j).scale ≤
      metricScalarAt (H.event i).terminal.metric x := by
    apply (le_div_iff₀ (R.neck j).scale_pos).mp
    linarith
  exact (not_lt_of_ge (hlow.trans hx)) (hscale j)

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem MetricCutCapEvent.subset_interior_old_of_isPreconnected
    (E : MetricCutCapEvent P Q a s) (hOld : E.old = E.transition.trace.retainedCore)
    {K : Set E.incoming.terminalRegularOpen} (hK : IsPreconnected K)
    (hcore : ∀ x ∈ K, x.val ∈ interior E.transition.trace.tubes.core)
    {x : E.incoming.terminalRegularOpen} (hx : x ∈ K) {q : Q.Carrier}
    (hcross : E.RegularCrossing x.val q) :
    ∀ y ∈ K, y.val ∈ interior (Subtype.val '' E.old) := by
  let f : K → E.transition.trace.tubes.core := fun y => ⟨y.val.val, interior_subset (hcore y.val y.property)⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hret : range f ⊆ E.transition.trace.retainedCore := by
    apply (isPreconnected_range hf).subset_isClopen E.transition.trace.isClopen_retainedCore
    obtain ⟨z, _, hz, _⟩ := hcross
    have hzf : f ⟨x, hx⟩ = z.val := Subtype.ext hz.symm
    refine ⟨f ⟨x, hx⟩, mem_range_self _, ?_⟩
    rw [hzf, ← hOld]
    exact z.property
  intro y hy
  rw [hOld]
  exact DifferentialGeometry.Topology.mem_interior_image_val_of_isOpen
    E.transition.trace.isClopen_retainedCore.isOpen
    (hret (mem_range_self ⟨y, hy⟩)) (hcore y hy)

theorem GeometricCutoffRecord.subset_interior_old_of_scalar_upper_bound
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    {L : ℝ} (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    {K : Set (H.event i).incoming.terminalRegularOpen} (hK : IsPreconnected K)
    (hscalar : ∀ y ∈ K, metricScalarAt (H.event i).terminal.metric y ≤ L)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ K)
    {q : (H.stage i.succ).Carrier} (hcross : (H.event i).RegularCrossing x.val q) :
    ∀ y ∈ K, y.val ∈ interior (Subtype.val '' (H.event i).old) :=
  (H.event i).subset_interior_old_of_isPreconnected hOld hK
    (fun y hy => R.scalar_sublevel_mem_interior_core hδ hscale y (hscalar y hy)) hx hcross

theorem GeometricCutoffRecord.exists_survivor_partialDiffeomorph_of_scalar_upper_bound
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    {L : ℝ} (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    {K : Set (H.event i).incoming.terminalRegularOpen} (hK : IsPreconnected K)
    (hscalar : ∀ y ∈ K, metricScalarAt (H.event i).terminal.metric y ≤ L)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ K)
    {q : (H.stage i.succ).Carrier} (hcross : (H.event i).RegularCrossing x.val q) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      K ⊆ F.source ∧ F x = q ∧
      (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
      ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
        (H.event i).outputMetric.inner (F y)
          (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
            (H.event i).terminal.metric.inner y v w := by
  have hKold := R.subset_interior_old_of_scalar_upper_bound hOld hδ hscale hK hscalar hx hcross
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨{y | y.val ∈ interior (Subtype.val '' (H.event i).old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  obtain ⟨F, hsource, hcrossF, _, hmetric⟩ :=
    (H.event i).exists_survivor_partialDiffeomorph W ⟨x, hKold x hx⟩ (fun _ hy => hy)
  have hKF : K ⊆ F.source := by rw [hsource]; exact hKold
  have hpoint : F x = q :=
    (H.event i).regularCrossing_right_unique (hcrossF x (hKold x hx)) hcross
  refine ⟨F, hKF, hpoint, ?_, ?_⟩
  · intro y hy
    exact hcrossF y (by change y ∈ (W : Set _); rwa [← hsource])
  · intro y hy
    exact hmetric y (by change y ∈ (W : Set _); rwa [← hsource])

theorem GeometricCutoffRecord.exists_survivor_neighborhood_of_scalar_upper_bound
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    {L : ℝ} (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    {K : Set (H.event i).incoming.terminalRegularOpen}
    (hKcompact : IsCompact K) (hK : IsPreconnected K)
    (hscalar : ∀ y ∈ K, metricScalarAt (H.event i).terminal.metric y ≤ L)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ K)
    {q : (H.stage i.succ).Carrier} (hcross : (H.event i).RegularCrossing x.val q) :
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
      (V : Set (H.event i).incoming.terminalRegularOpen),
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ F.source ∧ IsCompact (closure V) ∧
      F x = q ∧
      (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
      ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
        (H.event i).outputMetric.inner (F y)
          (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
            (H.event i).terminal.metric.inner y v w := by
  let : LocallyCompactSpace (H.event i).incoming.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace (H.event i).incoming.terminalRegularOpen
  obtain ⟨F, hKF, hpoint, hcrossF, hmetric⟩ :=
    R.exists_survivor_partialDiffeomorph_of_scalar_upper_bound hOld hδ hscale hK hscalar hx hcross
  obtain ⟨V, hV, hKV, hVF, hcompact⟩ :=
    exists_open_between_and_isCompact_closure hKcompact F.open_source hKF
  exact ⟨F, V, hV, hKV, hVF, hcompact, hpoint, hcrossF, hmetric⟩

universe v
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X]

theorem GeometricCutoffRecord.exists_survivor_chart_of_scalar_upper_bound
    [PreconnectedSpace X]
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    {L : ℝ} (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    (φ : X → (H.event i).incoming.terminalRegularOpen)
    (hφ : IsSmoothEmbedding I ThreeModel ∞ φ)
    (hscalar : ∀ y, metricScalarAt (H.event i).terminal.metric (φ y) ≤ L)
    (x : X) {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing (φ x).val q) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      range φ ⊆ F.source ∧
      ∃ ψ : X → (H.stage i.succ).Carrier, ψ = (F : _ → _) ∘ φ ∧
        IsSmoothEmbedding I ThreeModel ∞ ψ ∧ ψ x = q ∧
        (∀ y, (H.event i).RegularCrossing (φ y).val (ψ y)) ∧
        (∀ K : Set X, ψ '' K = (F : _ → _) '' (φ '' K)) ∧
        ∀ (y : X) (v w : TangentSpace I y),
          (H.event i).outputMetric.inner (ψ y) (mfderiv I ThreeModel ψ y v)
            (mfderiv I ThreeModel ψ y w) =
          (H.event i).terminal.metric.inner (φ y) (mfderiv I ThreeModel φ y v)
            (mfderiv I ThreeModel φ y w) := by
  have hscalar' : ∀ z ∈ range φ, metricScalarAt (H.event i).terminal.metric z ≤ L := by
    rintro z ⟨y, rfl⟩
    exact hscalar y
  obtain ⟨F, hsource, hpoint, hcrossF, hmetric⟩ :=
    R.exists_survivor_partialDiffeomorph_of_scalar_upper_bound hOld hδ hscale
      (isPreconnected_range hφ.contMDiff.continuous) hscalar' (mem_range_self x) hcross
  refine ⟨F, hsource, (F : _ → _) ∘ φ, rfl,
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F hφ hsource,
    hpoint, ?_, ?_, ?_⟩
  · intro y
    exact hcrossF (φ y) (hsource (mem_range_self y))
  · intro K
    exact (image_image (F : _ → _) φ K).symm
  · intro y v w
    exact (H.event i).survivor_chart_metric_inner F hmetric φ hφ.contMDiff hsource y v w

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
theorem exists_cutoff_cap_separation_tolerance_of_subset
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L →
          (interior L).Nonempty →
          frontier L = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
            ∀ j, Disjoint (Subtype.val '' K)
              ((H.event i).transition.trace.tubes.tube j ''
                {z : TubeDomain | z.2.val ∈ Icc (-1 : ℝ) 1}) := by
  obtain ⟨eta, heta, hsep⟩ := exists_neck_cap_separation_tolerance_of_subset hC hD hc
  refine ⟨min eta (1 / 12), lt_min heta (by norm_num), ?_⟩
  intro H i parameters R hδ epsb pb boundary hb s hs L K hLK hL hLi hfront q hq hscalar hboundary hdiam j
  have hsmall : R.delta j < 1 / 11 :=
    ((hδ j).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hk : ⌈(R.delta j)⁻¹⌉₊ ≤ R.order j := by
    have hf := Nat.ceil_le_floor_add_one ((R.delta j)⁻¹)
    have horder := (le_max_right (parameters.modelOrder + 6)
      (2 * ⌊(R.delta j)⁻¹⌋₊ + 4)).trans (R.order_lower j)
    omega
  obtain ⟨cut, _, hmap⟩ := (R.neck j).exists_spatialNeck le_rfl hsmall hk
  have hdis := hsep _ (H.event i).terminal.metric (R.delta j) epsb (R.neck j).center pb
    ((hδ j).trans (min_le_left _ _)) cut boundary hb s hs L K hLK hL hLi hfront q hq
    hscalar hboundary hdiam
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
  have hNx : (R.neck j).chart ⟨(z.1, z.2.val), R.tube_in_buffer j z⟩ = x :=
    Subtype.ext ((R.tube_eq j z (R.tube_in_buffer j z)).symm.trans heq)
  apply Set.disjoint_left.mp hdis hx
  refine ⟨(z.1, z.2.val), ⟨mem_univ _, hz⟩, ?_⟩
  exact (hmap ⟨(z.1, z.2.val), R.tube_in_buffer j z⟩).trans hNx

theorem exists_cutoff_cap_separation_tolerance
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (K : Set (H.event i).incoming.terminalRegularOpen), IsCompact K →
          (interior K).Nonempty →
          frontier K = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
            ∀ j, Disjoint (Subtype.val '' K)
              ((H.event i).transition.trace.tubes.tube j ''
                {z : TubeDomain | z.2.val ∈ Icc (-1 : ℝ) 1}) := by
  obtain ⟨eta, heta, hsep⟩ := exists_cutoff_cap_separation_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hδ epsb pb boundary hb s hs K hK hKi hfront q hq hscalar hboundary hdiam
  exact hsep H i parameters R hδ epsb pb boundary hb s hs K K Subset.rfl hK hKi hfront
    q hq hscalar hboundary hdiam

theorem exists_cutoff_cap_protection_tolerance_of_subset
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L → IsPreconnected K →
          (interior L).Nonempty →
          frontier L = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
            ∀ (x : (H.event i).incoming.terminalRegularOpen), x ∈ K →
              ∀ y : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val y →
              ∀ z ∈ K, z.val ∈ interior (Subtype.val '' (H.event i).old) := by
  obtain ⟨eta, heta, hsep⟩ := exists_cutoff_cap_separation_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ epsb pb boundary hb s hs L K hLK hL hconn hLi hfront
    q hq hscalar hboundary hdiam x hx y hcross
  have hdis := hsep H i parameters R hδ epsb pb boundary hb s hs L K hLK hL hLi hfront
    q hq hscalar hboundary hdiam
  apply (H.event i).subset_interior_old_of_isPreconnected hOld hconn _ hx hcross
  intro z hz
  let T := (H.event i).transition.trace.tubes
  let bands := ⋃ j, T.tube j '' {w : TubeDomain | w.2.val ∈ Icc (-1 : ℝ) 1}
  have hopen : IsOpen bandsᶜ := T.isCompact_iUnion_closedBand.isClosed.isOpen_compl
  have hsub : bandsᶜ ⊆ T.core := by
    intro w hw
    change w ∉ ⋃ j, T.removedBand j
    intro hm
    obtain ⟨j, a, ha, heq⟩ := mem_iUnion.mp hm
    exact hw (mem_iUnion.mpr ⟨j, a, ⟨ha.1.le, ha.2.le⟩, heq⟩)
  apply interior_maximal hsub hopen
  intro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact Set.disjoint_left.mp (hdis j) (mem_image_of_mem Subtype.val hz) hj

theorem exists_cutoff_cap_protection_tolerance
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (K : Set (H.event i).incoming.terminalRegularOpen), IsCompact K → IsPreconnected K →
          (interior K).Nonempty →
          frontier K = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
            ∀ (x : (H.event i).incoming.terminalRegularOpen), x ∈ K →
              ∀ y : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val y →
              ∀ z ∈ K, z.val ∈ interior (Subtype.val '' (H.event i).old) := by
  obtain ⟨eta, heta, hprotect⟩ := exists_cutoff_cap_protection_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ epsb pb boundary hb s hs K hK hconn hKi hfront
    q hq hscalar hboundary hdiam
  exact hprotect H i parameters R hOld hδ epsb pb boundary hb s hs K K Subset.rfl hK hconn
    hKi hfront q hq hscalar hboundary hdiam

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u v w z

theorem exists_cutoff_cap_survivor_chart_tolerance_of_subset
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L → IsPreconnected K →
          (interior L).Nonempty →
          frontier L = range (fun b : Sphere 2 => boundary.map (b, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤
                ENNReal.ofReal D) →
            ∀ (x : (H.event i).incoming.terminalRegularOpen), x ∈ K →
              ∀ y : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val y →
              ∀ {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
                {Y : Type w} [TopologicalSpace Y] {I : ModelWithCorners ℝ G Y}
                {X : Type z} [TopologicalSpace X] [ChartedSpace Y X]
                (φ : X → (H.event i).incoming.terminalRegularOpen),
                IsSmoothEmbedding I ThreeModel ∞ φ → range φ ⊆ K →
                ∃ F : PartialDiffeomorph ThreeModel ThreeModel
                    (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
                  K ⊆ F.source ∧ F x = y ∧
                  (∀ a ∈ F.source, (H.event i).RegularCrossing a.val (F a)) ∧
                  (∀ b : (H.event i).old, (H.event i).oldTerminal b ∈ F.source →
                    F ((H.event i).oldTerminal b) = (H.event i).oldOutput b) ∧
                  ∃ ψ : X → (H.stage i.succ).Carrier, ψ = (F : _ → _) ∘ φ ∧
                    IsSmoothEmbedding I ThreeModel ∞ ψ ∧
                    (∀ a, (H.event i).RegularCrossing (φ a).val (ψ a)) ∧
                    (∀ (a : X) (b : (H.event i).old), (H.event i).oldTerminal b = φ a →
                      ψ a = (H.event i).oldOutput b) ∧
                    (∀ A : Set X, ψ '' A = (F : _ → _) '' (φ '' A)) ∧
                    ∀ (a : X) (v w : TangentSpace I a),
                      (H.event i).outputMetric.inner (ψ a) (mfderiv I ThreeModel ψ a v)
                        (mfderiv I ThreeModel ψ a w) =
                        (H.event i).terminal.metric.inner (φ a) (mfderiv I ThreeModel φ a v)
                          (mfderiv I ThreeModel φ a w) := by
  obtain ⟨eta, heta, hprotect⟩ := exists_cutoff_cap_protection_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ epsb pb boundary hb s hs L K hLK hL hconn hLi hfront
    q hq hscalar hboundary hdiam x hx y hcross
  have hKold := hprotect H i parameters R hOld hδ epsb pb boundary hb s hs L K hLK hL hconn
    hLi hfront q hq hscalar hboundary hdiam x hx y hcross
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨{a | a.val ∈ interior (Subtype.val '' (H.event i).old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  intro G _ _ Y _ I X _ _ φ hφ himage
  obtain ⟨F, hsource, hcrossF, hold, htransfer⟩ :=
    (H.event i).exists_survivor_whole_chart_transfer (I := I) (X := X)
      W ⟨x, hKold x hx⟩ (fun _ ha => ha)
  have hKF : K ⊆ F.source := by rw [hsource]; exact hKold
  have hφW : range φ ⊆ W := himage.trans hKold
  refine ⟨F, hKF, (H.event i).regularCrossing_right_unique
    (hcrossF x (hKold x hx)) hcross, ?_, ?_, htransfer φ hφ hφW⟩
  · intro a ha
    exact hcrossF a (by change a ∈ (W : Set _); rwa [← hsource])
  · intro b hb
    exact hold b (by change (H.event i).oldTerminal b ∈ (W : Set _); rwa [← hsource])

theorem exists_cutoff_cap_survivor_chart_tolerance
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (K : Set (H.event i).incoming.terminalRegularOpen), IsCompact K → IsPreconnected K →
          (interior K).Nonempty →
          frontier K = range (fun b : Sphere 2 => boundary.map (b, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤
                ENNReal.ofReal D) →
            ∀ (x : (H.event i).incoming.terminalRegularOpen), x ∈ K →
              ∀ y : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val y →
              ∀ {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
                {Y : Type w} [TopologicalSpace Y] {I : ModelWithCorners ℝ G Y}
                {X : Type z} [TopologicalSpace X] [ChartedSpace Y X]
                (φ : X → (H.event i).incoming.terminalRegularOpen),
                IsSmoothEmbedding I ThreeModel ∞ φ → range φ ⊆ K →
                ∃ F : PartialDiffeomorph ThreeModel ThreeModel
                    (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
                  K ⊆ F.source ∧ F x = y ∧
                  (∀ a ∈ F.source, (H.event i).RegularCrossing a.val (F a)) ∧
                  (∀ b : (H.event i).old, (H.event i).oldTerminal b ∈ F.source →
                    F ((H.event i).oldTerminal b) = (H.event i).oldOutput b) ∧
                  ∃ ψ : X → (H.stage i.succ).Carrier, ψ = (F : _ → _) ∘ φ ∧
                    IsSmoothEmbedding I ThreeModel ∞ ψ ∧
                    (∀ a, (H.event i).RegularCrossing (φ a).val (ψ a)) ∧
                    (∀ (a : X) (b : (H.event i).old), (H.event i).oldTerminal b = φ a →
                      ψ a = (H.event i).oldOutput b) ∧
                    (∀ A : Set X, ψ '' A = (F : _ → _) '' (φ '' A)) ∧
                    ∀ (a : X) (v w : TangentSpace I a),
                      (H.event i).outputMetric.inner (ψ a) (mfderiv I ThreeModel ψ a v)
                        (mfderiv I ThreeModel ψ a w) =
                        (H.event i).terminal.metric.inner (φ a) (mfderiv I ThreeModel φ a v)
                          (mfderiv I ThreeModel φ a w) := by
  obtain ⟨eta, heta, hchart⟩ := exists_cutoff_cap_survivor_chart_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ epsb pb boundary hb s hs K hK hconn hKi hfront
    q hq hscalar hboundary hdiam
  exact hchart H i parameters R hOld hδ epsb pb boundary hb s hs K K Subset.rfl hK hconn
    hKi hfront q hq hscalar hboundary hdiam

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_cutoff_cap_protection_tolerance_of_scaled_subset
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (q : ℝ) (hq : 0 < q) (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (scaleMetric q hq (H.event i).terminal.metric) epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L → IsPreconnected K →
          (interior L).Nonempty →
          frontier L = range (fun z : Sphere 2 => boundary.map (z, s)) →
          (∀ x ∈ K, metricScalarAt (scaleMetric q hq (H.event i).terminal.metric) x ≤ C) →
          c ≤ metricScalarAt (scaleMetric q hq (H.event i).terminal.metric) pb →
          (∀ x ∈ K, ∀ y ∈ K,
            riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
          ∀ (x : (H.event i).incoming.terminalRegularOpen), x ∈ K →
            ∀ y : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val y →
            ∀ z ∈ K, z.val ∈ interior (Subtype.val '' (H.event i).old) := by
  obtain ⟨eta, heta, hprotect⟩ := exists_cutoff_cap_protection_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ q hq epsb pb boundary hb s hs L K hLK hL hK hLi hfront
    hscalar hboundary hdiam x hx y hcross
  have heq : scaleMetric q⁻¹ (inv_pos.mpr hq) (scaleMetric q hq (H.event i).terminal.metric) =
      (H.event i).terminal.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner]
    field_simp
  let nk : SpatialNeck (H.event i).terminal.metric epsb pb :=
    heq ▸ boundary.scaleMetric q⁻¹ (inv_pos.mpr hq)
  have hmap : nk.map = boundary.map := by
    have hcast {g h : SmoothRiemannianMetric ThreeModel (H.event i).incoming.terminalRegularOpen}
        (e : g = h) (n : SpatialNeck g epsb pb) :
        (e ▸ n : SpatialNeck h epsb pb).map = n.map := by
      cases e
      rfl
    exact (hcast heq (boundary.scaleMetric q⁻¹ (inv_pos.mpr hq))).trans rfl
  apply hprotect H i parameters R hOld hδ epsb pb nk hb s hs L K hLK hL hK hLi
    (by rw [hmap]; exact hfront) q hq ?_ ?_ hdiam x hx y hcross
  · intro z hz
    have h := hscalar z hz
    rw [metricScalarAt_scaleMetric, ← div_eq_inv_mul] at h
    exact (div_le_iff₀ hq).mp h
  · have h := hboundary
    rw [metricScalarAt_scaleMetric, ← div_eq_inv_mul] at h
    exact (le_div_iff₀ hq).mp h

theorem exists_cutoff_separation_tolerance_of_ricci_lower_bound
    {C D κ : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (∀ j, R.delta j ≤ eta) →
      ∀ (K : Set (H.event i).incoming.terminalRegularOpen) (q : ℝ) (hq : 0 < q),
        (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
        (∀ x ∈ K, ∀ y ∈ K,
          riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
        ∀ z ∈ K, (∀ v : TangentSpace ThreeModel z,
          κ * q * (H.event i).terminal.metric.inner z v v ≤
            ricciTensor (H.event i).terminal.metric z v v) →
        ∀ j, Disjoint (Subtype.val '' K)
          ((H.event i).transition.trace.tubes.tube j ''
            {w : TubeDomain | w.2.val ∈ Icc (-1 : ℝ) 1}) := by
  obtain ⟨eta, heta, hsep⟩ := exists_neck_separation_tolerance_of_ricci_lower_bound hC hD hκ
  refine ⟨min eta (1 / 12), lt_min heta (by norm_num), ?_⟩
  intro H i parameters R hδ K q hq hscalar hdiam z hz hRic j
  have hsmall : R.delta j < 1 / 11 :=
    ((hδ j).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hk : ⌈(R.delta j)⁻¹⌉₊ ≤ R.order j := by
    have hf := Nat.ceil_le_floor_add_one ((R.delta j)⁻¹)
    have horder := (le_max_right (parameters.modelOrder + 6)
      (2 * ⌊(R.delta j)⁻¹⌋₊ + 4)).trans (R.order_lower j)
    omega
  obtain ⟨cut, _, hmap⟩ := (R.neck j).exists_spatialNeck le_rfl hsmall hk
  have hdis := hsep _ (H.event i).terminal.metric (R.delta j) (R.neck j).center
    ((hδ j).trans (min_le_left _ _)) cut K q hq hscalar hdiam z hz hRic
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨w, hw, heq⟩
  have hNx : (R.neck j).chart ⟨(w.1, w.2.val), R.tube_in_buffer j w⟩ = x :=
    Subtype.ext ((R.tube_eq j w (R.tube_in_buffer j w)).symm.trans heq)
  apply Set.disjoint_left.mp hdis hx
  refine ⟨(w.1, w.2.val), ⟨mem_univ _, hw⟩, ?_⟩
  exact (hmap ⟨(w.1, w.2.val), R.tube_in_buffer j w⟩).trans hNx

theorem exists_cutoff_protection_tolerance_of_ricci_lower_bound
    {C D κ : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (K : Set (H.event i).incoming.terminalRegularOpen), IsPreconnected K →
        ∀ (q : ℝ) (hq : 0 < q),
        (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
        (∀ x ∈ K, ∀ y ∈ K,
          riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤ ENNReal.ofReal D) →
        ∀ z ∈ K, (∀ v : TangentSpace ThreeModel z,
          κ * q * (H.event i).terminal.metric.inner z v v ≤
            ricciTensor (H.event i).terminal.metric z v v) →
        ∀ x ∈ K, ∀ y : (H.stage i.succ).Carrier,
          (H.event i).RegularCrossing x.val y →
          ∀ w ∈ K, w.val ∈ interior (Subtype.val '' (H.event i).old) := by
  obtain ⟨eta, heta, hsep⟩ := exists_cutoff_separation_tolerance_of_ricci_lower_bound hC hD hκ
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ K hconn q hq hscalar hdiam z hz hRic x hx y hcross
  have hdis := hsep H i parameters R hδ K q hq hscalar hdiam z hz hRic
  apply (H.event i).subset_interior_old_of_isPreconnected hOld hconn _ hx hcross
  intro w hw
  let T := (H.event i).transition.trace.tubes
  let bands := ⋃ j, T.tube j '' {a : TubeDomain | a.2.val ∈ Icc (-1 : ℝ) 1}
  have hopen : IsOpen bandsᶜ := T.isCompact_iUnion_closedBand.isClosed.isOpen_compl
  have hsub : bandsᶜ ⊆ T.core := by
    intro a ha
    change a ∉ ⋃ j, T.removedBand j
    intro hm
    obtain ⟨j, b, hb, heq⟩ := mem_iUnion.mp hm
    exact ha (mem_iUnion.mpr ⟨j, b, ⟨hb.1.le, hb.2.le⟩, heq⟩)
  apply interior_maximal hsub hopen
  intro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact Set.disjoint_left.mp (hdis j) (mem_image_of_mem Subtype.val hw) hj


section

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem MetricCutCapEvent.exists_survivor_partialDiffeomorph_or_discarded_of_isPreconnected
    (E : MetricCutCapEvent P Q a s) (hOld : E.old = E.transition.trace.retainedCore)
    {K : Set E.incoming.terminalRegularOpen} (hK : IsPreconnected K)
    (hcore : ∀ x ∈ K, x.val ∈ interior E.transition.trace.tubes.core) :
    (∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      K ⊆ F.source ∧
      (∀ y ∈ F.source, E.RegularCrossing y.val (F y)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ F.source → F (E.oldTerminal z) = E.oldOutput z) ∧
      ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
        E.outputMetric.inner (F y) (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) y w) = E.terminal.metric.inner y v w) ∨
    ∀ x ∈ K, ∃ z : E.transition.trace.tubes.core, z.val = x.val ∧
      ∃ d : E.discarded.Carrier,
        E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z) = Sum.inr d := by
  classical
  by_cases hc : ∃ x ∈ K, ∃ q : Q.Carrier, E.RegularCrossing x.val q
  · obtain ⟨x, hx, q, hcross⟩ := hc
    have hKold := E.subset_interior_old_of_isPreconnected hOld hK hcore hx hcross
    let W : TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
      ⟨{y | y.val ∈ interior (Subtype.val '' E.old)},
        isOpen_interior.preimage continuous_subtype_val⟩
    obtain ⟨F, hsource, hcrossF, hold, hmetric⟩ :=
      E.exists_survivor_partialDiffeomorph W ⟨x, hKold x hx⟩ (fun _ hy => hy)
    left
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · rw [hsource]
      exact hKold
    · intro y hy
      apply hcrossF y
      rwa [hsource] at hy
    · intro z hz
      apply hold z
      rwa [hsource] at hz
    · intro y hy
      apply hmetric y
      rwa [hsource] at hy
  · right
    intro x hx
    let z : E.transition.trace.tubes.core := ⟨x.val, interior_subset (hcore x hx)⟩
    refine ⟨z, rfl, ?_⟩
    cases heq : E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z) with
    | inr d => exact ⟨d, rfl⟩
    | inl q =>
      have hz : z ∈ E.transition.trace.retainedCore := ⟨q, heq⟩
      have hxold : x.val ∈ interior (Subtype.val '' E.transition.trace.retainedCore) :=
        DifferentialGeometry.Topology.mem_interior_image_val_of_isOpen
          E.transition.trace.isClopen_retainedCore.isOpen hz (hcore x hx)
      obtain ⟨w, _, hw, _⟩ := E.exists_oldTerminal_eq_of_mem_interior_retained hOld x hxold
      exact (hc ⟨x, hx, E.oldOutput w, hw⟩).elim


end


theorem exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_tolerance
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (epsb : ℝ) (pb : (H.event i).incoming.terminalRegularOpen)
        (boundary : SpatialNeck (H.event i).terminal.metric epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L →
          IsPreconnected K → (interior L).Nonempty →
          frontier L = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            c * q ≤ metricScalarAt (H.event i).terminal.metric pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤
                ENNReal.ofReal D) →
            (∃ F : PartialDiffeomorph ThreeModel ThreeModel
                (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
              K ⊆ F.source ∧
              (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
              (∀ z : (H.event i).old, (H.event i).oldTerminal z ∈ F.source →
                F ((H.event i).oldTerminal z) = (H.event i).oldOutput z) ∧
              ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
                (H.event i).outputMetric.inner (F y)
                  (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
                  (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
                    (H.event i).terminal.metric.inner y v w) ∨
            ∀ x ∈ K, ∃ z : (H.event i).transition.trace.tubes.core, z.val = x.val ∧
              ∃ d : (H.event i).discarded.Carrier,
                (H.event i).transition.trace.presentation
                  ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d := by
  obtain ⟨eta, heta, hsep⟩ := exists_cutoff_cap_separation_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro H i parameters R hOld hδ epsb pb boundary hb s hs L K hLK hL hK hLi hfront
    q hq hscalar hboundary hdiam
  have hdis := hsep H i parameters R hδ epsb pb boundary hb s hs L K hLK hL hLi hfront
    q hq hscalar hboundary hdiam
  apply (H.event i).exists_survivor_partialDiffeomorph_or_discarded_of_isPreconnected hOld hK
  intro z hz
  let T := (H.event i).transition.trace.tubes
  let bands := ⋃ j, T.tube j '' {w : TubeDomain | w.2.val ∈ Icc (-1 : ℝ) 1}
  have hopen : IsOpen bandsᶜ := T.isCompact_iUnion_closedBand.isClosed.isOpen_compl
  have hsub : bandsᶜ ⊆ T.core := by
    intro w hw
    change w ∉ ⋃ j, T.removedBand j
    intro hm
    obtain ⟨j, a, ha, heq⟩ := mem_iUnion.mp hm
    exact hw (mem_iUnion.mpr ⟨j, a, ⟨ha.1.le, ha.2.le⟩, heq⟩)
  apply interior_maximal hsub hopen
  intro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact Set.disjoint_left.mp (hdis j) (mem_image_of_mem Subtype.val hz) hj


theorem exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_tolerance_of_sectional_lower_bound
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
      (parameters : CutoffParameters) (R : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, R.delta j ≤ eta) →
      ∀ (f : Sphere 2 → (H.event i).incoming.terminalRegularOpen),
        IsSmoothEmbedding I2 ThreeModel ∞ f →
        ∀ (L K : Set (H.event i).incoming.terminalRegularOpen), L ⊆ K → IsCompact L →
          IsPreconnected K → (interior L).Nonempty → frontier L = range f →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ C * q) →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (scaleMetric q hq (H.event i).terminal.metric) x y ≤
                ENNReal.ofReal D) →
            (∀ (z : Sphere 2) (u v : TangentSpace I2 z),
              (c * q) * ((H.event i).terminal.metric.inner (f z)
                (mfderiv I2 ThreeModel f z u) (mfderiv I2 ThreeModel f z u) *
                (H.event i).terminal.metric.inner (f z)
                  (mfderiv I2 ThreeModel f z v) (mfderiv I2 ThreeModel f z v) -
                ((H.event i).terminal.metric.inner (f z)
                  (mfderiv I2 ThreeModel f z u) (mfderiv I2 ThreeModel f z v)) ^ 2) ≤
              metricRm04StandardAt (H.event i).terminal.metric (f z)
                (mfderiv I2 ThreeModel f z u) (mfderiv I2 ThreeModel f z v)
                (mfderiv I2 ThreeModel f z v) (mfderiv I2 ThreeModel f z u)) →
            (∃ F : PartialDiffeomorph ThreeModel ThreeModel
                (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
              K ⊆ F.source ∧
              (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
              (∀ z : (H.event i).old, (H.event i).oldTerminal z ∈ F.source →
                F ((H.event i).oldTerminal z) = (H.event i).oldOutput z) ∧
              ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
                (H.event i).outputMetric.inner (F y)
                  (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
                  (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
                    (H.event i).terminal.metric.inner y v w) ∨
            ∀ x ∈ K, ∃ z : (H.event i).transition.trace.tubes.core, z.val = x.val ∧
              ∃ d : (H.event i).discarded.Carrier,
                (H.event i).transition.trace.presentation
                  ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d := by
  obtain ⟨eta, heta, hsep⟩ := exists_neck_cap_separation_tolerance_of_frontier_sectional_lower_bound hC hD hc
  refine ⟨min eta (1 / 12), lt_min heta (by norm_num), ?_⟩
  intro H i parameters R hOld hδ f hf L K hLK hL hK hLi hfront q hq hscalar hdiam hsec
  have hdis (j) : Disjoint (Subtype.val '' K)
      ((H.event i).transition.trace.tubes.tube j ''
        {z : TubeDomain | z.2.val ∈ Icc (-1 : ℝ) 1}) := by
    have hsmall : R.delta j < 1 / 11 :=
      ((hδ j).trans (min_le_right _ _)).trans_lt (by norm_num)
    have hk : ⌈(R.delta j)⁻¹⌉₊ ≤ R.order j := by
      have hh := Nat.ceil_le_floor_add_one ((R.delta j)⁻¹)
      have horder := (le_max_right (parameters.modelOrder + 6)
        (2 * ⌊(R.delta j)⁻¹⌋₊ + 4)).trans (R.order_lower j)
      omega
    obtain ⟨cut, _, hmap⟩ := (R.neck j).exists_spatialNeck le_rfl hsmall hk
    have hdis := hsep _ (H.event i).terminal.metric (R.delta j) (R.neck j).center
      ((hδ j).trans (min_le_left _ _)) cut f hf L K hLK hL hLi hfront q hq hscalar hdiam hsec
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hNx : (R.neck j).chart ⟨(z.1, z.2.val), R.tube_in_buffer j z⟩ = x :=
      Subtype.ext ((R.tube_eq j z (R.tube_in_buffer j z)).symm.trans heq)
    apply Set.disjoint_left.mp hdis hx
    refine ⟨(z.1, z.2.val), ⟨mem_univ _, hz⟩, ?_⟩
    exact (hmap ⟨(z.1, z.2.val), R.tube_in_buffer j z⟩).trans hNx
  apply (H.event i).exists_survivor_partialDiffeomorph_or_discarded_of_isPreconnected hOld hK
  intro z hz
  let T := (H.event i).transition.trace.tubes
  let bands := ⋃ j, T.tube j '' {w : TubeDomain | w.2.val ∈ Icc (-1 : ℝ) 1}
  have hopen : IsOpen bandsᶜ := T.isCompact_iUnion_closedBand.isClosed.isOpen_compl
  have hsub : bandsᶜ ⊆ T.core := by
    intro w hw
    change w ∉ ⋃ j, T.removedBand j
    intro hm
    obtain ⟨j, a, ha, heq⟩ := mem_iUnion.mp hm
    exact hw (mem_iUnion.mpr ⟨j, a, ⟨ha.1.le, ha.2.le⟩, heq⟩)
  apply interior_maximal hsub hopen
  intro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact Set.disjoint_left.mp (hdis j) (mem_image_of_mem Subtype.val hz) hj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
