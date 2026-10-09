import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StoppedCapCuttingSide
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCanonicalCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutNeckPath
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSpatialNeck
import DifferentialGeometry.Topology.ThreeManifold.PuncturedCapClassification
import DifferentialGeometry.Topology.ThreeManifold.CoreComponentBoundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UncutDiscardedClassification

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private theorem exists_isPoincareStandard_discarded_boundary_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ (C q0 q : ℝ) (Ctime : ℝ≥0), 0 ≤ C → 0 < q0 →
          q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (∀ x : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q0 < (H.event i).incoming.flow.scalar t x →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
              Ctime * (H.event i).incoming.flow.scalar t x ^ 2) →
          (∀ x : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q < (H.event i).incoming.flow.scalar t x →
            ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps x) →
            ∃ U : Set (H.stage i.castSucc).Carrier,
              (∀ y ∈ U, ∀ z ∈ U, (H.event i).incoming.flow.scalar t y ≤ C * (H.event i).incoming.flow.scalar t z) ∧
              (U = connectedComponent x ∨
                ∃ V : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore V) ∧ V ⊆ U ∧
                  riemannianBallOf ((H.event i).incoming.flow.base.metric t) x
                    (1000 / Real.sqrt (metricScalarAt ((H.event i).incoming.flow.base.metric t) x)) ⊆ interior V)) →
          ∀ _ : SmoothCutCapCompletion (H.event i).transition,
              ∀ (b : (H.event i).transition.trace.tubes.Boundary) (z : Sphere 2)
                (d : (H.event i).discarded.Carrier),
                (H.event i).transition.trace.presentation
                  ((H.event i).transition.trace.capping.coreInclusion
                    ((H.event i).transition.trace.tubes.coreBoundarySphere b z)) = Sum.inr d →
                  isPoincareStandard ((H.event i).discarded.toClosedOrientedManifold.component
                    (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨eta, heta, hpath⟩ := SphericalCapping.exists_cut_neck_standard_or_stopped_tolerance.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro eps heps H i parameters G hdelta C q0 q Ctime hC hq0 hprotected hscale hbound hspatial
    hc b sphereMark d hd
  have hepspath : eps ≤ eta := heps.trans (min_le_left _ _)
  have hepscap : eps ≤ 1 / 8646 := heps.trans (min_le_right _ _)
  obtain ⟨d₀, hd₀, hneck⟩ := G.exists_late_spatialNecks
    (hepscap.trans_lt (by norm_num)) hdelta
  obtain ⟨d₁, hd₁, hhigh⟩ := G.exists_late_scalar_gt_on_discarded_core
    hq0 hbound hprotected
  obtain ⟨d₂, hd₂, hcap⟩ :=
    G.exists_late_capCore_cutting_side_of_spatial_cap_of_cutting_scale hC hscale
  obtain ⟨t, htlow, htend⟩ := exists_between (max_lt hd₀.2 (max_lt hd₁.2 hd₂.2))
  have ht₀ : t ∈ Ioo d₀ (H.time i.succ) := ⟨(le_max_left _ _).trans_lt htlow, htend⟩
  have ht₁ : t ∈ Ioo d₁ (H.time i.succ) :=
    ⟨((le_max_left _ _).trans (le_max_right _ _)).trans_lt htlow, htend⟩
  have ht₂ : t ∈ Ioo d₂ (H.time i.succ) :=
    ⟨((le_max_right _ _).trans (le_max_right _ _)).trans_lt htlow, htend⟩
  choose neck _ hmap using hneck t ht₀
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
  have hdx : X.presentation (X.capping.coreInclusion (X.tubes.coreBoundarySphere b sphereMark)) =
      Sum.inr d :=
    (congrArg (H.event i).transition.presentation
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion (H.event i).transition hc _)).trans
        ((congrFun (H.event i).transition.presentation_eq _).trans hd)
  have hbq : (H.event i).transition.trace.tubes.coreBoundarySphere b sphereMark ∉
      (H.event i).transition.trace.retainedCore := by
    rintro ⟨z, hz⟩
    exact Sum.inr_ne_inl (hd.symm.trans hz)
  have hb : ¬ (H.event i).RetainedBoundary b := fun h => hbq (h sphereMark)
  rcases hpath eps hepspath (H.stage i.castSucc).toClosedOrientedManifold X.capped
      X.tubes X.capping ((H.event i).incoming.flow.base.metric t)
      (fun j => (G.neck j).center.val) neck (fun j z => (hmap j z).symm) b with hstd | hstop
  · obtain ⟨e⟩ := X.cappedDiscardedPresentationRealization (X.tubes.coreBoundarySphere b sphereMark) d hdx
    exact isPoincareStandard_of_diffeomorph e.val.symm (hstd sphereMark)
  · obtain ⟨R, p, nk, a, κ, hR, ha, hRzero, hRone, hinter, _, _, _, hstopped⟩ := hstop
    have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
      b sphereMark hbq R hR hRzero hinter
    have hpdiscard : nk.map (nk.center, a) ∈
        Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ := by
      apply hdiscard
      refine ⟨(κ.symm nk.center, 1), ⟨mem_univ _, by norm_num⟩, ?_⟩
      rw [hRone, κ.apply_symm_apply]
    obtain ⟨z, hz, hzp⟩ := hpdiscard
    have hscalar : q < (H.event i).incoming.flow.scalar t (nk.map (nk.center, a)) :=
      hzp ▸ hhigh t ht₁ z hz
    have ht : t ∈ Ioo (H.time i.castSucc) (H.time i.succ) := ⟨hd₁.1.trans_lt ht₁.1, ht₁.2⟩
    obtain ⟨U, hcomparison, hmodels⟩ := hspatial (nk.map (nk.center, a)) t ht hscalar hstopped
    obtain ⟨K, hK, hfront, hdis⟩ := hcap t ht₂ eps hepscap b hb R hR
      hRzero hinter p nk a ha κ hRone U hcomparison hmodels
    exact X.isPoincareStandard_discardedComponent_of_capCore_cutting_side hK.some b hfront hdis sphereMark d hdx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u


theorem exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ (C q0 q : ℝ) (Ctime : ℝ≥0), 0 ≤ C → 0 < q0 →
          q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (∀ x : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q0 < (H.event i).incoming.flow.scalar t x →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
              Ctime * (H.event i).incoming.flow.scalar t x ^ 2) →
          (∀ x : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q < (H.event i).incoming.flow.scalar t x →
            ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps x) →
            ∃ U : Set (H.stage i.castSucc).Carrier,
              (∀ y ∈ U, ∀ z ∈ U, (H.event i).incoming.flow.scalar t y ≤ C * (H.event i).incoming.flow.scalar t z) ∧
              (U = connectedComponent x ∨
                ∃ V : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore V) ∧ V ⊆ U ∧
                  riemannianBallOf ((H.event i).incoming.flow.base.metric t) x
                    (1000 / Real.sqrt (metricScalarAt ((H.event i).incoming.flow.base.metric t) x)) ⊆ interior V)) →
          (∀ (c : ConnectedComponents (H.stage i.castSucc).Carrier) (t : ℝ), t ∈ Ioo (H.time i.castSucc) (H.time i.succ) →
            ∀ x : ((H.stage i.castSucc).toClosedOrientedManifold.component c).Carrier, q < (H.event i).incoming.flow.scalar t x.val →
            ¬ Nonempty (SpatialNeck (((H.event i).incoming.flow.base.metric t).restrictOpen ((H.stage i.castSucc).componentOpen c)) eps x) →
            Nonempty (PositiveComponent (M := ((H.stage i.castSucc).toClosedOrientedManifold.component c).Carrier) univ) ∨
            admitsConstantPositiveSectionalCurvature (I := ThreeModel)
              (M := ((H.stage i.castSucc).toClosedOrientedManifold.component c).Carrier) ∨
            ∃ (K : CompactDomain ((H.stage i.castSucc).toClosedOrientedManifold.component c).Carrier) (v : ((H.stage i.castSucc).toClosedOrientedManifold.component c).Carrier)
              (nk : SpatialNeck (((H.event i).incoming.flow.base.metric t).restrictOpen ((H.stage i.castSucc).componentOpen c)) eps v) (level : ℝ),
              0 < metricScalarAt (((H.event i).incoming.flow.base.metric t).restrictOpen ((H.stage i.castSucc).componentOpen c)) x ∧
              Nonempty (CapCore K.carrier) ∧ |level| ≤ 4 ∧
              frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, level)) ∧
              riemannianBallOf (((H.event i).incoming.flow.base.metric t).restrictOpen ((H.stage i.castSucc).componentOpen c)) x
                (1000 / Real.sqrt (metricScalarAt (((H.event i).incoming.flow.base.metric t).restrictOpen ((H.stage i.castSucc).componentOpen c)) x)) ⊆ interior K.carrier) →
          SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded := by
  obtain ⟨eta₀, heta₀, hboundary⟩ := exists_isPoincareStandard_discarded_boundary_tolerance.{u}
  obtain ⟨eta₁, heta₁, hcomponent⟩ :=
    OrientedThreeStage.IncomingSlab.exists_component_poincareStandard_tolerance_of_spatial_neighborhoods.{u}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro eps heps H i parameters G hdelta C q0 q Ctime hC hq0 hprotected hscale hbound hspatial hcomponentSpatial hc D
  have hep : eps ≤ eta₀ := heps.trans (min_le_left _ _)
  have hepc : eps ≤ eta₁ := heps.trans (min_le_right _ _)
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
  obtain ⟨x, d, hd, hxd⟩ := X.exists_core_presentation_eq_inr_component D
  have hxd' : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion x) = Sum.inr d :=
    (congrFun (H.event i).transition.presentation_eq _).symm.trans
      ((congrArg (H.event i).transition.presentation
        (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
          (H.event i).transition hc x)).symm.trans hxd)
  have hstd : isPoincareStandard
      ((H.event i).discarded.toClosedOrientedManifold.component (ConnectedComponents.mk d)).Carrier := by
    rcases X.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty x with
      ⟨b, sphereMark, hbq⟩ | hlocal
    · let y := X.tubes.coreBoundarySphere b sphereMark
      have hconn : ConnectedComponents.mk (X.capping.coreInclusion y) =
          ConnectedComponents.mk (X.capping.coreInclusion x) := by
        have hmk : ConnectedComponents.mk y = ConnectedComponents.mk x :=
          ConnectedComponents.coe_eq_coe'.mpr hbq
        exact congrArg X.capping.coreInclusion.continuous.connectedComponentsMap hmk
      have hpres : ConnectedComponents.mk (X.presentation (X.capping.coreInclusion y)) =
          ConnectedComponents.mk (Sum.inr d : (H.stage i.succ).toClosedOrientedManifold.Carrier ⊕ X.discarded.Carrier) := by
        have hh := congrArg X.presentation.continuous.connectedComponentsMap hconn
        simpa only [Continuous.connectedComponentsMap_mk, hxd] using hh
      have hrange : X.presentation (X.capping.coreInclusion y) ∈
          range (@Sum.inr (H.stage i.succ).toClosedOrientedManifold.Carrier X.discarded.Carrier) :=
        isClopen_range_inr.connectedComponent_subset (mem_range_self d)
          (ConnectedComponents.coe_eq_coe'.mp hpres)
      obtain ⟨d', hd'⟩ := hrange
      have hdy : (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.coreInclusion
            ((H.event i).transition.trace.tubes.coreBoundarySphere b sphereMark)) = Sum.inr d' :=
        (congrFun (H.event i).transition.presentation_eq _).symm.trans
          ((congrArg (H.event i).transition.presentation
            (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
              (H.event i).transition hc y)).symm.trans hd'.symm)
      have hbound := hboundary eps hep H i parameters G hdelta C q0 q Ctime hC hq0
        hprotected hscale hbound hspatial hc b sphereMark d' hdy
      let r : (H.stage i.succ).toClosedOrientedManifold.Carrier ⊕ X.discarded.Carrier →
          X.discarded.Carrier := Sum.elim (fun _ => d) id
      have hr : Continuous r := continuous_const.sumElim continuous_id
      have heq : ConnectedComponents.mk d' = ConnectedComponents.mk d := by
        have hh := congrArg hr.connectedComponentsMap hpres
        rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk, ← hd'] at hh
        exact hh
      exact heq ▸ hbound
    · have hxnot : x ∉ (H.event i).transition.trace.retainedCore := by
        rintro ⟨q, hq⟩
        exact Sum.inr_ne_inl (hxd'.symm.trans hq)
      have hx : x ∈ X.coreComponentSet (ConnectedComponents.mk x.val) :=
        (ClosedOrientedManifold.mem_componentSet _ _ _).mpr rfl
      have hambient := hcomponent eps hepc (H.stage i.castSucc) (H.time i.castSucc)
        (H.time i.succ) (H.event i).incoming (H.event i).terminal q0 q
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ Ctime hq0 hprotected hbound
        (ConnectedComponents.mk x.val) (hcomponentSpatial (ConnectedComponents.mk x.val)) (by
        intro y hy
        have hyC : y.val ∈ (H.stage i.castSucc).toClosedOrientedManifold.componentSet
            (ConnectedComponents.mk x.val) := (ClosedOrientedManifold.mem_componentSet _ _ _).mpr hy
        have hycore := X.componentSet_subset_core_of_cutIndices_eq_empty _ hlocal hyC
        let z : X.tubes.core := ⟨y.val, hycore⟩
        have hn : z ∉ (H.event i).transition.trace.retainedCore :=
          (H.event i).transition.trace.connectedComponent_subset_compl_retainedCore x hxnot
            ((X.isPreconnected_coreComponentSet _ hlocal).subset_connectedComponent hx hyC)
        exact G.scalar_gt_protected_of_not_mem_retainedCore y hycore hn)
      exact X.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty _ hlocal x hx d hxd hambient
  change ConnectedComponents.mk (α := (H.event i).discarded.Carrier) d = D at hd
  exact hd ▸ hstd


theorem exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ C1 C2 q : ℝ, 1 ≤ C2 → 0 < q →
          q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C2 ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (∀ x : (H.stage i.castSucc).Carrier,
            ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
              q < (H.event i).incoming.flow.scalar t x →
                ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t,
                  W.capTubeHasNeckChart eps) →
          ∀ Ctime : ℝ≥0, (∀ x : (H.stage i.castSucc).Carrier,
            ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
              q < (H.event i).incoming.flow.scalar t x →
                |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
                  Ctime * (H.event i).incoming.flow.scalar t x ^ 2) →
          SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded := by
  obtain ⟨eta, heta, hclass⟩ := exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps H i parameters G hdelta C1 C2 q hC2 hq hprotected hscale hcanonical Ctime hbound hc
  apply hclass eps heps H i parameters G hdelta (C2 ^ 2) q q
    Ctime (sq_nonneg C2) hq hprotected hscale hbound ?_ ?_ hc
  · intro x t ht hx hstop
    obtain ⟨W, _⟩ := hcanonical x t ht hx
    refine ⟨W.domain.carrier, (fun y hy z hz => W.scalar_le_sq_mul_at_mem_domain hz y hy), ?_⟩
    cases htag : W.alternative with
    | neck data => exact (hstop ⟨data.strong.toSpatialNeck⟩).elim
    | positive whole data sec => exact Or.inl whole
    | round whole data => exact Or.inl whole
    | cap data depth =>
      refine Or.inr ⟨data.core.carrier, ⟨data.coreModel⟩, data.core_inside.trans interior_subset, ?_⟩
      have hball := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
        ((H.event i).incoming.flow.base.metric t) data.center_inside
        (r := ENNReal.ofReal (10000 / Real.sqrt ((H.event i).incoming.flow.scalar t x))) (by
          intro z hz
          have hztube : z ∈ data.tube := (data.overlap_eq.symm ▸ hz).2
          exact (ENNReal.ofReal_le_ofReal (depth z hztube)).trans ENNReal.ofReal_toReal_le)
      intro z hz
      exact hball (hz.trans_le (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))))
  · intro c t ht x hqx hx
    let U := (H.stage i.castSucc).componentOpen c
    let xU : U := ⟨x.val, x.property⟩
    let _ : CompactSpace U := ((H.stage i.castSucc).toClosedOrientedManifold.component c).compact
    let _ : SigmaCompactSpace U := inferInstance
    have hU : (U : Set (H.stage i.castSucc).Carrier) = connectedComponent (xU : (H.stage i.castSucc).Carrier) := by
      ext y
      change ConnectedComponents.mk y = c ↔ y ∈ connectedComponent (xU : (H.stage i.castSucc).Carrier)
      constructor
      · intro hy
        exact ConnectedComponents.coe_eq_coe'.mp (hy.trans xU.property.symm)
      · intro hy
        exact (ConnectedComponents.coe_eq_coe'.mpr hy).trans xU.property
    obtain ⟨W, hchart⟩ := hcanonical x.val t ht hqx
    rcases W.spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
        U xU hU hchart hx with hp | hr | hc
    · exact Or.inl hp
    · obtain ⟨z, hr⟩ := hr
      exact Or.inr (Or.inl
        (admitsConstantPositiveSectionalCurvature_of_roundComponent
          ((H.stage i.castSucc).toClosedOrientedManifold.component c) hr.some))
    · exact Or.inr (Or.inr hc)


theorem exists_poincareStandardDiscarded_cutting_scale_of_incoming :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eta →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (S : P.IncomingSlab a s) (L : S.TerminalLimitMetric),
        ∃ R : ℝ, 0 < R ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
          H.stage i.castSucc = P → H.time i.castSucc = a → H.time i.succ = s →
          HEq (H.event i).incoming S → HEq (H.event i).terminal L →
          ∀ (parameters : CutoffParameters) (G : GeometricCutoffRecord H i parameters),
            (∀ j, G.delta j ≤ eps) →
            R < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
            (∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
              (G.neck j).scale) →
            SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded := by
  obtain ⟨eta, heta, hclass⟩ := exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods.{u}
  refine ⟨min eta (1 / 44), lt_min heta (by norm_num), ?_⟩
  intro eps heps hsmall
  obtain ⟨C, hC, hcanonical⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      heps ((hsmall.trans (min_le_right _ _)).trans_lt (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro P a s S L
  obtain ⟨Q, hQ, hcan⟩ := hcanonical P a s S
  refine ⟨Q + 1, by linarith, ?_⟩
  intro H i hP ha hs hS hL
  cases hP
  cases ha
  cases hs
  cases eq_of_heq hS
  cases eq_of_heq hL
  intro parameters G hdelta hprotected hscale hc
  exact hclass eps (hsmall.trans (min_le_left _ _)) H i parameters G hdelta C C Q hC hQ
    (by linarith) hscale (fun x t ht hx => hcan x t ⟨ht.1.le, ht.2⟩ hx.le)
    ⟨C, zero_le_one.trans hC⟩
    (fun x t ht hx => (hcan x t ⟨ht.1.le, ht.2⟩ hx.le).choose.time_derivative) hc


theorem exists_poincareStandardDiscarded_cutting_scale :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eta →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
        ∃ L : ℝ, 0 < L ∧ ∀ (parameters : CutoffParameters)
          (G : GeometricCutoffRecord H i parameters),
          (∀ j, G.delta j ≤ eps) →
          L < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded := by
  obtain ⟨eta, heta, hclass⟩ := exists_poincareStandardDiscarded_cutting_scale_of_incoming.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps hsmall
  obtain ⟨C, hC, hCclass⟩ := hclass eps heps hsmall
  refine ⟨C, hC, ?_⟩
  intro H i
  obtain ⟨L, hL, hLclass⟩ := hCclass (H.stage i.castSucc) (H.time i.castSucc)
    (H.time i.succ) (H.event i).incoming (H.event i).terminal
  exact ⟨L, hL, hLclass H i rfl rfl rfl HEq.rfl HEq.rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
