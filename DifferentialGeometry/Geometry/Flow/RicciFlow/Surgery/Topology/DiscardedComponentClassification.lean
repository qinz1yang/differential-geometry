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
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private theorem exists_isPoincareStandard_discarded_boundary_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ (C1 C Q : ℝ), 1 ≤ C → 0 < Q →
          Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (∀ x : (H.stage i.castSucc).Carrier,
            ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
              Q ≤ (H.event i).incoming.flow.scalar t x →
                ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C x t,
                  W.capTubeHasNeckChart eps) →
          ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
            PhiAlmostNonnegative (H.event i).incoming.flow
              (Ico (H.time i.castSucc) (H.time i.succ)) Phi →
            ∀ _ : SmoothCutCapCompletion (H.event i).transition,
              ∀ (b : (H.event i).transition.trace.tubes.Boundary) (q : Sphere 2)
                (d : (H.event i).discarded.Carrier),
                (H.event i).transition.trace.presentation
                  ((H.event i).transition.trace.capping.coreInclusion
                    ((H.event i).transition.trace.tubes.coreBoundarySphere b q)) = Sum.inr d →
                  isPoincareStandard ((H.event i).discarded.toClosedOrientedManifold.component
                    (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨eta, heta, hpath⟩ := SphericalCapping.exists_cut_neck_standard_or_stopped_tolerance.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro eps heps H i parameters G hdelta C1 C Q hC hQ hprotected hscale hcanonical
    Phi hPhi hpinch hc b q d hd
  have hepspath : eps ≤ eta := heps.trans (min_le_left _ _)
  have hepscap : eps ≤ 1 / 8646 := heps.trans (min_le_right _ _)
  obtain ⟨d₀, hd₀, hneck⟩ := G.exists_late_spatialNecks
    (hepscap.trans_lt (by norm_num)) hdelta
  obtain ⟨d₁, hd₁, hcan⟩ := G.exists_late_canonical_on_discarded_core_with_cap_neck_charts
    hQ (zero_le_one.trans hC) hcanonical hPhi hpinch hprotected
  obtain ⟨d₂, hd₂, hcap⟩ :=
    G.exists_late_capCore_cutting_side_of_stopped_cylinder_of_cutting_scale hC hscale
  obtain ⟨t, htlow, htend⟩ := exists_between (max_lt hd₀.2 (max_lt hd₁.2 hd₂.2))
  have ht₀ : t ∈ Ioo d₀ (H.time i.succ) := ⟨(le_max_left _ _).trans_lt htlow, htend⟩
  have ht₁ : t ∈ Ioo d₁ (H.time i.succ) :=
    ⟨((le_max_left _ _).trans (le_max_right _ _)).trans_lt htlow, htend⟩
  have ht₂ : t ∈ Ioo d₂ (H.time i.succ) :=
    ⟨((le_max_right _ _).trans (le_max_right _ _)).trans_lt htlow, htend⟩
  choose neck _ hmap using hneck t ht₀
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
  have hdx : X.presentation (X.capping.coreInclusion (X.tubes.coreBoundarySphere b q)) =
      Sum.inr d :=
    (congrArg (H.event i).transition.presentation
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion (H.event i).transition hc _)).trans
        ((congrFun (H.event i).transition.presentation_eq _).trans hd)
  have hbq : (H.event i).transition.trace.tubes.coreBoundarySphere b q ∉
      (H.event i).transition.trace.retainedCore := by
    rintro ⟨z, hz⟩
    exact Sum.inr_ne_inl (hd.symm.trans hz)
  have hb : ¬ (H.event i).RetainedBoundary b := fun h => hbq (h q)
  rcases hpath eps hepspath (H.stage i.castSucc).toClosedOrientedManifold X.capped
      X.tubes X.capping ((H.event i).incoming.flow.base.metric t)
      (fun j => (G.neck j).center.val) neck (fun j z => (hmap j z).symm) b with hstd | hstop
  · obtain ⟨e⟩ := X.cappedDiscardedPresentationRealization (X.tubes.coreBoundarySphere b q) d hdx
    exact isPoincareStandard_of_diffeomorph e.val.symm (hstd q)
  · obtain ⟨R, p, nk, a, κ, hR, ha, hRzero, hRone, hinter, _, _, _, hstopped⟩ := hstop
    have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
      b q hbq R hR hRzero hinter
    have hpdiscard : nk.map (nk.center, a) ∈
        Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ := by
      apply hdiscard
      refine ⟨(κ.symm nk.center, 1), ⟨mem_univ _, by norm_num⟩, ?_⟩
      rw [hRone, κ.apply_symm_apply]
    obtain ⟨z, hz, hzp⟩ := hpdiscard
    obtain ⟨_, W, hW⟩ := hcan t ht₁ z hz
    have hwitness : ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C
        (nk.map (nk.center, a)) t, W.capTubeHasNeckChart eps := hzp ▸ ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := hwitness
    obtain ⟨K, hK, hfront, hdis⟩ := hcap t ht₂ eps C1 C hepscap le_rfl b hb R hR
      hRzero hinter p nk a ha κ hRone W' hW' hstopped
    exact X.isPoincareStandard_discardedComponent_of_capCore_cutting_side hK.some b hfront hdis q d hdx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

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
  obtain ⟨eta, heta, hboundary⟩ := exists_isPoincareStandard_discarded_boundary_tolerance.{u}
  refine ⟨min eta (1 / 44), lt_min heta (by norm_num), ?_⟩
  intro eps heps hsmall
  have hep := hsmall.trans (min_le_left _ _)
  obtain ⟨C, hC, hcanonical⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      heps ((hsmall.trans (min_le_right _ _)).trans_lt (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro P a s S L
  obtain ⟨Q, hQ, hcan⟩ := hcanonical P a s S
  obtain ⟨R, hR, hclass⟩ := L.exists_component_poincareStandard_threshold S
  refine ⟨max R Q, hR.trans_le (le_max_left _ _), ?_⟩
  intro H i hP ha hs hS hL
  cases hP
  cases ha
  cases hs
  cases eq_of_heq hS
  cases eq_of_heq hL
  intro parameters G hdelta hprotected hscale hc D
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      (H.event i).incoming.lt (H.event i).incoming.flow (H.event i).incoming.equation (by simp [ThreeSpace])
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
      ⟨b, q, hbq⟩ | hlocal
    · let y := X.tubes.coreBoundarySphere b q
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
            ((H.event i).transition.trace.tubes.coreBoundarySphere b q)) = Sum.inr d' :=
        (congrFun (H.event i).transition.presentation_eq _).symm.trans
          ((congrArg (H.event i).transition.presentation
            (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
              (H.event i).transition hc y)).symm.trans hd'.symm)
      have hbound := hboundary eps hep H i parameters G hdelta C C Q hC hQ
        ((le_max_right R Q).trans_lt hprotected) hscale hcan Phi hPhi hpinch hc b q d' hdy
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
      have hambient := hclass (ConnectedComponents.mk x.val) (by
        intro y hy
        have hyC : y.val ∈ (H.stage i.castSucc).toClosedOrientedManifold.componentSet
            (ConnectedComponents.mk x.val) := (ClosedOrientedManifold.mem_componentSet _ _ _).mpr hy
        have hycore := X.componentSet_subset_core_of_cutIndices_eq_empty _ hlocal hyC
        let z : X.tubes.core := ⟨y.val, hycore⟩
        have hn : z ∉ (H.event i).transition.trace.retainedCore :=
          (H.event i).transition.trace.connectedComponent_subset_compl_retainedCore x hxnot
            ((X.isPreconnected_coreComponentSet _ hlocal).subset_connectedComponent hx hyC)
        exact ((le_max_left R Q).trans_lt hprotected).trans
          (G.scalar_gt_protected_of_not_mem_retainedCore y hycore hn))
      exact X.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty _ hlocal x hx d hxd hambient
  change ConnectedComponents.mk (α := (H.event i).discarded.Carrier) d = D at hd
  exact hd ▸ hstd


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
