import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CompactComponentSpatialClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentClassification

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

open private exists_retained_coreComponent_subset_interior_of_closedBand_subset from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StoppedCapCuttingSide

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_late_spatiallyCanonical_on_discarded_core
    {eps C1 C2 Q : ℝ} {Ctime : ℝ≥0} (hQ : 0 < Q)
    (hcanonical : (H.event i).incoming.SpatiallyCanonicalBefore eps C1 C2 Q (H.time i.succ))
    (hbound : (H.event i).incoming.DerivativeBoundBefore Ctime Q (H.time i.succ))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative (H.event i).incoming.flow
      (Ico (H.time i.castSucc) (H.time i.succ)) Phi)
    (hprotected : Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ),
        ∀ z : (H.event i).transition.trace.tubes.core,
          z ∉ (H.event i).transition.trace.retainedCore →
            Q < (H.event i).incoming.flow.scalar t z.val ∧
              ∃ W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t)
                eps C1 C2 z.val, W.capTubeHasNeckChart eps := by
  let _ := (H.event i).transition.core_compact
  let F := Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ
  have hF : IsCompact F :=
    (H.event i).transition.trace.isClopen_retainedCore.compl.isClosed.isCompact.image
      continuous_subtype_val
  have hlow : ∀ x : (H.event i).incoming.terminalRegularOpen,
      x.val ∈ F → ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
        metricScalarAt (H.event i).terminal.metric x := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hxcore : x.val ∈ (H.event i).transition.trace.tubes.core := hzx ▸ z.property
    apply G.scalar_gt_protected_of_not_mem_retainedCore x hxcore
    exact (Subtype.ext hzx : z = ⟨x.val, hxcore⟩) ▸ hz
  obtain ⟨d, hd, hhigh⟩ := (H.event i).terminal.eventually_scalar_gt_on_closed_set
    hQ hbound hPhi hpinch hF.isClosed hprotected hlow
  refine ⟨d, hd, ?_⟩
  intro t ht z hz
  have h := hhigh t ht z.val ⟨z, hz, rfl⟩
  exact ⟨h, hcanonical z.val t ⟨hd.1.trans_lt ht.1, ht.2⟩ h⟩

include G in
theorem exists_late_not_closedBand_subset_spatialWitness_domain_of_cutting_scale
    {C : ℝ} (hC : 1 ≤ C)
    (hscale : ∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ (eps C1 C2 : ℝ), C2 ≤ C →
        ∀ (x : (H.stage i.castSucc).Carrier)
          (W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t) eps C1 C2 x),
          ∀ K ⊆ W.domain.carrier,
            frontier K ⊆ Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ →
            ∀ j : (H.event i).transition.trace.tubes.Index,
              ¬ (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K := by
  classical
  let A := ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hmarg (j : (H.event i).transition.trace.tubes.Index) :
      ∀ᶠ η : ℝ in 𝓝 (0 : ℝ), C ^ 2 * (A + η) < (G.neck j).scale := by
    have ht : Tendsto (fun η : ℝ => C ^ 2 * (A + η)) (𝓝 0) (𝓝 (C ^ 2 * A)) := by
      have ht₀ := (tendsto_const_nhds (x := A)).add (tendsto_id (x := (𝓝 (0 : ℝ))))
      have ht₁ := ht₀.const_mul (C ^ 2)
      simpa only [id_eq, add_zero] using ht₁
    exact ht.eventually_lt_const (hscale j)
  have hall : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, C ^ 2 * (A + η) < (G.neck j).scale :=
    (eventually_all.mpr hmarg).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, hηscale, hη⟩ := (hall.and self_mem_nhdsWithin).exists
  have hηpos : 0 < η := hη
  obtain ⟨d₀, hd₀, hanchors⟩ := G.exists_late_retained_component_scalar_anchors hηpos
  have hseed (j : (H.event i).transition.trace.tubes.Index) :
      ∀ᶠ t in 𝓝[<] H.time i.succ,
        C ^ 2 * (A + η) < (H.event i).incoming.flow.scalar t (G.neck j).center.val := by
    have hh : Tendsto (fun t => metricScalarAt ((H.event i).incoming.flow.base.metric t)
        (G.neck j).center.val) (𝓝[<] H.time i.succ) (𝓝 (G.neck j).scale) := by
      simpa only [(G.neck j).scale_scalar] using
        (H.event i).terminal.tendsto_metricScalarAt (G.neck j).center
    exact hh.eventually_const_lt (hηscale j)
  obtain ⟨d₁, hd₁, hseeds⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (H.event i).incoming.lt).mp
      (eventually_all.mpr hseed)
  refine ⟨max d₀ d₁, ⟨hd₀.1.trans (le_max_left _ _), max_lt hd₀.2 hd₁.2⟩, ?_⟩
  intro t ht eps C1 C2 hC2 x W K hKW hfront j hband
  obtain ⟨z, hz, hinside⟩ :=
    exists_retained_coreComponent_subset_interior_of_closedBand_subset G j hband hfront
  obtain ⟨y, hycore, hymk, _, hyscalar⟩ := hanchors z hz
  have hyK : y.val ∈ K := interior_subset
    (hinside ⟨⟨y.val, hycore⟩, ConnectedComponents.coe_eq_coe'.mp hymk, rfl⟩)
  have hcut : (G.neck j).center.val ∈ K := by
    apply hband
    let q : TubeDomain := ((G.neck j).sphereMark, ⟨0, by norm_num⟩)
    refine ⟨q, by norm_num [q], ?_⟩
    rw [G.tube_eq j q (G.tube_in_buffer j q)]
    exact congrArg Subtype.val (G.neck j).marked
  have hC2pos : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hxupper : (H.event i).incoming.flow.scalar t x ≤
      C2 * (H.event i).incoming.flow.scalar t y.val := by
    have hh := mul_le_mul_of_nonneg_left (W.scalar_bounds y.val (hKW hyK)).1 hC2pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul] at hh
  have hypos : 0 < (H.event i).incoming.flow.scalar t y.val :=
    (mul_pos (inv_pos.mpr hC2pos) W.Q_pos).trans_le (W.scalar_bounds y.val (hKW hyK)).1
  have htwice : (H.event i).incoming.flow.scalar t (G.neck j).center.val ≤
      C ^ 2 * (H.event i).incoming.flow.scalar t y.val := by
    have hupper := (W.scalar_bounds (G.neck j).center.val (hKW hcut)).2
    have hC2square : C2 ^ 2 ≤ C ^ 2 := sq_le_sq₀ hC2pos.le hCpos.le |>.mpr hC2
    calc
      _ ≤ C2 * (C2 * (H.event i).incoming.flow.scalar t y.val) :=
        hupper.trans (mul_le_mul_of_nonneg_left hxupper hC2pos.le)
      _ = C2 ^ 2 * (H.event i).incoming.flow.scalar t y.val := by ring
      _ ≤ C ^ 2 * (H.event i).incoming.flow.scalar t y.val :=
        mul_le_mul_of_nonneg_right hC2square hypos.le
  have hylt := hyscalar t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
  have hh := htwice.trans_lt (mul_lt_mul_of_pos_left hylt (sq_pos_of_pos hCpos))
  exact (not_lt_of_ge hh.le) (hseeds ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩ j)

include G in
theorem exists_late_capCore_cutting_side_of_stopped_cylinder_of_spatialWitness
    {C : ℝ} (hC : 1 ≤ C)
    (hscale : ∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ eps C1 C2 : ℝ, eps ≤ 1 / 8646 → C2 ≤ C →
        ∀ b : (H.event i).transition.trace.tubes.Boundary,
          ¬ (H.event i).RetainedBoundary b →
          ∀ R : PartialDiffeomorph IC I3 Cylinder (H.stage i.castSucc).Carrier ∞,
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source →
            (∀ q : Sphere 2, R (q, 0) = (H.event i).transition.trace.tubes.boundarySphere b q) →
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
              (⋃ j, (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
              range ((H.event i).transition.trace.tubes.boundarySphere b) →
            ∀ (p : (H.stage i.castSucc).Carrier)
              (nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps p)
              (a : ℝ), |a| ≤ 4 →
              ∀ κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                (∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a)) →
                ∀ W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t)
                    eps C1 C2 (nk.map (nk.center, a)),
                  W.capTubeHasNeckChart eps →
                  ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps
                    (nk.map (nk.center, a))) →
                  ∃ K : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore K) ∧
                      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
                      Disjoint K ((H.event i).transition.trace.tubes.removedBand b.1) := by
  obtain ⟨d, hd, hexclude⟩ :=
    G.exists_late_not_closedBand_subset_spatialWitness_domain_of_cutting_scale hC hscale
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 heps hC2 b hb R hR hRzero hinter p nk a ha κ hRone W hchart hstop
  obtain ⟨q₀, hq₀⟩ := not_forall.mp hb
  have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
    b q₀ hq₀ R hR hRzero hinter
  let _ : LocallyConnectedSpace (H.stage i.castSucc).Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace (H.stage i.castSucc).Carrier
  have hwhole : W.domain.carrier ≠ connectedComponent (nk.map (nk.center, a)) := by
    intro heq
    apply hexclude t ht eps C1 C2 hC2 _ W W.domain.carrier subset_rfl _ b.1
    · rw [heq]
      have hpoint : R (κ.symm nk.center, 1) = nk.map (nk.center, a) := by
        rw [hRone, κ.apply_symm_apply]
      rw [← hpoint]
      exact (H.event i).transition.trace.tubes.closedBand_subset_connectedComponent_of_cylinder
        b R (R.contMDiffOn_toFun.continuousOn.mono hR) hRzero (κ.symm nk.center)
    · rw [heq, isClopen_connectedComponent.frontier_eq]
      exact empty_subset _
  have hcapdata : ∃ (U : Set (H.stage i.castSucc).Carrier), Nonempty (CapCore U) ∧
      U ⊆ W.domain.carrier ∧
      riemannianBallOf ((H.event i).incoming.flow.base.metric t) (nk.map (nk.center, a))
        (1000 / Real.sqrt (metricScalarAt ((H.event i).incoming.flow.base.metric t)
          (nk.map (nk.center, a)))) ⊆ interior U := by
    cases htag : W.alternative with
    | neck data => exact (hstop ⟨data.neck⟩).elim
    | positive whole data sec => exact (hwhole whole).elim
    | round whole data => exact (hwhole whole).elim
    | cap data depth =>
      obtain ⟨U, _, _, hU, _, _, hUW, _, _, hball⟩ :=
        W.exists_capCore_with_neck_frontier hchart data depth htag
      exact ⟨U.carrier, hU, hUW, hball⟩
  obtain ⟨U, hU, hUW, hball⟩ := hcapdata
  have hslab := nk.image_slab_subset_of_ball_subset heps nk.center ha rfl hball
  have hlevel : |a| < eps⁻¹ := ha.trans_lt
    ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small]))
  obtain ⟨K, hK, _, _, hKfront, hKU⟩ :=
    hU.some.exists_capCore_side_of_sphere_embedding (fun q : Sphere 2 => nk.map (q, a))
      (nk.isSmoothEmbedding_level hlevel)
      (by
        rintro z ⟨q, rfl⟩
        exact hslab ⟨(q, a), ⟨mem_univ _, abs_le.mp ha⟩, rfl⟩)
  have hupperRange : range (fun q : Sphere 2 => R (q, 1)) =
      range (fun q : Sphere 2 => nk.map (q, a)) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨κ q, (hRone q).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨κ.symm q, ?_⟩
      change R (κ.symm q, 1) = nk.map (q, a)
      rw [hRone, κ.apply_symm_apply]
  rcases (H.event i).transition.trace.tubes.closedBand_subset_or_capCore_union_cylinder_cutting_side
      hK.some b R hR hRzero hinter (hKfront.trans hupperRange.symm) with hcaptured | hside
  · exfalso
    apply hexclude t ht eps C1 C2 hC2 _ W K (hKU.trans (interior_subset.trans hUW)) _
      b.1 (hcaptured.2.trans interior_subset)
    rw [hKfront, ← hupperRange]
    rintro z ⟨q, rfl⟩
    exact hdiscard ⟨(q, 1), ⟨mem_univ _, by norm_num⟩, rfl⟩
  · exact ⟨_, hside⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private theorem exists_isPoincareStandard_discarded_boundary_tolerance_of_spatiallyCanonical :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ (C1 C Q : ℝ), 1 ≤ C → 0 < Q →
          Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (H.event i).incoming.SpatiallyCanonicalBefore eps C1 C Q (H.time i.succ) →
          ∀ Ctime : ℝ≥0, (H.event i).incoming.DerivativeBoundBefore Ctime Q (H.time i.succ) →
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
    Ctime hbound Phi hPhi hpinch hc b q d hd
  have hepspath : eps ≤ eta := heps.trans (min_le_left _ _)
  have hepscap : eps ≤ 1 / 8646 := heps.trans (min_le_right _ _)
  obtain ⟨d₀, hd₀, hneck⟩ := G.exists_late_spatialNecks
    (hepscap.trans_lt (by norm_num)) hdelta
  obtain ⟨d₁, hd₁, hcan⟩ := G.exists_late_spatiallyCanonical_on_discarded_core
    hQ hcanonical hbound hPhi hpinch hprotected
  obtain ⟨d₂, hd₂, hcap⟩ :=
    G.exists_late_capCore_cutting_side_of_stopped_cylinder_of_spatialWitness hC hscale
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
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
        (H.event i).transition hc _)).trans
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
    have hwitness : ∃ W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t)
        eps C1 C (nk.map (nk.center, a)), W.capTubeHasNeckChart eps := hzp ▸ ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := hwitness
    obtain ⟨K, hK, hfront, hdis⟩ := hcap t ht₂ eps C1 C hepscap le_rfl b hb R hR
      hRzero hinter p nk a ha κ hRone W' hW' hstopped
    exact X.isPoincareStandard_discardedComponent_of_capCore_cutting_side hK.some b hfront hdis
      q d hdx

open OrientedThreeStage.IncomingSlab
  (exists_component_poincareStandard_tolerance_of_spatiallyCanonical) in
theorem exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (G : GeometricCutoffRecord H i parameters),
        (∀ j, G.delta j ≤ eps) →
        ∀ C1 C2 q : ℝ, 1 ≤ C2 → 0 < q →
          q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
          (∀ j, C2 ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
            (G.neck j).scale) →
          (H.event i).incoming.SpatiallyCanonicalBefore eps C1 C2 q (H.time i.succ) →
          ∀ Ctime : ℝ≥0, (H.event i).incoming.DerivativeBoundBefore Ctime q (H.time i.succ) →
          SmoothCutCapCompletion (H.event i).transition →
            (H.event i).poincareStandardDiscarded := by
  obtain ⟨eta₀, heta₀, hboundary⟩ :=
    exists_isPoincareStandard_discarded_boundary_tolerance_of_spatiallyCanonical.{u}
  obtain ⟨eta₁, heta₁, hcomponent⟩ :=
    exists_component_poincareStandard_tolerance_of_spatiallyCanonical.{u}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro eps heps H i parameters G hdelta C1 C2 q hC2 hq hprotected hscale hcanonical
    Ctime hbound hc D
  have hep : eps ≤ eta₀ := heps.trans (min_le_left _ _)
  have hepc : eps ≤ eta₁ := heps.trans (min_le_right _ _)
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      (H.event i).incoming.lt (H.event i).incoming.flow (H.event i).incoming.equation
      (by simp [ThreeSpace])
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
  obtain ⟨x, d, hd, hxd⟩ := X.exists_core_presentation_eq_inr_component D
  have hxd' : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion x) = Sum.inr d :=
    (congrFun (H.event i).transition.presentation_eq _).symm.trans
      ((congrArg (H.event i).transition.presentation
        (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
          (H.event i).transition hc x)).symm.trans hxd)
  have hstd : isPoincareStandard
      ((H.event i).discarded.toClosedOrientedManifold.component
        (ConnectedComponents.mk d)).Carrier := by
    rcases X.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty x with
      ⟨b, sphereMark, hbq⟩ | hlocal
    · let y := X.tubes.coreBoundarySphere b sphereMark
      have hconn : ConnectedComponents.mk (X.capping.coreInclusion y) =
          ConnectedComponents.mk (X.capping.coreInclusion x) := by
        have hmk : ConnectedComponents.mk y = ConnectedComponents.mk x :=
          ConnectedComponents.coe_eq_coe'.mpr hbq
        exact congrArg X.capping.coreInclusion.continuous.connectedComponentsMap hmk
      have hpres : ConnectedComponents.mk (X.presentation (X.capping.coreInclusion y)) =
          ConnectedComponents.mk (Sum.inr d :
            (H.stage i.succ).toClosedOrientedManifold.Carrier ⊕ X.discarded.Carrier) := by
        have hh := congrArg X.presentation.continuous.connectedComponentsMap hconn
        simpa only [Continuous.connectedComponentsMap_mk, hxd] using hh
      have hrange : X.presentation (X.capping.coreInclusion y) ∈
          range (@Sum.inr (H.stage i.succ).toClosedOrientedManifold.Carrier
            X.discarded.Carrier) :=
        isClopen_range_inr.connectedComponent_subset (mem_range_self d)
          (ConnectedComponents.coe_eq_coe'.mp hpres)
      obtain ⟨d', hd'⟩ := hrange
      have hdy : (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.coreInclusion
            ((H.event i).transition.trace.tubes.coreBoundarySphere b sphereMark)) =
              Sum.inr d' :=
        (congrFun (H.event i).transition.presentation_eq _).symm.trans
          ((congrArg (H.event i).transition.presentation
            (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
              (H.event i).transition hc y)).symm.trans hd'.symm)
      have hstdb := hboundary eps hep H i parameters G hdelta C1 C2 q hC2 hq
        hprotected hscale hcanonical Ctime hbound Phi hPhi hpinch hc b sphereMark d' hdy
      let r : (H.stage i.succ).toClosedOrientedManifold.Carrier ⊕ X.discarded.Carrier →
          X.discarded.Carrier := Sum.elim (fun _ => d) id
      have hr : Continuous r := continuous_const.sumElim continuous_id
      have heq : ConnectedComponents.mk d' = ConnectedComponents.mk d := by
        have hh := congrArg hr.connectedComponentsMap hpres
        rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
          ← hd'] at hh
        exact hh
      exact heq ▸ hstdb
    · have hxnot : x ∉ (H.event i).transition.trace.retainedCore := by
        rintro ⟨q, hq⟩
        exact Sum.inr_ne_inl (hxd'.symm.trans hq)
      have hx : x ∈ X.coreComponentSet (ConnectedComponents.mk x.val) :=
        (ClosedOrientedManifold.mem_componentSet _ _ _).mpr rfl
      have hambient := hcomponent eps hepc (H.stage i.castSucc) (H.time i.castSucc)
        (H.time i.succ) (H.event i).incoming (H.event i).terminal C1 C2 q
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ hq hprotected hcanonical
        Ctime hbound (ConnectedComponents.mk x.val) (by
        intro y hy
        have hyC : y.val ∈ (H.stage i.castSucc).toClosedOrientedManifold.componentSet
            (ConnectedComponents.mk x.val) :=
          (ClosedOrientedManifold.mem_componentSet _ _ _).mpr hy
        have hycore := X.componentSet_subset_core_of_cutIndices_eq_empty _ hlocal hyC
        let z : X.tubes.core := ⟨y.val, hycore⟩
        have hn : z ∉ (H.event i).transition.trace.retainedCore :=
          (H.event i).transition.trace.connectedComponent_subset_compl_retainedCore x hxnot
            ((X.isPreconnected_coreComponentSet _ hlocal).subset_connectedComponent hx hyC)
        exact G.scalar_gt_protected_of_not_mem_retainedCore y hycore hn)
      exact X.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty _ hlocal x hx d hxd
        hambient
  change ConnectedComponents.mk (α := (H.event i).discarded.Carrier) d = D at hd
  exact hd ▸ hstd

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
