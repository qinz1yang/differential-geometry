import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NoLeftNonCore_S51
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryPieceLift_S34

/-!
# CH12-S51 G2a: the stage-level collar `φ i` of the non-core block data, `hsm` and `hcol`

For the seam index `idx = (cidxEquiv_S19 D ht C).symm i` (core `c`, cusp `q`), the collar
`φ i = (cores.map c t ht ∘ (D.truncation c).cuspMap q)` corestricted to the component `C`
(its `val` equals the stage map on `cuspDomain`), is smooth on `cuspDomain` (`hsm`) and agrees with
the seam collar `(componentFamily_S19 D ht C).collar i` below height one (`hcol`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

/-- Corestriction of a smooth map on `cuspDomain` to a connected component of the stage. -/
theorem exists_compLift_S51 {Q : OrientedThreeStage.{u}} (C : ConnectedComponents Q.toClosedOrientedManifold.Carrier)
    (L : CuspHalfSpace → Q.toClosedOrientedManifold.Carrier) (hL : ContMDiffOn halfCollarModel (𝓡 3) ∞ L cuspDomain)
    (q₀ : CuspHalfSpace) (hq₀ : q₀ ∈ cuspDomain)
    (hq₀C : ConnectedComponents.mk (L q₀) = C) :
    ∃ L' : CuspHalfSpace → (Q.toClosedOrientedManifold.component C).Carrier,
      (∀ p ∈ cuspDomain, (L' p).val = L p) ∧
      ContMDiffOn halfCollarModel (𝓡 3) ∞ L' cuspDomain := by
  classical
  have hclosed : IsClosed (Q.toClosedOrientedManifold.componentOpen C : Set Q.toClosedOrientedManifold.Carrier) :=
    ClosedOrientedManifold.isClosed_componentSet Q.toClosedOrientedManifold C
  have hmem : ∀ p ∈ cuspDomain, L p ∈ (Q.toClosedOrientedManifold.componentOpen C : Set Q.toClosedOrientedManifold.Carrier) := by
    have hpre : IsPreconnected (L '' cuspDomain) :=
      isPreconnected_cuspDomain_S34.image L hL.continuousOn
    have hsub : L '' cuspDomain ⊆ (Q.toClosedOrientedManifold.componentOpen C : Set Q.toClosedOrientedManifold.Carrier) :=
      IsPreconnected.subset_left_of_subset_union (Q.toClosedOrientedManifold.componentOpen C).isOpen
        hclosed.isOpen_compl disjoint_compl_right (by rw [union_compl_self]; exact subset_univ _)
        ⟨L q₀, ⟨q₀, hq₀, rfl⟩, hq₀C⟩ hpre
    intro p hp
    exact hsub ⟨p, hp, rfl⟩
  have hq₀j' : L q₀ ∈ (Q.toClosedOrientedManifold.componentOpen C : Set Q.toClosedOrientedManifold.Carrier) := hq₀C
  refine ⟨fun p => if h : L p ∈ (Q.toClosedOrientedManifold.componentOpen C : Set Q.toClosedOrientedManifold.Carrier)
      then ⟨L p, h⟩ else ⟨L q₀, hq₀j'⟩, fun p hp => ?_, fun p hp => ?_⟩
  · exact congrArg Subtype.val (dite_eq_left (hmem p hp))
  · refine (ContMDiffWithinAt.subtypeVal_comp_iff (I := halfCollarModel) (I' := 𝓡 3)
      (Q.toClosedOrientedManifold.componentOpen C) _ cuspDomain p).mp ?_
    refine (hL p hp).congr (fun q hq => ?_) ?_
    · exact congrArg Subtype.val (dite_eq_left (hmem q hq))
    · exact congrArg Subtype.val (dite_eq_left (hmem p hp))

section Producer

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

/-- The stage collar map of the seam index `x`: `cores.map c t ∘ cuspMap q` is smooth on `cuspDomain`. -/
theorem contMDiffOn_stageCusp_S51 (x : SliceIdx_S19 D) :
    ContMDiffOn halfCollarModel (𝓡 3) ∞
      (fun p => cores.map x.1 t ht ((D.truncation x.1).cuspMap x.2 p)) cuspDomain := by
  refine ((cores.smooth x.1 t ht).comp
    (((D.truncation x.1).cuspEmbedding x.2).isImmersion.contMDiff).contMDiffOn ?_)
  intro p hp
  have h := D.deep_domain x.1 x.2 (p.1, halfSpaceOneLift (p.2.val 0 + D.level)) (by
    have h1 : p.2.val 0 < 100 := hp
    have h2 : 0 ≤ p.2.val 0 + D.level := by linarith [p.2.2, D.two_le]
    rw [GC.LongTime.CuspP1.lift_height_CPA2 h2]; linarith)
  exact h

/-- **G2a (hsm).**  The collar `φ i`, corestricted to the component `C`. -/
theorem exists_phi_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (x : CIdx_S19 D ht C) :
    ∃ φ : CuspHalfSpace → (sliceM_S28 C).Carrier,
      (∀ p ∈ cuspDomain, (φ p).val =
        cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p)) ∧
      ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain := by
  refine exists_compLift_S51 C _ (contMDiffOn_stageCusp_S51 D ht x.1) (halfZero.1.1 |> fun _ => ((1, 1), halfZero))
    (by change (0 : ℝ) < 100; norm_num) ?_
  have h0 := stageCollar_zero_S19 D ht x.1 (1, 1)
  have hsrc : ((1, 1), (0 : ℝ)) ∈ (stageCollar_S19 D ht x.1).source := by
    rw [stageCollar_source_S19]; exact zero_mem_source_S19 _
  have hmem := stageCollar_target_subset_comp_S19 D ht x.1 ((stageCollar_S19 D ht x.1).map_source hsrc)
  rw [h0] at hmem
  exact hmem.trans x.2

/-- **G2a (hcol).**  Below height one, the collar `φ i` is the seam collar of the family. -/
theorem phi_col_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (i : Fin (componentFamily_S19 D ht C).count)
    (φ : CuspHalfSpace → (sliceM_S28 C).Carrier)
    (hφ : ∀ p ∈ cuspDomain, (φ p).val =
      cores.map ((cidxEquiv_S19 D ht C).symm i).1.1 t ht
        ((D.truncation ((cidxEquiv_S19 D ht C).symm i).1.1).cuspMap
          ((cidxEquiv_S19 D ht C).symm i).1.2 p))
    (p : CuspHalfSpace) (hp : p.2.val 0 < 1) :
    φ p = (componentFamily_S19 D ht C).collar i (p.1, p.2.val 0) := by
  have hp0 : 0 ≤ p.2.val 0 := p.2.2
  have hsrc : (p.1, p.2.val 0) ∈ (stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm i).1).source := by
    rw [stageCollar_source_S19]; exact mem_signedSource_S51 p.1 (by linarith) hp
  apply Subtype.ext
  rw [hφ p (by change p.2.val 0 < 100; linarith)]
  have h1 : (((componentFamily_S19 D ht C).collar i (p.1, p.2.val 0)).val :
      (postStage F.observation t).Carrier) =
      stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm i).1 (p.1, p.2.val 0) :=
    restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (p.1, p.2.val 0) hsrc
  rw [h1, stageCollar_pos_S19 D ht _ p.1 (p.2.val 0) hp0 hp]
  have h2 : halfPoint (p.2.val 0) hp0 = p.2 := GC.GraphManifold.halfPoint_coord_eq p.2
  rw [h2]

/-- The cusp collar over `cuspDomain` lies in the domain of `cores.map`. -/
theorem stageCusp_mem_domain_S51 (x : SliceIdx_S19 D) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    (D.truncation x.1).cuspMap x.2 p ∈ (cores.domain x.1 t : Set (cores.model x.1).Carrier) := by
  have h1 : p.2.val 0 < 100 := hp
  have h2 : 0 ≤ p.2.val 0 + D.level := by linarith [p.2.2, D.two_le]
  exact D.deep_domain x.1 x.2 (p.1, halfSpaceOneLift (p.2.val 0 + D.level)) (by
    rw [GC.LongTime.CuspP1.lift_height_CPA2 h2]; linarith)

/-- **G2a (hemb).**  The corestricted collar is an embedding of `cuspDomain`. -/
theorem phi_emb_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (x : CIdx_S19 D ht C) (φ : CuspHalfSpace → (sliceM_S28 C).Carrier)
    (hφ : ∀ p ∈ cuspDomain, (φ p).val =
      cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain) :
    _root_.Topology.IsEmbedding (fun p : cuspDomain => φ p.val) := by
  have hcont : Continuous (fun p : cuspDomain => φ p.val) := hsm.continuousOn.domRestrict
  have hinner : _root_.Topology.IsEmbedding (fun p : cuspDomain =>
      (⟨(D.truncation x.1.1).cuspMap x.1.2 p.val, stageCusp_mem_domain_S51 D x.1 p.2⟩ :
        cores.domain x.1.1 t)) := by
    refine _root_.Topology.IsEmbedding.of_comp ?_ continuous_subtype_val ?_
    · exact (((D.truncation x.1.1).cuspEmbedding x.1.2).isImmersion.contMDiff.continuous.comp
        continuous_subtype_val).subtype_mk _
    · exact ((D.truncation x.1.1).cuspEmbedding x.1.2).isEmbedding.comp
        _root_.Topology.IsEmbedding.subtypeVal
  have hG : _root_.Topology.IsEmbedding (fun p : cuspDomain =>
      cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p.val)) :=
    (cores.embedding x.1.1 t ht).isEmbedding.comp hinner
  refine _root_.Topology.IsEmbedding.of_comp hcont continuous_subtype_val ?_
  have heq : (fun p : cuspDomain => ((φ p.val).val : (postStage F.observation t).Carrier)) =
      fun p : cuspDomain =>
        cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p.val) :=
    funext fun p : cuspDomain => hφ p.val p.2
  exact (heq.symm ▸ hG : _root_.Topology.IsEmbedding
    (fun p : cuspDomain => ((φ p.val).val : (postStage F.observation t).Carrier)))

/-- **G2a (himm).**  The corestricted collar is an immersion on `cuspDomain`. -/
theorem phi_imm_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (x : CIdx_S19 D ht C) (φ : CuspHalfSpace → (sliceM_S28 C).Carrier)
    (hφ : ∀ p ∈ cuspDomain, (φ p).val =
      cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain) :
    ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel (𝓡 3) φ p) := by
  intro p hp
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hnhds : cuspDomain ∈ nhds p := isOpen_cuspDomain_C4.mem_nhds hp
  have hφd : MDifferentiableAt halfCollarModel (𝓡 3) φ p :=
    (hsm.contMDiffAt hnhds).mdifferentiableAt hn
  have hy := stageCusp_mem_domain_S51 D x.1 hp
  have hcd : MDifferentiableAt halfCollarModel (𝓡 3) ((D.truncation x.1.1).cuspMap x.1.2) p :=
    ((((D.truncation x.1.1).cuspEmbedding x.1.2).isImmersion.contMDiff) p).mdifferentiableAt hn
  have hfd : MDifferentiableAt (𝓡 3) (𝓡 3) (cores.map x.1.1 t ht)
      ((D.truncation x.1.1).cuspMap x.1.2 p) :=
    ((cores.smooth x.1.1 t ht).contMDiffAt ((cores.domain x.1.1 t).isOpen.mem_nhds hy)).mdifferentiableAt hn
  have hvd : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : (sliceM_S28 C).Carrier → (postStage F.observation t).Carrier) (φ p) :=
    (isLocalDiffeomorph_subtype_val (I := 𝓡 3)
      ((postStage F.observation t).toClosedOrientedManifold.componentOpen C) (φ p)).mdifferentiableAt hn
  have hev : (fun q => (φ q).val) =ᶠ[nhds p]
      fun q => cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 q) :=
    Filter.eventuallyEq_of_mem hnhds (fun q hq => hφ q hq)
  have hder : ∀ a, mfderiv (𝓡 3) (𝓡 3) (cores.map x.1.1 t ht) ((D.truncation x.1.1).cuspMap x.1.2 p)
      (mfderiv halfCollarModel (𝓡 3) ((D.truncation x.1.1).cuspMap x.1.2) p a) =
      mfderiv halfCollarModel (𝓡 3) φ p a := fun a => by
    have h1 := mfderiv_comp p hfd hcd
    have h2 := mfderiv_comp p hvd hφd
    have h3 : mfderiv halfCollarModel (𝓡 3) (fun q => (φ q).val) p =
        mfderiv halfCollarModel (𝓡 3)
          (fun q => cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 q)) p :=
      hev.mfderiv_eq
    have h4 : mfderiv halfCollarModel (𝓡 3) (fun q => (φ q).val) p a =
        mfderiv halfCollarModel (𝓡 3) φ p a := by
      change mfderiv halfCollarModel (𝓡 3) ((Subtype.val : (sliceM_S28 C).Carrier → _) ∘ φ) p a = _
      rw [h2]
      exact mfderiv_subtype_val_apply (I := 𝓡 3) _ (φ p) _
    rw [← h4, h3]
    exact (congrArg (fun L => L a) h1).symm
  have hinjf : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (cores.map x.1.1 t ht)
      ((D.truncation x.1.1).cuspMap x.1.2 p)) := by
    exact (((isLocalDiffeomorphAt_map_S28 ht x.1.1 hy).mfderivToContinuousLinearEquiv (by simp))).injective
  intro a b hab
  exact cuspMap_immersion_C4 (D.truncation x.1.1) x.1.2 p
    (hinjf ((hder a).trans (hab.trans (hder b).symm)))

end Producer

end GC.LongTime.Ch12
