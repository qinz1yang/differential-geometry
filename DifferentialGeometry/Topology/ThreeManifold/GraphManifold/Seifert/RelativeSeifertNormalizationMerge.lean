import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitSphere

/-!
# The separating single-sphere reconstruction with its core formula

Lane BR, tier R7 (review 26 §7). For a single-tube spherical cut-cap transition `E` of a closed
connected oriented `M` whose two capped sides lie in different components `A`, `B`, the proof of
`MoveSplitSphere.nonempty_diffeomorph_connectedSum_of_cutCapVertex_ne` composes the paired-ball
uncapping diffeomorphism, the merge quotient step, the empty-gluing step and the sigma fibre
over the merged factor, and forgets all formulas. `exists_mergeDiffeomorph_core` re-runs the same
construction and keeps them: the diffeomorphism `K` from `M` onto the smooth connected sum of `A`
and `B` along the cap ball charts sends a core point `y` whose core image lies in `A` outside the
unit cap ball to `interiorLeft` of that core image. Core points avoid every cap ball of radius
`2` (`flagMap_ne_core`).
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.RelativeNormalization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem flagMap_ne_core {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (y : E.tubes.core) {K : ConnectedComponents E.capped.Carrier}
    (hy : ConnectedComponents.mk (E.capping.coreInclusion y) = K) (b : E.tubes.Boundary)
    {z : E3} (hz : z ∈ closedBall (0 : E3) 2) :
    PairedBallGluing.flagMap E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) b z ≠ ⟨K, ⟨E.capping.coreInclusion y, hy⟩⟩ := by
  intro h
  have hv := congrArg E.capped.componentUnionHomeomorph h
  have h1 : ((E.capComponentBallChart b).chart z).val = E.capping.coreInclusion y := hv
  rw [E.capComponentBallChart_apply_closedBall b hz] at h1
  exact Set.disjoint_left.mp (E.capping.disjoint_capBallChart_closedBall_core b)
    ⟨z, hz, rfl⟩ ⟨y, h1.symm⟩

theorem sigma_fiber_formula {M : ConnectedClosedOrientedManifold.{u} 3}
    {W : Type u} (X : W → ConnectedClosedOrientedManifold.{u} 3)
    (D : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Σ w, (X w).Carrier)) :
    ∃ w₀ : W, (∀ w, w = w₀) ∧ ∃ K : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (X w₀).Carrier,
      ∀ m, (⟨w₀, K m⟩ : Σ w, (X w).Carrier) = D m := by
  have : ConnectedSpace (Σ w, (X w).Carrier) :=
    D.toHomeomorph.connectedSpace_iff.mp inferInstance
  obtain ⟨p⟩ := (inferInstance : Nonempty (Σ w, (X w).Carrier))
  have hfst : IsLocallyConstant (Sigma.fst : (Σ w, (X w).Carrier) → W) :=
    isOpen_sigma_fst_preimage
  have hall : ∀ w, w = p.1 := fun w => by
    obtain ⟨x⟩ := (inferInstance : Nonempty (X w).Carrier)
    exact hfst.apply_eq_of_preconnectedSpace ⟨w, x⟩ p
  have hf := isLocalDiffeomorph_sigmaMk (I := 𝓡 3) (M := fun w => (X w).Carrier) (n := ∞) p.1
  have hbij : Function.Bijective (Sigma.mk (β := fun w => (X w).Carrier) p.1) := by
    refine ⟨sigma_mk_injective, ?_⟩
    rintro ⟨w, x⟩
    obtain rfl := hall w
    exact ⟨x, rfl⟩
  refine ⟨p.1, hall, D.trans (hf.diffeomorphOfBijective hbij).symm, fun m => ?_⟩
  change (hf.diffeomorphOfBijective hbij) ((hf.diffeomorphOfBijective hbij).symm (D m)) = D m
  exact (hf.diffeomorphOfBijective hbij).apply_symm_apply (D m)

theorem exists_mergeDiffeomorph_core {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true) :
    ∃ K : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (PairedBallGluing.mergeFactor E.capped.component
        E.cutCapVertex (fun a t => E.capComponentBallChart (a, t)) a boundaryAttachment
          none).Carrier,
      ∀ (y : E.tubes.core) (x : (E.capComponentBallChart (a, false)).interior),
        (x : (E.capped.component (E.cutCapVertex a false)).Carrier).val =
            E.capping.coreInclusion y →
          K y.val = ConnectedSumQuotient.interiorLeft (E.capComponentBallChart (a,
              false)).toBallChart
            (E.capComponentBallChart (a, true)).toBallChart boundaryAttachment.1 x := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a, t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let C := fun K =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N ep ch v) := fun v => (C v).toChartedSpace
  obtain ⟨b, hbL, hbR, hd', H, hfirst, hsecond, hu, -, J, hJ⟩ :=
    PairedBallGluing.exists_quotient_homeomorph_merge N ep ch a hd
      (fun e => boundaryAttachment) hsep
  let N' := PairedBallGluing.mergeFactor N ep ch a boundaryAttachment
  let ep' := fun e t => (PairedBallGluing.mergeFlag N ep ch a boundaryAttachment b e t).fst
  let ch' := fun e t => (PairedBallGluing.mergeFlag N ep ch a boundaryAttachment b e t).snd
  let C' := fun v =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd' v).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
  have : IsEmpty {e : E.tubes.Index // e ≠ a} :=
    ⟨fun e => e.property (Subsingleton.elim _ _)⟩
  obtain ⟨Qcharts', hm', hc', hs', D', hD'⟩ :=
    PairedBallGluing.exists_smooth_quotient_atlas_of_isEmpty N' ep' ch' hd'
      (fun e => boundaryAttachment) C'
  let _ := Qcharts'
  let _ := hm'
  have hbd := PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag N ep ch a
    boundaryAttachment hsep b hd'
  obtain ⟨A, -, hcH, hsH, G, hG⟩ :=
    PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives N ep ch hd a
      boundaryAttachment hsep b C C' H hfirst hsecond hu hbd hbL hbR
  let _ := A
  have hGc : (fun q => G q) = H := funext hG
  have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamCoreInclusion N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
    simpa only [hGc] using hh
  have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamChart N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
    simpa only [hGc] using hh
  have hrad := PairedBallGluing.merge_homeomorph_radialPoint N ep ch hd a boundaryAttachment
    hsep b H hfirst hsecond hu hbL hbR hd'
  obtain ⟨Qcharts, -, hc, hs, D, hD⟩ :=
    PairedBallGluing.exists_smooth_quotient_step_atlas N ep ch hd (fun e => boundaryAttachment) a
      N' ep' ch' hd' H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
  let _ := Qcharts
  obtain ⟨U, hU⟩ := exists_pairedBallQuotient_diffeomorph_core E C Qcharts hc
    (fun e z => hs e ⟨(z, 0), Set.mem_univ _, by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  obtain ⟨w₀, hall, K, hK⟩ := sigma_fiber_formula N' ((U.symm.trans D).trans D')
  obtain rfl := hall none
  refine ⟨K, fun y x hxy => ?_⟩
  let xc : (N (ep a false)).Carrier := x
  have hcoreA : ConnectedComponents.mk (E.capping.coreInclusion y) = ep a false := by
    rw [← hxy]
    exact xc.property
  have hxc : xc = ⟨E.capping.coreInclusion y, hcoreA⟩ := Subtype.ext hxy
  have hpf : (⟨ep a false, xc⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, PairedBallGluing.flagMap N ep ch p '' ball (0 : E3) 1 := by
    intro h
    obtain ⟨p, z, hz, hzx⟩ := mem_iUnion.mp h
    refine flagMap_ne_core E y hcoreA p (closedBall_subset_closedBall (by norm_num)
      (ball_subset_closedBall hz)) ?_
    rw [hzx, hxc]
  let xp : PairedBallGluing.PuncturedFactor N ep ch (ep a false) := ⟨xc, hpf⟩
  have hac : (⟨ep a false, xp⟩ : Σ v, PairedBallGluing.PuncturedFactor N ep ch v) ∈
      PairedBallGluing.allCore N ep ch hd := by
    intro h
    obtain ⟨e, h⟩ := mem_iUnion.mp h
    obtain ⟨t, h⟩ := mem_iUnion.mp h
    obtain ⟨z, hz⟩ := h
    have hflag : PairedBallGluing.flagMap N ep ch (e, t) z.val = ⟨ep a false, xc⟩ := by
      have h1 := congrArg (fun q : Σ v, PairedBallGluing.PuncturedFactor N ep ch v =>
        (⟨q.1, q.2.val⟩ : Σ v, (N v).Carrier)) hz
      exact h1
    refine flagMap_ne_core E y hcoreA (e, t) (?_ : z.val ∈ closedBall (0 : E3) 2) ?_
    · rw [mem_closedBall, dist_zero_right, norm_eq_of_mem_sphere z]
      norm_num
    · rw [hflag, hxc]
  let pc : PairedBallGluing.allCore N ep ch hd := ⟨⟨ep a false, xp⟩, hac⟩
  have hU1 := hU pc y hxy
  have hUs : U.symm y.val =
      PairedBallGluing.allCoreInclusion N ep ch hd (fun _ => boundaryAttachment) pc := by
    rw [← hU1, Diffeomorph.symm_apply_apply]
  have hDq : D (U.symm y.val) = Quot.mk _ (H (Quot.mk _ ⟨ep a false, xp⟩)) := by
    rw [hUs, hD]
    exact hJ _
  obtain ⟨y', hy'1, hy'2⟩ := hfirst xp
  rcases hH : H (Quot.mk _ ⟨ep a false, xp⟩) with ⟨w, z⟩
  cases w with
  | some v =>
    exfalso
    have hx : (⟨v.val, z.val⟩ : Σ v, (N v).Carrier) ∉
        ⋃ p, PairedBallGluing.flagMap N ep ch p '' ball (0 : E3) 1 := fun h =>
      z.property ((Set.ext_iff.mp (PairedBallGluing.mergeFlag_holes_some N ep ch a
        boundaryAttachment b v (ball (0 : E3) 1)) z.val).mpr h)
    rw [hH, PairedBallGluing.mergePuncturedFactorHomeomorph_some N ep ch a boundaryAttachment
      b hsep v z hx] at hy'1
    exact Sum.inr_ne_inl hy'1
  | none =>
    have hz' : z.val ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1 := fun h =>
      z.property ((Set.ext_iff.mp (PairedBallGluing.mergeFlag_holes_none N ep ch a
        boundaryAttachment b hsep (ball (0 : E3) 1)) z.val).mpr h)
    rw [hH, PairedBallGluing.mergePuncturedFactorHomeomorph_none N ep ch a boundaryAttachment
      b hsep z hz'] at hy'1
    have hzv : z.val = y'.val := congrArg Subtype.val (Sum.inl_injective hy'1)
    have h2 : D' (D (U.symm y.val)) = ⟨none, z.val⟩ := by
      rw [hDq, hH, hD']
      exact PairedBallGluing.quotientHomeomorphOfIsEmpty_mk N' ep' ch' hd'
        (fun _ => boundaryAttachment) none z
    have h3 := (hK y.val).trans h2
    have h4 : K y.val = z.val := eq_of_heq (Sigma.mk.inj h3).2
    rw [h4, hzv, hy'2]
    rfl

end GC.Seifert.RelativeNormalization
