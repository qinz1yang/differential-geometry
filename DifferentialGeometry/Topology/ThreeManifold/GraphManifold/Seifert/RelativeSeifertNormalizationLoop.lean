import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMerge
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Irreducible

/-!
# The non-separating single-sphere reconstruction with its core formula

Lane BR, tier R7 (review 26 §7). For a single-tube spherical cut-cap transition `E` of a closed
connected oriented `M` whose two capped sides lie in one component `A`, the proof of
`nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_of_cutCapVertex_eq` composes the paired-ball
uncapping diffeomorphism, the loop quotient step, the empty-gluing step and the sigma fibre over
the looped factor `A # S² × S¹`, and forgets all formulas. `exists_loopDiffeomorph_core` re-runs
the same construction and keeps them: there are a smooth self-attachment `S` of `A` along the two
cap ball charts, an oriented diffeomorphism `F : S ≅⁺ A # S² × S¹`, and a diffeomorphism `K` from
`M` onto `A # S² × S¹` sending a core point `y` whose core image lies in `A` outside both unit cap
balls to `F` of `coreToBand` of that core image.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.RelativeNormalization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_loopDiffeomorph_core {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    ∃ (S : SmoothSelfAttachment (E.capComponentBallChart (a, false))
        (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t)) a hloop.symm)
        (PairedBallGluing.disjoint_loop_charts E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t)) a hloop.symm
          E.pairwise_disjoint_capComponentBallChart_image) boundaryAttachment)
      (F : ClosedOrientedManifold.OrientedDiffeomorph
        S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (connectedSum (E.capped.component (E.cutCapVertex a false))
          sphereTwoTimesCircleLift).toClosedOrientedManifold)
      (K : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum (E.capped.component (E.cutCapVertex a false))
          sphereTwoTimesCircleLift).Carrier),
      ∀ (y : E.tubes.core) (x : SelfAttachment.coreInterior
          (E.capComponentBallChart (a, false)).toBallChart
          (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
            (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart),
        (x : (E.capped.component (E.cutCapVertex a false)).Carrier).val =
            E.capping.coreInclusion y →
          K y.val = F.val (SelfAttachment.coreToBand (E.capComponentBallChart (a,
              false)).toBallChart
            (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
              (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart
            (PairedBallGluing.disjoint_loop_charts E.capped.component E.cutCapVertex
              (fun a t => E.capComponentBallChart (a, t)) a hloop.symm
              E.pairwise_disjoint_capComponentBallChart_image)
            boundaryAttachment.val.toHomeomorph
            (SelfAttachment.coreInteriorToCore (E.capComponentBallChart (a, false)).toBallChart
              (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
                (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart x)) := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a, t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let C := fun K =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N ep ch v) := fun v => (C v).toChartedSpace
  obtain ⟨S, F, b, hb, hd', H, hfirst, hu, -, J, hJ⟩ :=
    PairedBallGluing.exists_quotient_homeomorph_loop N ep ch a hloop.symm hd
      (fun _ => boundaryAttachment) rfl
  let N' := PairedBallGluing.loopFactor N ep a
  let ep' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).fst
  let ch' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).snd
  let C' := fun v =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd' v).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
  have : IsEmpty {e : E.tubes.Index // e ≠ a} :=
    ⟨fun e => e.property (Subsingleton.elim _ _)⟩
  obtain ⟨Qcharts', hm', hc', hs', D', hD'⟩ :=
    PairedBallGluing.exists_smooth_quotient_atlas_of_isEmpty N' ep' ch' hd'
      (fun _ => boundaryAttachment) C'
  let _ := Qcharts'
  let _ := hm'
  obtain ⟨A, -, hcH, hsH, G, hG⟩ :=
    PairedBallGluing.exists_loop_smooth_atlas_of_factor_representatives N ep ch a hloop.symm
      hd S F b hb C C' H hfirst hu
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
  have hrad := PairedBallGluing.loop_homeomorph_radialPoint N ep ch a hloop.symm hd
    S F b hb H hfirst hu hd'
  obtain ⟨Qcharts, -, hc, hs, D, hD⟩ :=
    PairedBallGluing.exists_smooth_quotient_step_atlas N ep ch hd (fun _ => boundaryAttachment) a
      N' ep' ch' hd' H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
  let _ := Qcharts
  obtain ⟨U, hU⟩ := exists_pairedBallQuotient_diffeomorph_core E C Qcharts hc
    (fun e z => hs e ⟨(z, 0), Set.mem_univ _, by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  obtain ⟨w₀, hall, K, hK⟩ := sigma_fiber_formula N' ((U.symm.trans D).trans D')
  obtain rfl := hall none
  refine ⟨S, F, K, fun y x hxy => ?_⟩
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
      z.property ((Set.ext_iff.mp (PairedBallGluing.loopFlag_holes_some N ep ch a b hloop.symm v
        (ball (0 : E3) 1)) z.val).mpr h)
    have hsplit : PairedBallGluing.loopPuncturedFactorHomeomorphSplit N ep ch a b hloop.symm
        ⟨some v, z⟩ = Sum.inr ⟨v, ⟨z.val, hx⟩⟩ := rfl
    rw [hH, hsplit] at hy'1
    exact Sum.inr_ne_inl hy'1
  | none =>
    have hz' : z.val ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1 := fun h =>
      z.property ((Set.ext_iff.mp (PairedBallGluing.loopFlag_holes_none N ep ch a b
        (ball (0 : E3) 1)) z.val).mpr h)
    have hsplit : PairedBallGluing.loopPuncturedFactorHomeomorphSplit N ep ch a b hloop.symm
        ⟨none, z⟩ = Sum.inl ⟨z.val, hz'⟩ := rfl
    rw [hH, hsplit] at hy'1
    have hzv : z.val = y'.val := congrArg Subtype.val (Sum.inl_injective hy'1)
    have h2 : D' (D (U.symm y.val)) = ⟨none, z.val⟩ := by
      rw [hDq, hH, hD']
      exact PairedBallGluing.quotientHomeomorphOfIsEmpty_mk N' ep' ch' hd'
        (fun _ => boundaryAttachment) none z
    have h3 := (hK y.val).trans h2
    have h4 : K y.val = z.val := eq_of_heq (Sigma.mk.inj h3).2
    exact (h4.trans hzv).trans (hy'2.trans rfl)

end GC.Seifert.RelativeNormalization
