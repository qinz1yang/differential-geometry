import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationLoop
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationOriented
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMoves

/-!
# The oriented single-sphere reconstruction

Lane BR, tier R7 (review 26 §7.1, §7.3). In the non-separating case the diffeomorphism `K` of
`exists_loopDiffeomorph_core` from `M` onto `A # S² × S¹` preserves orientation: near an interior
core point `y`, `K ∘ val` agrees with `F ∘ coreToBand ∘ g`, `g` the core inclusion read in the
doubly punctured side `A`; `F` is an oriented diffeomorphism, `coreToBand` preserves orientation
(`SmoothSelfAttachment.coreToBand_preserves_orientation`), and `core_positive` with the component
orientation handles `g`. With the separating case (`orientedSingleSphere_of_ne`) this proves the
R7 contract `OrientedSingleSphere` (`orientedSingleSphere`) for every single-tube transition, with
the capped sides oriented as components of the capped manifold; no factor is replaced by its
opposite.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem loopDiffeomorph_preservesOrientation {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    (hloop : E.cutCapVertex a false = E.cutCapVertex a true)
    (S : SmoothSelfAttachment (E.capComponentBallChart (a, false))
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
          sphereTwoTimesCircleLift).Carrier)
    (hK : ∀ (y : E.tubes.core) (x : SelfAttachment.coreInterior
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
                (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart x))) :
    K.preservesOrientation M.orientation (connectedSum (E.capped.component (E.cutCapVertex a false))
      sphereTwoTimesCircleLift).orientation := by
  classical
  let _ := E.capping.coreCharts
  let _ := E.capping.coreSmooth
  obtain ⟨y, hint, hyA⟩ := exists_interior_core_mem E (a, false)
  have hmem : ∀ (y' : E.tubes.core)
      (h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false),
      (⟨E.capping.coreInclusion y', h⟩ : (E.capped.component (E.cutCapVertex a false)).Carrier) ∈
        SelfAttachment.coreInterior (E.capComponentBallChart (a, false)).toBallChart
            (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart := by
    rintro y' h (⟨z, hz, hzy⟩ | ⟨z, hz, hzy⟩)
    · exact capComponentBallChart_ne_core E y' (a, false) h
        (closedBall_subset_closedBall (by norm_num) hz) hzy
    · have hs := PairedBallGluing.incidenceChart_sigma_apply E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) (E.cutCapVertex a false)
        ⟨(a, true), hloop.symm⟩ z
      refine flagMap_ne_core E y' h (a, true) (closedBall_subset_closedBall (by norm_num) hz) ?_
      rw [← hs]
      change (⟨E.cutCapVertex a false, (PairedBallGluing.loopSecondChart E.capped.component
          E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).chart z⟩ :
        Σ v, (E.capped.component v).Carrier) = _
      rw [hzy]
  let x₀ : SelfAttachment.coreInterior (E.capComponentBallChart (a, false)).toBallChart
      (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart :=
    ⟨⟨E.capping.coreInclusion y, hyA⟩, hmem y hyA⟩
  let g : E.tubes.core → SelfAttachment.coreInterior (E.capComponentBallChart (a,
      false)).toBallChart (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart := fun y' =>
    if h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false then
      ⟨⟨E.capping.coreInclusion y', h⟩, hmem y' h⟩ else x₀
  have hgW : ∀ (y' : E.tubes.core)
      (h : ConnectedComponents.mk (E.capping.coreInclusion y') = E.cutCapVertex a false),
      g y' = ⟨⟨E.capping.coreInclusion y', h⟩, hmem y' h⟩ := fun y' h => by
    simp only [g, h, dite_true]
  have hgy : g y = x₀ := hgW y hyA
  let W : Set E.tubes.core := {y' | ConnectedComponents.mk (E.capping.coreInclusion y') =
    E.cutCapVertex a false}
  have hW : IsOpen W :=
    (ClosedOrientedManifold.isOpen_componentSet E.capped _).preimage
      E.capping.coreInclusion.continuous
  have hWy : W ∈ 𝓝 y := hW.mem_nhds hyA
  let _ := S.charts
  let _ := S.smooth
  let B := SelfAttachment.coreToBand (E.capComponentBallChart (a, false)).toBallChart
      (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart
    (PairedBallGluing.disjoint_loop_charts E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm
      E.pairwise_disjoint_capComponentBallChart_image) boundaryAttachment.val.toHomeomorph ∘
    SelfAttachment.coreInteriorToCore (E.capComponentBallChart (a, false)).toBallChart
        (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart
  let B' : SelfAttachment.coreInterior (E.capComponentBallChart (a, false)).toBallChart
      (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart →
      S.toConnectedClosedOrientedManifold.toClosedOrientedManifold.Carrier := B
  let b₀ : S.toConnectedClosedOrientedManifold.toClosedOrientedManifold.Carrier := B' (g y)
  have hKg : (K ∘ Subtype.val : E.tubes.core → _) =ᶠ[𝓝 y] ((F.val ∘ B') ∘ g) := by
    filter_upwards [hWy] with y' hy'
    exact hK y' (g y') (by rw [hgW y' hy'])
  have hjg : (E.capping.coreInclusion : E.tubes.core → E.capped.Carrier) =ᶠ[𝓝 y]
      (Subtype.val ∘ (Subtype.val ∘ g)) := by
    filter_upwards [hWy] with y' hy'
    change E.capping.coreInclusion y' = (g y').val.val
    rw [hgW y' hy']
  obtain ⟨hi, hj, hpos⟩ := E.capping.core_positive y hint
  have hval : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) y :=
    mdifferentiableAt_of_bijective hi
  have hjd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y :=
    mdifferentiableAt_of_bijective hj
  have hKd : MDifferentiableAt (𝓡 3) (𝓡 3) K y.val := K.mdifferentiable (by simp) _
  have hgd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) g y := by
    have h1 := hjd.congr_of_eventuallyEq hjg.symm
    rw [mdifferentiableAt_subtypeVal_comp_iff] at h1
    exact (mdifferentiableAt_subtypeVal_comp_iff
      (SelfAttachment.coreInterior (E.capComponentBallChart (a, false)).toBallChart
          (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart) g y).mp h1
  have hBl := S.coreToBand_isLocalDiffeomorph (g y)
  have hBd : MDifferentiableAt (𝓡 3) (𝓡 3) B' (g y) := hBl.mdifferentiableAt (by simp)
  have hFd : MDifferentiableAt (𝓡 3) (𝓡 3) F.val b₀ := F.val.mdifferentiable (by simp) _
  have hFBd : MDifferentiableAt (𝓡 3) (𝓡 3) (F.val ∘ B') (g y) := hFd.comp (g y) hBd
  have h1 : mfderiv (𝓡∂ 3) (𝓡 3) (K ∘ Subtype.val) y =
      (mfderiv (𝓡 3) (𝓡 3) K y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3) Subtype.val y) :=
    mfderiv_comp y hKd hval
  have h2 : mfderiv (𝓡∂ 3) (𝓡 3) ((F.val ∘ B') ∘ g) y =
      (mfderiv (𝓡 3) (𝓡 3) (F.val ∘ B') (g y)).comp (mfderiv (𝓡∂ 3) (𝓡 3) g y) :=
    mfderiv_comp y hFBd hgd
  have h2' : mfderiv (𝓡 3) (𝓡 3) (F.val ∘ B') (g y) =
      (mfderiv (𝓡 3) (𝓡 3) F.val b₀).comp (mfderiv (𝓡 3) (𝓡 3) B' (g y)) :=
    mfderiv_comp (g y) hFd hBd
  have h3 := hKg.mfderiv_eq (I := 𝓡∂ 3) (I' := 𝓡 3)
  have h4 : mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y = mfderiv (𝓡∂ 3) (𝓡 3) g y := by
    rw [hjg.mfderiv_eq, Topology.mfderiv_subtypeVal_comp]
    exact Topology.mfderiv_subtypeVal_comp
      (SelfAttachment.coreInterior (E.capComponentBallChart (a, false)).toBallChart
          (PairedBallGluing.loopSecondChart E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) a hloop.symm).toBallChart) g y
  have hKy : K y.val = F.val b₀ := hK y (g y) (by rw [hgy])
  have hlin : ∀ v : E3, mfderiv (𝓡 3) (𝓡 3) K y.val (mfderiv (𝓡∂ 3) (𝓡 3) Subtype.val y v) =
      mfderiv (𝓡 3) (𝓡 3) F.val b₀ (mfderiv (𝓡 3) (𝓡 3) B' (g y)
        (mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y v)) := by
    intro v
    have h5 := congrArg (fun f : E3 →L[ℝ] E3 => f v) (h1.symm.trans (h3.trans h2))
    rw [h4]
    rw [h2'] at h5
    exact h5
  let eV : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) y).toLinearMap hi
  let eJ : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) E.capping.coreInclusion y).toLinearMap hj
  let eB : E3 ≃ₗ[ℝ] E3 := (hBl.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let eF : E3 ≃ₗ[ℝ] E3 :=
    (F.val.mfderivToContinuousLinearEquiv (by simp) b₀).toLinearEquiv
  let eK : E3 ≃ₗ[ℝ] E3 := (K.mfderivToContinuousLinearEquiv (by simp) y.val).toLinearEquiv
  have heK : eK = ((eV.symm.trans eJ).trans eB).trans eF := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, rfl⟩ := eV.surjective v
    change mfderiv (𝓡 3) (𝓡 3) K y.val (eV w) = eF (eB (eJ (eV.symm (eV w))))
    rw [LinearEquiv.symm_apply_apply]
    exact hlin w
  have hpB := S.coreToBand_preserves_orientation (g y)
  have hpF := F.2 b₀
  have hv : (g y).val.val = E.capping.coreInclusion y := by rw [hgy]
  let Oc : E.capped.Carrier → Orientation ℝ E3 (Fin 3) := fun q =>
    E.capped.orientation.orientation q
  have hcomp : ((E.capped.component (E.cutCapVertex a false)).orientation.orientation (g y).val :
      Orientation ℝ E3 (Fin 3)) = E.capped.orientation.orientation (E.capping.coreInclusion y) :=
    (ClosedOrientedManifold.componentTangentOrientation_apply E.capped
      (E.cutCapVertex a false) (g y).val).trans (congrArg Oc hv)
  refine Diffeomorph.preservesOrientation_of_eq_at K _ _ y.val ?_
  let O : (connectedSum (E.capped.component (E.cutCapVertex a false))
      sphereTwoTimesCircleLift).Carrier → Orientation ℝ E3 (Fin 3) := fun q =>
    (connectedSum (E.capped.component (E.cutCapVertex a false))
      sphereTwoTimesCircleLift).orientation.orientation q
  change Orientation.map (Fin 3) eK (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3)) =
    O (K y.val)
  rw [congrArg O hKy, heK]
  have step1 := orientation_map_trans' ((eV.symm.trans eJ).trans eB) eF
    (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3))
  have step2 := orientation_map_trans' (eV.symm.trans eJ) eB
    (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3))
  have step3 : Orientation.map (Fin 3) (eV.symm.trans eJ)
      (M.orientation.orientation y.val : Orientation ℝ E3 (Fin 3)) =
        (E.capped.orientation.orientation (E.capping.coreInclusion y) :
          Orientation ℝ E3 (Fin 3)) := hpos
  refine step1.trans ?_
  rw [step2, step3, ← hcomp]
  exact (congrArg (Orientation.map (Fin 3) eF) hpB).trans hpF

theorem orientedSingleSphere_of_eq {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        sphereTwoTimesCircleLift.ulift.{0, u}).toClosedOrientedManifold
      M.toClosedOrientedManifold) := by
  obtain ⟨S, F, K, hK⟩ := exists_loopDiffeomorph_core E a hloop
  have hKo := loopDiffeomorph_preservesOrientation E a hloop S F K hK
  let K' : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        sphereTwoTimesCircleLift).toClosedOrientedManifold := ⟨K, hKo⟩
  obtain ⟨G⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    (M := E.capped.component (E.cutCapVertex a false))
    (M' := E.capped.component (E.cutCapVertex a false))
    (N := sphereTwoTimesCircleLift) (N' := sphereTwoTimesCircleLift.ulift.{0, u})
    (ClosedOrientedManifold.OrientedDiffeomorph.refl
      (E.capped.component (E.cutCapVertex a false)).toClosedOrientedManifold)
    (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold)
  exact ⟨(K'.trans G).symm⟩

theorem orientedSingleSphere : OrientedSingleSphere.{u} := by
  intro M P X a hsub
  exact ⟨fun h => orientedSingleSphere_of_ne X a h, fun h => orientedSingleSphere_of_eq X a h⟩

end GC.Seifert.RelativeNormalization
