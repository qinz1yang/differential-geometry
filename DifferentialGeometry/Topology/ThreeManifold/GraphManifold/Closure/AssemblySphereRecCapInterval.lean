import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecShellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapBall
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSides

/-!
# FC42 sphere recursion, packet S3a: an `S² × I` side and its cap make a ball

Lane ASM-SPH (review 40 §2.1 table, row "`S² × I` with one cap ⇒ ball, the other sphere boundary
kept"). For the cut-and-capped data `X : SphereCutCapped W S E` and a piece `P` of `W` on side `j`
of the seam, parametrized by `e₀ : S² × [0, 1] ≅ P` with the end `0` on the seam sphere and the end
`1` in `W.interior`:

* `range_subset_interior_of_sphereIcc`: the piece lies in `W.interior`;
* `exists_capUnion_ballPiece`: the lifted piece and the cap of its copy form a piece of the capped
  carrier with the ball model (a ball chart restricted to the closed unit cell), whose image is the
  union and whose model boundary is the lift of the end `1` — for the ACTUAL attaching map: the cap
  extends to a ball chart (`exists_ballChart_of_closedCell_bijective`), the shell to a partial
  diffeomorphism around `S² × [0, 1]`, and `exists_ballChart_of_shell_cap` glues them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
  GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsCapInt_ASMSPH : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothCapInt_ASMSPH : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance ballChartsSuccCapInt_ASMSPH :
    ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothSuccCapInt_ASMSPH : IsManifold (𝓡∂ (2 + 1)) ∞ (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance ballUliftCharts_ASMSPH :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} (ClosedCell 3)) :=
  DifferentialGeometry.Topology.uliftChartedSpace _ _

local instance ballUliftSmooth_ASMSPH : IsManifold (𝓡∂ 3) ∞ (ULift.{u} (ClosedCell 3)) :=
  DifferentialGeometry.Topology.isManifold_ulift _ _

local instance sphereDimCapInt_ASMSPH :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- The boundary of `S² × [0, 1]` is `S² × {0, 1}`. -/
theorem snd_eq_of_isBoundaryPoint_sphereIcc
    {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1}
    (hp : ((𝓡 2).prod (𝓡∂ 1)).IsBoundaryPoint p) : p.2 = iccZero ∨ p.2 = iccOne := by
  have hmem : p ∈ ((𝓡 2).prod (𝓡∂ 1)).boundary
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) := hp
  rw [boundary_product] at hmem
  rcases hmem.2 with h | h
  · left
    rw [h]
    exact Subtype.ext rfl
  · right
    rw [h]
    exact Subtype.ext rfl

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

section Interval

variable (P : PieceEmbedding W) (j : Fin 2)
  (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
  (e₀ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1),
    𝓡∂ 3⟯ P.Piece)

include e₀ in
/-- An `S² × I` piece whose ends lie on the seam sphere and in `W.interior` lies in `W.interior`. -/
theorem range_subset_interior_of_sphereIcc
    (hcut : (range fun z => P.map (e₀ (z, iccZero))) = S.zeroSphere)
    (hfar : ∀ z, P.map (e₀ (z, iccOne)) ∈ W.interior) : range P.map ⊆ W.interior := by
  rintro _ ⟨q, rfl⟩
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact P.isInteriorPoint_map hq
  · obtain ⟨p, rfl⟩ := e₀.surjective q
    have hp : ((𝓡 2).prod (𝓡∂ 1)).IsBoundaryPoint p :=
      ((e₀.isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)).mpr hq
    rcases snd_eq_of_isBoundaryPoint_sphereIcc hp with h | h
    · have hx : P.map (e₀ (p.1, iccZero)) ∈ S.zeroSphere := hcut ▸ ⟨p.1, rfl⟩
      rw [show p = (p.1, iccZero) from Prod.ext rfl h]
      exact S.target_interior (S.zeroSphere_subset_target hx)
    · rw [show p = (p.1, iccOne) from Prod.ext rfl h]
      exact hfar p.1

/-- **`S² × I` ∪ cap = ball** (actual attaching map): the lifted piece and the cap of its copy
form a piece of the capped carrier with the ball model, with image the union and model boundary
the lift of the end `1`. -/
theorem exists_capUnion_ballPiece
    (hcut : (range fun z => P.map (e₀ (z, iccZero))) = S.zeroSphere)
    (hfar : ∀ z, P.map (e₀ (z, iccOne)) ∈ W.interior) :
    ∃ (P' : PieceEmbedding X.Q) (_ : P'.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3),
      range P'.map = range (X.liftPiece P j hside).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm j)) ∧
      P'.map '' (𝓡∂ 3).boundary P'.Piece =
        range fun z => (X.liftPiece P j hside).map (e₀ (z, iccOne)) := by
  set L := X.liftPiece P j hside with hLdef
  set J := Fin.cast X.h2.symm j with hJdef
  set U := X.Q.interior with hUdef
  have hrange := range_subset_interior_of_sphereIcc P e₀ hcut hfar
  have hLint : ∀ q, L.map q ∈ U := X.liftPiece_mem_interior P j hside hrange
  have hcapint : ∀ x, X.capping.cap J x ∈ U := fun x =>
    range_relativeSphereCap_subset_interior X.capping J ⟨x, rfl⟩
  have hU : ∀ y ∈ U, X.Q.model.IsInteriorPoint y := fun _ hy => hy
  have hUb : BoundarylessManifold X.Q.model U := boundarylessManifold_of_forall_isInteriorPoint U hU
  have hzero : S.zeroSphere ⊆ range P.map := by
    rw [← hcut]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  -- the shell and the cap, in the open set of interior points
  let F₀U : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → U :=
    fun p => ⟨L.map (e₀ p), hLint _⟩
  let capU : ClosedCell 3 → U := fun x => ⟨X.capping.cap J x, hcapint x⟩
  have hF₀ : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) X.Q.model ∞ (fun p => L.map (e₀ p)) :=
    L.smooth.comp e₀.contMDiff
  have hF₀U : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) X.Q.model ∞ F₀U :=
    (ContMDiff.subtypeVal_comp_iff U F₀U).mp hF₀
  have hF₀Ub : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) X.Q.model F₀U p) := by
    intro p
    rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U F₀U p]
    change Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) X.Q.model (L.map ∘ e₀) p)
    rw [mfderiv_comp p (L.smooth.mdifferentiableAt (by simp))
      (e₀.contMDiff.mdifferentiableAt (by simp))]
    exact (L.mfderiv_bijective _).comp (e₀.mfderivToContinuousLinearEquiv (by simp) p).bijective
  have hcapU : ContMDiff (𝓡∂ 3) X.Q.model ∞ capU :=
    (ContMDiff.subtypeVal_comp_iff U capU).mp (X.capping.cap_embedding J).contMDiff
  have hcapUb : ∀ x, Bijective (mfderiv (𝓡∂ 3) X.Q.model capU x) := by
    intro x
    rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U capU x]
    exact X.mfderiv_cap_bijective J x
  have hF₀Ui : Injective F₀U := fun p q h =>
    e₀.injective (L.injective (congrArg Subtype.val h))
  have hcapUi : Injective capU := fun x y h =>
    (X.capping.cap_embedding J).isEmbedding.injective (congrArg Subtype.val h)
  -- the interior atlas
  let := DifferentialGeometry.Manifold.interiorChartedSpace X.Q.model ∞ (M := U)
  have := DifferentialGeometry.Manifold.interiorIsManifold X.Q.model ∞ (M := U)
  let D := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph X.Q.model ∞ (M := U)
  have hDb : ∀ y : U, Bijective (mfderiv X.Q.model (𝓡 3) D y) := fun y =>
    (D.mfderivToContinuousLinearEquiv (by simp) y).bijective
  let F₀' := D ∘ F₀U
  let cap' := D ∘ capU
  have hF₀' : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀' := D.contMDiff.comp hF₀U
  have hF₀'b : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀' p) := by
    intro p
    rw [mfderiv_comp p (D.contMDiff.mdifferentiableAt (by simp))
      (hF₀U.mdifferentiableAt (by simp))]
    exact (hDb _).comp (hF₀Ub p)
  have hcap' : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ cap' := D.contMDiff.comp hcapU
  have hcap'b : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) cap' x) := by
    intro x
    rw [mfderiv_comp x (D.contMDiff.mdifferentiableAt (by simp))
      (hcapU.mdifferentiableAt (by simp))]
    exact (hDb _).comp (hcapUb x)
  obtain ⟨G, hGsrc, hGeq⟩ := exists_ballChart_of_closedCell_bijective cap' hcap' hcapUi hcap'b
  -- the cut sphere, seen in the open set
  let K₀ : Set U := {y | (y : X.Q.Carrier) ∈ range fun z => X.capping.core (X.cutSphere j z)}
  have hGval : ∀ x : ClosedCell 3, (G x.val : X.Q.Carrier) = X.capping.cap J x := fun x => by
    rw [hGeq x]
    rfl
  have hGK : G '' Metric.sphere 0 1 = K₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxn : ‖x‖ = 1 := by simpa using hx
      let w : ClosureSphere.{u} := ULift.up ⟨x, by simpa using hxn⟩
      have hw : closureSphereToBall w = ⟨x, hxn.le⟩ := rfl
      refine ⟨X.capping.attaching J w, ?_⟩
      change X.capping.core (X.cutSphere j _) = (G (⟨x, hxn.le⟩ : ClosedCell 3).val : X.Q.Carrier)
      rw [hGval, ← hw, X.capping.boundary_eq]
      rfl
    · rintro ⟨z, hz⟩
      let w := (X.capping.attaching J).symm z
      refine ⟨(closureSphereToBall w).val, w.down.2, ?_⟩
      apply Subtype.ext
      rw [hGval, X.capping.boundary_eq, Diffeomorph.apply_symm_apply]
      exact hz
  have hFK : (range fun z => F₀' (z, iccZero)) = K₀ := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z', hz'⟩ : P.map (e₀ (z, iccZero)) ∈ S.zeroSphere := hcut ▸ ⟨z, rfl⟩
      refine ⟨z', ?_⟩
      change X.capping.core (X.cutSphere j z') = L.map (e₀ (z, iccZero))
      rw [X.liftPiece_map_of_mem P j hside hz'.symm]
    · rintro ⟨z', hz'⟩
      obtain ⟨z, hz⟩ : S.collar (z', 0) ∈ range fun z => P.map (e₀ (z, iccZero)) :=
        hcut.symm ▸ ⟨z', rfl⟩
      refine ⟨z, Subtype.ext ?_⟩
      change L.map (e₀ (z, iccZero)) = (y : X.Q.Carrier)
      rw [X.liftPiece_map_of_mem P j hside hz]
      exact hz'
  have hGs : G '' Metric.sphere 0 1 = range fun z => F₀' (z, iccZero) := hGK.trans hFK.symm
  have hinter : range F₀' ∩ G '' Metric.closedBall 0 1 ⊆ G '' Metric.sphere 0 1 := by
    rintro y ⟨⟨p, rfl⟩, ⟨x, hx, hxy⟩⟩
    rw [hGK]
    have hmem : (F₀' p : X.Q.Carrier) ∈ range L.map ∩ range (X.capping.cap J) := by
      refine ⟨⟨e₀ p, rfl⟩, ⟨⟨x, by simpa using hx⟩, ?_⟩⟩
      rw [← hxy]
      exact (hGval ⟨x, by simpa using hx⟩).symm
    rw [X.range_liftPiece_inter_cap P j hside hzero] at hmem
    exact hmem
  obtain ⟨A, hAsrc, hAcl, hAsph⟩ :=
    exists_ballChart_of_shell_cap F₀' hF₀' (fun p q h => hF₀Ui (D.injective h)) hF₀'b G hGsrc hGs
      hinter
  -- the ball piece
  let f : ClosedCell 3 → X.Q.Carrier := fun x => (D.symm (A x.val) : X.Q.Carrier)
  have hval : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) :=
    (isSmoothEmbedding_closedCell_inclusion 2).contMDiff
  have hAs : ∀ x : ClosedCell 3, x.val ∈ A.source := fun x =>
    hAsrc (mem_closedBall_zero_iff.mpr x.2)
  have hAv : ContMDiff (𝓡∂ 3) (𝓡 3) ∞
      (A ∘ (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3))) :=
    A.contMDiffOn.comp_contMDiff hval hAs
  have hDA : ContMDiff (𝓡∂ 3) X.Q.model ∞
      (D.symm ∘ (A ∘ (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)))) :=
    D.symm.contMDiff.comp hAv
  have hf : ContMDiff (𝓡∂ 3) X.Q.model ∞ f := contMDiff_subtype_val.comp hDA
  have hfb : ∀ x, Bijective (mfderiv (𝓡∂ 3) X.Q.model f x) := by
    intro x
    have h1 : mfderiv (𝓡∂ 3) X.Q.model f x = mfderiv (𝓡∂ 3) X.Q.model
        (D.symm ∘ (A ∘ (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)))) x :=
      DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U _ x
    rw [h1]
    rw [mfderiv_comp x (D.symm.contMDiff.mdifferentiableAt (by simp))
      (hAv.mdifferentiableAt (by simp)),
      mfderiv_comp x ((A.mdifferentiableAt (by simp) (hAs x)))
        (hval.mdifferentiableAt (by simp))]
    refine (D.symm.mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
      (((A.isLocalDiffeomorphAt _ _ _ (hAs x)).mfderivToContinuousLinearEquiv
        (by simp)).bijective.comp ?_)
    have hinjv : Injective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x) :=
      ((isSmoothEmbedding_closedCell_inclusion 2).isImmersion.isImmersionAt _).mfderiv_injective
        (by simp)
    exact bijective_of_injective_continuousLinearMap (V := EuclideanSpace ℝ (Fin 3)) hinjv
  have hfi : Injective f := by
    intro x y h
    have h' : A x.val = A y.val := D.symm.injective (Subtype.ext h)
    exact Subtype.ext (A.toPartialEquiv.injOn (hAs x) (hAs y) h')
  have hfimg : ∀ s : Set (EuclideanSpace ℝ (Fin 3)), s ⊆ Metric.closedBall 0 1 →
      f '' {x : ClosedCell 3 | x.val ∈ s} = Subtype.val '' (A '' s) := by
    intro s hs
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A x.val, ⟨x.val, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, mem_closedBall_zero_iff.mp (hs hx)⟩, hx, rfl⟩
  -- the piece, on the lifted cell
  let e' : ULift.{u} (ClosedCell 3) ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
    (DifferentialGeometry.Topology.uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm
  have hconn : ConnectedSpace (ULift.{u} (ClosedCell 3)) := by
    have := closedCell_three_connectedSpace
    exact (Homeomorph.ulift : ULift.{u} (ClosedCell 3) ≃ₜ ClosedCell 3).symm.surjective.connectedSpace
      (Homeomorph.ulift : ULift.{u} (ClosedCell 3) ≃ₜ ClosedCell 3).symm.continuous
  let P' : PieceEmbedding X.Q :=
    { Piece := ULift.{u} (ClosedCell 3)
      compact := (Homeomorph.ulift : ULift.{u} (ClosedCell 3) ≃ₜ ClosedCell 3).symm.compactSpace
      secondCountable := (Homeomorph.ulift : ULift.{u} (ClosedCell 3) ≃ₜ ClosedCell 3).secondCountableTopology
      connected := hconn
      map := f ∘ e'
      smooth := hf.comp e'.contMDiff
      mfderiv_bijective := fun q => by
        rw [mfderiv_comp q (hf.mdifferentiableAt (by simp)) (e'.contMDiff.mdifferentiableAt (by simp))]
        exact (hfb _).comp (e'.mfderivToContinuousLinearEquiv (by simp) q).bijective
      injective := hfi.comp e'.injective }
  have hrangeP : range P'.map = range f := e'.surjective.range_comp f
  have hbdP : P'.map '' (𝓡∂ 3).boundary P'.Piece = f '' (𝓡∂ 3).boundary (ClosedCell 3) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨e' q, ((e'.isLocalDiffeomorph q).isBoundaryPoint_iff (by simp)).mp hq, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e'.symm x, ((e'.isLocalDiffeomorph _).isBoundaryPoint_iff (by simp)).mpr ?_, ?_⟩
      · rw [Diffeomorph.apply_symm_apply]
        exact hx
      · change f (e' (e'.symm x)) = f x
        rw [Diffeomorph.apply_symm_apply]
  refine ⟨P', e', ?_, ?_⟩
  · have hr : range f = f '' {x : ClosedCell 3 | x.val ∈ Metric.closedBall 0 1} := by
      rw [← image_univ]
      congr 1
      ext x
      simp only [mem_univ, true_iff]
      exact mem_closedBall_zero_iff.mpr x.2
    rw [hrangeP, hr, hfimg _ subset_rfl, hAcl, image_union]
    congr 1
    · ext y
      constructor
      · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
        exact ⟨e₀ p, rfl⟩
      · rintro ⟨q, rfl⟩
        obtain ⟨p, rfl⟩ := e₀.surjective q
        exact ⟨F₀' p, ⟨p, rfl⟩, rfl⟩
    · ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, mem_closedBall_zero_iff.mp hx⟩, (hGval ⟨x, _⟩).symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨G x.val, ⟨x.val, mem_closedBall_zero_iff.mpr x.2, rfl⟩, hGval x⟩
  · have hb : (𝓡∂ 3).boundary (ClosedCell 3) =
        {x : ClosedCell 3 | x.val ∈ Metric.sphere 0 1} := by
      rw [closedCell_boundary_eq_sphere 2]
      ext x
      simp
    rw [hbdP, hb, hfimg _ Metric.sphere_subset_closedBall, hAsph]
    ext y
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨F₀' (z, iccOne), ⟨z, rfl⟩, rfl⟩

end Interval

end SphereCutCapped

/-! ## Certificate level -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- A face that is not an external port lies in `W.interior`. -/
theorem face_subset_interior (f : Fin D.faceCount) (hf : ∀ i, D.faceKind f ≠ .external i) :
    D.face f ⊆ W.interior := by
  cases hk : D.faceKind f with
  | external i => exact (hf i hk).elim
  | torusSeam c b =>
    rw [(D.face_torusSeam f c b hk).1]
    rintro _ ⟨t, rfl⟩
    apply (D.torusSeam c).target_interior
    apply (D.torusSeam c).collar.map_source
    rw [(D.torusSeam c).source_eq]
    exact ⟨by norm_num, by norm_num⟩
  | sphereSeam c b =>
    rw [(D.face_sphereSeam f c b hk).1]
    rintro _ ⟨z, rfl⟩
    exact (D.sphereSeam c).target_interior
      ((D.sphereSeam c).collar.map_source ((D.sphereSeam c).zero_mem_source z))
  | partitioned =>
    rw [← D.face_partition f hk]
    rintro x ((hx | hx) | hx)
    · obtain ⟨h, hx⟩ := mem_iUnion.mp hx
      obtain ⟨b, hx⟩ := mem_iUnion.mp hx
      obtain ⟨-, ⟨y, rfl⟩⟩ := mem_iUnion.mp hx
      exact (D.handle h).interior ⟨_, rfl⟩
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      obtain ⟨-, hx⟩ := mem_iUnion.mp hx
      rw [D.arcFace_eq j] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact D.circ.domain_interior y.2
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      obtain ⟨-, hx⟩ := mem_iUnion.mp hx
      rw [D.loopFace_eq j] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact D.circ.domain_interior y.2

/-- A face is not a torus port if it is the injective image of the two-sphere. -/
theorem faceKind_ne_external_of_sphere (f : Fin D.faceCount)
    {g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → W.Carrier} (hg : Continuous g)
    (hginj : Injective g) (hface : D.face f = range g) (i : Fin n) :
    D.faceKind f ≠ .external i := by
  intro hk
  have h1 : range g = range (E.torusMap i) := hface.symm.trans (D.face_external f i hk).1
  let φ : range g ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ((hg.isClosedEmbedding hginj).isEmbedding.toHomeomorph).symm
  let ψ : range g ≃ₜ Circle × Circle :=
    (Homeomorph.setCongr h1).trans
      (homeomorphRangeOfTorus (E.torusMap_isEmbedding i).continuous
        (E.torusMap_isEmbedding i).injective)
  exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ ψ

/-- The two ends of an `S² × I` piece, and its model boundary. -/
theorem boundary_image_sphereIcc (Q : PieceEmbedding W)
    (e₁ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1),
      𝓡∂ 3⟯ Q.Piece) :
    Q.map '' (𝓡∂ 3).boundary Q.Piece =
      (range fun z => Q.map (e₁ (z, iccZero))) ∪ range fun z => Q.map (e₁ (z, iccOne)) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, rfl⟩ := e₁.surjective q
    have hp : ((𝓡 2).prod (𝓡∂ 1)).IsBoundaryPoint p :=
      ((e₁.isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)).mpr hq
    rcases snd_eq_of_isBoundaryPoint_sphereIcc hp with h | h
    · exact Or.inl ⟨p.1, by rw [show p = (p.1, iccZero) from Prod.ext rfl h]; rfl⟩
    · exact Or.inr ⟨p.1, by rw [show p = (p.1, iccOne) from Prod.ext rfl h]; rfl⟩
  · have hbd : ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (t : Icc (0 : ℝ) 1),
        (t = iccZero ∨ t = iccOne) → e₁ (z, t) ∈ (𝓡∂ 3).boundary Q.Piece := by
      intro z t ht
      apply ((e₁.isLocalDiffeomorph (z, t)).isBoundaryPoint_iff (by simp)).mp
      have hmem : (z, t) ∈ ((𝓡 2).prod (𝓡∂ 1)).boundary
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) := by
        rw [boundary_product]
        refine ⟨mem_univ _, ?_⟩
        rcases ht with rfl | rfl
        · exact Or.inl (Subtype.ext rfl)
        · exact Or.inr (Subtype.ext rfl)
      exact hmem
    rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨_, hbd z iccZero (Or.inl rfl), rfl⟩
    · exact ⟨_, hbd z iccOne (Or.inr rfl), rfl⟩

/-- The `S² × I` side of a sphere seam, parametrized with its end `0` on the seam sphere and its
end `1` (the rest of its model boundary) in `W.interior`. -/
theorem exists_sphereIcc_param (c : Fin D.sphereSeamCount) (b : Bool) {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :
    ∃ e₀ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1),
        𝓡∂ 3⟯ (D.vertex (D.sphereSide c b)).piece.Piece,
      (range fun z => (D.vertex (D.sphereSide c b)).piece.map (e₀ (z, iccZero))) =
        (D.sphereSeam c).zeroSphere ∧
      (∀ z, (D.vertex (D.sphereSide c b)).piece.map (e₀ (z, iccOne)) ∈ W.interior) ∧
      (D.vertex (D.sphereSide c b)).boundaryImage \ (D.sphereSeam c).zeroSphere =
        range fun z => (D.vertex (D.sphereSide c b)).piece.map (e₀ (z, iccOne)) := by
  set v := D.sphereSide c b with hvdef
  set Q := (D.vertex v).piece with hQdef
  have hQ : Q = P := by rw [hQdef, hv]; rfl
  have e₂ : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ Q.Piece := hQ ▸ e
  let e₁ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1),
      𝓡∂ 3⟯ Q.Piece :=
    ((DifferentialGeometry.Topology.uliftDiffeomorph (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).prodCongr
        (Diffeomorph.refl (𝓡∂ 1) (Icc (0 : ℝ) 1) ∞)).trans e₂
  let tOf : Bool → Icc (0 : ℝ) 1 := fun β => if β then iccOne else iccZero
  let A : Bool → Set W.Carrier := fun β => range fun z => Q.map (e₁ (z, tOf β))
  have hcont : ∀ β, Continuous fun z => Q.map (e₁ (z, tOf β)) := fun β =>
    Q.continuous_map.comp (e₁.continuous.comp (continuous_id.prodMk continuous_const))
  have hinj' : ∀ β, Injective fun z => Q.map (e₁ (z, tOf β)) := fun β z w h =>
    congrArg Prod.fst (e₁.injective (Q.injective h))
  have hS2 : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  have hconn : ∀ β, IsPreconnected (A β) := fun β => (isConnected_range (hcont β)).isPreconnected
  have hclosed : ∀ β, IsClosed (A β) := fun β => (isCompact_range (hcont β)).isClosed
  have htOf : ∀ β, tOf β ≠ tOf (!β) := by
    intro β h
    have h' := congrArg Subtype.val h
    cases β <;> simp [tOf, iccZero, iccOne] at h'
  have hdisj : ∀ β, Disjoint (A β) (A (!β)) := by
    intro β
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    have h := congrArg Prod.snd (e₁.injective (Q.injective hw))
    exact htOf β h.symm
  have hbI : (D.vertex v).boundaryImage = A false ∪ A true := boundary_image_sphereIcc Q e₁
  have hbI' : ∀ β, (D.vertex v).boundaryImage = A β ∪ A (!β) := by
    intro β
    cases β
    · exact hbI
    · rw [hbI, union_comm]
      rfl
  -- a face of `v` meeting an end is that end
  have hface : ∀ (f' : Fin D.faceCount), D.faceOwner f' = v → ∀ (β : Bool) (x : W.Carrier),
      x ∈ D.face f' → x ∈ A β → D.face f' = A β := by
    intro f' hf' β x hxf hxA
    have hsubB : D.face f' ⊆ (D.vertex v).boundaryImage := hf' ▸ D.face_subset_boundaryImage f'
    apply Subset.antisymm
    · rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (D.isConnected_face f').isPreconnected)
        (A β) (A (!β)) (hclosed β) (hclosed (!β)) (hbI' β ▸ hsubB)
        (by rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj β), inter_empty]) with h | h
      · exact h
      · exact (Set.disjoint_left.mp (hdisj β) hxA (h hxf)).elim
    · rw [D.face_eq_connectedComponentIn f' hxf, hf']
      exact (hconn β).subset_connectedComponentIn hxA (hbI' β ▸ subset_union_left)
  -- the cut end
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face c b
  have hfZ : D.face f = (D.sphereSeam c).zeroSphere := (D.face_sphereSeam f c b hfk).1
  obtain ⟨z₀, hz₀⟩ := D.face_nonempty f
  have hz₀B : z₀ ∈ A false ∪ A true := hbI ▸ (hfo ▸ D.face_subset_boundaryImage f) hz₀
  obtain ⟨β, hβ⟩ : ∃ β, z₀ ∈ A β := by
    rcases hz₀B with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have hZA : (D.sphereSeam c).zeroSphere = A β := hfZ ▸ hface f hfo β z₀ hz₀ hβ
  -- the far end lies in `W.interior`
  have hfar : A (!β) ⊆ W.interior := by
    intro x hx
    have hxB : x ∈ (D.vertex v).boundaryImage := by rw [hbI' β]; exact Or.inr hx
    rw [← D.face_exhausted v] at hxB
    obtain ⟨f', hf'⟩ := mem_iUnion.mp hxB
    obtain ⟨hf'o, hxf'⟩ := mem_iUnion.mp hf'
    have hfeq := hface f' hf'o (!β) x hxf' hx
    exact D.face_subset_interior f'
      (fun i => D.faceKind_ne_external_of_sphere f' (hcont (!β)) (hinj' (!β)) hfeq i) hxf'
  have hdiff : (D.vertex v).boundaryImage \ (D.sphereSeam c).zeroSphere = A (!β) := by
    rw [hbI' β, hZA, union_sdiff_left]
    exact (hdisj β).symm.sdiff_eq_left
  cases β with
  | false =>
    refine ⟨e₁, hZA.symm, fun z => hfar ⟨z, rfl⟩, hdiff⟩
  | true =>
    let e₀ := ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      iccReflect).trans e₁
    have h0 : ∀ z, e₀ (z, iccZero) = e₁ (z, iccOne) := fun z => by
      change e₁ (z, iccReflect iccZero) = e₁ (z, iccOne)
      congr 2
      exact Subtype.ext (by rw [iccReflect_val]; simp [iccZero, iccOne])
    have h1 : ∀ z, e₀ (z, iccOne) = e₁ (z, iccZero) := fun z => by
      change e₁ (z, iccReflect iccOne) = e₁ (z, iccZero)
      congr 2
      exact Subtype.ext (by rw [iccReflect_val]; simp [iccZero, iccOne])
    refine ⟨e₀, ?_, fun z => ?_, ?_⟩
    · rw [hZA]
      ext x
      simp only [mem_range, h0]
      rfl
    · rw [h1]
      exact hfar ⟨z, rfl⟩
    · rw [hdiff]
      ext x
      simp only [mem_range, h1]
      rfl

/-- **S3a, `S² × I` ∪ one cap = ball** (actual attaching map): the lifted `S² × I` side and the cap
of its copy form a piece of the capped carrier with the ball model, whose image is the union and
whose model boundary is the transport of the uncut end. -/
theorem exists_capUnion_ball_of_sphereInterval (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool) {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :
    ∃ (P' : PieceEmbedding X.Q) (_ : P'.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3),
      range P'.map = range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) ∧
      P'.map '' (𝓡∂ 3).boundary P'.Piece =
        X.transport '' ((D.vertex (D.sphereSide c b)).boundaryImage \
          (D.sphereSeam c).zeroSphere) := by
  obtain ⟨e₀, hcut, hfar, hdiff⟩ := D.exists_sphereIcc_param c b hv
  have hcap : X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c (D.sphereSide c b)))) =
      X.capping.cap (Fin.cast X.h2.symm (sideCopy b)) := by
    rw [D.sideCopy_vertexSide c b]
  obtain ⟨P', e', hr, hbd⟩ := X.exists_capUnion_ballPiece (D.vertex (D.sphereSide c b)).piece
    (sideCopy (D.vertexSide c (D.sphereSide c b)))
    (fun _ _ hp h => D.vertex_side_condition c (D.sphereSide c b) hp h) e₀ hcut hfar
  have hnot : ∀ z, (D.vertex (D.sphereSide c b)).piece.map (e₀ (z, iccOne)) ∉
      (D.sphereSeam c).zeroSphere := fun z => by
    have h : (D.vertex (D.sphereSide c b)).piece.map (e₀ (z, iccOne)) ∈
        (D.vertex (D.sphereSide c b)).boundaryImage \ (D.sphereSeam c).zeroSphere := by
      rw [hdiff]
      exact ⟨z, rfl⟩
    exact h.2
  refine ⟨P', e', ?_, ?_⟩
  · rw [hr, hcap]
    rfl
  · rw [hbd, hdiff]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, (X.liftPiece_map_of_notMem _ _ _ (hnot z)).symm⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, X.liftPiece_map_of_notMem _ _ _ (hnot z)⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
