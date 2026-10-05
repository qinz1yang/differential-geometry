import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapInterval
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleThirdPiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionRounding

/-!
# FC42 normalization, packets N2–N3 (tools): splitting an `S² × I` vertex at its middle sphere

Lane ASM-NRM3 (route of `build-logs/resume/state-ASM-NRM.md`, "D″ for N3a"). For an injective piece
`P` with `e : S² × [0, 1] ≅ P` (the data of an `S² × I` vertex):

* `isLocalDiffeomorphAt_of_interior_bijective_on`: the inverse function theorem between interior
  points of manifolds that may have boundary, for a map smooth on an open neighbourhood;
* the halves: `iccHalfMap` (`t ↦ t / 2`, `t ↦ (1 + t) / 2`), `PieceEmbedding.sphereHalf` (same piece
  type, map reparametrized), their images (`mem_range_sphereHalf_true_iff`, …, `range_sphereHalf_union`)
  through the height `PieceEmbedding.sphereHeight`, their model boundaries
  (`image_boundary_sphereHalf_true/false`) through the level spheres `PieceEmbedding.sphereLevel`, and
  `disjoint_interior_sphereHalf`;
* the middle seam `PieceEmbedding.middleSeam` (collar `(z, s) ↦ P (e (z, 1/2 + s/4))`, an injective
  local diffeomorphism on `S² × (-1, 1)`), its target inside the compact middle zone
  `PieceEmbedding.middleZone` (`S² × [1/4, 3/4]`), which lies in `interior (range P.map) ∩ W.interior`;
* the circle region is the closure of its interior in the open-set form
  `CircleRegion.inter_interior_region_nonempty` (depth zero; depth one: a regular defining function
  has no local minimum; a corner: the diagonal of its corner chart);
* certificate level: the ambient interior of a vertex image meets no other vertex, handle, region
  point, or (if the vertex is no torus side) torus seam collar; the faces of an `S² × I` vertex are
  its end spheres (`face_eq_sphereLevel_of_sphereInterval`, `exists_face_eq_sphereLevel`), so it is no
  torus side and owns no port; the middle sphere meets no face; the vertex side of a rim chart
  avoiding the middle zone stays in the half of its end sphere (`rimChart_mem_sphereHalf`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASMNRM3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMNRM3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

section IFT

variable {E F H H' S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

/-- **Inverse function theorem between interior points** (both models may have boundary): a map
smooth on an open neighbourhood of an interior point, with bijective differential there and an
interior image point, is a local diffeomorphism there. -/
theorem isLocalDiffeomorphAt_of_interior_bijective_on {f : S → M} {U : Set S} (hU : IsOpen U)
    (hf : ContMDiffOn I J ∞ f U) {x : S} (hxU : x ∈ U)
    (hx : I.IsInteriorPoint x) (hfx : J.IsInteriorPoint (f x))
    (hbij : Bijective (mfderiv I J f x)) : IsLocalDiffeomorphAt I J ∞ f x := by
  let cS := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let cM := DifferentialGeometry.Manifold.interiorChart J ∞ (f x)
  have hxS : x ∈ cS.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hxM : f x ∈ cM.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J ∞ (f x)).mpr hfx
  have hxx : cS.symm (cS x) = x := cS.left_inv hxS
  have hfat : ContMDiffAt I J ∞ f x := hf.contMDiffAt (hU.mem_nhds hxU)
  let G : E → F := cM ∘ f ∘ cS.symm
  let D₀ : Set S := U ∩ f ⁻¹' cM.source
  have hD₀ : IsOpen D₀ := hf.continuousOn.isOpen_inter_preimage hU cM.open_source
  let V : Set E := cS.target ∩ cS.symm ⁻¹' D₀
  have hV : IsOpen V := cS.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hD₀
  have hcx : cS x ∈ V := ⟨cS.map_source hxS, by
    change cS.symm (cS x) ∈ D₀
    rw [hxx]
    exact ⟨hxU, hxM⟩⟩
  have hG : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G V :=
    cM.contMDiffOn_toFun.comp ((hf.mono inter_subset_left).comp
      (cS.contMDiffOn_invFun.mono inter_subset_left) (fun y hy => hy.2))
      (fun y hy => hy.2.2)
  have hcS : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ cS.symm (cS x) :=
    cS.symm.isLocalDiffeomorphAt _ _ _ (cS.map_source hxS)
  have hcM : IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ cM (f x) := cM.isLocalDiffeomorphAt _ _ _ hxM
  let A₁ : E ≃L[ℝ] E := hcS.mfderivToContinuousLinearEquiv (by simp)
  let A₂ : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap hbij).toContinuousLinearEquiv
  let A₃ : F ≃L[ℝ] F := hcM.mfderivToContinuousLinearEquiv (by simp)
  have h1 : HasMFDerivAt 𝓘(ℝ, E) I cS.symm (cS x) (A₁ : E →L[ℝ] E) :=
    (hcS.mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt I J f (cS.symm (cS x)) (A₂ : E →L[ℝ] F) := by
    rw [hxx]
    exact (hfat.mdifferentiableAt (by simp)).hasMFDerivAt
  have h3 : HasMFDerivAt J 𝓘(ℝ, F) cM (f (cS.symm (cS x))) (A₃ : F →L[ℝ] F) := by
    rw [hxx]
    exact (hcM.mdifferentiableAt (by simp)).hasMFDerivAt
  have hGd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) G (cS x) ((A₁.trans (A₂.trans A₃) : E ≃L[ℝ] F) :
      E →L[ℝ] F) := by
    have hc := h3.comp (cS x) (h2.comp (cS x) h1)
    have heq : ((A₁.trans (A₂.trans A₃) : E ≃L[ℝ] F) : E →L[ℝ] F) =
        (A₃ : F →L[ℝ] F).comp ((A₂ : E →L[ℝ] F).comp (A₁ : E →L[ℝ] E)) := by
      ext v
      rfl
    rw [heq]
    exact hc
  have hGloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G (cS x) :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      G hG hV (cS x) hcx _ hGd
  have hGx : G (cS x) ∈ cM.target := by
    change cM (f (cS.symm (cS x))) ∈ cM.target
    rw [hxx]
    exact cM.map_source hxM
  have hcMs : IsLocalDiffeomorphAt 𝓘(ℝ, F) J ∞ cM.symm (G (cS x)) :=
    cM.symm.isLocalDiffeomorphAt _ _ _ hGx
  have htot := ((cS.isLocalDiffeomorphAt _ _ _ hxS).comp _ _ hGloc).comp _ _ hcMs
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ htot
  filter_upwards [cS.open_source.mem_nhds hxS,
    hf.continuousOn.continuousAt (hU.mem_nhds hxU) |>.preimage_mem_nhds
      (cM.open_source.mem_nhds hxM)] with y hy hyM
  have ey : cS.toPartialEquiv.symm (cS.toPartialEquiv y) = y := cS.toPartialEquiv.left_inv hy
  have eM : cM.toPartialEquiv.symm (cM.toPartialEquiv (f y)) = f y :=
    cM.toPartialEquiv.left_inv hyM
  change f y = cM.toPartialEquiv.symm (cM.toPartialEquiv (f (cS.toPartialEquiv.symm
    (cS.toPartialEquiv y))))
  rw [ey, eM]

end IFT

/-! ## The halves of the unit interval -/

/-- The two halves of `[0, 1]`: `t ↦ t / 2` (`b = true`, the lower half) and `t ↦ (1 + t) / 2`
(`b = false`, the upper half). -/
def iccHalfMap (b : Bool) (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨((t : ℝ) + cond b 0 1) / 2, by
    cases b
    · exact ⟨by simp only [Bool.cond_false]; linarith [t.2.1], by simp only [Bool.cond_false]; linarith [t.2.2]⟩
    · exact ⟨by simp only [Bool.cond_true]; linarith [t.2.1], by simp only [Bool.cond_true]; linarith [t.2.2]⟩⟩

theorem iccHalfMap_val (b : Bool) (t : Icc (0 : ℝ) 1) :
    (iccHalfMap b t : ℝ) = ((t : ℝ) + cond b 0 1) / 2 := rfl

theorem contMDiff_iccHalfMap (b : Bool) : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (iccHalfMap b) := by
  have ha : ContDiff ℝ ∞ (fun x : ℝ => (x + cond b 0 1) / 2) := by fun_prop
  refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const 2) _
  · exact ha.contMDiff.comp contMDiff_subtypeVal_Icc

theorem mfderiv_iccHalfMap_bijective (b : Bool) (t : Icc (0 : ℝ) 1) :
    Bijective (mfderiv (𝓡∂ 1) (𝓡∂ 1) (iccHalfMap b) t) := by
  set a : ℝ → ℝ := fun x => (x + cond b 0 1) / 2 with ha_def
  have hval : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (iccHalfMap b t) :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp)
  have hval' : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) t :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) (iccHalfMap b) t :=
    (contMDiff_iccHalfMap b).mdifferentiableAt (by simp)
  have hda : HasDerivAt a (1 / 2) (t : ℝ) := by
    have := ((hasDerivAt_id (t : ℝ)).add_const (cond b 0 1)).div_const 2
    simpa [ha_def] using this
  have hma : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a (t : ℝ) :=
    hda.differentiableAt.mdifferentiableAt
  have hc1 := mfderiv_comp t hval hι
  have hc2 := mfderiv_comp t hma hval'
  have hfun : (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) ∘ iccHalfMap b =
      a ∘ (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) := rfl
  rw [hfun] at hc1
  rw [hc1] at hc2
  have hs := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).isImmersion
  have hinj : Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) (iccHalfMap b) t) := by
    intro v w hvw
    apply hs.mfderiv_injective (by simp) t
    have h1 : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (iccHalfMap b t)
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) (iccHalfMap b) t v) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a (t : ℝ)
          (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) t v) :=
      DFunLike.congr_fun hc2 v
    have h2 : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (iccHalfMap b t)
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) (iccHalfMap b) t w) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a (t : ℝ)
          (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) t w) :=
      DFunLike.congr_fun hc2 w
    rw [hvw] at h1
    have hL : ∀ x : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a (t : ℝ) x = x * (1 / 2) := by
      intro x
      rw [mfderiv_eq_fderiv]
      calc fderiv ℝ a (t : ℝ) x = fderiv ℝ a (t : ℝ) (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
        _ = x • fderiv ℝ a (t : ℝ) 1 := map_smul _ _ _
        _ = x * (1 / 2) := by rw [fderiv_apply_one_eq_deriv, hda.deriv, smul_eq_mul]
    have h3 := h1.symm.trans h2
    set X := mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) t
    let x₁ : ℝ := X v
    let x₂ : ℝ := X w
    have h4 : x₁ * (1 / 2 : ℝ) = x₂ * (1 / 2 : ℝ) :=
      ((hL (X v)).symm.trans h3).trans (hL (X w))
    have h5 : x₁ = x₂ := mul_right_cancel₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) h4
    exact h5
  exact bijective_of_injective_continuousLinearMap (V := EuclideanSpace ℝ (Fin 1)) hinj

theorem injective_iccHalfMap (b : Bool) : Injective (iccHalfMap b) := by
  intro t t' h
  have h' := congrArg Subtype.val h
  rw [iccHalfMap_val, iccHalfMap_val] at h'
  exact Subtype.ext (by linarith)

/-- The midpoint of `[0, 1]`. -/
def iccMid : Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

theorem iccHalfMap_true_zero : iccHalfMap true iccZero = iccZero :=
  Subtype.ext (by simp [iccHalfMap_val, iccZero])

theorem iccHalfMap_true_one : iccHalfMap true iccOne = iccMid :=
  Subtype.ext (by simp [iccHalfMap_val, iccOne, iccMid])

theorem iccHalfMap_false_zero : iccHalfMap false iccZero = iccMid :=
  Subtype.ext (by simp [iccHalfMap_val, iccZero, iccMid])

theorem iccHalfMap_false_one : iccHalfMap false iccOne = iccOne :=
  Subtype.ext (by norm_num [iccHalfMap_val, iccOne])

/-- The boundary points of `S² × [0, 1]` are the two ends. -/
theorem isBoundaryPoint_sphereIcc_iff {p : ClosureSphere.{u} × Icc (0 : ℝ) 1} :
    ((𝓡 2).prod (𝓡∂ 1)).IsBoundaryPoint p ↔ p.2 = iccZero ∨ p.2 = iccOne := by
  change p ∈ ((𝓡 2).prod (𝓡∂ 1)).boundary (ClosureSphere.{u} × Icc (0 : ℝ) 1) ↔ _
  have h0 : (⊥ : Icc (0 : ℝ) 1) = iccZero := Subtype.ext rfl
  have h1 : (⊤ : Icc (0 : ℝ) 1) = iccOne := Subtype.ext rfl
  rw [boundary_product, h0, h1]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-! ## The halves of an `S² × I` piece -/

section Halves

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X]
  (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ X)

/-- The reparametrization of an `S² × I` piece by a half of the interval. -/
def sphereHalfReparam (b : Bool) (q : X) : X :=
  e (Prod.map id (iccHalfMap b) (e.symm q))

theorem sphereHalfReparam_apply (b : Bool) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    sphereHalfReparam e b (e p) = e (p.1, iccHalfMap b p.2) := by
  simp only [sphereHalfReparam, Diffeomorph.symm_apply_apply]
  rfl

theorem contMDiff_sphereHalfReparam (b : Bool) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (sphereHalfReparam e b) :=
  e.contMDiff.comp ((contMDiff_id.prodMap (contMDiff_iccHalfMap b)).comp e.symm.contMDiff)

theorem injective_sphereHalfReparam (b : Bool) : Injective (sphereHalfReparam e b) := by
  intro q q' h
  have h1 := e.injective h
  have hA := congrArg Prod.fst h1
  have hB := congrArg Prod.snd h1
  exact e.symm.injective (Prod.ext hA (injective_iccHalfMap b hB))

theorem mfderiv_sphereHalfReparam_bijective (b : Bool) (q : X) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (sphereHalfReparam e b) q) := by
  have hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (Prod.map id (iccHalfMap b) : ClosureSphere.{u} × Icc (0 : ℝ) 1 → _) :=
    contMDiff_id.prodMap (contMDiff_iccHalfMap b)
  rw [show sphereHalfReparam e b = e ∘ (Prod.map id (iccHalfMap b) ∘ e.symm) from rfl,
    mfderiv_comp q (e.contMDiff.mdifferentiableAt (by simp))
      ((hm.comp e.symm.contMDiff).mdifferentiableAt (by simp)),
    mfderiv_comp q (hm.mdifferentiableAt (by simp)) (e.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_prodMap mdifferentiableAt_id ((contMDiff_iccHalfMap b).mdifferentiableAt (by simp)),
    mfderiv_id]
  exact (e.mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
    ((Function.bijective_id.prodMap (mfderiv_iccHalfMap_bijective b _)).comp
      (e.symm.mfderivToContinuousLinearEquiv (by simp) q).bijective)

end Halves

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W)
  (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)

/-- **A half of an `S² × I` piece**: the same piece type, the map reparametrized by
`t ↦ t / 2` (`b = true`) or `t ↦ (1 + t) / 2` (`b = false`). -/
def sphereHalf (b : Bool) : PieceEmbedding W :=
  { P with
    map := P.map ∘ sphereHalfReparam e b
    smooth := P.smooth.comp (contMDiff_sphereHalfReparam e b)
    mfderiv_bijective := fun q => by
      rw [mfderiv_comp q (P.smooth.mdifferentiableAt (by simp))
        ((contMDiff_sphereHalfReparam e b).mdifferentiableAt (by simp))]
      exact (P.mfderiv_bijective _).comp (mfderiv_sphereHalfReparam_bijective e b q)
    injective := P.injective.comp (injective_sphereHalfReparam e b) }

theorem sphereHalf_map_apply (b : Bool) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    (P.sphereHalf e b).map (e p) = P.map (e (p.1, iccHalfMap b p.2)) := by
  change P.map (sphereHalfReparam e b (e p)) = _
  rw [sphereHalfReparam_apply]

/-- The level sphere at height `t` of an `S² × I` piece. -/
def sphereLevel (t : Icc (0 : ℝ) 1) : Set W.Carrier :=
  range fun z : ClosureSphere.{u} => P.map (e (z, t))

/-- The height (the interval coordinate) of a point of an `S² × I` piece. -/
def sphereHeight (x : W.Carrier) : ℝ :=
  ((e.symm (invFun P.map x)).2 : ℝ)

theorem sphereHeight_map (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    P.sphereHeight e (P.map (e p)) = p.2 := by
  simp only [sphereHeight, leftInverse_invFun P.injective (e p), Diffeomorph.symm_apply_apply]

theorem exists_eq_map_of_mem_range {x : W.Carrier} (hx : x ∈ range P.map) :
    ∃ p : ClosureSphere.{u} × Icc (0 : ℝ) 1, x = P.map (e p) := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨e.symm q, by rw [Diffeomorph.apply_symm_apply]⟩

theorem continuousOn_sphereHeight : ContinuousOn (P.sphereHeight e) (range P.map) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (range P.map).domRestrict (P.sphereHeight e) =
      fun x => ((e.symm (P.homeomorphRange.symm x)).2 : ℝ) := by
    funext x
    have hq : invFun P.map (x : W.Carrier) = P.homeomorphRange.symm x := by
      apply P.injective
      rw [invFun_eq x.2, ← P.homeomorphRange_apply, Homeomorph.apply_symm_apply]
    simp only [domRestrict_apply, sphereHeight, hq]
  rw [h]
  exact continuous_subtype_val.comp
    (continuous_snd.comp (e.symm.continuous.comp P.homeomorphRange.symm.continuous))

variable {P e} in
theorem mem_sphereLevel_iff {x : W.Carrier} {t : Icc (0 : ℝ) 1} :
    x ∈ P.sphereLevel e t ↔ x ∈ range P.map ∧ P.sphereHeight e x = t := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨_, rfl⟩, P.sphereHeight_map e (z, t)⟩
  · rintro ⟨hx, ht⟩
    obtain ⟨p, rfl⟩ := P.exists_eq_map_of_mem_range e hx
    rw [sphereHeight_map] at ht
    refine ⟨p.1, ?_⟩
    rw [show t = p.2 from Subtype.ext ht.symm]

variable {P e} in
theorem mem_range_sphereHalf_true_iff {x : W.Carrier} :
    x ∈ range (P.sphereHalf e true).map ↔ x ∈ range P.map ∧ P.sphereHeight e x ≤ 1 / 2 := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, e p = q := ⟨e.symm q, e.apply_symm_apply q⟩
    rw [sphereHalf_map_apply, sphereHeight_map, iccHalfMap_val]
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp only [Bool.cond_true, add_zero]
    linarith [p.2.2.2]
  · rintro ⟨hx, ht⟩
    obtain ⟨p, rfl⟩ := P.exists_eq_map_of_mem_range e hx
    rw [sphereHeight_map] at ht
    let s : Icc (0 : ℝ) 1 := ⟨2 * p.2, by linarith [p.2.2.1], by linarith⟩
    refine ⟨e (p.1, s), ?_⟩
    rw [sphereHalf_map_apply]
    have hs : iccHalfMap true s = p.2 := Subtype.ext (by simp [iccHalfMap_val, s])
    simp only [hs]

variable {P e} in
theorem mem_range_sphereHalf_false_iff {x : W.Carrier} :
    x ∈ range (P.sphereHalf e false).map ↔ x ∈ range P.map ∧ 1 / 2 ≤ P.sphereHeight e x := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, e p = q := ⟨e.symm q, e.apply_symm_apply q⟩
    rw [sphereHalf_map_apply, sphereHeight_map, iccHalfMap_val]
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp only [Bool.cond_false]
    linarith [p.2.2.1]
  · rintro ⟨hx, ht⟩
    obtain ⟨p, rfl⟩ := P.exists_eq_map_of_mem_range e hx
    rw [sphereHeight_map] at ht
    let s : Icc (0 : ℝ) 1 := ⟨2 * p.2 - 1, by linarith, by linarith [p.2.2.2]⟩
    refine ⟨e (p.1, s), ?_⟩
    rw [sphereHalf_map_apply]
    have hs : iccHalfMap false s = p.2 := Subtype.ext (by simp [iccHalfMap_val, s])
    simp only [hs]

theorem range_sphereHalf_subset (b : Bool) : range (P.sphereHalf e b).map ⊆ range P.map := by
  intro x hx
  cases b
  · exact (PieceEmbedding.mem_range_sphereHalf_false_iff.mp hx).1
  · exact (PieceEmbedding.mem_range_sphereHalf_true_iff.mp hx).1

theorem range_sphereHalf_union :
    range (P.sphereHalf e true).map ∪ range (P.sphereHalf e false).map = range P.map := by
  refine Subset.antisymm (union_subset (P.range_sphereHalf_subset e true)
    (P.range_sphereHalf_subset e false)) fun x hx => ?_
  rcases le_total (P.sphereHeight e x) (1 / 2) with h | h
  · exact Or.inl (PieceEmbedding.mem_range_sphereHalf_true_iff.mpr ⟨hx, h⟩)
  · exact Or.inr (PieceEmbedding.mem_range_sphereHalf_false_iff.mpr ⟨hx, h⟩)

theorem sphereLevel_sphereHalf (b : Bool) (t : Icc (0 : ℝ) 1) :
    (P.sphereHalf e b).sphereLevel e t = P.sphereLevel e (iccHalfMap b t) := by
  unfold sphereLevel
  congr 1
  funext z
  exact P.sphereHalf_map_apply e b (z, t)

/-- The model boundary of an `S² × I` piece is the union of its two end spheres. -/
theorem image_boundary_sphereInterval :
    P.map '' (𝓡∂ 3).boundary P.Piece = P.sphereLevel e iccZero ∪ P.sphereLevel e iccOne := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, e p = q := ⟨e.symm q, e.apply_symm_apply q⟩
    have hp : ((𝓡 2).prod (𝓡∂ 1)).IsBoundaryPoint p :=
      ((e.isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)).mpr hq
    rcases isBoundaryPoint_sphereIcc_iff.mp hp with h | h
    · exact Or.inl ⟨p.1, by rw [show p = (p.1, iccZero) from Prod.ext rfl h]⟩
    · exact Or.inr ⟨p.1, by rw [show p = (p.1, iccOne) from Prod.ext rfl h]⟩
  · have hbd : ∀ (z : ClosureSphere.{u}) (t : Icc (0 : ℝ) 1), (t = iccZero ∨ t = iccOne) →
        e (z, t) ∈ (𝓡∂ 3).boundary P.Piece := fun z t ht =>
      ((e.isLocalDiffeomorph (z, t)).isBoundaryPoint_iff (by simp)).mp
        (isBoundaryPoint_sphereIcc_iff.mpr ht)
    rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨_, hbd z iccZero (Or.inl rfl), rfl⟩
    · exact ⟨_, hbd z iccOne (Or.inr rfl), rfl⟩

theorem image_boundary_sphereHalf_true :
    (P.sphereHalf e true).map '' (𝓡∂ 3).boundary (P.sphereHalf e true).Piece =
      P.sphereLevel e iccZero ∪ P.sphereLevel e iccMid := by
  rw [image_boundary_sphereInterval (P.sphereHalf e true) e, sphereLevel_sphereHalf,
    sphereLevel_sphereHalf, iccHalfMap_true_zero, iccHalfMap_true_one]

theorem image_boundary_sphereHalf_false :
    (P.sphereHalf e false).map '' (𝓡∂ 3).boundary (P.sphereHalf e false).Piece =
      P.sphereLevel e iccMid ∪ P.sphereLevel e iccOne := by
  rw [image_boundary_sphereInterval (P.sphereHalf e false) e, sphereLevel_sphereHalf,
    sphereLevel_sphereHalf, iccHalfMap_false_zero, iccHalfMap_false_one]

end PieceEmbedding

/-! ## The middle collar parameter -/

/-- The collar parameter `s ↦ 1/2 + s/4` of the middle sphere, clipped to `[0, 1]`. -/
def middleCollarParam (s : ℝ) : Icc (0 : ℝ) 1 :=
  projIcc 0 1 zero_le_one (1 / 2 + s / 4)

theorem middleCollarParam_val {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    (middleCollarParam s : ℝ) = 1 / 2 + s / 4 := by
  rw [middleCollarParam, projIcc_of_mem]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem middleCollarParam_zero : middleCollarParam 0 = iccMid :=
  Subtype.ext (by rw [middleCollarParam_val ⟨by norm_num, by norm_num⟩]; simp [iccMid])

theorem contMDiffAt_middleCollarParam {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ middleCollarParam s := by
  have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => 1 / 2 + x / 4) :=
    (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => 1 / 2 + x / 4)).contMDiff
  have hpr : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (projIcc (0 : ℝ) 1 zero_le_one) (1 / 2 + s / 4) :=
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).contMDiffAt
      (Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2]))
  exact hpr.comp s ha.contMDiffAt

theorem mfderiv_middleCollarParam_bijective {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) middleCollarParam s) := by
  set a : ℝ → ℝ := fun x => 1 / 2 + x / 4 with ha_def
  have hev : (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) ∘ middleCollarParam =ᶠ[𝓝 s] a := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact middleCollarParam_val hx
  have hval : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ))
      (middleCollarParam s) :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp)
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) middleCollarParam s :=
    (contMDiffAt_middleCollarParam hs).mdifferentiableAt (by simp)
  have hda : HasDerivAt a (1 / 4) s := by
    have := ((hasDerivAt_id s).div_const 4).const_add (1 / 2 : ℝ)
    simpa [ha_def] using this
  have hc := mfderiv_comp s hval hm
  rw [hev.mfderiv_eq] at hc
  have hL : ∀ x : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a s x = x * (1 / 4) := by
    intro x
    rw [mfderiv_eq_fderiv]
    calc fderiv ℝ a s x = fderiv ℝ a s (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = x • fderiv ℝ a s 1 := map_smul _ _ _
      _ = x * (1 / 4) := by rw [fderiv_apply_one_eq_deriv, hda.deriv, smul_eq_mul]
  have hinj : Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) middleCollarParam s) := by
    intro v w hvw
    have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a s v =
        mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (middleCollarParam s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) middleCollarParam s v) := DFunLike.congr_fun hc v
    have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a s w =
        mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (middleCollarParam s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) middleCollarParam s w) := DFunLike.congr_fun hc w
    rw [hvw, ← h2] at h1
    let x₁ : ℝ := v
    let x₂ : ℝ := w
    have h4 : x₁ * (1 / 4 : ℝ) = x₂ * (1 / 4 : ℝ) := ((hL v).symm.trans h1).trans (hL w)
    have h5 : x₁ = x₂ := mul_right_cancel₀ (by norm_num : (1 / 4 : ℝ) ≠ 0) h4
    exact h5
  have hd : Module.finrank ℝ ℝ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) := by simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hinj⟩

/-- An interior point of `S² × [0, 1]`: the height lies in the open interval. -/
theorem isInteriorPoint_sphereIcc {p : ClosureSphere.{u} × Icc (0 : ℝ) 1}
    (h0 : 0 < (p.2 : ℝ)) (h1 : (p.2 : ℝ) < 1) : ((𝓡 2).prod (𝓡∂ 1)).IsInteriorPoint p := by
  rcases ((𝓡 2).prod (𝓡∂ 1)).isInteriorPoint_or_isBoundaryPoint p with h | h
  · exact h
  · rcases isBoundaryPoint_sphereIcc_iff.mp h with h' | h'
    · rw [h'] at h0
      exact absurd h0 (lt_irrefl _)
    · rw [h'] at h1
      exact absurd h1 (lt_irrefl _)

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W)
  (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)

/-- The middle collar map `(z, s) ↦ P (e (z, 1/2 + s/4))`. -/
def middleCollarMap (p : ClosureSphere.{u} × ℝ) : W.Carrier :=
  P.map (e (p.1, middleCollarParam p.2))

theorem isInteriorPoint_middle {p : ClosureSphere.{u} × ℝ} (hp : p ∈ sphereSignedCollarSource) :
    (𝓡∂ 3).IsInteriorPoint (e (p.1, middleCollarParam p.2)) := by
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  apply ((e.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp
  apply isInteriorPoint_sphereIcc
  · rw [middleCollarParam_val hs]; linarith [hs.1]
  · rw [middleCollarParam_val hs]; linarith [hs.2]

theorem isOpen_sphereSignedCollarSource :
    IsOpen (sphereSignedCollarSource : Set (ClosureSphere.{u} × ℝ)) :=
  isOpen_univ.prod isOpen_Ioo

theorem isLocalDiffeomorphOn_middleCollarMap :
    IsLocalDiffeomorphOn sphereSignedCollarModel W.model ∞ (P.middleCollarMap e)
      sphereSignedCollarSource := by
  have hm : ∀ p ∈ (sphereSignedCollarSource : Set (ClosureSphere.{u} × ℝ)),
      ContMDiffAt sphereSignedCollarModel ((𝓡 2).prod (𝓡∂ 1)) ∞
        (Prod.map id middleCollarParam : ClosureSphere.{u} × ℝ → _) p :=
    fun p hp => contMDiffAt_id.prodMap (contMDiffAt_middleCollarParam hp.2)
  have hsm : ContMDiffOn sphereSignedCollarModel W.model ∞ (P.middleCollarMap e)
      sphereSignedCollarSource := fun p hp =>
    ((P.smooth.comp e.contMDiff).contMDiffAt.comp p (hm p hp)).contMDiffWithinAt
  rintro ⟨p, hp⟩
  apply isLocalDiffeomorphAt_of_interior_bijective_on isOpen_sphereSignedCollarSource hsm hp
    (BoundarylessManifold.isInteriorPoint) (P.isInteriorPoint_map (P.isInteriorPoint_middle e hp))
  have hmd : MDifferentiableAt sphereSignedCollarModel ((𝓡 2).prod (𝓡∂ 1))
      (Prod.map id middleCollarParam : ClosureSphere.{u} × ℝ → _) p :=
    (hm p hp).mdifferentiableAt (by simp)
  rw [show P.middleCollarMap e = (P.map ∘ e) ∘ Prod.map id middleCollarParam from rfl,
    mfderiv_comp p ((P.smooth.comp e.contMDiff).mdifferentiableAt (by simp)) hmd,
    mfderiv_comp _ (P.smooth.mdifferentiableAt (by simp)) (e.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_prodMap mdifferentiableAt_id
      ((contMDiffAt_middleCollarParam hp.2).mdifferentiableAt (by simp)), mfderiv_id]
  exact ((P.mfderiv_bijective _).comp (e.mfderivToContinuousLinearEquiv (by simp) _).bijective).comp
    (Function.bijective_id.prodMap (mfderiv_middleCollarParam_bijective hp.2))

theorem injOn_middleCollarMap : InjOn (P.middleCollarMap e) sphereSignedCollarSource := by
  rintro p hp q hq h
  have h' := e.injective (P.injective h)
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg (fun r => (r.2 : ℝ)) h'
  simp only [middleCollarParam_val hp.2, middleCollarParam_val hq.2] at h2
  exact Prod.ext h1 (by linarith)

theorem exists_middleCollar :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model (ClosureSphere.{u} × ℝ) W.Carrier ∞,
      d.source = sphereSignedCollarSource ∧
        d.target = P.middleCollarMap e '' sphereSignedCollarSource ∧
        (d : ClosureSphere.{u} × ℝ → W.Carrier) = P.middleCollarMap e := by
  have : Nonempty (ClosureSphere.{u} × ℝ) :=
    ⟨(ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, 0)⟩
  exact DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
    isOpen_sphereSignedCollarSource (P.isLocalDiffeomorphOn_middleCollarMap e)
    (P.injOn_middleCollarMap e)

theorem middleCollarMap_mem_interior {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ sphereSignedCollarSource) : P.middleCollarMap e p ∈ W.interior :=
  P.isInteriorPoint_map (P.isInteriorPoint_middle e hp)

/-- **The middle sphere seam** of an `S² × I` piece: the collar `(z, s) ↦ P (e (z, 1/2 + s/4))`. -/
def middleSeam : SphereSeam W where
  collar := (P.exists_middleCollar e).choose
  source_eq := (P.exists_middleCollar e).choose_spec.1
  target_interior := by
    rw [(P.exists_middleCollar e).choose_spec.2.1]
    rintro _ ⟨p, hp, rfl⟩
    exact P.middleCollarMap_mem_interior e hp

theorem middleSeam_collar_apply (p : ClosureSphere.{u} × ℝ) :
    (P.middleSeam e).collar p = P.map (e (p.1, middleCollarParam p.2)) :=
  congrFun (P.exists_middleCollar e).choose_spec.2.2 p

theorem middleSeam_target :
    (P.middleSeam e).collar.target = P.middleCollarMap e '' sphereSignedCollarSource :=
  (P.exists_middleCollar e).choose_spec.2.1

theorem middleSeam_zeroSphere : (P.middleSeam e).zeroSphere = P.sphereLevel e iccMid := by
  unfold SphereSeam.zeroSphere sphereLevel
  congr 1
  funext z
  rw [middleSeam_collar_apply, middleCollarParam_zero]

theorem continuous_middleCollarParam : Continuous middleCollarParam :=
  continuous_projIcc.comp (continuous_const.add (continuous_id.div_const 4))

theorem middleSeam_collar_mem_range (p : ClosureSphere.{u} × ℝ) :
    (P.middleSeam e).collar p ∈ range P.map := by
  rw [middleSeam_collar_apply]
  exact ⟨_, rfl⟩

theorem sphereHeight_middleSeam_collar {p : ClosureSphere.{u} × ℝ}
    (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    P.sphereHeight e ((P.middleSeam e).collar p) = 1 / 2 + p.2 / 4 := by
  rw [middleSeam_collar_apply, sphereHeight_map, middleCollarParam_val hp]

/-- The compact middle zone `P (e (S² × [1/4, 3/4]))`. -/
def middleZone : Set W.Carrier :=
  (fun p => P.map (e p)) '' {p : ClosureSphere.{u} × Icc (0 : ℝ) 1 | (p.2 : ℝ) ∈ Icc (1 / 4) (3 / 4)}

theorem isCompact_middleZone : IsCompact (P.middleZone e) :=
  ((isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)).isCompact).image
    (P.continuous_map.comp e.continuous)

variable {P e} in
theorem mem_middleZone_iff {x : W.Carrier} :
    x ∈ P.middleZone e ↔ x ∈ range P.map ∧ P.sphereHeight e x ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨_, rfl⟩, by rw [sphereHeight_map]; exact hp⟩
  · rintro ⟨hx, ht⟩
    obtain ⟨p, rfl⟩ := P.exists_eq_map_of_mem_range e hx
    rw [sphereHeight_map] at ht
    exact ⟨p, ht, rfl⟩

theorem middleZone_subset : P.middleZone e ⊆ interior (range P.map) ∩ W.interior := by
  rintro _ ⟨p, hp, rfl⟩
  have hq : (𝓡∂ 3).IsInteriorPoint (e p) :=
    ((e.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp
      (isInteriorPoint_sphereIcc (by linarith [hp.1]) (by linarith [hp.2]))
  exact ⟨P.toPieceFold.map_mem_interior_range hq, P.isInteriorPoint_map hq⟩

theorem middleSeam_target_subset_middleZone :
    (P.middleSeam e).collar.target ⊆ P.middleZone e := by
  rw [middleSeam_target]
  rintro _ ⟨p, hp, rfl⟩
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  refine ⟨(p.1, middleCollarParam p.2), ?_, rfl⟩
  change (middleCollarParam p.2 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)
  rw [middleCollarParam_val hs]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem middleSeam_target_subset :
    (P.middleSeam e).collar.target ⊆ interior (range P.map) ∩ W.interior :=
  (P.middleSeam_target_subset_middleZone e).trans (P.middleZone_subset e)

/-- **The interiors of the two halves are disjoint.** -/
theorem disjoint_interior_sphereHalf :
    Disjoint (interior (range (P.sphereHalf e true).map))
      (interior (range (P.sphereHalf e false).map)) := by
  rw [Set.disjoint_left]
  intro x hxT hxF
  obtain ⟨hx, hle⟩ := PieceEmbedding.mem_range_sphereHalf_true_iff.mp (interior_subset hxT)
  obtain ⟨-, hge⟩ := PieceEmbedding.mem_range_sphereHalf_false_iff.mp (interior_subset hxF)
  obtain ⟨p, rfl⟩ := P.exists_eq_map_of_mem_range e hx
  rw [sphereHeight_map] at hle hge
  have hp2 : p.2 = middleCollarParam 0 := by
    rw [middleCollarParam_zero]
    exact Subtype.ext (le_antisymm hle hge)
  let g : ℝ → W.Carrier := fun s => P.map (e (p.1, middleCollarParam s))
  have hg : Continuous g :=
    P.continuous_map.comp (e.continuous.comp (continuous_const.prodMk continuous_middleCollarParam))
  have hg0 : g 0 = P.map (e p) := by
    simp only [g, ← hp2]
  have hN : g ⁻¹' interior (range (P.sphereHalf e true).map) ∈ 𝓝 (0 : ℝ) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact isOpen_interior.mem_nhds hxT)
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  set s := min (b / 2) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by norm_num)
  have hsb : s < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hgs := interior_subset (hab ⟨by linarith, hsb⟩)
  obtain ⟨-, hle'⟩ := PieceEmbedding.mem_range_sphereHalf_true_iff.mp hgs
  simp only [g, sphereHeight_map, middleCollarParam_val ⟨by linarith, hs1⟩] at hle'
  linarith

/-- The level map of an `S² × I` piece is continuous. -/
theorem continuous_sphereLevelMap (t : Icc (0 : ℝ) 1) :
    Continuous fun z : ClosureSphere.{u} => P.map (e (z, t)) :=
  P.continuous_map.comp (e.continuous.comp (continuous_id.prodMk continuous_const))

theorem injective_sphereLevelMap (t : Icc (0 : ℝ) 1) :
    Injective fun z : ClosureSphere.{u} => P.map (e (z, t)) := fun _ _ h =>
  congrArg Prod.fst (e.injective (P.injective h))

theorem isPreconnected_sphereLevel (t : Icc (0 : ℝ) 1) : IsPreconnected (P.sphereLevel e t) := by
  have : ConnectedSpace ClosureSphere.{u} :=
    have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_iff_connectedSpace.mp (isConnected_sphere (by
        rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
    Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  exact isPreconnected_range (P.continuous_sphereLevelMap e t)

theorem isClosed_sphereLevel (t : Icc (0 : ℝ) 1) : IsClosed (P.sphereLevel e t) :=
  (isCompact_range (P.continuous_sphereLevelMap e t)).isClosed

theorem sphereLevel_nonempty (t : Icc (0 : ℝ) 1) : (P.sphereLevel e t).Nonempty :=
  ⟨_, ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, rfl⟩⟩

theorem disjoint_sphereLevel {t t' : Icc (0 : ℝ) 1} (h : t ≠ t') :
    Disjoint (P.sphereLevel e t) (P.sphereLevel e t') := by
  rw [Set.disjoint_left]
  rintro _ ⟨_, rfl⟩ ⟨_, hw⟩
  exact h (congrArg Prod.snd (e.injective (P.injective hw))).symm

theorem middleSeam_collar_mem_sphereHalf_true (z : ClosureSphere.{u}) {s : ℝ} (hs0 : s ≤ 0)
    (hs1 : -1 < s) : (P.middleSeam e).collar (z, s) ∈ range (P.sphereHalf e true).map := by
  refine PieceEmbedding.mem_range_sphereHalf_true_iff.mpr ⟨P.middleSeam_collar_mem_range e _, ?_⟩
  rw [sphereHeight_middleSeam_collar _ _ ⟨hs1, by linarith⟩]
  linarith

theorem middleSeam_collar_mem_sphereHalf_false (z : ClosureSphere.{u}) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : (P.middleSeam e).collar (z, s) ∈ range (P.sphereHalf e false).map := by
  refine PieceEmbedding.mem_range_sphereHalf_false_iff.mpr ⟨P.middleSeam_collar_mem_range e _, ?_⟩
  rw [sphereHeight_middleSeam_collar _ _ ⟨by linarith, hs1⟩]
  linarith

/-- A level sphere is a two-sphere. -/
def sphereLevelHomeomorph (t : Icc (0 : ℝ) 1) :
    P.sphereLevel e t ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (((P.continuous_sphereLevelMap e t).isClosedEmbedding
    (P.injective_sphereLevelMap e t)).isEmbedding.toHomeomorph).symm.trans Homeomorph.ulift

theorem sphereLevel_mid_subset_middleZone : P.sphereLevel e iccMid ⊆ P.middleZone e := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(z, iccMid), ?_, rfl⟩
  change (1 / 2 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)
  constructor <;> norm_num

/-- A level sphere is not a torus. -/
theorem false_of_sphereLevel_eq_range_torus {t : Icc (0 : ℝ) 1} {g : Circle × Circle → W.Carrier}
    (hg : Continuous g) (hginj : Injective g) (h : P.sphereLevel e t = range g) : False := by
  let φ : P.sphereLevel e t ≃ₜ SphereTwo := P.sphereLevelHomeomorph e t
  let ψ : P.sphereLevel e t ≃ₜ Circle × Circle :=
    (Homeomorph.setCongr h).trans (homeomorphRangeOfTorus hg hginj)
  exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ ψ

end PieceEmbedding

/-! ## The circle region is the closure of its interior (open-set form) -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- **Every point of the cornered base is a limit of depth-zero points**: depth zero trivially,
depth one since the regular defining function has no local minimum, a corner along the diagonal of
its corner chart. -/
theorem cornerBase_subset_closure_negBase :
    R.cornerBase ⊆ closure {b | ∀ l, R.defining l b < 0} := by
  intro b hb
  rcases R.depth_cases hb with h0 | ⟨l, hl, hother⟩ | ⟨k, rfl⟩
  · exact subset_closure h0
  · by_contra hnot
    have hN : (closure {b | ∀ l, R.defining l b < 0})ᶜ ∈ 𝓝 b :=
      isClosed_closure.isOpen_compl.mem_nhds hnot
    have hO : ∀ᶠ b' in 𝓝 b, ∀ l', l' ≠ l → R.defining l' b' < 0 := by
      refine Filter.eventually_all.mpr fun l' => ?_
      by_cases hl' : l' = l
      · exact Filter.Eventually.of_forall fun _ h => (h hl').elim
      · exact ((R.defining_smooth l').continuous.continuousAt.eventually_lt continuousAt_const
          (hother l' hl')).mono fun _ h _ => h
    have hmin : IsLocalMin (R.defining l) b := by
      filter_upwards [hN, hO] with b' h1 h2
      rw [hl]
      refine not_lt.mp fun hlt => h1 (subset_closure fun l' => ?_)
      by_cases hl' : l' = l
      · rw [hl']
        exact hlt
      · exact h2 l' hl'
    apply R.defining_regular l _ hl
    ext v
    exact congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => A v)
      (hmin.mvfderiv_eq_zero (I := 𝓡 2) BoundarylessManifold.isInteriorPoint)
  · have hsrc : ((0 : ℝ), (0 : ℝ)) ∈ (R.cornerChart k).source := by
      rw [R.cornerChart_source]
      exact ⟨by norm_num, by norm_num⟩
    have hc : ContinuousAt (R.cornerChart k) ((0 : ℝ), (0 : ℝ)) :=
      (R.cornerChart k).toOpenPartialHomeomorph.continuousAt hsrc
    have hdiag : Tendsto (fun t : ℝ => ((t, t) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
      ((continuous_id.prodMk continuous_id).tendsto' 0 (0, 0) rfl).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto (hc.tendsto.comp hdiag) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have hbox : ((t, t) : ℝ × ℝ) ∈ rimBox 2 :=
      ⟨by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2],
        by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]⟩
    have hsc : 0 < R.cornerScale k := R.cornerScale_pos k
    intro l
    change R.defining l (R.cornerChart k (t, t)) < 0
    by_cases h1 : l = R.cornerFirst k
    · rw [h1, R.chart_first k _ hbox]
      have := mul_pos hsc ht.1
      linarith
    by_cases h2 : l = R.cornerSecond k
    · rw [h2, R.chart_second k _ hbox]
      have := mul_pos hsc ht.1
      linarith
    exact R.chart_other k l _ h1 h2 hbox

/-- **An open set meeting the cornered region meets its ambient interior.** -/
theorem inter_interior_region_nonempty {O : Set W.Carrier} (hO : IsOpen O)
    (hne : (O ∩ R.region).Nonempty) : (O ∩ interior R.region).Nonempty := by
  obtain ⟨_, hxO, z, hz, rfl⟩ := hne
  let U : Set R.domain := Subtype.val ⁻¹' O
  have hU : IsOpen U := hO.preimage continuous_subtype_val
  have hPU : IsOpen (R.proj '' U) := R.isOpenMap_proj_of_submersion U hU
  obtain ⟨_, ⟨z', hz'U, rfl⟩, hb⟩ :=
    mem_closure_iff.mp (R.cornerBase_subset_closure_negBase hz) _ hPU ⟨z, hxO, rfl⟩
  exact ⟨z', hz'U, R.mem_interior_region_of_defining_neg z'.2 hb⟩

end CircleRegion

/-! ## Certificate level: what the interior of a vertex image avoids; faces of an `S² × I` vertex -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The ambient interior of a vertex image meets no other vertex image. -/
theorem disjoint_interior_image_vertex {j k : Fin D.vertexCount} (hjk : j ≠ k) :
    Disjoint (interior (D.vertex k).image) (D.vertex j).image := by
  rw [Set.disjoint_left]
  intro x hxk hxj
  rw [Vertex.image_eq_range_piece] at hxj
  obtain ⟨q, rfl⟩ := hxj
  obtain ⟨w, hwO, hwV⟩ := exists_mem_inter_interior_range (I := 𝓡∂ 3) finrank_euclideanSpace_fin
    (D.vertex j).piece.smooth (D.vertex j).piece.mfderiv_bijective isOpen_interior hxk
  rw [← Vertex.image_eq_range_piece] at hwV
  exact Set.disjoint_left.mp (D.vertex_disjoint hjk) hwV hwO

/-- The ambient interior of a vertex image meets no handle. -/
theorem disjoint_interior_image_handle (k : Fin D.vertexCount) (h : Fin D.handleCount) :
    Disjoint (interior (D.vertex k).image) (range (D.handle h).map) := by
  rw [Set.disjoint_left]
  rintro x hxk ⟨y, rfl⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  obtain ⟨w, hwO, hwH⟩ := exists_mem_inter_interior_range (I := (𝓡∂ 2).prod (𝓡∂ 1)) hdim
    (D.handle h).smooth (D.handle h).mfderiv_bijective isOpen_interior hxk
  exact Set.disjoint_left.mp (D.vertex_handle_disjoint k h) hwO hwH

/-- The ambient interior of a vertex image meets no point of the cornered circle region. -/
theorem disjoint_interior_image_region (k : Fin D.vertexCount) :
    Disjoint (interior (D.vertex k).image) D.circ.region := by
  rw [Set.disjoint_left]
  intro x hx hxR
  obtain ⟨y, hyO, hyR⟩ := D.circ.inter_interior_region_nonempty isOpen_interior ⟨x, hx, hxR⟩
  exact Set.disjoint_left.mp (D.circ_vertex_disjoint k) hyR hyO

/-- The ambient interior of a vertex image that is no torus side meets no torus seam collar. -/
theorem disjoint_interior_image_torusSeam {k : Fin D.vertexCount}
    (hk : ∀ c b, D.torusSide c b ≠ some k) (c : Fin D.torusSeamCount) :
    Disjoint (interior (D.vertex k).image) (D.torusSeam c).collar.target := by
  rw [Set.disjoint_left]
  intro x hxO hxT
  set χ := (D.torusSeam c).collar with hχ
  have hsrc : ∀ r, r ∈ χ.source ↔ -1 < r.2 ∧ r.2 < 1 := fun r => by
    rw [hχ, (D.torusSeam c).source_eq]
    rfl
  have hp : χ.symm x ∈ χ.source := χ.map_target hxT
  have hpx : χ (χ.symm x) = x := χ.right_inv hxT
  set V : Set (Torus × ℝ) := χ.source ∩ χ ⁻¹' interior (D.vertex k).image with hVdef
  have hV : IsOpen V := χ.contMDiffOn.continuousOn.isOpen_inter_preimage χ.open_source isOpen_interior
  have hpV : χ.symm x ∈ V := ⟨hp, by rw [mem_preimage, hpx]; exact hxO⟩
  -- a parameter of nonzero height in `V`
  obtain ⟨q, hqV, hq0⟩ : ∃ q ∈ V, q.2 ≠ 0 := by
    by_cases h0 : (χ.symm x).2 = 0
    · have hN : (fun s : ℝ => ((χ.symm x).1, s)) ⁻¹' V ∈ 𝓝 (0 : ℝ) := by
        refine (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds ?_
        rw [← h0]
        exact hV.mem_nhds hpV
      obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
      exact ⟨((χ.symm x).1, b / 2), hab ⟨by linarith, by linarith⟩, by
        change b / 2 ≠ 0
        linarith⟩
    · exact ⟨χ.symm x, hpV, h0⟩
  -- the open image of the parameters of one sign lies on one side
  have key : ∀ (β : Bool) (V' : Set (Torus × ℝ)), IsOpen V' → V' ⊆ V → q ∈ V' →
      (∀ r ∈ V', χ r ∈ (D.torusSide c β).elim D.circ.region fun j => (D.vertex j).image) →
      False := by
    intro β V' hV' hV'V hqV' hside
    have hU : IsOpen (χ '' V') :=
      χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV' (hV'V.trans inter_subset_left)
    have hUO : χ '' V' ⊆ interior (D.vertex k).image := by
      rintro _ ⟨r, hr, rfl⟩
      exact (hV'V hr).2
    cases hs : D.torusSide c β with
    | none =>
      have hUR : χ '' V' ⊆ interior D.circ.region := by
        refine interior_maximal ?_ hU
        rintro _ ⟨r, hr, rfl⟩
        have := hside r hr
        rw [hs] at this
        exact this
      exact Set.disjoint_left.mp (D.circ_vertex_disjoint k) (hUR ⟨q, hqV', rfl⟩)
        (hUO ⟨q, hqV', rfl⟩)
    | some j =>
      have hjk : j ≠ k := fun h => hk c β (hs.trans (congrArg some h))
      have hUj : χ '' V' ⊆ interior (D.vertex j).image := by
        refine interior_maximal ?_ hU
        rintro _ ⟨r, hr, rfl⟩
        have := hside r hr
        rw [hs] at this
        exact this
      exact Set.disjoint_left.mp (D.vertex_disjoint hjk) (hUj ⟨q, hqV', rfl⟩)
        (hUO ⟨q, hqV', rfl⟩)
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · refine key true (V ∩ {r | r.2 < 0}) (hV.inter (isOpen_lt continuous_snd continuous_const))
      inter_subset_left ⟨hqV, hneg⟩ fun r hr => ?_
    have hr' := (hsrc r).mp hr.1.1
    have := D.torusSide_neg c r.1 r.2 hr'.1 (le_of_lt hr.2)
    exact this
  · refine key false (V ∩ {r | 0 < r.2}) (hV.inter (isOpen_lt continuous_const continuous_snd))
      inter_subset_left ⟨hqV, hpos⟩ fun r hr => ?_
    have hr' := (hsrc r).mp hr.1.1
    have := D.torusSide_pos c r.1 r.2 (le_of_lt hr.2) hr'.2
    exact this

section SphereInterval

variable {D} {k : Fin D.vertexCount} {P : PieceEmbedding W}
  {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}

theorem image_eq_of_sphereInterval (hv : D.vertex k = .slim P (.sphereInterval e)) :
    (D.vertex k).image = range P.map := by
  rw [hv]
  rfl

theorem boundaryImage_eq_of_sphereInterval (hv : D.vertex k = .slim P (.sphereInterval e)) :
    (D.vertex k).boundaryImage = P.sphereLevel e iccZero ∪ P.sphereLevel e iccOne := by
  rw [hv]
  exact P.image_boundary_sphereInterval e

/-- **The faces of an `S² × I` vertex are its two end spheres.** -/
theorem face_eq_sphereLevel_of_sphereInterval (hv : D.vertex k = .slim P (.sphereInterval e))
    (f : Fin D.faceCount) (hf : D.faceOwner f = k) :
    D.face f = P.sphereLevel e iccZero ∨ D.face f = P.sphereLevel e iccOne := by
  have hB := boundaryImage_eq_of_sphereInterval hv
  have hsub : D.face f ⊆ P.sphereLevel e iccZero ∪ P.sphereLevel e iccOne := by
    rw [← hB, ← hf]
    exact D.face_subset_boundaryImage f
  have h01 : iccZero ≠ iccOne := fun h => by
    have := congrArg Subtype.val h
    norm_num [iccZero, iccOne] at this
  have hdisj := P.disjoint_sphereLevel e h01
  have hpre := (D.isConnected_face f).isPreconnected
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
  have hempty : D.face f ∩ (P.sphereLevel e iccZero ∩ P.sphereLevel e iccOne) = ∅ := by
    rw [hdisj.inter_eq, inter_empty]
  have hown : (D.vertex (D.faceOwner f)).boundaryImage =
      P.sphereLevel e iccZero ∪ P.sphereLevel e iccOne := by
    rw [hf]
    exact hB
  have hfill : ∀ t, P.sphereLevel e t ⊆ P.sphereLevel e iccZero ∪ P.sphereLevel e iccOne →
      D.face f ⊆ P.sphereLevel e t → D.face f = P.sphereLevel e t := by
    intro t ht01 ht
    refine Subset.antisymm ht ?_
    obtain ⟨z, hz⟩ := D.face_nonempty f
    have htB : P.sphereLevel e t ⊆ (D.vertex (D.faceOwner f)).boundaryImage := by
      rw [hown]
      exact ht01
    exact D.subset_face_of_isPreconnected f (P.isPreconnected_sphereLevel e t) htB (ht hz) hz
  rcases hpre _ _ (P.isClosed_sphereLevel e iccZero) (P.isClosed_sphereLevel e iccOne) hsub
    hempty with h | h
  · exact Or.inl (hfill _ subset_union_left h)
  · exact Or.inr (hfill _ subset_union_right h)

/-- Each end sphere of an `S² × I` vertex is one of its faces. -/
theorem exists_face_eq_sphereLevel (hv : D.vertex k = .slim P (.sphereInterval e))
    {t : Icc (0 : ℝ) 1} (ht : t = iccZero ∨ t = iccOne) :
    ∃ f, D.faceOwner f = k ∧ D.face f = P.sphereLevel e t := by
  obtain ⟨x, hx⟩ := P.sphereLevel_nonempty e t
  have hxB : x ∈ (D.vertex k).boundaryImage := by
    rw [boundaryImage_eq_of_sphereInterval hv]
    rcases ht with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  rw [← D.face_exhausted] at hxB
  obtain ⟨f, hxf⟩ := mem_iUnion.mp hxB
  obtain ⟨hf, hxf⟩ := mem_iUnion.mp hxf
  refine ⟨f, hf, ?_⟩
  have h01 : iccZero ≠ iccOne := fun h => by
    have := congrArg Subtype.val h
    norm_num [iccZero, iccOne] at this
  rcases face_eq_sphereLevel_of_sphereInterval hv f hf with h | h
  · rcases ht with rfl | rfl
    · exact h
    · rw [h] at hxf
      exact (Set.disjoint_left.mp (P.disjoint_sphereLevel e h01) hxf hx).elim
  · rcases ht with rfl | rfl
    · rw [h] at hxf
      exact (Set.disjoint_left.mp (P.disjoint_sphereLevel e h01) hx hxf).elim
    · exact h

/-- An `S² × I` vertex is no torus side. -/
theorem torusSide_ne_of_sphereInterval (hv : D.vertex k = .slim P (.sphereInterval e))
    (c : Fin D.torusSeamCount) (b : Bool) : D.torusSide c b ≠ some k := by
  intro hs
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b k hs
  have hface := (D.face_torusSeam f c b hfk).1
  have hsrc0 : ∀ t : Torus, (t, (0 : ℝ)) ∈ (D.torusSeam c).collar.source := fun t => by
    rw [(D.torusSeam c).source_eq]
    exact ⟨by norm_num, by norm_num⟩
  have hcont : Continuous fun t : Torus => (D.torusSeam c).collar (t, 0) :=
    (D.torusSeam c).collar.contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      hsrc0
  have hinj : Injective fun t : Torus => (D.torusSeam c).collar (t, 0) := fun t t' h =>
    congrArg Prod.fst ((D.torusSeam c).collar.injOn (hsrc0 t) (hsrc0 t') h)
  rcases face_eq_sphereLevel_of_sphereInterval hv f hfo with h | h
  · exact P.false_of_sphereLevel_eq_range_torus e hcont hinj (h.symm.trans hface)
  · exact P.false_of_sphereLevel_eq_range_torus e hcont hinj (h.symm.trans hface)

/-- An `S² × I` vertex owns no external port. -/
theorem externalOwner_ne_of_sphereInterval (hv : D.vertex k = .slim P (.sphereInterval e))
    (i : Fin n) : D.externalOwner i ≠ k := by
  intro hi
  obtain ⟨f, hfk⟩ := D.external_face i
  obtain ⟨hface, hown⟩ := D.face_external f i hfk
  have hcont := (E.torusMap_isEmbedding i).continuous
  have hinj := (E.torusMap_isEmbedding i).injective
  rcases face_eq_sphereLevel_of_sphereInterval hv f (hown.symm.trans hi) with h | h
  · exact P.false_of_sphereLevel_eq_range_torus e hcont hinj (h.symm.trans hface)
  · exact P.false_of_sphereLevel_eq_range_torus e hcont hinj (h.symm.trans hface)

/-- **The middle sphere of an `S² × I` vertex meets no face.** -/
theorem disjoint_face_sphereLevel_mid (hv : D.vertex k = .slim P (.sphereInterval e))
    (f : Fin D.faceCount) : Disjoint (D.face f) (P.sphereLevel e iccMid) := by
  by_cases hf : D.faceOwner f = k
  · have h0 : iccZero ≠ iccMid := fun h => by
      have := congrArg Subtype.val h
      norm_num [iccZero, iccMid] at this
    have h1 : iccOne ≠ iccMid := fun h => by
      have := congrArg Subtype.val h
      norm_num [iccOne, iccMid] at this
    rcases face_eq_sphereLevel_of_sphereInterval hv f hf with h | h
    · rw [h]
      exact P.disjoint_sphereLevel e h0
    · rw [h]
      exact P.disjoint_sphereLevel e h1
  · have hsub : D.face f ⊆ (D.vertex (D.faceOwner f)).image := by
      refine (D.face_subset_boundaryImage f).trans ?_
      rw [Vertex.image_eq_range_piece]
      exact image_subset_range _ _
    have hmid : P.sphereLevel e iccMid ⊆ interior (D.vertex k).image := by
      rw [image_eq_of_sphereInterval hv]
      exact fun x hx => (P.middleZone_subset e (P.sphereLevel_mid_subset_middleZone e hx)).1
    exact ((D.disjoint_interior_image_vertex hf).mono hmid hsub).symm

/-- **The rim chart of a handle end at an `S² × I` vertex stays in one half.** If the rim chart
target avoids the middle zone, the vertex side `{y ≤ 0}` of the rim chart (a connected set through
the rim circle, which lies on the end sphere of the handle face) lies in the half of that end. -/
theorem rimChart_mem_sphereHalf (hv : D.vertex k = .slim P (.sphereInterval e))
    {h : Fin D.handleCount} {b : Bool} (hk : D.handleEnd h b = k)
    (hrim : Disjoint (D.rimChart h b).target (P.middleZone e)) (β : Bool)
    (hface : D.face (D.handleFace h b) = P.sphereLevel e (cond β iccZero iccOne))
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart h b).source) (hp2 : p.2.2 ≤ 0) :
    D.rimChart h b p ∈ range (P.sphereHalf e β).map := by
  set χ := D.rimChart h b with hχ
  let A : Set (Circle × (ℝ × ℝ)) := {p | p ∈ χ.source ∧ p.2.2 ≤ 0}
  have hA : A = univ ×ˢ (Ioo (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 0) := by
    ext q
    have hs : q ∈ χ.source ↔ q.2 ∈ rimBox 2 := D.rim_source h b
    constructor
    · rintro ⟨hq, h3⟩
      obtain ⟨h1, h2⟩ := hs.mp hq
      exact ⟨mem_univ _, abs_lt.mp h1, ⟨(abs_lt.mp h2).1, h3⟩⟩
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨hs.mpr ⟨abs_lt.mpr h1, abs_lt.mpr ⟨h2, by linarith⟩⟩, h3⟩
  have hApre : IsPreconnected A := by
    rw [hA]
    exact isPreconnected_univ.prod (isPreconnected_Ioo.prod isPreconnected_Ioc)
  have hCpre : IsPreconnected (χ '' A) :=
    hApre.image _ (χ.contMDiffOn.continuousOn.mono fun q hq => hq.1)
  have hCsub : χ '' A ⊆ range P.map := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← image_eq_of_sphereInterval hv, ← hk]
    exact (D.rim_vertex h b hq.1).mpr hq.2
  have hCzone : ∀ x ∈ χ '' A, x ∉ P.middleZone e := by
    rintro _ ⟨q, hq, rfl⟩ hz
    exact Set.disjoint_left.mp hrim (χ.map_source hq.1) hz
  have hH : IsPreconnected (P.sphereHeight e '' (χ '' A)) :=
    hCpre.image _ ((P.continuousOn_sphereHeight e).mono hCsub)
  have hp₀ : ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ A :=
    ⟨(D.rim_source h b).mpr ⟨by norm_num, by norm_num⟩, le_rfl⟩
  have hx₀ : χ ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ D.face (D.handleFace h b) := by
    apply D.handleEnd_face h b
    have hmem : χ ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ χ '' {q | q.2 = (0, 0)} := ⟨_, rfl, rfl⟩
    rw [hχ, D.rim_label h b] at hmem
    obtain ⟨y, -, hy⟩ := hmem
    exact ⟨y, hy⟩
  rw [hface] at hx₀
  obtain ⟨-, hh₀⟩ := PieceEmbedding.mem_sphereLevel_iff.mp hx₀
  have hxp : χ p ∈ χ '' A := ⟨p, ⟨hp, hp2⟩, rfl⟩
  have hxr := hCsub hxp
  have hmid : (1 / 2 : ℝ) ∉ P.sphereHeight e '' (χ '' A) := by
    rintro ⟨x, hx, hx2⟩
    refine hCzone x hx (PieceEmbedding.mem_middleZone_iff.mpr ⟨hCsub hx, ?_⟩)
    rw [hx2]
    constructor <;> norm_num
  have hin₀ : P.sphereHeight e (χ ((1 : Circle), ((0 : ℝ), (0 : ℝ)))) ∈
      P.sphereHeight e '' (χ '' A) := ⟨_, ⟨_, hp₀, rfl⟩, rfl⟩
  have hinp : P.sphereHeight e (χ p) ∈ P.sphereHeight e '' (χ '' A) := ⟨_, hxp, rfl⟩
  cases β
  · have h1 : P.sphereHeight e (χ ((1 : Circle), ((0 : ℝ), (0 : ℝ)))) = 1 := hh₀
    refine PieceEmbedding.mem_range_sphereHalf_false_iff.mpr ⟨hxr, not_lt.mp fun hlt => hmid ?_⟩
    rw [h1] at hin₀
    exact hH.Icc_subset hinp hin₀ ⟨hlt.le, by norm_num⟩
  · have h0 : P.sphereHeight e (χ ((1 : Circle), ((0 : ℝ), (0 : ℝ)))) = 0 := hh₀
    refine PieceEmbedding.mem_range_sphereHalf_true_iff.mpr ⟨hxr, not_lt.mp fun hlt => hmid ?_⟩
    rw [h0] at hin₀
    exact hH.Icc_subset hin₀ hinp ⟨by norm_num, hlt.le⟩

/-- The middle seam of an `S² × I` vertex lies in the ambient interior of the vertex image. -/
theorem middleSeam_target_subset_interior (hv : D.vertex k = .slim P (.sphereInterval e)) :
    (P.middleSeam e).collar.target ⊆ interior (D.vertex k).image := by
  rw [image_eq_of_sphereInterval hv]
  exact fun x hx => (P.middleSeam_target_subset e hx).1

/-- **Consumer: the middle seam of an `S² × I` vertex is protected.** Its collar target lies in
`W.interior` and meets no other vertex, no handle, no point of the cornered circle region and no
torus seam collar. -/
theorem middleSeam_target_disjoint (hv : D.vertex k = .slim P (.sphereInterval e)) :
    (P.middleSeam e).collar.target ⊆ W.interior ∧
      (∀ j, j ≠ k → Disjoint (P.middleSeam e).collar.target (D.vertex j).image) ∧
      (∀ h, Disjoint (P.middleSeam e).collar.target (range (D.handle h).map)) ∧
      Disjoint (P.middleSeam e).collar.target D.circ.region ∧
      ∀ c, Disjoint (P.middleSeam e).collar.target (D.torusSeam c).collar.target := by
  have hsub := middleSeam_target_subset_interior hv
  exact ⟨(P.middleSeam e).target_interior,
    fun j hj => (D.disjoint_interior_image_vertex hj).mono_left hsub,
    fun h => (D.disjoint_interior_image_handle k h).mono_left hsub,
    (D.disjoint_interior_image_region k).mono_left hsub,
    fun c => (D.disjoint_interior_image_torusSeam (torusSide_ne_of_sphereInterval hv) c).mono_left
      hsub⟩

end SphereInterval

end DecompositionCertificate

end GC.GraphManifold.Assembly
