import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.ULift

/-!
# The standard solid torus

The solid torus is realised inside the standard three-sphere as the regular sublevel set
`{‖z₁‖² ≤ ‖z₂‖²}` of the Clifford height. We record its structure as a compact oriented
three-manifold with boundary, the half collar of its boundary torus, the closed unit disc as a
compact surface with boundary, and the global trivialisation of the circle fibration
`(z₁, z₂) ↦ √2 z₁` over the disc.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

def openDiffeomorphOfForall {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (h : ∀ x, x ∈ U) : U ≃ₘ⟮I, I⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

def CircleFibration.ofProductDiffeomorph {C : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier} (B : CompactSurface.{u})
    (Φ : U ≃ₘ⟮C.model, (SurfaceModel.model B.kind).prod (𝓡 1)⟯ B.Carrier × Circle) :
    CircleFibration C U where
  base := B
  projection := ⟨fun x => (Φ x).1, continuous_fst.comp Φ.continuous⟩
  surjective b := ⟨Φ.symm (b, 1), by simp⟩
  smooth := contMDiff_fst.comp Φ.contMDiff
  neighborhood _ := ⊤
  mem_neighborhood _ := trivial
  trivialization _ := (openDiffeomorphOfForall (TopologicalSpace.Opens.comap
      ⟨fun x => (Φ x).1, continuous_fst.comp Φ.continuous⟩ ⊤) (fun _ => trivial)).trans
    (Φ.trans ((openDiffeomorphOfForall (⊤ : TopologicalSpace.Opens B.Carrier)
      (fun _ => trivial)).symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)))
  projection_trivialization _ _ := rfl

theorem secondCountableTopology_sphereCarrier : SecondCountableTopology SphereCarrier.{u} :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) _

attribute [local instance] secondCountableTopology_sphereCarrier

def solidTorusSet : Set SphereCarrier.{u} := {p | cliffordHeight p ≤ 0}

def solidTorusAtlas : SmoothBoundaryAtlas (𝓡 3) 3 solidTorusSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    contMDiff_cliffordHeight 0 cliffordHeight_regular

instance : ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{u} :=
  solidTorusAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 3) ∞ solidTorusSet.{u} := solidTorusAtlas.isManifold

theorem isClosed_solidTorusSet : IsClosed solidTorusSet.{u} :=
  isClosed_le contMDiff_cliffordHeight.continuous continuous_const

instance : CompactSpace solidTorusSet.{u} :=
  isCompact_iff_compactSpace.mp isClosed_solidTorusSet.isCompact

theorem contMDiff_solidTorus_val :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u}) :=
  solidTorusAtlas.contMDiff_subtype_val

theorem contMDiff_solidTorus_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → solidTorusSet.{u}) :
    ContMDiff J (𝓡∂ 3) ∞ f ↔ ContMDiff J (𝓡 3) ∞ (Subtype.val ∘ f) :=
  solidTorusAtlas.contMDiff_iff_subtype_val f

theorem contMDiffOn_solidTorus_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → solidTorusSet.{u}) (s : Set X) :
    ContMDiffOn J (𝓡∂ 3) ∞ f s ↔ ContMDiffOn J (𝓡 3) ∞ (Subtype.val ∘ f) s :=
  solidTorusAtlas.contMDiffOn_iff_subtype_val f s

theorem solidTorus_isBoundaryPoint_iff (p : solidTorusSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint p ↔ cliffordHeight p.val = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin contMDiff_cliffordHeight 0 cliffordHeight_regular p

theorem solidTorus_isInteriorPoint_iff (p : solidTorusSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint p ↔ cliffordHeight p.val < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin contMDiff_cliffordHeight 0 cliffordHeight_regular p

theorem norm_sphereSecond_sq_ge_of_mem {p : SphereCarrier.{u}} (hp : p ∈ solidTorusSet) :
    1 / 2 ≤ ‖sphereSecond p‖ ^ 2 := by
  have hp' : cliffordHeight p ≤ 0 := hp
  rw [norm_sphereSecond_sq_eq]
  linarith

theorem sphereSecond_ne_zero_of_mem {p : SphereCarrier.{u}} (hp : p ∈ solidTorusSet) :
    sphereSecond p ≠ 0 := by
  intro h
  have h' := norm_sphereSecond_sq_ge_of_mem hp
  rw [h, norm_zero] at h'
  norm_num at h'

def solidTorusCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := solidTorusSet.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ solidTorusSet.{u})
  orientation := solidTorusAtlas.orientation standardThreeSphereLift.orientation

theorem seamClamp_neg_nonpos {s : ℝ} (hs : 0 ≤ s) : seamClamp (-s) ≤ 0 :=
  max_le (by norm_num) ((min_le_right _ _).trans (neg_nonpos.mpr hs))

def solidTorusCollarMap (q : Torus × EuclideanHalfSpace 1) : solidTorusSet.{u} :=
  ⟨cliffordSeamMap (q.1, -q.2.val 0), by
    change cliffordHeight _ ≤ 0
    rw [cliffordHeight_cliffordSeamMap]
    exact seamClamp_neg_nonpos q.2.2⟩

theorem solidTorusCollarMap_val (q : Torus × EuclideanHalfSpace 1) :
    (solidTorusCollarMap.{u} q).val = cliffordSeam (q.1, -q.2.val 0) := rfl

def solidTorusCollarInv (p : solidTorusSet.{u}) : Torus × EuclideanHalfSpace 1 :=
  ((unitOf (sphereFirst p.val), unitOf (sphereSecond p.val)),
    halfPoint (-cliffordHeight p.val) (neg_nonneg.mpr p.2))

theorem halfPoint_eq_halfSpaceOneLift (s : ℝ) (hs : 0 ≤ s) :
    halfPoint s hs = Manifold.halfSpaceOneLift s := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change s = max s 0
  exact (max_eq_left hs).symm

theorem halfPoint_val_zero (s : ℝ) (hs : 0 ≤ s) : (halfPoint s hs).val 0 = s := rfl

theorem halfPoint_coord_eq (h : EuclideanHalfSpace 1) : halfPoint (h.val 0) h.2 = h := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  rfl

def solidTorusCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      solidTorusSet.{u} ∞ where
  toFun := solidTorusCollarMap
  invFun := solidTorusCollarInv
  source := halfCollarSource
  target := {p | sphereFirst p.val ≠ 0}
  map_source' := by
    intro q hq
    change sphereFirst (cliffordSeamMap (q.1, -q.2.val 0)) ≠ 0
    rw [sphereFirst_cliffordSeamMap]
    have hq' : q.2.val 0 < 1 := hq
    exact smul_ne_zero (seamFirst_pos (by linarith)).ne' (Circle.coe_ne_zero _)
  map_target' := by
    intro p hp
    change -cliffordHeight p.val < 1
    have h₁ : 0 < ‖sphereFirst p.val‖ ^ 2 := by positivity [norm_pos_iff.mpr hp]
    rw [norm_sphereFirst_sq_eq] at h₁
    linarith
  left_inv' := by
    intro q hq
    obtain ⟨⟨v, w⟩, h⟩ := q
    have hq' : h.val 0 < 1 := hq
    have h0 : 0 ≤ h.val 0 := h.2
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact unitOf_smul (seamFirst_pos (by linarith)) v
    · exact unitOf_smul (seamSecond_pos (by linarith)) w
    · change halfPoint (-cliffordHeight (cliffordSeamMap ((v, w), -h.val 0))) _ = h
      simp only [cliffordHeight_cliffordSeamMap,
        seamClamp_of_mem (by linarith : (-1 : ℝ) ≤ -h.val 0) (by linarith : -h.val 0 ≤ 1),
        neg_neg]
      exact halfPoint_coord_eq h
  right_inv' := by
    intro p hp
    have hmem : p.val ∈ cliffordSeamTarget := ⟨hp, sphereSecond_ne_zero_of_mem p.2⟩
    apply Subtype.ext
    change cliffordSeamMap ((unitOf (sphereFirst p.val), unitOf (sphereSecond p.val)),
      -(halfPoint (-cliffordHeight p.val) _).val 0) = p.val
    rw [halfPoint_val_zero, neg_neg]
    exact cliffordSeam.right_inv hmem
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_ne_fun
    (contMDiff_sphereFirst.continuous.comp continuous_subtype_val) continuous_const
  contMDiffOn_toFun := by
    rw [contMDiffOn_solidTorus_iff]
    have hmap : ContMDiff halfCollarModel signedCollarModel ∞
        (fun q : Torus × EuclideanHalfSpace 1 => (q.1, -q.2.val 0)) :=
      contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).neg
    have h := cliffordSeam.contMDiffOn.comp hmap.contMDiffOn (fun q hq => by
      have hq' : q.2.val 0 < 1 := hq
      have h0 : 0 ≤ q.2.val 0 := q.2.2
      exact ⟨by linarith, by linarith⟩)
    exact h
  contMDiffOn_invFun := by
    have hval := contMDiff_solidTorus_val.{u}
    have hfirst : ContMDiffOn (𝓡∂ 3) (𝓡 1) ∞
        (fun p : solidTorusSet.{u} => unitOf (sphereFirst p.val)) {p | sphereFirst p.val ≠ 0} :=
      contMDiffOn_unitOf.comp (contMDiff_sphereFirst.comp hval).contMDiffOn (fun p hp => hp)
    have hsecond : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
        (fun p : solidTorusSet.{u} => unitOf (sphereSecond p.val)) := by
      intro p
      exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds
        (sphereSecond_ne_zero_of_mem p.2))).comp p (contMDiff_sphereSecond.comp hval p)
    have hheight : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞
        (fun p : solidTorusSet.{u} => halfPoint (-cliffordHeight p.val) (neg_nonneg.mpr p.2)) := by
      have heq : (fun p : solidTorusSet.{u} =>
          halfPoint (-cliffordHeight p.val) (neg_nonneg.mpr p.2)) =
          fun p => Manifold.halfSpaceOneLift (-cliffordHeight p.val) := by
        funext p
        exact halfPoint_eq_halfSpaceOneLift _ _
      rw [heq]
      intro p
      exact (Manifold.contMDiffOn_halfSpaceOneLift.comp
        (contMDiff_cliffordHeight.comp hval).neg.contMDiffOn
        (fun q _ => show (0 : ℝ) ≤ -cliffordHeight q.val from neg_nonneg.mpr q.2)) p trivial
    exact (hfirst.prodMk hsecond.contMDiffOn).prodMk hheight.contMDiffOn

theorem solidTorusCollar_apply (q : Torus × EuclideanHalfSpace 1) :
    solidTorusCollar.{u} q = solidTorusCollarMap q := rfl

theorem solidTorusCollar_source : solidTorusCollar.{u}.source = halfCollarSource := rfl

theorem cliffordHeight_solidTorusCollar_zero (t : Torus) :
    cliffordHeight (solidTorusCollar.{u} (t, halfZero)).val = 0 := by
  change cliffordHeight (cliffordSeamMap (t, -halfZero.val 0)) = 0
  rw [cliffordHeight_cliffordSeamMap]
  change seamClamp (-halfZero.val 0) = 0
  rw [show halfZero.val 0 = 0 from rfl, neg_zero, seamClamp_of_mem (by norm_num) (by norm_num)]

def solidTorusBoundary : BoundaryTori solidTorusCarrier.{u} 1 where
  collar _ := solidTorusCollar
  source_eq _ := rfl
  boundary_zero _ t := (solidTorus_isBoundaryPoint_iff _).mpr
    (cliffordHeight_solidTorusCollar_zero t)
  disjoint i j h := (h (Subsingleton.elim i j)).elim

def unitDiscSet : Set ℂ := {w | ‖w‖ ^ 2 ≤ 1}

theorem unitDisc_normSq_regular (w : ℂ) (hw : ‖w‖ ^ 2 = 1) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ => ‖z‖ ^ 2) w ≠ 0 := by
  rw [mfderiv_eq_fderiv, fderiv_norm_sq_apply]
  intro h
  have h1 := DFunLike.congr_fun h w
  change 2 • (innerSL ℝ w) w = 0 at h1
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hw] at h1
  norm_num at h1

def unitDiscAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 unitDiscSet :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    (contDiff_norm_sq ℝ).contMDiff 1 unitDisc_normSq_regular

instance : ChartedSpace (EuclideanHalfSpace 2) unitDiscSet := unitDiscAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 2) ∞ unitDiscSet := unitDiscAtlas.isManifold

theorem isCompact_unitDiscSet : IsCompact unitDiscSet := by
  refine isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_norm.pow 2) continuous_const) ?_
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset fun w hw => ?_
  rw [mem_closedBall_zero_iff]
  have hw' : ‖w‖ ^ 2 ≤ 1 := hw
  nlinarith [norm_nonneg w]

theorem isConnected_unitDiscSet : IsConnected unitDiscSet := by
  have hconv : Convex ℝ unitDiscSet := by
    have heq : unitDiscSet = closedBall (0 : ℂ) 1 := by
      ext w
      rw [mem_closedBall_zero_iff]
      change ‖w‖ ^ 2 ≤ 1 ↔ ‖w‖ ≤ 1
      rw [pow_le_one_iff_of_nonneg (norm_nonneg w) two_ne_zero]
    rw [heq]
    exact convex_closedBall 0 1
  exact ⟨⟨0, by simp [unitDiscSet]⟩, hconv.isPreconnected⟩

abbrev UnitDisc : Type u := ULift.{u} unitDiscSet

instance : ChartedSpace (EuclideanHalfSpace 2) UnitDisc.{u} := uliftChartedSpace _ _

instance : IsManifold (𝓡∂ 2) ∞ UnitDisc.{u} := isManifold_ulift _ _

def unitDiscSurface : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := UnitDisc.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 2) UnitDisc.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 2) ∞ UnitDisc.{u})
  compact := @ULift.compactSpace _ _ (isCompact_iff_compactSpace.mp isCompact_unitDiscSet)
  secondCountable := Homeomorph.ulift.secondCountableTopology
  connected := (Homeomorph.ulift : UnitDisc.{u} ≃ₜ unitDiscSet).connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp isConnected_unitDiscSet)

theorem sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

def discPointOfSolidTorus (p : solidTorusSet.{u}) : unitDiscSet :=
  ⟨(√2 : ℝ) • sphereFirst p.val, by
    change ‖(√2 : ℝ) • sphereFirst p.val‖ ^ 2 ≤ 1
    have hp : cliffordHeight p.val ≤ 0 := p.2
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sqrt_two_sq, norm_sphereFirst_sq_eq]
    linarith⟩

def discOfSolidTorus (p : solidTorusSet.{u}) : UnitDisc.{u} := ULift.up (discPointOfSolidTorus p)

theorem discOfSolidTorus_val (p : solidTorusSet.{u}) :
    (discOfSolidTorus p).down.val = (√2 : ℝ) • sphereFirst p.val := rfl

def discCircleSecond (w : ℂ) : ℝ := √(1 - ‖w‖ ^ 2 / 2)

theorem discCircleSecond_sq {w : ℂ} (hw : ‖w‖ ^ 2 ≤ 1) :
    discCircleSecond w ^ 2 = 1 - ‖w‖ ^ 2 / 2 :=
  Real.sq_sqrt (by linarith)

theorem discCircleSecond_pos {w : ℂ} (hw : ‖w‖ ^ 2 ≤ 1) : 0 < discCircleSecond w :=
  Real.sqrt_pos.mpr (by linarith)

theorem norm_discCircle_sq {w : ℂ} (hw : ‖w‖ ^ 2 ≤ 1) (v : Circle) :
    ‖(√2 : ℝ)⁻¹ • w‖ ^ 2 + ‖discCircleSecond w • (v : ℂ)‖ ^ 2 = 1 := by
  rw [norm_smul, norm_smul, Circle.norm_coe, mul_one, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, discCircleSecond_sq hw, inv_pow, sqrt_two_sq]
  ring

def solidTorusOfDiscCircle (q : UnitDisc.{u} × Circle) : solidTorusSet.{u} :=
  ⟨sphereOfPair ((√2 : ℝ)⁻¹ • q.1.down.val) (discCircleSecond q.1.down.val • (q.2 : ℂ))
    (norm_discCircle_sq q.1.down.2 q.2), by
    change cliffordHeight _ ≤ 0
    have hw : ‖q.1.down.val‖ ^ 2 ≤ 1 := q.1.down.2
    rw [cliffordHeight, sphereFirst_sphereOfPair, sphereSecond_sphereOfPair, norm_smul, norm_smul,
      Circle.norm_coe, mul_one, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      discCircleSecond_sq hw, inv_pow, sqrt_two_sq]
    linarith⟩

theorem contMDiff_discOfSolidTorus :
    ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ discOfSolidTorus.{u} := by
  have h : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ discPointOfSolidTorus.{u} :=
    (unitDiscAtlas.contMDiff_iff_subtype_val discPointOfSolidTorus).mpr
      ((contDiff_const_smul (√2 : ℝ)).contMDiff.comp
        (contMDiff_sphereFirst.comp contMDiff_solidTorus_val))
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp h

theorem contMDiff_unitOf_sphereSecond_solidTorus :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ (fun p : solidTorusSet.{u} => unitOf (sphereSecond p.val)) := by
  intro p
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds
    (sphereSecond_ne_zero_of_mem p.2))).comp p
      (contMDiff_sphereSecond.comp contMDiff_solidTorus_val p)

theorem contMDiff_disc_val :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun w : UnitDisc.{u} => w.down.val) :=
  unitDiscAtlas.contMDiff_subtype_val.comp (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm.contMDiff

theorem contMDiff_solidTorusOfDiscCircle :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ solidTorusOfDiscCircle.{u} := by
  rw [contMDiff_solidTorus_iff]
  have hw : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : UnitDisc.{u} × Circle => q.1.down.val) := contMDiff_disc_val.comp contMDiff_fst
  have hsecond : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitDisc.{u} × Circle => discCircleSecond q.1.down.val) := by
    intro q
    have hpos : 0 < 1 - ‖q.1.down.val‖ ^ 2 / 2 := by
      have := q.1.down.2
      change ‖q.1.down.val‖ ^ 2 ≤ 1 at this
      linarith
    have hinner : ContDiffAt ℝ ∞ (fun w : ℂ => 1 - ‖w‖ ^ 2 / 2) q.1.down.val :=
      (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)).contDiffAt
    have hd : ContDiffAt ℝ ∞ discCircleSecond q.1.down.val :=
      (Real.contDiffAt_sqrt hpos.ne').comp q.1.down.val hinner
    exact ContMDiffAt.comp (g := discCircleSecond)
      (f := fun q : UnitDisc.{u} × Circle => q.1.down.val) q hd.contMDiffAt (hw q)
  refine contMDiffOn_univ.mp (contMDiffOn_of_sphereFirst_sphereSecond isOpen_univ ?_ ?_)
  · simp only [Function.comp_apply, solidTorusOfDiscCircle, sphereFirst_sphereOfPair]
    exact ((contDiff_const_smul ((√2 : ℝ)⁻¹)).contMDiff.comp hw).contMDiffOn
  · simp only [Function.comp_apply, solidTorusOfDiscCircle, sphereSecond_sphereOfPair]
    exact contMDiffOn_smul_of_real hsecond.contMDiffOn
      (contMDiff_circle_coe.comp contMDiff_snd).contMDiffOn

def solidTorusDiscCircle :
    solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, (𝓡∂ 2).prod (𝓡 1)⟯ UnitDisc.{u} × Circle where
  toFun p := (discOfSolidTorus p, unitOf (sphereSecond p.val))
  invFun := solidTorusOfDiscCircle
  left_inv p := by
    apply Subtype.ext
    apply sphere_ext
    · change (√2 : ℝ)⁻¹ • (√2 : ℝ) • sphereFirst p.val = sphereFirst p.val
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    · change discCircleSecond ((√2 : ℝ) • sphereFirst p.val) •
        (unitOf (sphereSecond p.val) : ℂ) = sphereSecond p.val
      have hd : discCircleSecond ((√2 : ℝ) • sphereFirst p.val) = ‖sphereSecond p.val‖ := by
        rw [discCircleSecond, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sqrt_two_sq,
          norm_sphereFirst_sq_eq, ← Real.sqrt_sq (norm_nonneg (sphereSecond p.val)),
          norm_sphereSecond_sq_eq]
        congr 1
        ring
      rw [hd, norm_smul_unitOf]
  right_inv q := by
    obtain ⟨⟨⟨w, hw⟩⟩, v⟩ := q
    have hw' : ‖w‖ ^ 2 ≤ 1 := hw
    refine Prod.ext ?_ ?_
    · apply ULift.ext
      apply Subtype.ext
      change (√2 : ℝ) • sphereFirst (solidTorusOfDiscCircle (⟨⟨w, hw⟩⟩, v)).val = w
      simp only [solidTorusOfDiscCircle, sphereFirst_sphereOfPair]
      rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    · change unitOf (sphereSecond (solidTorusOfDiscCircle (⟨⟨w, hw⟩⟩, v)).val) = v
      simp only [solidTorusOfDiscCircle, sphereSecond_sphereOfPair]
      exact unitOf_smul (discCircleSecond_pos hw') v
  contMDiff_toFun := contMDiff_discOfSolidTorus.prodMk contMDiff_unitOf_sphereSecond_solidTorus
  contMDiff_invFun := contMDiff_solidTorusOfDiscCircle

def solidTorusTopDiffeomorph :
    (⊤ : TopologicalSpace.Opens solidTorusCarrier.{u}.Carrier) ≃ₘ⟮solidTorusCarrier.{u}.model,
      (SurfaceModel.model unitDiscSurface.{u}.kind).prod (𝓡 1)⟯
      unitDiscSurface.{u}.Carrier × Circle :=
  (openDiffeomorphOfForall (⊤ : TopologicalSpace.Opens solidTorusCarrier.{u}.Carrier)
    (fun _ => trivial)).trans solidTorusDiscCircle

def solidTorusFibration : CircleFibration solidTorusCarrier.{u} ⊤ :=
  CircleFibration.ofProductDiffeomorph unitDiscSurface solidTorusTopDiffeomorph

end GC.GraphManifold
