import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorse
import DifferentialGeometry.Topology.VectorField.Transport
import DifferentialGeometry.Topology.VectorField.Pushforward
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.Interval.Tangent
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorseBicollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorseExistence

/-!
# Collar pieces of old ports

Chapter 6, lane MD5, tier T3 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3, errata after
review 8). Main result `exists_oldPortCollarPiece`: for a half collar `c₀` of a boundary torus
inside `U` and a lifted level-0 bicollar of the same component, the component of
`{f ∘ π ≤ level 0}` through the torus is a smooth embedded `T² × [0, level 0]`, equal to `c₀`
near the torus and to the lifted bicollar flow near the level. It is the time-reparametrised
flow of a field equal to the collar normal near the torus, to the lifted generator near the
level, and with positive rate of `f ∘ π` in between (`exists_portPiece`); the range is the
component by an open–closed argument (`range_eq_connectedComponentIn`).

Boundary correspondence of a circle fibration: a point of the total space is a boundary point
exactly when its projection is one
(`CircleFibration.isBoundaryPoint_iff`), read off from a bundle chart `π⁻¹ N ≃ N × S¹` and the
boundaryless circle factor. Hence `u = f ∘ π` vanishes exactly on the boundary of the total space
(`BaseMorseData.f_projection_eq_zero_iff`), and a lifted level bicollar raises `u` affinely,
`u (Φ̃ r x) = u x + κ r` on the band `|s| < width` (`LiftedBicollar.f_projection_flow`). The
projection is a submersion (`CircleFibration.surjective_mfderiv_projection'`, from the chart), so
`du ≠ 0` wherever `f ∘ π ≤ level 0` (`BaseMorseData.mfderiv_f_projection_ne_zero`), in particular
on the boundary. Strictly inward normal derivative: for a half collar `c₀` of a boundary torus and
a function `r ≥ 0` on the collar, vanishing on the torus, with `dr ≠ 0` there, the derivative of
`r ∘ c₀` in the normal direction `halfCollarNormal` is positive (`pos_mfderiv_halfCollarNormal`:
`d(r ∘ c₀)` kills the torus directions, is nonzero because `c₀` is a local diffeomorphism, and is
`≥ 0` on the normal by Fermat on the half space).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem CircleFibration.isBoundaryPoint_iff (F : CircleFibration C U) (x : U) :
    C.model.IsBoundaryPoint x.val ↔
      (SurfaceModel.model F.base.kind).IsBoundaryPoint (F.projection x) := by
  let N := F.neighborhood (F.projection x)
  let x' : TopologicalSpace.Opens.comap F.projection N := ⟨x, F.mem_neighborhood _⟩
  have h1 : C.model.IsBoundaryPoint x.val ↔ C.model.IsBoundaryPoint x' := by
    rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (x := x'),
      ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (x := x)]
  have h2 : C.model.IsBoundaryPoint x' ↔
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)).IsBoundaryPoint
        (F.trivialization (F.projection x) x') := by
    have h := (F.trivialization (F.projection x)).preimage_boundary (by simp)
    have h' := congrArg (fun s => x' ∈ s) h
    exact h'.symm.to_iff
  have h3 : ((SurfaceModel.model F.base.kind).prod (𝓡 1)).IsBoundaryPoint
        (F.trivialization (F.projection x) x') ↔
      (SurfaceModel.model F.base.kind).IsBoundaryPoint
        (F.trivialization (F.projection x) x').1 := by
    have h := ModelWithCorners.boundary_of_boundaryless_right (I := SurfaceModel.model F.base.kind)
      (J := 𝓡 1) (M := N) (N := Circle)
    have h' := congrArg (fun s => F.trivialization (F.projection x) x' ∈ s) h
    have h'' : F.trivialization (F.projection x) x' ∈
        ((SurfaceModel.model F.base.kind).prod (𝓡 1)).boundary (N × Circle) ↔
        (F.trivialization (F.projection x) x').1 ∈
          (SurfaceModel.model F.base.kind).boundary N := by
      rw [h' |>.to_iff]
      exact ⟨fun hp => hp.1, fun hp => ⟨hp, mem_univ _⟩⟩
    exact h''
  have h4 : (SurfaceModel.model F.base.kind).IsBoundaryPoint
        (F.trivialization (F.projection x) x').1 ↔
      (SurfaceModel.model F.base.kind).IsBoundaryPoint (F.projection x) := by
    rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val,
      F.projection_trivialization]
  exact h1.trans (h2.trans (h3.trans h4))

theorem BaseMorseData.f_projection_eq_zero_iff (F : CircleFibration C U) (D : BaseMorseData F.base)
    (x : U) : D.f (F.projection x) = 0 ↔ C.model.IsBoundaryPoint x.val := by
  rw [D.eq_zero_iff, CircleFibration.isBoundaryPoint_iff F x]

theorem LiftedBicollar.lt_one_of_lt_width {F : CircleFibration C U}
    {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞} (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (L : LiftedBicollar F c) {s : ℝ} (hs : |s| < L.width) : -1 < s ∧ s < 1 := by
  have h := L.mem_source 1 L.reach (by rw [abs_of_pos (L.width_pos.trans L.width_lt_reach)])
  rw [hc] at h
  obtain ⟨-, h2⟩ := h
  have h3 := L.width_lt_reach
  constructor <;> linarith [abs_lt.mp hs]

theorem LiftedBicollar.f_projection_flow {F : CircleFibration C U} (D : BaseMorseData F.base)
    {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞} (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {ℓ : ℝ}
    (hf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = ℓ + D.κ * s) (L : LiftedBicollar F c)
    {x : U} {θ : Circle} {s r : ℝ} (hx : F.projection x = c (θ, s)) (hs : |s| < L.width)
    (hsr : |s + r| < L.width) :
    D.f (F.projection (L.flow r x)) = D.f (F.projection x) + D.κ * r := by
  have h1 := L.lt_one_of_lt_width hc hs
  have h2 := L.lt_one_of_lt_width hc hsr
  rw [L.projection_flow, hx, L.baseFlow_apply θ s r hs hsr, hf θ _ h2.1 h2.2,
    hf θ _ h1.1 h1.2]
  ring

theorem CircleFibration.surjective_mfderiv_projection' (F : CircleFibration C U) (x : U) :
    Function.Surjective (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x) := by
  let N := F.neighborhood (F.projection x)
  let W := TopologicalSpace.Opens.comap F.projection N
  let x' : W := ⟨x, F.mem_neighborhood _⟩
  let τ := F.trivialization (F.projection x)
  have hτd : MDifferentiableAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ x' :=
    τ.contMDiff.mdifferentiableAt (by simp)
  have hp : (fun y : W => F.projection y.val) = fun y : W => ((τ y).1 : F.base.Carrier) := by
    funext y
    exact (F.projection_trivialization _ y).symm
  have hc1 : mfderiv C.model (SurfaceModel.model F.base.kind) (fun y : W => F.projection y.val) x' =
      (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x).comp
        (mfderiv C.model C.model (Subtype.val : W → U) x') := by
    have h1 : MDifferentiableAt C.model (SurfaceModel.model F.base.kind) F.projection x :=
      F.smooth.mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt C.model C.model (Subtype.val : W → U) x' :=
      (contMDiff_subtype_val (I := C.model) (n := ∞)).mdifferentiableAt (by simp)
    exact mfderiv_comp x' h1 h2
  have hc2 : mfderiv C.model (SurfaceModel.model F.base.kind)
      (fun y : W => ((τ y).1 : F.base.Carrier)) x' =
      mfderiv C.model (SurfaceModel.model F.base.kind) (fun y : W => (τ y).1) x' :=
    DifferentialGeometry.mfderiv_subtypeVal_comp (fun y : W => (τ y).1) x'
  have hc3 : mfderiv C.model (SurfaceModel.model F.base.kind) (fun y : W => (τ y).1) x' =
      (mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (SurfaceModel.model F.base.kind)
        Prod.fst (τ x')).comp
        (mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ x') :=
    mfderiv_comp x' mdifferentiableAt_fst hτd
  have hval : mfderiv C.model C.model (Subtype.val : W → U) x' = ContinuousLinearMap.id ℝ _ :=
    mfderiv_subtype_val (I := C.model) W x'
  intro v
  have hτs : Function.Surjective
      (mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ x') :=
    (τ.mfderivToContinuousLinearEquiv (by simp) x').surjective
  obtain ⟨w, hw⟩ := hτs (v, 0)
  refine ⟨w, ?_⟩
  have hpm : mfderiv C.model (SurfaceModel.model F.base.kind)
      (fun y : W => F.projection y.val) x' =
      mfderiv C.model (SurfaceModel.model F.base.kind)
        (fun y : W => ((τ y).1 : F.base.Carrier)) x' := by
    rw [hp]
  have h := congrArg (fun L => L w) (hc1.symm.trans (hpm.trans (hc2.trans hc3)))
  have h2 : (mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) Prod.fst (τ x')).comp
      (mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ x') w = v := by
    change mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) Prod.fst (τ x')
      (mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ x' w) = v
    rw [hw, mfderiv_fst]
    rfl
  have h3 : mfderiv C.model C.model (Subtype.val : W → U) x' w = w := by
    rw [hval]
    rfl
  exact (congrArg (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x)
    h3.symm).trans (h.trans h2)

theorem BaseMorseData.mfderiv_f_projection_ne_zero (F : CircleFibration C U)
    (D : BaseMorseData F.base) {x : U} (hx : D.f (F.projection x) ≤ D.level 0) :
    mfderiv C.model 𝓘(ℝ, ℝ) (fun y => D.f (F.projection y)) x ≠ 0 := by
  intro h
  have hc : mfderiv C.model 𝓘(ℝ, ℝ) (fun y => D.f (F.projection y)) x =
      (mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) D.f (F.projection x)).comp
        (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x) :=
    mfderiv_comp x (D.smooth.mdifferentiableAt (by simp)) (F.smooth.mdifferentiableAt (by simp))
  apply D.mfderiv_ne_zero_of_le hx
  ext v
  obtain ⟨w, rfl⟩ := CircleFibration.surjective_mfderiv_projection' F x v
  have h1 := congrArg (fun L => L w) (hc.symm.trans h)
  simpa using h1

def halfCollarNormal : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
    EuclideanSpace ℝ (Fin 1) := (0, EuclideanSpace.single 0 1)

theorem pos_mfderiv_halfCollarNormal {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X]
    (c₀ : PartialDiffeomorph halfCollarModel I (Torus × EuclideanHalfSpace 1) X ∞)
    (hsrc : c₀.source = halfCollarSource) {r : X → ℝ} (t : Torus)
    (hr : MDifferentiableAt I 𝓘(ℝ, ℝ) r (c₀ (t, halfZero)))
    (hr0 : ∀ t', r (c₀ (t', halfZero)) = 0) (hnn : ∀ q ∈ c₀.source, 0 ≤ r (c₀ q))
    (hne : mfderiv I 𝓘(ℝ, ℝ) r (c₀ (t, halfZero)) ≠ 0) :
    (0 : ℝ) < (show ℝ from
      mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) (t, halfZero) halfCollarNormal) := by
  set x : Torus × EuclideanHalfSpace 1 := (t, halfZero) with hxdef
  have hx : x ∈ c₀.source := by
    rw [hsrc]
    change (0 : ℝ) < 1
    norm_num
  have hc₀d : MDifferentiableAt halfCollarModel I c₀ x :=
    (c₀.contMDiffOn.contMDiffAt (c₀.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hloc : IsLocalDiffeomorphAt halfCollarModel I ∞ c₀ x := ⟨c₀, hx, fun y hy => rfl⟩
  have hcomp : mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) x =
      (mfderiv I 𝓘(ℝ, ℝ) r (c₀ x)).comp (mfderiv halfCollarModel I c₀ x) :=
    mfderiv_comp x hr hc₀d
  set L := mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) x with hL
  have hLne : L ≠ 0 := by
    intro h0
    apply hne
    ext v
    obtain ⟨w, hw⟩ := (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective v
    have h1 := congrArg (fun A => A w) (hcomp.symm.trans h0)
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1
    rw [← hw]
    exact h1
  have htor : ∀ v : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1), L (v, 0) = 0 := by
    intro v
    let g : Torus → Torus × EuclideanHalfSpace 1 := fun t' => (t', halfZero)
    have hg : MDifferentiableAt torusModel halfCollarModel g t :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hconst : (fun t' => r (c₀ (g t'))) = fun t'' => (0 : ℝ) := funext hr0
    have hd : mfderiv torusModel 𝓘(ℝ, ℝ) (fun t' => r (c₀ (g t'))) t = 0 := by
      rw [hconst]
      exact mfderiv_const
    have hrc : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) (g t) :=
      hr.comp x hc₀d
    have hcg := mfderiv_comp t hrc hg
    have hgd : mfderiv torusModel halfCollarModel g t v = (v, 0) := by
      have h := ((hasMFDerivAt_id t).prodMk
        (hasMFDerivAt_const (I := torusModel) (I' := 𝓡∂ 1) halfZero t)).mfderiv
      have hge : g = fun y => (id y, halfZero) := rfl
      rw [hge, h]
      rfl
    have h1 := congrArg (fun A => A v) (hcg.symm.trans hd)
    have h2 : (mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) x)
        (mfderiv torusModel halfCollarModel g t v) = 0 := h1
    rw [hgd] at h2
    exact h2
  have hrc : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ) (fun q => r (c₀ q)) x := hr.comp x hc₀d
  have hfd := hrc.hasMFDerivAt.2
  have hmin : IsLocalMinOn (writtenInExtChartAt halfCollarModel 𝓘(ℝ, ℝ) x (fun q => r (c₀ q)))
      (range halfCollarModel) (extChartAt halfCollarModel x x) := by
    have hval : writtenInExtChartAt halfCollarModel 𝓘(ℝ, ℝ) x (fun q => r (c₀ q))
        (extChartAt halfCollarModel x x) = 0 := by
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        Function.comp_apply, id_eq]
      rw [(extChartAt halfCollarModel x).left_inv (mem_extChartAt_source x)]
      exact hr0 t
    filter_upwards [nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds
      (c₀.open_source.mem_nhds hx))] with y hy
    rw [hval]
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_apply, id_eq]
    exact hnn _ hy
  have hcone : halfCollarNormal ∈ posTangentConeAt (range halfCollarModel)
      (extChartAt halfCollarModel x x) := by
    apply mem_posTangentConeAt_of_segment_subset
    apply halfCollarModel.convex_range.segment_subset
      (extChartAt_target_subset_range x (mem_extChartAt_target x))
    rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
      range_modelWithCornersEuclideanHalfSpace]
    refine ⟨mem_univ _, ?_⟩
    have h2 : (extChartAt halfCollarModel x x).2 = (halfZero : EuclideanHalfSpace 1).val := rfl
    have h3 : ((halfZero : EuclideanHalfSpace 1).val : EuclideanSpace ℝ (Fin 1)) 0 = 0 := rfl
    change (0 : ℝ) ≤ ((extChartAt halfCollarModel x x).2 + EuclideanSpace.single 0 1 :
      EuclideanSpace ℝ (Fin 1)) 0
    rw [h2, PiLp.add_apply, h3]
    simp
  have hnn' := hmin.hasFDerivWithinAt_nonneg hfd hcone
  have hge : (0 : ℝ) ≤ L halfCollarNormal := hnn'
  refine lt_of_le_of_ne hge fun h0 => hLne ?_
  let L' : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
      →L[ℝ] ℝ := L
  have htor' : ∀ v, L' (v, 0) = 0 := htor
  have h0' : L' halfCollarNormal = 0 := h0.symm
  have hL' : L' = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : w = ((w.1, 0) : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) + (w.2 0) • halfCollarNormal := by
      refine Prod.ext (by simp [halfCollarNormal]) ?_
      ext i
      fin_cases i
      simp [halfCollarNormal]
    rw [hw, map_add, map_smul, htor', h0']
    simp
  exact hL'

section NormalField

theorem contMDiff_halfSpace_constSection (v : EuclideanSpace ℝ (Fin 1)) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent ∞
      (fun h : EuclideanHalfSpace 1 =>
        (⟨h, v⟩ : TangentBundle (𝓡∂ 1) (EuclideanHalfSpace 1))) := by
  intro h
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  convert contMDiffAt_const (c := v) using 1
  ext h'
  simp

theorem contMDiff_halfCollarNormal :
    ContMDiff halfCollarModel halfCollarModel.tangent ∞
      (fun q : Torus × EuclideanHalfSpace 1 =>
        (⟨q, halfCollarNormal⟩ :
          TangentBundle halfCollarModel (Torus × EuclideanHalfSpace 1))) := by
  have h1 : ContMDiff torusModel torusModel.tangent ∞
      (fun p : Torus => (⟨p, 0⟩ : TangentBundle torusModel Torus)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace torusModel)
  have h2 := contMDiff_halfSpace_constSection (EuclideanSpace.single 0 1)
  exact contMDiff_equivTangentBundleProd_symm.comp ((h1.comp contMDiff_fst).prodMk
    (h2.comp contMDiff_snd))

theorem hasMFDerivAt_halfSpaceOneLift {t : ℝ} (ht : 0 < t) :
    HasMFDerivAt 𝓘(ℝ) (𝓡∂ 1) Manifold.halfSpaceOneLift t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) := by
  let T := PiLp.equivOfUnique 2 ℝ (fun i : Fin 1 ↦ ℝ)
  have hd : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) Manifold.halfSpaceOneLift t :=
    ((Manifold.contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds ht)).mdifferentiableAt
      (by simp))
  have hc := Manifold.hasMFDerivAt_halfSpaceOneCoordinate (Manifold.halfSpaceOneLift t)
  have hcomp := hc.comp t hd.hasMFDerivAt
  have hid : (fun t' : ℝ => (Manifold.halfSpaceOneLift t').1 0) =ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    change max t' 0 = t'
    exact max_eq_left ht'.le
  have h1 : T.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ) (𝓡∂ 1) Manifold.halfSpaceOneLift t) =
      ContinuousLinearMap.id ℝ ℝ := by
    have h2 := (hcomp.congr_of_eventuallyEq hid.symm).mfderiv
    rw [mfderiv_id] at h2
    exact h2.symm
  have h3 : mfderiv 𝓘(ℝ) (𝓡∂ 1) Manifold.halfSpaceOneLift t = T.symm.toContinuousLinearMap := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h4 : T (mfderiv 𝓘(ℝ) (𝓡∂ 1) Manifold.halfSpaceOneLift t v) = v :=
      congrArg (fun L => L v) h1
    change _ = T.symm v
    conv_rhs => rw [← h4]
    exact (T.symm_apply_apply _).symm
  have h5 : T.symm.toContinuousLinearMap =
      (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    refine ContinuousLinearMap.ext_ring ?_
    change T.symm 1 = (1 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
    rw [one_smul]
    ext i
    fin_cases i
    simp [T]
  exact hd.hasMFDerivAt.congr_mfderiv (h3.trans h5)

variable {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]

def halfCollarNormalField (z : Torus × EuclideanHalfSpace 1) : TangentSpace halfCollarModel z :=
  halfCollarNormal

def collarNormalField
    (e : PartialDiffeomorph halfCollarModel I (Torus × EuclideanHalfSpace 1) M ∞)
    (x : M) : TangentSpace I x :=
  VectorField.mpullback I halfCollarModel e.symm halfCollarNormalField x

theorem collarNormalField_apply
    (e : PartialDiffeomorph halfCollarModel I (Torus × EuclideanHalfSpace 1) M ∞)
    {q : Torus × EuclideanHalfSpace 1} (hq : q ∈ e.source) :
    collarNormalField e (e q) = mfderiv halfCollarModel I e q halfCollarNormal :=
  DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply e (by simp)
    halfCollarNormalField hq

theorem hasMFDerivAt_collarRay
    (e : PartialDiffeomorph halfCollarModel I (Torus × EuclideanHalfSpace 1) M ∞)
    (p : Torus) {t : ℝ} (ht : 0 < t) (hsrc : (p, Manifold.halfSpaceOneLift t) ∈ e.source) :
    HasMFDerivAt 𝓘(ℝ) I (fun s => e (p, Manifold.halfSpaceOneLift s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (collarNormalField e (e (p, Manifold.halfSpaceOneLift t)))) := by
  have hg := (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := torusModel) p t).prodMk
    (hasMFDerivAt_halfSpaceOneLift ht)
  have he := (e.mdifferentiableAt (by simp) hsrc).hasMFDerivAt
  have hcomp := he.comp t hg
  rw [collarNormalField_apply e hsrc]
  refine hcomp.congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  change mfderiv halfCollarModel I e (p, Manifold.halfSpaceOneLift t)
      (0, (1 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =
    (1 : ℝ) • mfderiv halfCollarModel I e (p, Manifold.halfSpaceOneLift t) halfCollarNormal
  rw [one_smul, one_smul]
  rfl

end NormalField

section PortSetup

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  (D : BaseMorseData F.base)

def portHeight (x : U) : ℝ := D.f (F.projection x)

theorem contMDiff_portHeight : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ (portHeight F D) :=
  D.smooth.comp F.smooth

theorem portHeight_nonneg (x : U) : 0 ≤ portHeight F D x := D.nonneg _

theorem isInteriorPoint_of_portHeight_pos {x : U} (hx : 0 < portHeight F D x) :
    C.model.IsInteriorPoint x := by
  rw [ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val,
    ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have h := (BaseMorseData.f_projection_eq_zero_iff F D x).mpr hb
  change portHeight F D x = 0 at h
  linarith

theorem isCompact_portHeight (α β : ℝ) :
    IsCompact {x : U | portHeight F D x ∈ Icc α β} :=
  CircleFibration.isCompact_preimage F (isClosed_Icc.preimage D.smooth.continuous)

theorem mfderiv_portHeight_ne_zero_of {x : U}
    (hx : mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) D.f (F.projection x) ≠ 0) :
    mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x ≠ 0 := by
  intro h
  have hc : mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x =
      (mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) D.f (F.projection x)).comp
        (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x) :=
    mfderiv_comp x (D.smooth.mdifferentiableAt (by simp)) (F.smooth.mdifferentiableAt (by simp))
  apply hx
  ext v
  obtain ⟨w, rfl⟩ := CircleFibration.surjective_mfderiv_projection' F x v
  exact congrArg (fun L => L w) (hc.symm.trans h)

theorem mfderiv_portHeight_ne_zero {x : U} (hx : portHeight F D x < D.level 0 + 2 * D.κ) :
    mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x ≠ 0 := by
  apply mfderiv_portHeight_ne_zero_of F D
  rcases le_or_gt (portHeight F D x) (D.level 0) with h | h
  · exact D.mfderiv_ne_zero_of_le h
  · intro h0
    have h1 := D.field_unit 0 (F.projection x) (by
      change |portHeight F D x - D.level 0| < 2 * D.κ
      rw [abs_of_pos (by linarith)]
      linarith)
    rw [h0] at h1
    have h2 : (0 : ℝ) = 1 := h1
    norm_num at h2

variable {F} (c₀ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1)
  C.Carrier ∞) (hsrc : c₀.source = halfCollarSource) (hown : c₀.target ⊆ U)

include hsrc hown in
theorem nonempty_opens_of_collar : Nonempty U := by
  have h : ((1 : Torus), halfZero) ∈ c₀.source := by
    rw [hsrc]
    change (0 : ℝ) < 1
    norm_num
  exact ⟨⟨c₀ (1, halfZero), hown (c₀.map_source h)⟩⟩

def portCollar : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞ :=
  c₀.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal U
    (nonempty_opens_of_collar c₀ hsrc hown)).symm

theorem portCollar_source : (portCollar c₀ hsrc hown).source = c₀.source := by
  ext q
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    change c₀ q ∈ (U.openPartialHomeomorphSubtypeCoe
      (nonempty_opens_of_collar c₀ hsrc hown)).target
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hown (c₀.map_source h)

theorem portCollar_apply_val {q : Torus × EuclideanHalfSpace 1} (hq : q ∈ c₀.source) :
    (portCollar c₀ hsrc hown q).val = c₀ q := by
  change (U.openPartialHomeomorphSubtypeCoe (nonempty_opens_of_collar c₀ hsrc hown)).symm
    (c₀ q) = c₀ q
  exact (U.openPartialHomeomorphSubtypeCoe _).right_inv (by
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hown (c₀.map_source hq))

end PortSetup

section CollarWidth

theorem continuous_tangentFibre_real :
    Continuous fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ => (v.2 : ℝ) :=
  continuous_snd.comp (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous

theorem continuousOn_mfderiv_apply_const {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] [IsManifold I ∞ X] {g : X → ℝ} {s : Set X} (hs : IsOpen s)
    (hg : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g s) (V : (x : X) → TangentSpace I x)
    (hV : Continuous fun x => (⟨x, V x⟩ : TangentBundle I X)) :
    ContinuousOn (fun x => (mfderiv I 𝓘(ℝ, ℝ) g x (V x) : ℝ)) s := by
  have h1 := hg.continuousOn_tangentMapWithin (by simp) hs.uniqueMDiffOn
  have h2 : ContinuousOn (fun x => tangentMapWithin I 𝓘(ℝ, ℝ) g s ⟨x, V x⟩) s :=
    h1.comp hV.continuousOn fun x hx => hx
  refine (continuous_tangentFibre_real.comp_continuousOn h2).congr fun x hx => ?_
  change (mfderiv I 𝓘(ℝ, ℝ) g x (V x) : ℝ) = (mfderivWithin I 𝓘(ℝ, ℝ) g s x (V x) : ℝ)
  rw [mfderivWithin_of_isOpen hs hx]

theorem exists_collarWidth {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X]
    (e : PartialDiffeomorph halfCollarModel I (Torus × EuclideanHalfSpace 1) X ∞)
    (hsrc : e.source = halfCollarSource) {P : Torus × EuclideanHalfSpace 1 → Prop}
    (hP : IsOpen {q | q ∈ e.source ∧ P q}) (h0 : ∀ t, P (t, halfZero)) :
    ∃ a > 0, a < 1 ∧ ∀ t s (hs : 0 ≤ s), s ≤ a → P (t, halfPoint s hs) := by
  have hzero : ∀ t : Torus, (t, halfZero) ∈ e.source := fun t => by
    rw [hsrc]
    change (0 : ℝ) < 1
    norm_num
  obtain ⟨u₁, v₁, -, hv₁, hu₁, hz, huv⟩ := generalized_tube_lemma isCompact_univ
    (isCompact_singleton (x := halfZero)) hP (fun q hq => by
      obtain ⟨t, h⟩ := q
      have hh : h = halfZero := hq.2
      subst hh
      exact ⟨hzero t, h0 t⟩)
  have hcont : Continuous fun s : ℝ => Manifold.halfSpaceOneLift s := by
    rw [show (fun s : ℝ => Manifold.halfSpaceOneLift s) =
      fun s => (Manifold.halfSpaceOneHomeomorph.symm ⟨max 0 s, le_max_left 0 s⟩) from
      funext Manifold.halfSpaceOneLift_eq]
    exact Manifold.halfSpaceOneHomeomorph.symm.continuous.comp
      ((continuous_const.max continuous_id).subtype_mk _)
  have h00 : Manifold.halfSpaceOneLift 0 = halfZero := by
    rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift 0 le_rfl]
    rfl
  have hmem : (fun s : ℝ => Manifold.halfSpaceOneLift s) ⁻¹' v₁ ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h00]; exact hv₁.mem_nhds (hz rfl))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min (ε / 2) (1 / 2), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun t s hs hsa => ?_⟩
  have hsv : halfPoint s hs ∈ v₁ := by
    rw [GC.GraphManifold.halfPoint_eq_halfSpaceOneLift]
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs]
    linarith [min_le_left (ε / 2) (1 / 2)]
  exact (huv ⟨hu₁ (mem_univ t), hsv⟩).2

end CollarWidth

section LocalOpen

open DifferentialGeometry.Topology.Manifold

variable {X H H' M : Type*} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H} {J : ModelWithCorners ℝ E H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem image_mem_nhds_of_mfderiv_injective {ι : X → M} (hι : ContMDiff I J ∞ ι) {q : X}
    (hq : I.IsInteriorPoint q) (hqi : J.IsInteriorPoint (ι q))
    (hinjq : Function.Injective (mfderiv I J ι q)) (hdim : Module.finrank ℝ E' = Module.finrank ℝ E)
    {N : Set X} (hN : N ∈ 𝓝 q) : ι '' N ∈ 𝓝 (ι q) := by
  let c := DifferentialGeometry.Manifold.interiorChart J ∞ (ι q)
  have hxc : ι q ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J ∞ (ι q)).mpr hqi
  let O : TopologicalSpace.Opens X :=
    ⟨ι ⁻¹' c.source ∩ interior N,
      (c.open_source.preimage hι.continuous).inter isOpen_interior⟩
  let q' : O := ⟨q, hxc, mem_interior_iff_mem_nhds.mpr hN⟩
  let f : O → E := fun y => c (ι y.val)
  have hf : ContMDiff I 𝓘(ℝ, E) ∞ f := by
    intro y
    have h1 : ContMDiffAt J 𝓘(ℝ, E) ∞ c (ι y.val) :=
      c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds y.2.1)
    exact h1.comp y (hι.contMDiffAt.comp y contMDiff_subtype_val.contMDiffAt)
  have hq' : I.IsInteriorPoint q' :=
    ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr hq
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) f q') := by
    have hcd : MDifferentiableAt J 𝓘(ℝ, E) c (ι q) :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hxc)).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt I J ι q := hι.mdifferentiableAt (by simp)
    have hvd : MDifferentiableAt I I (Subtype.val : O → X) q' :=
      (contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiableAt (by simp)
    have h1 : mfderiv I 𝓘(ℝ, E) f q' = (mfderiv J 𝓘(ℝ, E) c (ι q)).comp
        ((mfderiv I J ι q).comp (mfderiv I I (Subtype.val : O → X) q')) := by
      rw [← mfderiv_comp q' hιd hvd]
      exact mfderiv_comp q' hcd (hιd.comp q' hvd)
    have hloc : IsLocalDiffeomorphAt J 𝓘(ℝ, E) ∞ c (ι q) := c.isLocalDiffeomorphAt J 𝓘(ℝ, E) ∞ hxc
    have hc : Function.Injective (mfderiv J 𝓘(ℝ, E) c (ι q)) :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
    have hv : mfderiv I I (Subtype.val : O → X) q' = ContinuousLinearMap.id ℝ _ :=
      mfderiv_subtype_val (I := I) O q'
    rw [h1, hv]
    exact hc.comp (hinjq.comp fun v w h => h)
  obtain ⟨Φ, hqΦ, hfΦ⟩ :=
    isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv hf hq' hdim hinj
  let W : Set M := c.source ∩ c ⁻¹' Φ.target
  have hW : IsOpen W :=
    c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source Φ.open_target
  have hxW : ι q ∈ W := by
    refine ⟨hxc, ?_⟩
    change f q' ∈ Φ.target
    rw [hfΦ hqΦ]
    exact Φ.map_source hqΦ
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  rintro y ⟨hyc, hyΦ⟩
  let z := Φ.symm (c y)
  have hz : z ∈ Φ.source := Φ.map_target hyΦ
  have h1 : f z = c y := by
    rw [hfΦ hz]
    exact Φ.right_inv hyΦ
  exact ⟨z.val, interior_subset z.2.2, c.toOpenPartialHomeomorph.injOn z.2.1 hyc h1⟩

end LocalOpen

section Profiles

def portBumpProfile (a M s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a / 2) / (a / 2)) *
    (1 - Real.smoothTransition ((s - M * a) / (a / 2)))

theorem contDiff_portBumpProfile (a M : ℝ) : ContDiff ℝ ∞ (portBumpProfile a M) := by
  unfold portBumpProfile
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop)))

theorem portBumpProfile_nonneg (a M s : ℝ) : 0 ≤ portBumpProfile a M s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem portBumpProfile_le_one (a M s : ℝ) : portBumpProfile a M s ≤ 1 := by
  unfold portBumpProfile
  have h1 := Real.smoothTransition.le_one ((s - a / 2) / (a / 2))
  have h2 := Real.smoothTransition.nonneg ((s - a / 2) / (a / 2))
  have h3 := Real.smoothTransition.nonneg ((s - M * a) / (a / 2))
  have h4 := Real.smoothTransition.le_one ((s - M * a) / (a / 2))
  nlinarith

theorem portBumpProfile_eq_one {a M s : ℝ} (ha : 0 < a) (hs1 : a ≤ s) (hs2 : s ≤ M * a) :
    portBumpProfile a M s = 1 := by
  unfold portBumpProfile
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    linarith

theorem portBumpProfile_eq_zero_of_le {a M s : ℝ} (ha : 0 < a) (hs : s ≤ a / 2) :
    portBumpProfile a M s = 0 := by
  unfold portBumpProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by positivity)), zero_mul]

theorem portBumpProfile_eq_zero_of_ge {a M s : ℝ} (ha : 0 < a) (hs : M * a + a / 2 ≤ s) :
    portBumpProfile a M s = 0 := by
  unfold portBumpProfile
  rw [Real.smoothTransition.one_of_one_le (x := (s - M * a) / (a / 2))
    (by rw [le_div_iff₀ (by positivity)]; linarith)]
  ring

def slopeProfile (m ν κ L w y : ℝ) : ℝ :=
  (ν * Real.smoothTransition ((y - m / 2) / (m / 2)) +
      (κ - ν) * Real.smoothTransition ((y - (L - κ * w)) / (κ * w / 2))) *
    (1 - Real.smoothTransition ((y - (L + κ * w / 2)) / (κ * w / 2)))

theorem contDiff_slopeProfile (m ν κ L w : ℝ) : ContDiff ℝ ∞ (slopeProfile m ν κ L w) := by
  unfold slopeProfile
  refine ((contDiff_const.mul (Real.smoothTransition.contDiff.comp (by fun_prop))).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp (by fun_prop)))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop)))

variable {m ν κ L w : ℝ}

theorem slopeProfile_nonneg (hν : 0 ≤ ν) (hνκ : ν ≤ κ) (y : ℝ) : 0 ≤ slopeProfile m ν κ L w y :=
  mul_nonneg (add_nonneg (mul_nonneg hν (Real.smoothTransition.nonneg _))
    (mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)))
    (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem slopeProfile_eq_zero_of_le (hm : 0 < m) (hmL : m / 2 ≤ L - κ * w) (hκw : 0 < κ * w)
    {y : ℝ} (hy : y ≤ m / 2) : slopeProfile m ν κ L w y = 0 := by
  unfold slopeProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity))]
  ring

theorem slopeProfile_eq_zero_of_ge (hκw : 0 < κ * w) {y : ℝ} (hy : L + κ * w ≤ y) :
    slopeProfile m ν κ L w y = 0 := by
  unfold slopeProfile
  rw [Real.smoothTransition.one_of_one_le (x := (y - (L + κ * w / 2)) / (κ * w / 2))
    (by rw [le_div_iff₀ (by positivity)]; linarith)]
  ring

theorem slopeProfile_eq_slow (hm : 0 < m) (hκw : 0 < κ * w) {y : ℝ} (hy1 : m ≤ y)
    (hy2 : y ≤ L - κ * w) : slopeProfile m ν κ L w y = ν := by
  unfold slopeProfile
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity))]
  ring

theorem slopeProfile_eq_band (hm : 0 < m) (hmL : m ≤ L - κ * w / 2) (hκw : 0 < κ * w) {y : ℝ}
    (hy1 : L - κ * w / 2 ≤ y) (hy2 : y ≤ L + κ * w / 2) : slopeProfile m ν κ L w y = κ := by
  unfold slopeProfile
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith),
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity))]
  ring

theorem slopeProfile_le_slow (hν : 0 ≤ ν) (hκw : 0 < κ * w) {y : ℝ} (hy : y ≤ L - κ * w) :
    slopeProfile m ν κ L w y ≤ ν := by
  unfold slopeProfile
  rw [Real.smoothTransition.zero_of_nonpos (x := (y - (L - κ * w)) / (κ * w / 2))
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
  have h1 := Real.smoothTransition.le_one ((y - m / 2) / (m / 2))
  have h2 := Real.smoothTransition.nonneg ((y - (L + κ * w / 2)) / (κ * w / 2))
  have h3 := Real.smoothTransition.le_one ((y - (L + κ * w / 2)) / (κ * w / 2))
  have h4 := Real.smoothTransition.nonneg ((y - m / 2) / (m / 2))
  have h5 : ν * Real.smoothTransition ((y - m / 2) / (m / 2)) ≤ ν := by nlinarith
  have h6 : 0 ≤ ν * Real.smoothTransition ((y - m / 2) / (m / 2)) := mul_nonneg hν h4
  rw [mul_zero, add_zero]
  nlinarith

theorem slopeProfile_pos (hm : 0 < m) (hν : 0 < ν) (hνκ : ν ≤ κ) (hκw : 0 < κ * w) {y : ℝ}
    (hy1 : m / 2 < y) (hy2 : y < L + κ * w) : 0 < slopeProfile m ν κ L w y := by
  unfold slopeProfile
  have h1 : 0 < Real.smoothTransition ((y - m / 2) / (m / 2)) :=
    Real.smoothTransition.pos_of_pos (div_pos (by linarith) (by positivity))
  have h2 : Real.smoothTransition ((y - (L + κ * w / 2)) / (κ * w / 2)) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by rw [div_lt_one (by positivity)]; linarith)
  have h3 := Real.smoothTransition.nonneg ((y - (L - κ * w)) / (κ * w / 2))
  apply mul_pos
  · nlinarith
  · linarith

end Profiles

section PortField

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)

open Classical in
def portBump (a M : ℝ) (x : U) : ℝ :=
  if x ∈ e.target then portBumpProfile a M ((e.symm x).2.val 0) else 0

theorem portBump_nonneg (a M : ℝ) (x : U) : 0 ≤ portBump e a M x := by
  unfold portBump
  split_ifs
  · exact portBumpProfile_nonneg a M _
  · exact le_rfl

theorem portBump_le_one (a M : ℝ) (x : U) : portBump e a M x ≤ 1 := by
  unfold portBump
  split_ifs
  · exact portBumpProfile_le_one a M _
  · norm_num

theorem portBump_apply {a M : ℝ} {q : Torus × EuclideanHalfSpace 1} (hq : q ∈ e.source) :
    portBump e a M (e q) = portBumpProfile a M (q.2.val 0) := by
  unfold portBump
  rw [ite_eq_left (e.map_source hq)]
  erw [e.left_inv hq]

theorem isCompact_portStrip (hsrc : e.source = halfCollarSource) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : β < 1) :
    IsCompact (range fun q : Torus × Icc α β => e (q.1, halfPoint q.2.1 (hα.trans q.2.2.1))) := by
  apply isCompact_range
  have hcont : Continuous fun q : Torus × Icc α β =>
      ((q.1, halfPoint q.2.1 (hα.trans q.2.2.1)) : Torus × EuclideanHalfSpace 1) := by
    refine continuous_fst.prodMk (Continuous.subtype_mk ?_ _)
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      continuous_subtype_val.comp continuous_snd)
  refine ContinuousOn.comp_continuous e.toOpenPartialHomeomorph.continuousOn hcont fun q => ?_
  change _ ∈ e.source
  rw [hsrc]
  exact lt_of_le_of_lt (mem_Icc.mp q.2.2).2 hβ

theorem portBump_eq_zero_of_not_mem {a M : ℝ} (ha : 0 < a) {x : U}
    (hx : x ∉ range fun q : Torus × Icc (a / 2) (M * a + a / 2) =>
      e (q.1, halfPoint q.2.1 ((by positivity : (0 : ℝ) ≤ a / 2).trans q.2.2.1))) :
    portBump e a M x = 0 := by
  unfold portBump
  split_ifs with hxt
  · set s := (e.symm x).2.val 0 with hs
    by_cases h1 : s ≤ a / 2
    · exact portBumpProfile_eq_zero_of_le ha h1
    by_cases h2 : M * a + a / 2 ≤ s
    · exact portBumpProfile_eq_zero_of_ge ha h2
    push Not at h1 h2
    exfalso
    apply hx
    refine ⟨((e.symm x).1, ⟨s, h1.le, h2.le⟩), ?_⟩
    change e ((e.symm x).1, halfPoint s _) = x
    rw [show ((e.symm x).1, halfPoint s ((by positivity : (0 : ℝ) ≤ a / 2).trans h1.le)) =
      e.symm x from Prod.ext rfl (GC.GraphManifold.halfPoint_coord_eq _)]
    exact e.right_inv hxt
  · rfl

theorem contMDiff_portBump (hsrc : e.source = halfCollarSource) {a M : ℝ} (ha : 0 < a)
    (hMa : M * a + a / 2 < 1) : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ (portBump e a M) := by
  intro x
  by_cases hx : x ∈ e.target
  · have h1 : ContMDiffOn C.model 𝓘(ℝ, ℝ) ∞
        (fun y => portBumpProfile a M ((e.symm y).2.val 0)) e.target :=
      (contDiff_portBumpProfile a M).contMDiff.comp_contMDiffOn
        (Manifold.contMDiff_halfSpaceOneCoordinate.comp_contMDiffOn
          (contMDiff_snd.comp_contMDiffOn e.contMDiffOn_invFun))
    refine (h1.contMDiffAt (e.open_target.mem_nhds hx)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    unfold portBump
    rw [ite_eq_left hy]
  · have hK := (isCompact_portStrip e hsrc (by positivity : (0 : ℝ) ≤ a / 2) hMa).isClosed
    have hxK : x ∉ range fun q : Torus × Icc (a / 2) (M * a + a / 2) =>
        e (q.1, halfPoint q.2.1 ((by positivity : (0 : ℝ) ≤ a / 2).trans q.2.2.1)) := by
      rintro ⟨q, rfl⟩
      apply hx
      apply e.map_source
      rw [hsrc]
      exact lt_of_le_of_lt q.2.2.2 hMa
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    exact portBump_eq_zero_of_not_mem e ha hy

variable (F : CircleFibration C U) (D : BaseMorseData F.base)

def portField (a M : ℝ) (z : ℝ → ℝ) (V : (x : U) → TangentSpace C.model x) (x : U) :
    TangentSpace C.model x :=
  portBump e a M x • collarNormalField e x + (1 - portBump e a M x) • (z (portHeight F D x) • V x)

theorem contMDiff_portField (hsrc : e.source = halfCollarSource) {a M : ℝ} (ha : 0 < a)
    (hMa : M * a + a / 2 < 1) {z : ℝ → ℝ} (hz : ContDiff ℝ ∞ z)
    {V : (x : U) → TangentSpace C.model x}
    (hV : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle C.model U))) :
    ContMDiff C.model C.model.tangent ∞
      (fun x => (⟨x, portField e F D a M z V x⟩ : TangentBundle C.model U)) := by
  have hb := contMDiff_portBump e hsrc ha hMa
  have h2 : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, (1 - portBump e a M x) •
      (z (portHeight F D x) • V x)⟩ : TangentBundle C.model U)) :=
    (contMDiff_const.sub hb).smul_section
      (((hz.contMDiff.comp (contMDiff_portHeight F D))).smul_section hV)
  have h1 : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, portBump e a M x •
      collarNormalField e x⟩ : TangentBundle C.model U)) := by
    intro x
    by_cases hx : x ∈ e.target
    · have hW : ContMDiffAt C.model C.model.tangent ∞
          (fun y => (⟨y, collarNormalField e y⟩ : TangentBundle C.model U)) x :=
        DifferentialGeometry.VectorField.contMDiffAt_mpullback_partialDiffeomorph e.symm
          (by simp) hx (contMDiff_halfCollarNormal (e.symm x))
      exact (hb x).smul_section hW
    · have hK := (isCompact_portStrip e hsrc (by positivity : (0 : ℝ) ≤ a / 2) hMa).isClosed
      have hxK : x ∉ range fun q : Torus × Icc (a / 2) (M * a + a / 2) =>
          e (q.1, halfPoint q.2.1 ((by positivity : (0 : ℝ) ≤ a / 2).trans q.2.2.1)) := by
        rintro ⟨q, rfl⟩
        apply hx
        apply e.map_source
        rw [hsrc]
        exact lt_of_le_of_lt q.2.2.2 hMa
      refine (Bundle.contMDiff_zeroSection ℝ (TangentSpace C.model) x).congr_of_eventuallyEq ?_
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      rw [portBump_eq_zero_of_not_mem e ha hy, zero_smul]
      rfl
  exact h1.add_section h2

end PortField

section RayCalculus

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  {g : U → ℝ} (hg : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ g)

include hg in
theorem hasDerivAt_portRay (p : Torus) {σ : ℝ} (hσ : 0 < σ)
    (hsrc : (p, Manifold.halfSpaceOneLift σ) ∈ e.source) :
    HasDerivAt (fun σ' => g (e (p, Manifold.halfSpaceOneLift σ')))
      (mfderiv C.model 𝓘(ℝ, ℝ) g (e (p, Manifold.halfSpaceOneLift σ))
        (collarNormalField e (e (p, Manifold.halfSpaceOneLift σ)))) σ := by
  have h1 := hasMFDerivAt_collarRay e p hσ hsrc
  have h2 :=
    (hg.mdifferentiableAt (x := e (p, Manifold.halfSpaceOneLift σ)) (by simp)).hasMFDerivAt
  have h3 := h2.comp σ h1
  let D : ℝ →L[ℝ] ℝ := (mfderiv C.model 𝓘(ℝ, ℝ) g (e (p, Manifold.halfSpaceOneLift σ))).comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight (collarNormalField e (e (p, Manifold.halfSpaceOneLift σ))))
  have h4 : HasFDerivAt (fun σ' => g (e (p, Manifold.halfSpaceOneLift σ'))) D σ :=
    hasMFDerivAt_iff_hasFDerivAt.mp h3
  have h6 : D 1 = mfderiv C.model 𝓘(ℝ, ℝ) g (e (p, Manifold.halfSpaceOneLift σ))
      (collarNormalField e (e (p, Manifold.halfSpaceOneLift σ))) := by
    change mfderiv C.model 𝓘(ℝ, ℝ) g (e (p, Manifold.halfSpaceOneLift σ))
      ((1 : ℝ) • collarNormalField e (e (p, Manifold.halfSpaceOneLift σ))) = _
    rw [one_smul]
  exact h4.hasDerivAt.congr_deriv h6

theorem continuousOn_mfderiv_apply {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] [IsManifold I ∞ X] {f : X → ℝ} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f s) (V : (x : X) → TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I X)) s) :
    ContinuousOn (fun x => (mfderiv I 𝓘(ℝ, ℝ) f x (V x) : ℝ)) s := by
  have h1 := hf.continuousOn_tangentMapWithin (by simp) hs.uniqueMDiffOn
  have h2 : ContinuousOn (fun x => tangentMapWithin I 𝓘(ℝ, ℝ) f s ⟨x, V x⟩) s :=
    h1.comp hV fun x hx => hx
  refine (continuous_tangentFibre_real.comp_continuousOn h2).congr fun x hx => ?_
  change (mfderiv I 𝓘(ℝ, ℝ) f x (V x) : ℝ) = (mfderivWithin I 𝓘(ℝ, ℝ) f s x (V x) : ℝ)
  rw [mfderivWithin_of_isOpen hs hx]

include hg in
theorem continuousOn_portNormalDerivative :
    ContinuousOn (fun x => (mfderiv C.model 𝓘(ℝ, ℝ) g x (collarNormalField e x) : ℝ))
      e.target := by
  refine continuousOn_mfderiv_apply e.open_target (hg.contMDiffOn (s := e.target)) _ ?_
  intro x hx
  exact (DifferentialGeometry.VectorField.contMDiffAt_mpullback_partialDiffeomorph e.symm
    (by simp) hx (contMDiff_halfCollarNormal (e.symm x))).continuousAt.continuousWithinAt

end RayCalculus

section FieldDerivative

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (F : CircleFibration C U) (D : BaseMorseData F.base)

def heightRate (x : U) (v : TangentSpace C.model x) : ℝ :=
  mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x v

variable {a M : ℝ} {z : ℝ → ℝ} {V : (x : U) → TangentSpace C.model x}

theorem heightRate_portField (x : U)
    (hV : z (portHeight F D x) ≠ 0 → heightRate F D x (V x) = 1) :
    heightRate F D x (portField e F D a M z V x) =
      portBump e a M x * heightRate F D x (collarNormalField e x) +
        (1 - portBump e a M x) * z (portHeight F D x) := by
  have hlin : heightRate F D x (portField e F D a M z V x) =
      portBump e a M x * heightRate F D x (collarNormalField e x) +
        (1 - portBump e a M x) * (z (portHeight F D x) * heightRate F D x (V x)) := by
    unfold portField heightRate
    rw [map_add, map_smul, map_smul, map_smul]
    rfl
  rw [hlin]
  by_cases hz : z (portHeight F D x) = 0
  · rw [hz]
    ring
  · rw [hV hz]
    ring

theorem heightRate_portField_nonneg (x : U)
    (hV : z (portHeight F D x) ≠ 0 → heightRate F D x (V x) = 1)
    (hW : 0 < portBump e a M x → 0 < heightRate F D x (collarNormalField e x))
    (hz : 0 ≤ z (portHeight F D x)) :
    0 ≤ heightRate F D x (portField e F D a M z V x) := by
  rw [heightRate_portField e F D x hV]
  have hb0 := portBump_nonneg e a M x
  have hb1 := portBump_le_one e a M x
  have h1 : 0 ≤ portBump e a M x * heightRate F D x (collarNormalField e x) := by
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h, zero_mul]
    · exact (mul_pos h (hW h)).le
  have h2 : 0 ≤ (1 - portBump e a M x) * z (portHeight F D x) :=
    mul_nonneg (by linarith) hz
  linarith

theorem heightRate_portField_pos (x : U)
    (hV : z (portHeight F D x) ≠ 0 → heightRate F D x (V x) = 1)
    (hW : 0 < portBump e a M x → 0 < heightRate F D x (collarNormalField e x))
    (hz : 0 < z (portHeight F D x)) :
    0 < heightRate F D x (portField e F D a M z V x) := by
  rw [heightRate_portField e F D x hV]
  have hb0 := portBump_nonneg e a M x
  have hb1 := portBump_le_one e a M x
  rcases eq_or_lt_of_le hb1 with h | h
  · rw [h, sub_self, zero_mul, add_zero, one_mul]
    exact hW (by rw [h]; norm_num)
  · have h1 : 0 ≤ portBump e a M x * heightRate F D x (collarNormalField e x) := by
      rcases eq_or_lt_of_le hb0 with h' | h'
      · rw [← h', zero_mul]
      · exact (mul_pos h' (hW h')).le
    have h2 : 0 < (1 - portBump e a M x) * z (portHeight F D x) :=
      mul_pos (by linarith) hz
    linarith

theorem heightRate_portField_of_bump_zero (x : U) (hb : portBump e a M x = 0)
    (hV : z (portHeight F D x) ≠ 0 → heightRate F D x (V x) = 1) :
    heightRate F D x (portField e F D a M z V x) = z (portHeight F D x) := by
  rw [heightRate_portField e F D x hV, hb]
  ring

end FieldDerivative

section BandAnalysis

theorem affine_of_rate_in_band_of_le {h h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t)
    {α β c t₀ t₁ : ℝ} (hrate : ∀ t, h t ∈ Ioo α β → h' t = c) (h0 : h t₀ ∈ Ioo α β)
    (h1 : h t₀ + c * (t₁ - t₀) ∈ Ioo α β) (ht : t₀ ≤ t₁) :
    h t₁ = h t₀ + c * (t₁ - t₀) := by
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hmem : ∀ x ∈ Icc t₀ t₁, h t₀ + c * (x - t₀) ∈ Ioo α β := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨h0a, h0b⟩ := h0
    obtain ⟨h1a, h1b⟩ := h1
    rcases le_total 0 c with hc | hc
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  have key : Icc t₀ t₁ ⊆ {x | h x = h t₀ + c * (x - t₀)} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · exact (isClosed_eq hcont (by fun_prop)).inter isClosed_Icc
    · change h t₀ = h t₀ + c * (t₀ - t₀)
      ring
    · rintro x ⟨hx, hxI⟩
      have hx' : h x = h t₀ + c * (x - t₀) := hx
      have hxb : h x ∈ Ioo α β := by
        rw [hx']
        exact hmem x (Ico_subset_Icc_self hxI)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_Ioo.preimage hcont) x hxb
      have hD : ∀ z ∈ Ioo (x - ε) (x + ε),
          HasDerivWithinAt (fun z => h z - c * z) 0 (Ioo (x - ε) (x + ε)) z := by
        intro z hz
        have hzb : h z ∈ Ioo α β := hball (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [hz.1, hz.2])
        have h2 : HasDerivAt (fun z => h z - c * z) (h' z - c * 1) z :=
          (hd z).sub ((hasDerivAt_id z).const_mul c)
        rw [hrate z hzb, mul_one, sub_self] at h2
        exact h2.hasDerivWithinAt
      refine Filter.mem_of_superset (Ico_mem_nhdsGT (by linarith : x < x + ε)) ?_
      intro y hy
      have hxm : x ∈ Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
      have hym : y ∈ Ioo (x - ε) (x + ε) := ⟨by linarith [hy.1], hy.2⟩
      have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD (C := 0)
        (fun y hy => by simp) (convex_Ioo _ _) hxm hym
      have h3 : (h y - c * y) - (h x - c * x) = 0 :=
        norm_le_zero_iff.mp (by simpa only [zero_mul] using hn)
      change h y = h t₀ + c * (y - t₀)
      linarith
  exact key ⟨ht, le_rfl⟩

theorem affine_of_rate_in_band {h h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t)
    {α β c t₀ t₁ : ℝ} (hrate : ∀ t, h t ∈ Ioo α β → h' t = c) (h0 : h t₀ ∈ Ioo α β)
    (h1 : h t₀ + c * (t₁ - t₀) ∈ Ioo α β) : h t₁ = h t₀ + c * (t₁ - t₀) := by
  rcases le_total t₀ t₁ with ht | ht
  · exact affine_of_rate_in_band_of_le hd hrate h0 h1 ht
  · have hd' : ∀ t, HasDerivAt (fun t => h (-t)) (-h' (-t)) t := by
      intro t
      have h2 : HasDerivAt (fun t => h (-t)) (h' (-t) * -1) t := (hd (-t)).comp t (hasDerivAt_neg t)
      rw [mul_neg_one] at h2
      exact h2
    have h2 := affine_of_rate_in_band_of_le (h := fun t => h (-t)) hd' (c := -c) (t₀ := -t₀)
      (t₁ := -t₁) (fun t ht => by rw [hrate (-t) ht]) (by simpa only [neg_neg] using h0)
      (by
        have h3 : h (- -t₀) + -c * (-t₁ - -t₀) = h t₀ + c * (t₁ - t₀) := by
          rw [neg_neg]
          ring
        change h (- -t₀) + -c * (-t₁ - -t₀) ∈ Ioo α β
        rw [h3]
        exact h1) (by linarith)
    simp only [neg_neg] at h2
    linarith

end BandAnalysis

section RayMonotone

theorem continuous_halfSpaceOneLift : Continuous fun s : ℝ => Manifold.halfSpaceOneLift s := by
  rw [show (fun s : ℝ => Manifold.halfSpaceOneLift s) =
    fun s => (Manifold.halfSpaceOneHomeomorph.symm ⟨max 0 s, le_max_left 0 s⟩) from
    funext Manifold.halfSpaceOneLift_eq]
  exact Manifold.halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk _)

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)

theorem lift_mem_source (hsrc : e.source = halfCollarSource) (p : Torus) {s : ℝ} (hs : s < 1) :
    (p, Manifold.halfSpaceOneLift s) ∈ e.source := by
  rw [hsrc]
  change max s 0 < 1
  exact max_lt hs one_pos

theorem continuousOn_portRay (hsrc : e.source = halfCollarSource) {g : U → ℝ}
    (hg : Continuous g) (p : Torus) :
    ContinuousOn (fun s => g (e (p, Manifold.halfSpaceOneLift s))) (Iio 1) := by
  refine hg.comp_continuousOn (e.toOpenPartialHomeomorph.continuousOn.comp
    (continuous_const.prodMk continuous_halfSpaceOneLift).continuousOn ?_)
  intro s hs
  exact lift_mem_source e hsrc p hs

theorem strictMonoOn_portRay (hsrc : e.source = halfCollarSource) {g : U → ℝ}
    (hg : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ g) (p : Torus) {a₀ : ℝ} (ha₀ : a₀ < 1)
    (hpos : ∀ s, 0 < s → s < a₀ → (0 : ℝ) < (show ℝ from mfderiv C.model 𝓘(ℝ, ℝ) g
      (e (p, Manifold.halfSpaceOneLift s))
        (collarNormalField e (e (p, Manifold.halfSpaceOneLift s))))) :
    StrictMonoOn (fun s => g (e (p, Manifold.halfSpaceOneLift s))) (Icc 0 a₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 a₀)
  · exact (continuousOn_portRay e hsrc hg.continuous p).mono fun s hs => lt_of_le_of_lt hs.2 ha₀
  · intro s hs
    rw [interior_Icc] at hs
    exact lt_of_lt_of_eq (hpos s hs.1 hs.2)
      (hasDerivAt_portRay e hg p hs.1 (lift_mem_source e hsrc p (hs.2.trans ha₀))).deriv.symm

end RayMonotone

section CollarConstants

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (F : CircleFibration C U) (D : BaseMorseData F.base)

theorem halfSpaceOneLift_zero : Manifold.halfSpaceOneLift 0 = halfZero := by
  rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift 0 le_rfl]
  rfl

theorem portHeight_collar_zero
    (hb : ∀ t, C.model.IsBoundaryPoint (e (t, halfZero)).val) (t : Torus) :
    portHeight F D (e (t, halfZero)) = 0 :=
  (BaseMorseData.f_projection_eq_zero_iff F D _).mpr (hb t)

theorem portRate_pos_zero (hsrc : e.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (e (t, halfZero)).val) (t : Torus) :
    0 < heightRate F D (e (t, halfZero)) (collarNormalField e (e (t, halfZero))) := by
  have hq : (t, halfZero) ∈ e.source := by
    rw [hsrc]
    change (0 : ℝ) < 1
    norm_num
  have hu := contMDiff_portHeight F D
  have h := pos_mfderiv_halfCollarNormal e hsrc (r := portHeight F D) t
    (hu.mdifferentiableAt (by simp)) (portHeight_collar_zero e F D hb)
    (fun q hq => portHeight_nonneg F D _)
    (mfderiv_portHeight_ne_zero F D (by
      rw [portHeight_collar_zero e F D hb t]
      linarith [D.κ_pos, D.two_κ_lt_level]))
  have hc := mfderiv_comp (t, halfZero) (hu.mdifferentiableAt (x := e (t, halfZero)) (by simp))
    (e.mdifferentiableAt (by simp) hq)
  unfold heightRate
  rw [collarNormalField_apply e hq]
  have h2 := congrArg (fun L => L halfCollarNormal) hc
  exact lt_of_lt_of_eq h h2

theorem exists_portCollarWidth (hsrc : e.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (e (t, halfZero)).val) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ a₀ > 0, a₀ < 1 ∧ a₀ < ℓ / 2 ∧ ∀ t s, 0 ≤ s → s ≤ a₀ →
      0 < heightRate F D (e (t, Manifold.halfSpaceOneLift s))
        (collarNormalField e (e (t, Manifold.halfSpaceOneLift s))) ∧
      portHeight F D (e (t, Manifold.halfSpaceOneLift s)) < ℓ / 4 := by
  have hcont : ContinuousOn (fun q => (heightRate F D (e q) (collarNormalField e (e q)),
      portHeight F D (e q))) e.source := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact (continuousOn_portNormalDerivative e (contMDiff_portHeight F D)).comp
        e.toOpenPartialHomeomorph.continuousOn fun q hq => e.map_source hq
    · exact (contMDiff_portHeight F D).continuous.comp_continuousOn
        e.toOpenPartialHomeomorph.continuousOn
  obtain ⟨a₀, ha₀, ha₀1, hP⟩ := exists_collarWidth e hsrc
    (P := fun q => 0 < heightRate F D (e q) (collarNormalField e (e q)) ∧
      portHeight F D (e q) < ℓ / 4)
    (hcont.isOpen_inter_preimage e.open_source (isOpen_Ioi.prod isOpen_Iio))
    (fun t => ⟨portRate_pos_zero e F D hsrc hb t, by
      rw [portHeight_collar_zero e F D hb t]
      positivity⟩)
  refine ⟨min a₀ (ℓ / 4), lt_min ha₀ (by positivity), lt_of_le_of_lt (min_le_left _ _) ha₀1,
    lt_of_le_of_lt (min_le_right _ _) (by linarith), fun t s hs hsa => ?_⟩
  have h := hP t s hs (hsa.trans (min_le_left _ _))
  rw [GC.GraphManifold.halfPoint_eq_halfSpaceOneLift s hs] at h
  exact h

theorem exists_portSeparation (hsrc : e.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (e (t, halfZero)).val) {a₀ a₁ : ℝ} (ha₁ : 0 < a₁)
    (ha₁₀ : a₁ < a₀) (ha₀ : a₀ < 1)
    (hrate : ∀ t s, 0 ≤ s → s ≤ a₀ → 0 < heightRate F D (e (t, Manifold.halfSpaceOneLift s))
      (collarNormalField e (e (t, Manifold.halfSpaceOneLift s)))) :
    ∃ μ > 0, (∀ t, μ ≤ portHeight F D (e (t, Manifold.halfSpaceOneLift a₁))) ∧
      ∃ a' > 0, ∀ t s, 0 ≤ s → s ≤ a' →
        portHeight F D (e (t, Manifold.halfSpaceOneLift s)) < μ := by
  have hfc : Continuous fun t : Torus => portHeight F D (e (t, Manifold.halfSpaceOneLift a₁)) := by
    exact (contMDiff_portHeight F D).continuous.comp
      (e.toOpenPartialHomeomorph.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => lift_mem_source e hsrc t (ha₁₀.trans ha₀))
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hfc.continuousOn
  have hmono := strictMonoOn_portRay e hsrc (contMDiff_portHeight F D) t₀ ha₀
    (fun s hs hsa => hrate t₀ s hs.le hsa.le)
  have hpos : 0 < portHeight F D (e (t₀, Manifold.halfSpaceOneLift a₁)) := by
    have h := hmono ⟨le_rfl, (ha₁.trans ha₁₀).le⟩ ⟨ha₁.le, ha₁₀.le⟩ ha₁
    simp only at h
    rw [halfSpaceOneLift_zero, portHeight_collar_zero e F D hb] at h
    exact h
  refine ⟨_, hpos, fun t => ht₀ (mem_univ t), ?_⟩
  have hcont : ContinuousOn (fun q => portHeight F D (e q)) e.source :=
    (contMDiff_portHeight F D).continuous.comp_continuousOn e.toOpenPartialHomeomorph.continuousOn
  obtain ⟨a', ha', -, hP⟩ := exists_collarWidth e hsrc
    (P := fun q => portHeight F D (e q) < portHeight F D (e (t₀, Manifold.halfSpaceOneLift a₁)))
    (hcont.isOpen_inter_preimage e.open_source isOpen_Iio)
    (fun t => by
      rw [portHeight_collar_zero e F D hb t]
      exact hpos)
  refine ⟨a', ha', fun t s hs hsa => ?_⟩
  have h := hP t s hs hsa
  rw [GC.GraphManifold.halfPoint_eq_halfSpaceOneLift s hs] at h
  exact h

end CollarConstants

section LiftGenerator

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} {F : CircleFibration C U}
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞} (L : LiftedBicollar F c)

def liftGenerator (x : U) : TangentSpace C.model x :=
  mfderiv (𝓘(ℝ, ℝ).prod C.model) C.model (fun q : ℝ × U => L.flow q.1 q.2) ((0 : ℝ), x)
    ((1 : ℝ), (0 : TangentSpace C.model x))

theorem contMDiff_liftGenerator :
    ContMDiff C.model C.model.tangent ∞
      (fun x => (⟨x, liftGenerator L x⟩ : TangentBundle C.model U)) := by
  have hT := L.smooth.contMDiff_tangentMap (m := ∞) (by simp)
  have h1 : ContMDiff C.model 𝓘(ℝ, ℝ).tangent ∞
      (fun x : U => (⟨(0 : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := contMDiff_const
  have h2 : ContMDiff C.model C.model.tangent ∞
      (fun x : U => (⟨x, 0⟩ : TangentBundle C.model U)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace C.model)
  have h := hT.comp (contMDiff_equivTangentBundleProd_symm.comp (h1.prodMk h2))
  refine h.congr fun x => ?_
  change (⟨x, liftGenerator L x⟩ : TangentBundle C.model U) = ⟨L.flow 0 x, liftGenerator L x⟩
  rw [L.flow_zero]

theorem hasMFDerivAt_liftFlow (z : U) (r₀ : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) C.model (fun r => L.flow (r - r₀) z) r₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (liftGenerator L z)) := by
  have h0 : HasFDerivAt (fun r : ℝ => r - r₀) (ContinuousLinearMap.id ℝ ℝ) r₀ :=
    (hasFDerivAt_id r₀).sub_const r₀
  have h1 := hasMFDerivAt_iff_hasFDerivAt.mpr h0
  have hin : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod C.model) (fun r : ℝ => (r - r₀, z)) r₀
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) := h1.prodMk (hasMFDerivAt_const z r₀)
  have hFl : HasMFDerivAt (𝓘(ℝ, ℝ).prod C.model) C.model (fun q : ℝ × U => L.flow q.1 q.2)
      (r₀ - r₀, z)
      (mfderiv (𝓘(ℝ, ℝ).prod C.model) C.model (fun q : ℝ × U => L.flow q.1 q.2) (0, z)) := by
    rw [sub_self]
    exact (L.smooth.mdifferentiableAt (by simp)).hasMFDerivAt
  refine (hFl.comp r₀ hin).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  change mfderiv (𝓘(ℝ, ℝ).prod C.model) C.model (fun q : ℝ × U => L.flow q.1 q.2) (0, z)
    ((1 : ℝ), (0 : TangentSpace C.model z)) = (1 : ℝ) • liftGenerator L z
  rw [one_smul]
  rfl

theorem isMIntegralCurve_liftFlow (y : U) :
    IsMIntegralCurve (fun r => L.flow r y) (liftGenerator L) := by
  intro r₀
  have heq : (fun r => L.flow r y) = fun r => L.flow (r - r₀) (L.flow r₀ y) := by
    funext r
    rw [← L.flow_add, sub_add_cancel]
  have h : HasMFDerivAt 𝓘(ℝ, ℝ) C.model (fun r => L.flow r y) r₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (liftGenerator L (L.flow r₀ y))) := by
    rw [heq]
    exact hasMFDerivAt_liftFlow L (L.flow r₀ y) r₀
  exact h

theorem heightRate_liftGenerator (D : BaseMorseData F.base)
    (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {ℓ : ℝ}
    (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = ℓ + D.κ * s) {x : U} {θ : Circle} {s : ℝ}
    (hx : F.projection x = c (θ, s)) (hs : |s| < L.width) :
    heightRate F D x (liftGenerator L x) = D.κ := by
  have hev : (fun r => portHeight F D (L.flow r x)) =ᶠ[𝓝 0]
      fun r => portHeight F D x + D.κ * r := by
    have hcont : Continuous fun r : ℝ => |s + r| := by fun_prop
    have hev' : ∀ᶠ r in 𝓝 (0 : ℝ), |s + r| < L.width :=
      hcont.continuousAt.eventually (gt_mem_nhds (by
        change |s + 0| < L.width
        rw [add_zero]
        exact hs))
    filter_upwards [hev'] with r hr
    exact LiftedBicollar.f_projection_flow D hc hcf L hx hs hr
  have hd1 : HasDerivAt (fun r => portHeight F D (L.flow r x)) D.κ 0 := by
    have h2 : HasDerivAt (fun r => portHeight F D x + D.κ * r) (D.κ * 1) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul D.κ).const_add (portHeight F D x)
    rw [mul_one] at h2
    exact h2.congr_of_eventuallyEq hev
  have hu : HasMFDerivAt C.model 𝓘(ℝ, ℝ) (portHeight F D) (L.flow (0 - 0) x)
      (mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x) := by
    rw [sub_self, L.flow_zero]
    exact ((contMDiff_portHeight F D).mdifferentiableAt (by simp)).hasMFDerivAt
  have h3 := hu.comp 0 (hasMFDerivAt_liftFlow L x 0)
  let Dl : ℝ →L[ℝ] ℝ := (mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x).comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight (liftGenerator L x))
  have h4 : HasFDerivAt (fun r => portHeight F D (L.flow (r - 0) x)) Dl 0 :=
    hasMFDerivAt_iff_hasFDerivAt.mp h3
  have h5 : HasDerivAt (fun r => portHeight F D (L.flow r x)) (Dl 1) 0 := by
    refine h4.hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    change portHeight F D (L.flow r x) = portHeight F D (L.flow (r - 0) x)
    rw [sub_zero]
  have h6 := hd1.unique h5
  rw [h6]
  change mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x (liftGenerator L x) =
    mfderiv C.model 𝓘(ℝ, ℝ) (portHeight F D) x ((1 : ℝ) • liftGenerator L x)
  rw [one_smul]

end LiftGenerator

section BandCutoff

def bandProfile (w s : ℝ) : ℝ :=
  Real.smoothTransition ((w - s) / (w / 2)) * Real.smoothTransition ((w + s) / (w / 2))

theorem contDiff_bandProfile (w : ℝ) : ContDiff ℝ ∞ (bandProfile w) := by
  unfold bandProfile
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem bandProfile_nonneg (w s : ℝ) : 0 ≤ bandProfile w s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bandProfile_le_one (w s : ℝ) : bandProfile w s ≤ 1 := by
  unfold bandProfile
  have h1 := Real.smoothTransition.le_one ((w - s) / (w / 2))
  have h2 := Real.smoothTransition.nonneg ((w - s) / (w / 2))
  have h3 := Real.smoothTransition.nonneg ((w + s) / (w / 2))
  have h4 := Real.smoothTransition.le_one ((w + s) / (w / 2))
  nlinarith

theorem bandProfile_eq_one {w s : ℝ} (hw : 0 < w) (hs : |s| ≤ w / 2) : bandProfile w s = 1 := by
  unfold bandProfile
  obtain ⟨h1, h2⟩ := abs_le.mp hs
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith),
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith), one_mul]

theorem bandProfile_eq_zero {w s : ℝ} (hw : 0 < w) (hs : w ≤ |s|) : bandProfile w s = 0 := by
  unfold bandProfile
  rcases le_abs'.mp hs with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (x := (w + s) / (w / 2))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (w - s) / (w / 2))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), zero_mul]

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞)

open Classical in
def bandCutoff (w : ℝ) (x : U) : ℝ :=
  if F.projection x ∈ c.target then bandProfile w (c.symm (F.projection x)).2 else 0

theorem bandCutoff_nonneg (w : ℝ) (x : U) : 0 ≤ bandCutoff F c w x := by
  unfold bandCutoff
  split_ifs
  · exact bandProfile_nonneg w _
  · exact le_rfl

theorem bandCutoff_le_one (w : ℝ) (x : U) : bandCutoff F c w x ≤ 1 := by
  unfold bandCutoff
  split_ifs
  · exact bandProfile_le_one w _
  · norm_num

theorem bandCutoff_apply (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (w : ℝ) {x : U} {θ : Circle}
    {s : ℝ} (hx : F.projection x = c (θ, s)) (hs : -1 < s ∧ s < 1) :
    bandCutoff F c w x = bandProfile w s := by
  have hsrc : (θ, s) ∈ c.source := by
    rw [hc]
    exact hs
  unfold bandCutoff
  rw [hx, ite_eq_left (c.map_source hsrc)]
  erw [c.left_inv hsrc]

theorem isCompact_bandImage (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {w : ℝ} (hw1 : w < 1) :
    IsCompact (c '' (univ ×ˢ Icc (-w) w)) := by
  refine (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (c.toOpenPartialHomeomorph.continuousOn.mono ?_)
  rintro ⟨θ, s⟩ ⟨-, hs⟩
  change _ ∈ c.source
  rw [hc]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem exists_of_bandCutoff_ne_zero {w : ℝ} (hw : 0 < w) {x : U}
    (hx : bandCutoff F c w x ≠ 0) :
    ∃ θ s, F.projection x = c (θ, s) ∧ |s| < w ∧ (θ, s) ∈ c.source := by
  unfold bandCutoff at hx
  split_ifs at hx with h
  · refine ⟨(c.symm (F.projection x)).1, (c.symm (F.projection x)).2, (c.right_inv h).symm,
      ?_, c.map_target h⟩
    by_contra hs
    exact hx (bandProfile_eq_zero hw (not_lt.mp hs))
  · exact absurd rfl hx

theorem contMDiff_bandCutoff (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {w : ℝ} (hw : 0 < w)
    (hw1 : w < 1) : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ (bandCutoff F c w) := by
  intro x
  by_cases hx : F.projection x ∈ c.target
  · have h1 : ContMDiffAt C.model 𝓘(ℝ, ℝ) ∞
        (fun y => bandProfile w (c.symm (F.projection y)).2) x := by
      have hs : ContMDiffAt (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ c.symm
          (F.projection x) := c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hx)
      exact (contDiff_bandProfile w).contMDiff.contMDiffAt.comp x
        (contMDiffAt_snd.comp x (hs.comp x (F.smooth x)))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(c.open_target.preimage F.smooth.continuous).mem_nhds hx] with y hy
    unfold bandCutoff
    rw [ite_eq_left (show F.projection y ∈ c.target from hy)]
  · have hK : IsClosed (F.projection ⁻¹' (c '' (univ ×ˢ Icc (-w) w))) :=
      (isCompact_bandImage F c hc hw1).isClosed.preimage F.smooth.continuous
    have hxK : x ∉ F.projection ⁻¹' (c '' (univ ×ˢ Icc (-w) w)) := by
      rintro ⟨q, hq, hqx⟩
      apply hx
      rw [← hqx]
      apply c.map_source
      rw [hc]
      obtain ⟨-, hq2⟩ := hq
      exact ⟨by linarith [hq2.1], by linarith [hq2.2]⟩
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    by_contra hne
    obtain ⟨θ, s, hys, hsw, -⟩ := exists_of_bandCutoff_ne_zero F c hw hne
    exact hy ⟨(θ, s), ⟨mem_univ _, (abs_le.mp hsw.le)⟩, hys.symm⟩

end BandCutoff

section PortVectorField

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (F : CircleFibration C U) (D : BaseMorseData F.base)
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞} (L : LiftedBicollar F c)

theorem exists_of_portBump_ne_zero {a M : ℝ} (ha : 0 < a) {x : U} (hx : portBump e a M x ≠ 0) :
    ∃ p s, a / 2 < s ∧ s < M * a + a / 2 ∧ x = e (p, Manifold.halfSpaceOneLift s) := by
  unfold portBump at hx
  split_ifs at hx with hxt
  · set s := (e.symm x).2.val 0 with hs
    have h1 : a / 2 < s := by
      by_contra h
      exact hx (portBumpProfile_eq_zero_of_le ha (not_lt.mp h))
    have h2 : s < M * a + a / 2 := by
      by_contra h
      exact hx (portBumpProfile_eq_zero_of_ge ha (not_lt.mp h))
    refine ⟨(e.symm x).1, s, h1, h2, ?_⟩
    have h3 : ((e.symm x).1, Manifold.halfSpaceOneLift s) = e.symm x := by
      refine Prod.ext rfl ?_
      rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift s (by linarith)]
      exact GC.GraphManifold.halfPoint_coord_eq _
    rw [h3]
    exact (e.right_inv hxt).symm
  · exact absurd rfl hx

def bandField (V₀ : (x : U) → TangentSpace C.model x) (w : ℝ) (x : U) : TangentSpace C.model x :=
  (1 - bandCutoff F c w x) • V₀ x + (bandCutoff F c w x / D.κ) • liftGenerator L x

theorem contMDiff_bandField (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {w : ℝ} (hw : 0 < w)
    (hw1 : w < 1) {V₀ : (x : U) → TangentSpace C.model x}
    (hV₀ : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, V₀ x⟩ : TangentBundle C.model U))) :
    ContMDiff C.model C.model.tangent ∞
      (fun x => (⟨x, bandField F D L V₀ w x⟩ : TangentBundle C.model U)) := by
  have hψ := contMDiff_bandCutoff F c hc hw hw1
  exact ((contMDiff_const.sub hψ).smul_section hV₀).add_section
    ((hψ.div_const D.κ).smul_section (contMDiff_liftGenerator L))

theorem heightRate_bandField (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s) {w : ℝ} (hw : 0 < w)
    (hwL : w < L.width) {V₀ : (x : U) → TangentSpace C.model x} {x : U}
    (h1 : bandCutoff F c w x ≠ 1 → heightRate F D x (V₀ x) = 1) :
    heightRate F D x (bandField F D L V₀ w x) = 1 := by
  have hlin : heightRate F D x (bandField F D L V₀ w x) =
      (1 - bandCutoff F c w x) * heightRate F D x (V₀ x) +
        (bandCutoff F c w x / D.κ) * heightRate F D x (liftGenerator L x) := by
    unfold bandField heightRate
    rw [map_add, map_smul, map_smul]
    rfl
  have hκ := D.κ_pos
  have hX : bandCutoff F c w x ≠ 0 → heightRate F D x (liftGenerator L x) = D.κ := by
    intro hne
    obtain ⟨θ, s, hxs, hsw, -⟩ := exists_of_bandCutoff_ne_zero F c hw hne
    exact heightRate_liftGenerator L D hc hcf hxs (hsw.trans hwL)
  rw [hlin]
  rcases eq_or_ne (bandCutoff F c w x) 1 with hψ | hψ
  · rw [hψ, hX (by rw [hψ]; norm_num)]
    field_simp
    ring
  · rw [h1 hψ]
    rcases eq_or_ne (bandCutoff F c w x) 0 with hψ0 | hψ0
    · rw [hψ0]
      ring
    · rw [hX hψ0]
      field_simp
      ring

def portVectorField (a M μ ν w : ℝ) (V₀ : (x : U) → TangentSpace C.model x) (x : U) :
    TangentSpace C.model x :=
  portField e F D a M (slopeProfile μ ν D.κ (D.level 0) w) (bandField F D L V₀ w) x

theorem contMDiff_portVectorField (hsrc : e.source = halfCollarSource)
    (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {a M μ ν w : ℝ} (ha : 0 < a)
    (hMa : M * a + a / 2 < 1) (hw : 0 < w) (hw1 : w < 1) {V₀ : (x : U) → TangentSpace C.model x}
    (hV₀ : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, V₀ x⟩ : TangentBundle C.model U))) :
    ContMDiff C.model C.model.tangent ∞
      (fun x => (⟨x, portVectorField e F D L a M μ ν w V₀ x⟩ : TangentBundle C.model U)) :=
  contMDiff_portField e F D hsrc ha hMa (contDiff_slopeProfile _ _ _ _ _)
    (contMDiff_bandField F D L hc hw hw1 hV₀)

theorem heightRate_bandField_of_slope (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s) {μ ν w : ℝ}
    (hw : 0 < w) (hwL : w < L.width) (hμ : 0 < μ) (hμℓ : μ / 2 ≤ D.level 0 - D.κ * w)
    {V₀ : (x : U) → TangentSpace C.model x}
    (hV₀ : ∀ x, portHeight F D x ∈ Icc (μ / 2) (D.level 0 + D.κ * w) →
      heightRate F D x (V₀ x) = 1) (x : U)
    (hz : slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) ≠ 0) :
    heightRate F D x (bandField F D L V₀ w x) = 1 := by
  have hκw : 0 < D.κ * w := mul_pos D.κ_pos hw
  refine heightRate_bandField F D L hc hcf hw hwL fun hψ1 => hV₀ x ⟨?_, ?_⟩
  · by_contra h
    exact hz (slopeProfile_eq_zero_of_le hμ hμℓ hκw (not_le.mp h).le)
  · by_contra h
    exact hz (slopeProfile_eq_zero_of_ge hκw (not_le.mp h).le)

end PortVectorField

section PortVectorFieldRates

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (F : CircleFibration C U) (D : BaseMorseData F.base)
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞} (L : LiftedBicollar F c)
  {a M a₀ μ ν w : ℝ} {V₀ : (x : U) → TangentSpace C.model x}

theorem portBump_eq_zero_of_high (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ →
      portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < D.level 0 / 4)
    {x : U} (hx : D.level 0 / 4 ≤ portHeight F D x) : portBump e a M x = 0 := by
  by_contra hne
  obtain ⟨p, s, hs1, hs2, rfl⟩ := exists_of_portBump_ne_zero e ha hne
  linarith [hcol p s (by linarith) (by linarith)]

theorem portRate_pos_of_portBump (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ → 0 < heightRate F D (e (p, Manifold.halfSpaceOneLift s))
      (collarNormalField e (e (p, Manifold.halfSpaceOneLift s))))
    {x : U} (hx : 0 < portBump e a M x) : 0 < heightRate F D x (collarNormalField e x) := by
  obtain ⟨p, s, hs1, hs2, rfl⟩ := exists_of_portBump_ne_zero e ha hx.ne'
  exact hcol p s (by linarith) (by linarith)

variable (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
  (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s)
  (hw : 0 < w) (hwL : w < L.width) (hμ : 0 < μ) (hμℓ : μ / 2 ≤ D.level 0 - D.κ * w)
  (hV₀ : ∀ x, portHeight F D x ∈ Icc (μ / 2) (D.level 0 + D.κ * w) →
    heightRate F D x (V₀ x) = 1)

include hc hcf hw hwL hμ hμℓ hV₀

theorem heightRate_portVectorField (x : U) :
    heightRate F D x (portVectorField e F D L a M μ ν w V₀ x) =
      portBump e a M x * heightRate F D x (collarNormalField e x) +
        (1 - portBump e a M x) * slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) :=
  heightRate_portField e F D x (heightRate_bandField_of_slope F D L hc hcf hw hwL hμ hμℓ hV₀ x)

theorem heightRate_portVectorField_nonneg (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ → 0 < heightRate F D (e (p, Manifold.halfSpaceOneLift s))
      (collarNormalField e (e (p, Manifold.halfSpaceOneLift s))))
    (hν : 0 ≤ ν) (hνκ : ν ≤ D.κ) (x : U) :
    0 ≤ heightRate F D x (portVectorField e F D L a M μ ν w V₀ x) :=
  heightRate_portField_nonneg e F D x
    (heightRate_bandField_of_slope F D L hc hcf hw hwL hμ hμℓ hV₀ x)
    (portRate_pos_of_portBump e F D ha hMa hcol) (slopeProfile_nonneg hν hνκ _)

theorem heightRate_portVectorField_pos (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ → 0 < heightRate F D (e (p, Manifold.halfSpaceOneLift s))
      (collarNormalField e (e (p, Manifold.halfSpaceOneLift s))))
    (hν : 0 < ν) (hνκ : ν ≤ D.κ) {x : U} (hx : portHeight F D x ∈ Icc μ (D.level 0)) :
    0 < heightRate F D x (portVectorField e F D L a M μ ν w V₀ x) :=
  heightRate_portField_pos e F D x
    (heightRate_bandField_of_slope F D L hc hcf hw hwL hμ hμℓ hV₀ x)
    (portRate_pos_of_portBump e F D ha hMa hcol)
    (slopeProfile_pos hμ hν hνκ (mul_pos D.κ_pos hw) (by linarith [hx.1])
      (by linarith [hx.2, mul_pos D.κ_pos hw]))

theorem heightRate_portVectorField_of_high (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ →
      portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < D.level 0 / 4)
    {x : U} (hx : D.level 0 / 4 ≤ portHeight F D x) :
    heightRate F D x (portVectorField e F D L a M μ ν w V₀ x) =
      slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) :=
  heightRate_portField_of_bump_zero e F D x (portBump_eq_zero_of_high e F D ha hMa hcol hx)
    (heightRate_bandField_of_slope F D L hc hcf hw hwL hμ hμℓ hV₀ x)

end PortVectorFieldRates

section PortVectorFieldValues

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (F : CircleFibration C U) (D : BaseMorseData F.base)
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞} (L : LiftedBicollar F c)
  {a M a₀ μ ν w : ℝ} {V₀ : (x : U) → TangentSpace C.model x}

theorem portVectorField_ray (hsrc : e.source = halfCollarSource) (ha : 0 < a) (p : Torus)
    {s : ℝ} (hs1 : a ≤ s) (hs2 : s ≤ M * a) (hs3 : s < 1) :
    portVectorField e F D L a M μ ν w V₀ (e (p, Manifold.halfSpaceOneLift s)) =
      collarNormalField e (e (p, Manifold.halfSpaceOneLift s)) := by
  have hq := lift_mem_source e hsrc p hs3
  have hb : portBump e a M (e (p, Manifold.halfSpaceOneLift s)) = 1 := by
    rw [portBump_apply e hq]
    change portBumpProfile a M (max s 0) = 1
    rw [max_eq_left (by linarith)]
    exact portBumpProfile_eq_one ha hs1 hs2
  unfold portVectorField portField
  rw [hb, sub_self, zero_smul, one_smul, add_zero]

theorem portVectorField_eq_liftGenerator (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hw : 0 < w) (hw1 : w < 1) (ha : 0 < a) (hMa : M * a + a / 2 ≤ a₀)
    (hcol : ∀ p s, 0 ≤ s → s ≤ a₀ →
      portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < D.level 0 / 4)
    (hμ : 0 < μ) (hμℓ : μ ≤ D.level 0 - D.κ * w / 2)
    (hℓ4 : D.level 0 / 4 ≤ D.level 0 - D.κ * w / 2) {x : U} {θ : Circle} {s : ℝ}
    (hx : F.projection x = c (θ, s)) (hs : |s| ≤ w / 2)
    (hu : portHeight F D x ∈ Icc (D.level 0 - D.κ * w / 2) (D.level 0 + D.κ * w / 2)) :
    portVectorField e F D L a M μ ν w V₀ x = liftGenerator L x := by
  have hχ := portBump_eq_zero_of_high e F D ha hMa hcol (hℓ4.trans hu.1)
  have hs1 : -1 < s ∧ s < 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hs
    constructor <;> linarith
  have hψ : bandCutoff F c w x = 1 := by
    rw [bandCutoff_apply F c hc w hx hs1]
    exact bandProfile_eq_one hw hs
  have hζ : slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) = D.κ :=
    slopeProfile_eq_band hμ hμℓ (mul_pos D.κ_pos hw) hu.1 hu.2
  unfold portVectorField portField bandField
  rw [hχ, hψ, hζ, zero_smul, zero_add, sub_zero, one_smul, sub_self, zero_smul, zero_add,
    smul_smul, mul_one_div_cancel D.κ_pos.ne', one_smul]

theorem portVectorField_eq_zero (ha : 0 < a) (hμ : 0 < μ) (hw : 0 < w)
    (hμℓ : μ / 2 ≤ D.level 0 - D.κ * w) {x : U}
    (h1 : x ∉ range fun q : Torus × Icc (a / 2) (M * a + a / 2) =>
      e (q.1, halfPoint q.2.1 ((by positivity : (0 : ℝ) ≤ a / 2).trans q.2.2.1)))
    (h2 : portHeight F D x ∉ Icc (μ / 2) (D.level 0 + D.κ * w)) :
    portVectorField e F D L a M μ ν w V₀ x = 0 := by
  have hχ := portBump_eq_zero_of_not_mem e ha h1
  have hζ : slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) = 0 := by
    rcases not_and_or.mp h2 with h | h
    · exact slopeProfile_eq_zero_of_le hμ hμℓ (mul_pos D.κ_pos hw) (not_le.mp h).le
    · exact slopeProfile_eq_zero_of_ge (mul_pos D.κ_pos hw) (not_le.mp h).le
  unfold portVectorField portField
  rw [hχ, hζ, zero_smul, zero_smul, smul_zero, zero_add]

theorem tsupport_portVectorField (hsrc : e.source = halfCollarSource) (ha : 0 < a)
    (hMa : M * a + a / 2 < 1) (hμ : 0 < μ) (hw : 0 < w) (hμℓ : μ / 2 ≤ D.level 0 - D.κ * w)
    (hpos : ∀ p s, a / 2 ≤ s → s ≤ M * a + a / 2 →
      0 < portHeight F D (e (p, Manifold.halfSpaceOneLift s))) :
    IsCompact (tsupport (portVectorField e F D L a M μ ν w V₀)) ∧
      ∀ x ∈ tsupport (portVectorField e F D L a M μ ν w V₀), C.model.IsInteriorPoint x := by
  set K₁ := range fun q : Torus × Icc (a / 2) (M * a + a / 2) =>
    e (q.1, halfPoint q.2.1 ((by positivity : (0 : ℝ) ≤ a / 2).trans q.2.2.1)) with hK₁
  set K₂ := {x : U | portHeight F D x ∈ Icc (μ / 2) (D.level 0 + D.κ * w)} with hK₂
  have hc₁ : IsCompact K₁ := isCompact_portStrip e hsrc (by positivity) hMa
  have hc₂ : IsCompact K₂ := isCompact_portHeight F D _ _
  have hsub : tsupport (portVectorField e F D L a M μ ν w V₀) ⊆ K₁ ∪ K₂ := by
    refine closure_minimal ?_ (hc₁.union hc₂).isClosed
    intro x hx
    by_contra h
    rw [mem_union, not_or] at h
    exact hx (portVectorField_eq_zero e F D L ha hμ hw hμℓ h.1 h.2)
  refine ⟨(hc₁.union hc₂).of_isClosed_subset (isClosed_tsupport _) hsub, fun x hx => ?_⟩
  apply isInteriorPoint_of_portHeight_pos F D
  rcases hsub hx with ⟨q, rfl⟩ | h
  · have h1 := hpos q.1 q.2.1 q.2.2.1 q.2.2.2
    rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift] at h1
    exact h1
  · have h1 : μ / 2 ≤ portHeight F D x := h.1
    linarith

end PortVectorFieldValues

section FlowLines

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}

theorem hasDerivAt_height_flow (F : CircleFibration C U) (D : BaseMorseData F.base)
    (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y) (x : U) (t : ℝ) :
    HasDerivAt (fun t => portHeight F D (Φ t x)) (heightRate F D (Φ t x) (Y (Φ t x))) t := by
  have h := DifferentialGeometry.Manifold.hasDerivWithinAt_scalar_comp_integralCurve
    ((hΦY x).isMIntegralCurveOn univ) (mem_univ t)
    ((contMDiff_portHeight F D).mdifferentiableAt (x := Φ t x) (by simp))
  exact hasDerivWithinAt_univ.mp h

theorem monotone_height_flow (F : CircleFibration C U) (D : BaseMorseData F.base)
    (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y)
    (hr : ∀ x, 0 ≤ heightRate F D x (Y x)) (x : U) :
    Monotone fun t => portHeight F D (Φ t x) := by
  have hd := hasDerivAt_height_flow F D hΦY x
  refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
  rw [(hd t).deriv]
  exact hr _

theorem hasMFDerivAt_collarRay_shift (p : Torus) (b : ℝ) {t : ℝ} (ht : 0 < b + t)
    (hsrc : (p, Manifold.halfSpaceOneLift (b + t)) ∈ e.source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) C.model (fun t' => e (p, Manifold.halfSpaceOneLift (b + t'))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (collarNormalField e (e (p, Manifold.halfSpaceOneLift (b + t))))) := by
  have h1 := hasMFDerivAt_collarRay e p ht hsrc
  have h0 : HasFDerivAt (fun t' : ℝ => b + t') (ContinuousLinearMap.id ℝ ℝ) t :=
    (hasFDerivAt_id t).const_add b
  have h2 := h1.comp t (hasMFDerivAt_iff_hasFDerivAt.mpr h0)
  refine h2.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
  rfl

theorem portFlow_ray (hsrc : e.source = halfCollarSource)
    (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y) {a b : ℝ}
    (hb1 : b < 1)
    (hYray : ∀ p s, a < s → s < b →
      Y (e (p, Manifold.halfSpaceOneLift s)) =
        collarNormalField e (e (p, Manifold.halfSpaceOneLift s)))
    (hint : ∀ p s, a < s → s < b → C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)))
    (ha : 0 < a) (hab : 2 * a < b) (p : Torus) {t : ℝ} (ht : t ∈ Ioo (-a) (b - 2 * a)) :
    Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))) =
      e (p, Manifold.halfSpaceOneLift (2 * a + t)) := by
  have hray : IsMIntegralCurveOn (fun t' => e (p, Manifold.halfSpaceOneLift (2 * a + t'))) Y
      (Ioo (-a) (b - 2 * a)) := by
    intro t' ht'
    have hs : 0 < 2 * a + t' := by linarith [ht'.1]
    have hsrc' := lift_mem_source e hsrc p (by linarith [ht'.2] : 2 * a + t' < 1)
    have h := hasMFDerivAt_collarRay_shift e p (2 * a) hs hsrc'
    rw [← hYray p (2 * a + t') (by linarith [ht'.1]) (by linarith [ht'.2])] at h
    exact h.hasMFDerivWithinAt
  have hflow : IsMIntegralCurveOn (fun t' => Φ t' (e (p, Manifold.halfSpaceOneLift (2 * a)))) Y
      (Ioo (-a) (b - 2 * a)) := (hΦY _).isMIntegralCurveOn _
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := 0)
    ⟨by linarith, by linarith⟩
    (fun t' ht' => hint p _ (by linarith [ht'.1]) (by linarith [ht'.2])) (hY.of_le (by simp))
    hray hflow (by simp only [add_zero, hΦ0])
  exact (heq ht).symm

theorem injective_mfderiv_flow
    (hΦs : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ t (Φ s x) = Φ (s + t) x) (t : ℝ) (x : U) :
    Function.Injective (mfderiv C.model C.model (Φ t) x) := by
  have hd : ∀ s y, MDifferentiableAt C.model C.model (Φ s) y := fun s y =>
    (hΦs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
  have hcomp : mfderiv C.model C.model (fun y => Φ (-t) (Φ t y)) x =
      (mfderiv C.model C.model (Φ (-t)) (Φ t x)).comp (mfderiv C.model C.model (Φ t) x) :=
    mfderiv_comp x (hd _ _) (hd _ _)
  have hid : (fun y => Φ (-t) (Φ t y)) = id := funext fun y => by
    rw [hΦadd, add_neg_cancel, hΦ0]
    rfl
  rw [hid, mfderiv_id] at hcomp
  intro v w hvw
  have h1 := congrArg (fun L => L v) hcomp
  have h2 := congrArg (fun L => L w) hcomp
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  exact (h1.trans (congrArg _ hvw)).trans h2.symm

theorem contMDiff_portFlowMap (hsrc : e.source = halfCollarSource)
    (hΦs : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => Φ p.1 p.2)) {b : ℝ}
    (hb : b < 1) :
    ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞
      (fun q : Torus × ℝ => Φ q.2 (e (q.1, Manifold.halfSpaceOneLift b))) := by
  have hE : ContMDiff torusModel C.model ∞
      (fun p : Torus => e (p, Manifold.halfSpaceOneLift b)) := by
    intro p
    have h1 : ContMDiffAt halfCollarModel C.model ∞ e (p, Manifold.halfSpaceOneLift b) :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (lift_mem_source e hsrc p hb))
    exact h1.comp p (contMDiffAt_id.prodMk contMDiffAt_const)
  exact hΦs.comp (contMDiff_snd.prodMk (hE.comp contMDiff_fst))

end FlowLines

section FlowMap

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}
  (hsrc : e.source = halfCollarSource)
  (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
  (hΦs : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => Φ p.1 p.2))
  (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ t (Φ s x) = Φ (s + t) x)
  (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y) {a b : ℝ} (hb1 : b < 1)
  (hYray : ∀ p s, a < s → s < b →
    Y (e (p, Manifold.halfSpaceOneLift s)) =
      collarNormalField e (e (p, Manifold.halfSpaceOneLift s)))
  (hint : ∀ p s, a < s → s < b → C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)))
  (ha : 0 < a) (hab : 2 * a < b)

include hsrc hY hΦs hΦ0 hΦadd hΦY hb1 hYray hint ha hab in
theorem injective_mfderiv_portFlowMap (q : Torus × ℝ) :
    Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model
      (fun q : Torus × ℝ => Φ q.2 (e (q.1, Manifold.halfSpaceOneLift (2 * a)))) q) := by
  set G := fun q : Torus × ℝ => Φ q.2 (e (q.1, Manifold.halfSpaceOneLift (2 * a))) with hG
  have hGs : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ G :=
    contMDiff_portFlowMap e hsrc hΦs (by linarith)
  obtain ⟨p, t₀⟩ := q
  have hsrc' := lift_mem_source e hsrc p (by linarith : 2 * a + 0 < 1)
  have he := (e.mdifferentiableAt (by simp) hsrc').hasMFDerivAt
  have hheq : IsLocalDiffeomorphAt halfCollarModel C.model ∞ e
      (p, Manifold.halfSpaceOneLift (2 * a + 0)) := ⟨e, hsrc', fun y hy => rfl⟩
  have heinj : Function.Injective (mfderiv halfCollarModel C.model e
      (p, Manifold.halfSpaceOneLift (2 * a + 0))) :=
    (hheq.mfderivToContinuousLinearEquiv (by simp)).injective
  have h0 : HasFDerivAt (fun t' : ℝ => 2 * a + t') (ContinuousLinearMap.id ℝ ℝ) 0 :=
    (hasFDerivAt_id 0).const_add (2 * a)
  have hl := (hasMFDerivAt_halfSpaceOneLift (by linarith : 0 < 2 * a + 0)).comp 0
    (hasMFDerivAt_iff_hasFDerivAt.mpr h0)
  have hin := (hasMFDerivAt_fst (I := torusModel) (I' := 𝓘(ℝ, ℝ)) (p, (0 : ℝ))).prodMk
    (hl.comp (p, (0 : ℝ)) (hasMFDerivAt_snd (I := torusModel) (I' := 𝓘(ℝ, ℝ)) (p, (0 : ℝ))))
  have hR := he.comp (p, (0 : ℝ)) hin
  have hloc : G =ᶠ[𝓝 (p, (0 : ℝ))]
      fun q : Torus × ℝ => e (q.1, Manifold.halfSpaceOneLift (2 * a + q.2)) := by
    have hmem : Ioo (-a) (b - 2 * a) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hmem] with q hq
    exact portFlow_ray e hsrc hY hΦ0 hΦY hb1 hYray hint ha hab q.1 hq
  have hinj0 : Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model G (p, 0)) := by
    rw [(hR.congr_of_eventuallyEq_abuse hloc).mfderiv]
    intro v w hvw
    have h1 := heinj hvw
    have hf := congrArg Prod.fst h1
    have hs := congrArg Prod.snd h1
    simp only [Function.comp_apply] at hf hs
    refine Prod.ext hf ?_
    have hs' : (v.2 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) =
        (w.2 : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := hs
    have hs'' := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hs'
    simpa using hs''
  have hsub : HasFDerivAt (fun t : ℝ => t - t₀) (ContinuousLinearMap.id ℝ ℝ) t₀ :=
    (hasFDerivAt_id t₀).sub_const t₀
  have hsh := (hasMFDerivAt_fst (I := torusModel) (I' := 𝓘(ℝ, ℝ)) (p, t₀)).prodMk
    ((hasMFDerivAt_iff_hasFDerivAt.mpr hsub).comp (p, t₀)
      (hasMFDerivAt_snd (I := torusModel) (I' := 𝓘(ℝ, ℝ)) (p, t₀)))
  have hG0 : HasMFDerivAt (torusModel.prod 𝓘(ℝ, ℝ)) C.model G (p, t₀ - t₀)
      (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model G (p, 0)) := by
    rw [sub_self]
    exact (hGs.mdifferentiableAt (by simp)).hasMFDerivAt
  have hΦd : HasMFDerivAt C.model C.model (Φ t₀) (G (p, t₀ - t₀))
      (mfderiv C.model C.model (Φ t₀) (G (p, t₀ - t₀))) :=
    ((hΦs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := hΦd.comp (p, t₀) (hG0.comp (p, t₀) hsh)
  have hc' := hc.congr_of_eventuallyEq_abuse (f₁ := G) (Filter.Eventually.of_forall fun q => by
    change Φ q.2 _ = Φ t₀ (Φ (q.2 - t₀) _)
    rw [hΦadd, sub_add_cancel])
  rw [hc'.mfderiv]
  have hshinj : Function.Injective
      (((ContinuousLinearMap.fst ℝ (TangentSpace torusModel p) (TangentSpace 𝓘(ℝ, ℝ) t₀)).prod
        ((ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (TangentSpace torusModel p)
          (TangentSpace 𝓘(ℝ, ℝ) t₀)))) : _ → _) := by
    intro v w hvw
    have hf := congrArg Prod.fst hvw
    have hs := congrArg Prod.snd hvw
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst'] at hf hs
    exact Prod.ext hf hs
  exact (injective_mfderiv_flow hΦs hΦ0 hΦadd t₀ _).comp (hinj0.comp hshinj)

end FlowMap

section FlowMapInjective

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}
  (hsrc : e.source = halfCollarSource)
  (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
  (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ t (Φ s x) = Φ (s + t) x)
  (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y) {a b : ℝ} (hb1 : b < 1)
  (hYray : ∀ p s, a < s → s < b →
    Y (e (p, Manifold.halfSpaceOneLift s)) =
      collarNormalField e (e (p, Manifold.halfSpaceOneLift s)))
  (hint : ∀ p s, a < s → s < b → C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)))
  (ha : 0 < a) (hab : 2 * a < b) {F : CircleFibration C U} {D : BaseMorseData F.base}
  (hmono : ∀ x, Monotone fun t => portHeight F D (Φ t x)) {a₁ μ : ℝ} (ha₁ : 2 * a < a₁)
  (ha₁b : a₁ < b) (hμ₁ : ∀ p, μ ≤ portHeight F D (e (p, Manifold.halfSpaceOneLift a₁)))
  (hμ₂ : ∀ p, portHeight F D (e (p, Manifold.halfSpaceOneLift (2 * a))) < μ)

include hsrc hY hΦ0 hΦY hb1 hYray hint ha hab hmono ha₁ ha₁b hμ₁ hμ₂ in
theorem portFlowMap_return (p p' : Torus) {τ : ℝ} (hτ : 0 ≤ τ)
    (h : Φ τ (e (p, Manifold.halfSpaceOneLift (2 * a))) =
      e (p', Manifold.halfSpaceOneLift (2 * a))) : τ = 0 ∧ p = p' := by
  rcases lt_or_ge τ (a₁ - 2 * a) with hτ1 | hτ1
  · rw [portFlow_ray e hsrc hY hΦ0 hΦY hb1 hYray hint ha hab p (t := τ)
      ⟨by linarith, by linarith⟩] at h
    have h2 := e.toOpenPartialHomeomorph.injOn (lift_mem_source e hsrc p (by linarith))
      (lift_mem_source e hsrc p' (by linarith)) h
    have h3 : (Manifold.halfSpaceOneLift (2 * a + τ)).val 0 =
        (Manifold.halfSpaceOneLift (2 * a)).val 0 :=
      congrArg (fun q : Torus × EuclideanHalfSpace 1 => q.2.val 0) h2
    change max (2 * a + τ) 0 = max (2 * a) 0 at h3
    rw [max_eq_left (by linarith), max_eq_left (by linarith)] at h3
    exact ⟨by linarith, congrArg Prod.fst h2⟩
  · exfalso
    have h1 := hmono (e (p, Manifold.halfSpaceOneLift (2 * a))) hτ1
    simp only at h1
    rw [portFlow_ray e hsrc hY hΦ0 hΦY hb1 hYray hint ha hab p (t := a₁ - 2 * a)
      ⟨by linarith, by linarith⟩, h, show 2 * a + (a₁ - 2 * a) = a₁ by ring] at h1
    linarith [hμ₁ p, hμ₂ p']

include hsrc hY hΦ0 hΦadd hΦY hb1 hYray hint ha hab hmono ha₁ ha₁b hμ₁ hμ₂ in
theorem injective_portFlowMap :
    Function.Injective
      (fun q : Torus × ℝ => Φ q.2 (e (q.1, Manifold.halfSpaceOneLift (2 * a)))) := by
  have key : ∀ {p p' : Torus} {t t' : ℝ}, t' ≤ t →
      Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))) =
        Φ t' (e (p', Manifold.halfSpaceOneLift (2 * a))) → t = t' ∧ p = p' := by
    intro p p' t t' htt h
    have h2 := congrArg (Φ (-t')) h
    rw [hΦadd, hΦadd, add_neg_cancel, hΦ0, ← sub_eq_add_neg] at h2
    obtain ⟨h3, h4⟩ := portFlowMap_return e hsrc hY hΦ0 hΦY hb1 hYray hint ha hab hmono ha₁ ha₁b
      hμ₁ hμ₂ p p' (sub_nonneg.mpr htt) h2
    exact ⟨by linarith, h4⟩
  rintro ⟨p, t⟩ ⟨p', t'⟩ h
  change Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))) =
    Φ t' (e (p', Manifold.halfSpaceOneLift (2 * a))) at h
  rcases le_total t' t with htt | htt
  · obtain ⟨h1, h2⟩ := key htt h
    rw [h1, h2]
  · obtain ⟨h1, h2⟩ := key htt h.symm
    rw [h1, h2]

end FlowMapInjective

section ArrivalAnalysis

variable {h h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t) (hmono : Monotone h)

include hd hmono in
theorem arrival_char {ℓ κ b T : ℝ} (hκ : 0 < κ) (hb : 0 < b)
    (hband : ∀ t, h t ∈ Ioo (ℓ - κ * b) (ℓ + κ * b) → h' t = κ) (hT : h T = ℓ) :
    (∀ t, |t - T| < b → h t = ℓ + κ * (t - T)) ∧ (∀ t, h t ≤ ℓ ↔ t ≤ T) ∧
      (∀ t, h t < ℓ ↔ t < T) := by
  have hTb : h T ∈ Ioo (ℓ - κ * b) (ℓ + κ * b) := by
    rw [hT]
    constructor <;> nlinarith
  have hloc : ∀ t, |t - T| < b → h t = ℓ + κ * (t - T) := by
    intro t ht
    have h1 := affine_of_rate_in_band hd hband (t₀ := T) (t₁ := t) hTb (by
      rw [hT]
      obtain ⟨h2, h3⟩ := abs_lt.mp ht
      constructor <;> nlinarith)
    rw [h1, hT]
  have habove : ∀ t, T < t → ℓ < h t := by
    intro t ht
    rcases lt_or_ge t (T + b) with h1 | h1
    · rw [hloc t (by rw [abs_lt]; constructor <;> linarith)]
      nlinarith
    · have h2 := hmono (show T + b / 2 ≤ t by linarith)
      rw [hloc (T + b / 2) (by rw [abs_lt]; constructor <;> linarith)] at h2
      nlinarith
  have hbelow : ∀ t, t < T → h t < ℓ := by
    intro t ht
    rcases lt_or_ge (T - b) t with h1 | h1
    · rw [hloc t (by rw [abs_lt]; constructor <;> linarith)]
      nlinarith
    · have h2 := hmono (show t ≤ T - b / 2 by linarith)
      rw [hloc (T - b / 2) (by rw [abs_lt]; constructor <;> linarith)] at h2
      nlinarith
  refine ⟨hloc, fun t => ⟨fun h1 => ?_, fun h1 => ?_⟩, fun t => ⟨fun h1 => ?_, hbelow t⟩⟩
  · by_contra h2
    linarith [habove t (not_le.mp h2)]
  · rcases eq_or_lt_of_le h1 with h2 | h2
    · rw [h2, hT]
    · exact (hbelow t h2).le
  · by_contra h2
    rcases eq_or_lt_of_le (not_lt.mp h2) with h3 | h3
    · rw [← h3, hT] at h1
      exact lt_irrefl _ h1
    · linarith [habove t h3]

include hd hmono in
theorem exists_arrival {ℓ μ ε t₁ : ℝ} (hε : 0 < ε) (hμℓ : μ ≤ ℓ) (h1 : μ ≤ h t₁)
    (hrate : ∀ t, h t ∈ Icc μ ℓ → ε ≤ h' t) (h0 : h 0 ≤ ℓ) (ht₁ : 0 ≤ t₁) :
    ∃ T, 0 ≤ T ∧ h T = ℓ := by
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  set t₂ := t₁ + (ℓ - μ) / ε with ht₂
  have h12 : t₁ ≤ t₂ := by
    have : 0 ≤ (ℓ - μ) / ε := div_nonneg (by linarith) hε.le
    linarith
  have hreach : ℓ ≤ h t₂ := by
    by_contra hlt
    push Not at hlt
    have hmem : ∀ t ∈ Icc t₁ t₂, h t ∈ Icc μ ℓ := fun t ht =>
      ⟨h1.trans (hmono ht.1), ((hmono ht.2).trans hlt.le)⟩
    have hmvt := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc t₁ t₂)
      hcont.continuousOn (fun t ht => (hd t).differentiableAt.differentiableWithinAt)
      (C := ε) (fun t ht => by
        rw [(hd t).deriv]
        exact hrate t (hmem t (interior_subset ht))) t₁ ⟨le_rfl, h12⟩ t₂ ⟨h12, le_rfl⟩ h12
    have hε' : ε * (t₂ - t₁) = ℓ - μ := by
      rw [ht₂]
      field_simp
      ring
    linarith
  obtain ⟨T, hT, hTv⟩ := intermediate_value_Icc (ht₁.trans h12) hcont.continuousOn ⟨h0, hreach⟩
  exact ⟨T, hT.1, hTv⟩

include hd hmono in
theorem le_arrival {α β ν T : ℝ} (hν : 0 < ν) (hαβ : α ≤ β) (h0 : h 0 ≤ α) (hT : β ≤ h T)
    (hT0 : 0 ≤ T) (hslow : ∀ t, h t ∈ Icc α β → h' t ≤ ν) : (β - α) / ν ≤ T := by
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  obtain ⟨ta, hta, htav⟩ := intermediate_value_Icc hT0 hcont.continuousOn
    ⟨h0, hαβ.trans hT⟩
  obtain ⟨tb, htb, htbv⟩ := intermediate_value_Icc hta.2 hcont.continuousOn
    ⟨htav.symm ▸ hαβ, hT⟩
  have hmvt := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc ta tb)
    hcont.continuousOn (fun t ht => (hd t).differentiableAt.differentiableWithinAt)
    (C := ν) (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      refine hslow t ⟨?_, ?_⟩
      · rw [← htav]
        exact hmono ht.1.le
      · rw [← htbv]
        exact hmono ht.2.le) ta ⟨le_rfl, htb.1⟩ tb ⟨htb.1, le_rfl⟩ htb.1
  rw [htav, htbv] at hmvt
  rw [div_le_iff₀ hν]
  nlinarith [hta.1, htb.2]

end ArrivalAnalysis

section ArrivalSmooth

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem contMDiff_arrival {G : Torus × ℝ → U}
    (hG : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ G) {g : U → ℝ}
    (hg : ContMDiff C.model 𝓘(ℝ, ℝ) ∞ g) {h' : Torus → ℝ → ℝ}
    (hd : ∀ p t, HasDerivAt (fun t => g (G (p, t))) (h' p t) t) {ℓ κ b : ℝ} (hκ : 0 < κ)
    (hb : 0 < b) (hband : ∀ p t, g (G (p, t)) ∈ Ioo (ℓ - κ * b) (ℓ + κ * b) → h' p t = κ)
    {T : Torus → ℝ} (hchar : ∀ p t, g (G (p, t)) ≤ ℓ ↔ t ≤ T p)
    (hchar' : ∀ p t, g (G (p, t)) < ℓ ↔ t < T p) (hT : ∀ p, g (G (p, T p)) = ℓ) :
    ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ T := by
  intro p₀
  have hslice : ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ (fun p => g (G (p, T p₀))) :=
    hg.comp (hG.comp (contMDiff_id.prodMk contMDiff_const))
  have hφ : ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ (fun p => T p₀ + (ℓ - g (G (p, T p₀))) / κ) :=
    contMDiff_const.add ((contMDiff_const.sub hslice).div_const κ)
  refine (hφ p₀).congr_of_eventuallyEq ?_
  have hκb : 0 < κ * b := mul_pos hκ hb
  have hmem : Ioo (ℓ - κ * b) (ℓ + κ * b) ∈ 𝓝 (g (G (p₀, T p₀))) := by
    rw [hT p₀]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hslice.continuous.continuousAt.preimage_mem_nhds hmem] with p hp
  have h1 := affine_of_rate_in_band (hd p) (hband p) (t₀ := T p₀)
    (t₁ := T p₀ + (ℓ - g (G (p, T p₀))) / κ) hp (by
      have h2 : g (G (p, T p₀)) + κ * (T p₀ + (ℓ - g (G (p, T p₀))) / κ - T p₀) = ℓ := by
        field_simp
        ring
      rw [h2]
      exact ⟨by linarith, by linarith⟩)
  have h2 : g (G (p, T p₀ + (ℓ - g (G (p, T p₀))) / κ)) = ℓ := by
    rw [h1]
    field_simp
    ring
  have h3 := (hchar p _).mp h2.le
  have h4 : ¬ (T p₀ + (ℓ - g (G (p, T p₀))) / κ < T p) := fun h5 => by
    have h6 := (hchar' p _).mpr h5
    rw [h2] at h6
    exact lt_irrefl ℓ h6
  exact (le_antisymm h3 (not_lt.mp h4)).symm

end ArrivalSmooth

section Reparametrisation

def stretchProfile (s₀ s₁ s : ℝ) : ℝ := Real.smoothTransition ((s - s₀) / (s₁ - s₀))

theorem contDiff_stretchProfile (s₀ s₁ : ℝ) : ContDiff ℝ ∞ (stretchProfile s₀ s₁) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem monotone_stretchProfile {s₀ s₁ : ℝ} (h : s₀ < s₁) : Monotone (stretchProfile s₀ s₁) :=
  fun x y hxy => Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem stretchProfile_eq_zero {s₀ s₁ s : ℝ} (h : s₀ < s₁) (hs : s ≤ s₀) :
    stretchProfile s₀ s₁ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem stretchProfile_eq_one {s₀ s₁ s : ℝ} (h : s₀ < s₁) (hs : s₁ ≤ s) :
    stretchProfile s₀ s₁ s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

def portTime (a ℓ s₀ s₁ : ℝ) (T : Torus → ℝ) (q : Torus × ℝ) : ℝ :=
  q.2 - 2 * a + (T q.1 - ℓ + 2 * a) * stretchProfile s₀ s₁ q.2

theorem contMDiff_portTime (a ℓ s₀ s₁ : ℝ) {T : Torus → ℝ}
    (hT : ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ T) :
    ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (portTime a ℓ s₀ s₁ T) := by
  have h2 : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : Torus × ℝ => q.2) :=
    contMDiff_snd
  exact (h2.sub contMDiff_const).add (((hT.comp contMDiff_fst).sub contMDiff_const).add
    contMDiff_const |>.mul ((contDiff_stretchProfile s₀ s₁).contMDiff.comp h2))

theorem portTime_of_le {a ℓ s₀ s₁ : ℝ} (h : s₀ < s₁) (T : Torus → ℝ) (p : Torus) {s : ℝ}
    (hs : s ≤ s₀) : portTime a ℓ s₀ s₁ T (p, s) = s - 2 * a := by
  unfold portTime
  rw [stretchProfile_eq_zero h hs, mul_zero, add_zero]

theorem portTime_of_ge {a ℓ s₀ s₁ : ℝ} (h : s₀ < s₁) (T : Torus → ℝ) (p : Torus) {s : ℝ}
    (hs : s₁ ≤ s) : portTime a ℓ s₀ s₁ T (p, s) = s - ℓ + T p := by
  unfold portTime
  rw [stretchProfile_eq_one h hs]
  ring

theorem hasDerivAt_portTime (a ℓ s₀ s₁ : ℝ) (T : Torus → ℝ) (p : Torus) (s : ℝ) :
    HasDerivAt (fun s => portTime a ℓ s₀ s₁ T (p, s))
      (1 + (T p - ℓ + 2 * a) * deriv (stretchProfile s₀ s₁) s) s := by
  have h1 : HasDerivAt (stretchProfile s₀ s₁) (deriv (stretchProfile s₀ s₁) s) s :=
    ((contDiff_stretchProfile s₀ s₁).differentiable (by simp) s).hasDerivAt
  have h2 := ((hasDerivAt_id s).sub_const (2 * a)).add (h1.const_mul (T p - ℓ + 2 * a))
  exact h2

theorem one_le_deriv_portTime {a ℓ s₀ s₁ : ℝ} (h : s₀ < s₁) {T : Torus → ℝ} {p : Torus}
    (hT : ℓ - 2 * a ≤ T p) (s : ℝ) :
    1 ≤ 1 + (T p - ℓ + 2 * a) * deriv (stretchProfile s₀ s₁) s := by
  have h1 := (monotone_stretchProfile h).deriv_nonneg (x := s)
  nlinarith

theorem strictMono_portTime {a ℓ s₀ s₁ : ℝ} (h : s₀ < s₁) {T : Torus → ℝ} {p : Torus}
    (hT : ℓ - 2 * a ≤ T p) : StrictMono (fun s => portTime a ℓ s₀ s₁ T (p, s)) := by
  intro x y hxy
  have h1 := monotone_stretchProfile h hxy.le
  change x - 2 * a + (T p - ℓ + 2 * a) * stretchProfile s₀ s₁ x <
    y - 2 * a + (T p - ℓ + 2 * a) * stretchProfile s₀ s₁ y
  nlinarith

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem injective_mfderiv_reparam {G : Torus × ℝ → U}
    (hG : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ G)
    (hGinj : ∀ q, Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model G q))
    {τ : Torus × ℝ → ℝ} (hτ : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ τ)
    (hτs : ∀ p s, ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (fun s => τ (p, s)) d s) (q : Torus × ℝ) :
    Function.Injective
      (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model (fun q => G (q.1, τ q)) q) := by
  obtain ⟨p, s⟩ := q
  set Dτ := mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) τ (p, s) with hDτ
  have hτd : HasMFDerivAt (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) τ (p, s) Dτ :=
    (hτ.mdifferentiableAt (by simp)).hasMFDerivAt
  have hΘ := (hasMFDerivAt_fst (I := torusModel) (I' := 𝓘(ℝ, ℝ)) (p, s)).prodMk hτd
  have hGd : HasMFDerivAt (torusModel.prod 𝓘(ℝ, ℝ)) C.model G (p, τ (p, s))
      (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model G (p, τ (p, s))) :=
    (hG.mdifferentiableAt (by simp)).hasMFDerivAt
  have hA := (hGd.comp (p, s) hΘ).congr_of_eventuallyEq_abuse
    (f₁ := fun q => G (q.1, τ q)) (Filter.Eventually.of_forall fun q => rfl)
  rw [hA.mfderiv]
  refine (hGinj _).comp ?_
  obtain ⟨d, hd0, hd⟩ := hτs p s
  have hslice := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := torusModel) p s).prodMk
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) s)
  have hc := hτd.comp s hslice
  let Dl : ℝ →L[ℝ] ℝ := Dτ.comp ((0 : ℝ →L[ℝ] TangentSpace torusModel p).prod
    (ContinuousLinearMap.id ℝ ℝ))
  have hc' : HasFDerivAt (fun s' => τ (p, s')) Dl s := hasMFDerivAt_iff_hasFDerivAt.mp hc
  have hd' : Dl 1 = d := hc'.hasDerivAt.unique hd
  intro v w hvw
  have h1 := congrArg Prod.fst hvw
  have h2 := congrArg Prod.snd hvw
  change v.1 = w.1 at h1
  change Dτ v = Dτ w at h2
  have h3 : v - w = ((0 : TangentSpace torusModel p), v.2 - w.2) := by
    refine Prod.ext ?_ rfl
    change v.1 - w.1 = 0
    rw [h1, sub_self]
  have h4 : Dτ (v - w) = 0 := by rw [map_sub, h2, sub_self]
  rw [h3] at h4
  have h5 : Dl (v.2 - w.2) = 0 := h4
  have h6 : Dl (v.2 - w.2) = (v.2 - w.2) * d := by
    rw [← hd']
    have h7 := Dl.map_smul (v.2 - w.2) 1
    simpa using h7
  rw [h6] at h5
  have h8 : v.2 = w.2 := by
    rcases mul_eq_zero.mp h5 with h9 | h9
    · linarith
    · exact absurd h9 hd0
  exact Prod.ext h1 h8

end Reparametrisation

section PieceMap

variable {ℓ : ℝ} [Fact (0 < ℓ)]

theorem injective_mfderiv_subtypeVal_Icc (z : Icc (0 : ℝ) ℓ) :
    Function.Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) ℓ → ℝ) z) := by
  intro v w h
  apply (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc z).injective
  rw [DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply,
    DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply, h]

theorem contMDiff_liftIcc :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (fun s : Icc (0 : ℝ) ℓ => Manifold.halfSpaceOneLift s.1) :=
  Manifold.contMDiffOn_halfSpaceOneLift.comp_contMDiff contMDiff_subtypeVal_Icc fun s => s.2.1

theorem injective_mfderiv_liftIcc (z : Icc (0 : ℝ) ℓ) :
    Function.Injective
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) (fun s : Icc (0 : ℝ) ℓ => Manifold.halfSpaceOneLift s.1) z) := by
  have hc := mfderiv_comp z
    (Manifold.contMDiff_halfSpaceOneCoordinate.mdifferentiableAt (by simp))
    ((contMDiff_liftIcc (ℓ := ℓ)).mdifferentiableAt (x := z) (by simp))
  have heq : (fun t : EuclideanHalfSpace 1 => t.1 0) ∘
      (fun s : Icc (0 : ℝ) ℓ => Manifold.halfSpaceOneLift s.1) = Subtype.val := by
    funext s
    change max s.1 0 = s.1
    exact max_eq_left s.2.1
  rw [heq] at hc
  intro v w h
  apply injective_mfderiv_subtypeVal_Icc z
  rw [hc]
  exact congrArg (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun t : EuclideanHalfSpace 1 => t.1 0)
    (Manifold.halfSpaceOneLift z.1)) h

theorem contMDiff_collarIcc :
    ContMDiff (torusModel.prod (𝓡∂ 1)) halfCollarModel ∞
      (fun q : Torus × Icc (0 : ℝ) ℓ => (q.1, Manifold.halfSpaceOneLift q.2.1)) :=
  contMDiff_fst.prodMk ((contMDiff_liftIcc (ℓ := ℓ)).comp contMDiff_snd)

theorem contMDiff_valIcc :
    ContMDiff (torusModel.prod (𝓡∂ 1)) (torusModel.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : Torus × Icc (0 : ℝ) ℓ => (q.1, q.2.1)) :=
  contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd)

theorem bijective_of_injective_tangent {C : CompactCarrier.{u}} {q : Torus × Icc (0 : ℝ) ℓ}
    {x : C.Carrier}
    (L : TangentSpace (torusModel.prod (𝓡∂ 1)) q →L[ℝ] TangentSpace C.model x)
    (hL : Function.Injective L) : Function.Bijective L := by
  let _ : FiniteDimensional ℝ (TangentSpace (torusModel.prod (𝓡∂ 1)) q) :=
    inferInstanceAs (FiniteDimensional ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)))
  let _ : FiniteDimensional ℝ (TangentSpace C.model x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  have hd : Module.finrank ℝ (TangentSpace (torusModel.prod (𝓡∂ 1)) q) =
      Module.finrank ℝ (TangentSpace C.model x) := by
    change Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp [Module.finrank_prod]
  exact ⟨hL, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hL⟩

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (A : Torus × ℝ → U) (a₁ : ℝ)

open Classical in
def portPieceMap (q : Torus × Icc (0 : ℝ) ℓ) : U :=
  if q.2.1 < a₁ then e (q.1, Manifold.halfSpaceOneLift q.2.1) else A (q.1, q.2.1)

omit [Fact (0 < ℓ)] in
theorem portPieceMap_of_lt {q : Torus × Icc (0 : ℝ) ℓ} (hq : q.2.1 < a₁) :
    portPieceMap e A a₁ q = e (q.1, Manifold.halfSpaceOneLift q.2.1) := by
  unfold portPieceMap
  rw [ite_eq_left hq]

omit [Fact (0 < ℓ)] in
theorem portPieceMap_of_gt {a : ℝ}
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s))
    {q : Torus × Icc (0 : ℝ) ℓ} (hq : a < q.2.1) :
    portPieceMap e A a₁ q = A (q.1, q.2.1) := by
  unfold portPieceMap
  split_ifs with h
  · exact (hagree q.1 q.2.1 hq h).symm
  · rfl

omit [Fact (0 < ℓ)] in
theorem eventuallyEq_portPieceMap_low (q : Torus × Icc (0 : ℝ) ℓ) (hq : q.2.1 < a₁) :
    portPieceMap e A a₁ =ᶠ[𝓝 q] fun q => e (q.1, Manifold.halfSpaceOneLift q.2.1) := by
  have hO : IsOpen {q : Torus × Icc (0 : ℝ) ℓ | q.2.1 < a₁} :=
    isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd)
  filter_upwards [hO.mem_nhds hq] with q' hq'
  exact portPieceMap_of_lt e A a₁ hq'

omit [Fact (0 < ℓ)] in
theorem eventuallyEq_portPieceMap_high {a : ℝ}
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s))
    (q : Torus × Icc (0 : ℝ) ℓ) (hq : a < q.2.1) :
    portPieceMap e A a₁ =ᶠ[𝓝 q] fun q => A (q.1, q.2.1) := by
  have hO : IsOpen {q : Torus × Icc (0 : ℝ) ℓ | a < q.2.1} :=
    isOpen_Ioi.preimage (continuous_subtype_val.comp continuous_snd)
  filter_upwards [hO.mem_nhds hq] with q' hq'
  exact portPieceMap_of_gt e A a₁ hagree hq'

theorem contMDiff_portPieceMap (hsrc : e.source = halfCollarSource) {a : ℝ} (haa₁ : a < a₁)
    (ha₁ : a₁ < 1) (hA : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ A)
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s)) :
    ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (portPieceMap (ℓ := ℓ) e A a₁) := by
  intro q
  by_cases hq : q.2.1 < a₁
  · refine ContMDiffAt.congr_of_eventuallyEq ?_ (eventuallyEq_portPieceMap_low e A a₁ q hq)
    have he : ContMDiffAt halfCollarModel C.model ∞ e (q.1, Manifold.halfSpaceOneLift q.2.1) :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (lift_mem_source e hsrc q.1 (hq.trans ha₁)))
    exact he.comp q ((contMDiff_collarIcc (ℓ := ℓ)) q)
  · refine ContMDiffAt.congr_of_eventuallyEq ?_
      (eventuallyEq_portPieceMap_high e A a₁ hagree q (by linarith [not_lt.mp hq]))
    exact (hA.comp (contMDiff_valIcc (ℓ := ℓ))) q

theorem injective_mfderiv_portPieceMap (hsrc : e.source = halfCollarSource) {a : ℝ}
    (haa₁ : a < a₁) (ha₁ : a₁ < 1) (hA : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ A)
    (hAinj : ∀ q, Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model A q))
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s))
    (q : Torus × Icc (0 : ℝ) ℓ) :
    Function.Injective (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (portPieceMap e A a₁) q) := by
  by_cases hq : q.2.1 < a₁
  · have hsrc' := lift_mem_source e hsrc q.1 (hq.trans ha₁)
    have he := (e.mdifferentiableAt (by simp) hsrc').hasMFDerivAt
    have hloc : IsLocalDiffeomorphAt halfCollarModel C.model ∞ e
        (q.1, Manifold.halfSpaceOneLift q.2.1) := ⟨e, hsrc', fun y hy => rfl⟩
    have heinj : Function.Injective (mfderiv halfCollarModel C.model e
        (q.1, Manifold.halfSpaceOneLift q.2.1)) :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
    have hι := ((contMDiff_liftIcc (ℓ := ℓ)).mdifferentiableAt (x := q.2) (by simp)).hasMFDerivAt
    have hin := (hasMFDerivAt_fst (I := torusModel) (I' := 𝓡∂ 1) q).prodMk
      (hι.comp q (hasMFDerivAt_snd (I := torusModel) (I' := 𝓡∂ 1) q))
    have hK := (he.comp q hin).congr_of_eventuallyEq_abuse
      (eventuallyEq_portPieceMap_low e A a₁ q hq)
    rw [hK.mfderiv]
    refine heinj.comp ?_
    intro v w hvw
    have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    change v.1 = w.1 at h1
    change mfderiv (𝓡∂ 1) (𝓡∂ 1) (fun s : Icc (0 : ℝ) ℓ => Manifold.halfSpaceOneLift s.1) q.2
      v.2 = mfderiv (𝓡∂ 1) (𝓡∂ 1) (fun s : Icc (0 : ℝ) ℓ => Manifold.halfSpaceOneLift s.1) q.2
      w.2 at h2
    exact Prod.ext h1 (injective_mfderiv_liftIcc q.2 h2)
  · have hq' : a < q.2.1 := by linarith [not_lt.mp hq]
    have hAd := (hA.mdifferentiableAt (x := (q.1, q.2.1)) (by simp)).hasMFDerivAt
    have hv := ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ℓ) (n := ∞)).mdifferentiableAt
      (x := q.2) (by simp)).hasMFDerivAt
    have hin := (hasMFDerivAt_fst (I := torusModel) (I' := 𝓡∂ 1) q).prodMk
      (hv.comp q (hasMFDerivAt_snd (I := torusModel) (I' := 𝓡∂ 1) q))
    have hK := (hAd.comp q hin).congr_of_eventuallyEq_abuse
      (eventuallyEq_portPieceMap_high e A a₁ hagree q hq')
    rw [hK.mfderiv]
    refine (hAinj _).comp ?_
    intro v w hvw
    have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    change v.1 = w.1 at h1
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) ℓ → ℝ) q.2 v.2 =
      mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) ℓ → ℝ) q.2 w.2 at h2
    exact Prod.ext h1 (injective_mfderiv_subtypeVal_Icc q.2 h2)

end PieceMap

section PieceInjective

variable {ℓ : ℝ} {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (A : Torus × ℝ → U) (a₁ : ℝ)

theorem injective_portPieceMap (hsrc : e.source = halfCollarSource) {a : ℝ} (haa₁ : a < a₁)
    (ha₁ : a₁ < 1)
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s))
    (hAinj : ∀ p p' s s', a < s → a < s' → A (p, s) = A (p', s') → p = p' ∧ s = s')
    {g : U → ℝ} {μ : ℝ}
    (hlow : ∀ p s, 0 ≤ s → s ≤ a → g (e (p, Manifold.halfSpaceOneLift s)) < μ)
    (hhigh : ∀ p s, a₁ ≤ s → μ ≤ g (A (p, s))) :
    Function.Injective (portPieceMap (ℓ := ℓ) e A a₁) := by
  have hlowK : ∀ q : Torus × Icc (0 : ℝ) ℓ, q.2.1 ≤ a → g (portPieceMap e A a₁ q) < μ :=
    fun q hq => by
      rw [portPieceMap_of_lt e A a₁ (lt_of_le_of_lt hq haa₁)]
      exact hlow q.1 q.2.1 q.2.2.1 hq
  have hhighK : ∀ q : Torus × Icc (0 : ℝ) ℓ, a₁ ≤ q.2.1 → μ ≤ g (portPieceMap e A a₁ q) :=
    fun q hq => by
      rw [portPieceMap_of_gt e A a₁ hagree (lt_of_lt_of_le haa₁ hq)]
      exact hhigh q.1 q.2.1 hq
  have hboth : ∀ q q' : Torus × Icc (0 : ℝ) ℓ, a < q.2.1 → a < q'.2.1 →
      portPieceMap e A a₁ q = portPieceMap e A a₁ q' → q = q' := by
    intro q q' hq hq' h
    rw [portPieceMap_of_gt e A a₁ hagree hq, portPieceMap_of_gt e A a₁ hagree hq'] at h
    obtain ⟨h1, h2⟩ := hAinj _ _ _ _ hq hq' h
    exact Prod.ext h1 (Subtype.ext h2)
  intro q q' h
  rcases lt_or_ge q.2.1 a₁ with hq | hq <;> rcases lt_or_ge q'.2.1 a₁ with hq' | hq'
  · rw [portPieceMap_of_lt e A a₁ hq, portPieceMap_of_lt e A a₁ hq'] at h
    have h2 := e.toOpenPartialHomeomorph.injOn (lift_mem_source e hsrc q.1 (hq.trans ha₁))
      (lift_mem_source e hsrc q'.1 (hq'.trans ha₁)) h
    have h3 : (Manifold.halfSpaceOneLift q.2.1).val 0 =
        (Manifold.halfSpaceOneLift q'.2.1).val 0 :=
      congrArg (fun r : Torus × EuclideanHalfSpace 1 => r.2.val 0) h2
    change max q.2.1 0 = max q'.2.1 0 at h3
    rw [max_eq_left q.2.2.1, max_eq_left q'.2.2.1] at h3
    have h4 : q.1 = q'.1 :=
      congrArg (fun r : Torus × EuclideanHalfSpace 1 => r.1) h2
    exact Prod.ext h4 (Subtype.ext h3)
  · rcases lt_or_ge a q.2.1 with ha | ha
    · exact hboth q q' ha (by linarith) h
    · have h1 := hlowK q ha
      rw [h] at h1
      linarith [hhighK q' hq']
  · rcases lt_or_ge a q'.2.1 with ha | ha
    · exact hboth q q' (by linarith) ha h
    · have h1 := hlowK q' ha
      rw [← h] at h1
      linarith [hhighK q hq]
  · exact hboth q q' (by linarith) (by linarith) h

end PieceInjective

section PieceRange

theorem range_eq_connectedComponentIn {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [ConnectedSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f)
    {S : Set Y} {y₀ : Y} (hy₀ : y₀ ∈ range f) (hS : range f ⊆ S)
    (hopen : ∀ x, ∃ O, IsOpen O ∧ f x ∈ O ∧ O ∩ S ⊆ range f) :
    range f = connectedComponentIn S y₀ := by
  refine subset_antisymm ((isConnected_range hf).isPreconnected.subset_connectedComponentIn hy₀ hS)
    ?_
  choose O hO hxO hOS using hopen
  set W := ⋃ x, O x with hW
  have hWo : IsOpen W := isOpen_iUnion hO
  have hcl : IsClosed (range f) := (isCompact_range hf).isClosed
  have hR := (isPreconnected_connectedComponentIn (F := S) (x := y₀))
  rcases isPreconnected_iff_subset_of_disjoint.mp hR W (range f)ᶜ hWo hcl.isOpen_compl
    (fun y hy => by
      by_cases hy : y ∈ range f
      · obtain ⟨x, rfl⟩ := hy
        exact Or.inl (mem_iUnion.mpr ⟨x, hxO x⟩)
      · exact Or.inr hy)
    (by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hyR hyW hyc
      obtain ⟨x, hx⟩ := mem_iUnion.mp hyW
      exact hyc (hOS x ⟨hx, connectedComponentIn_subset S y₀ hyR⟩)) with h | h
  · intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp (h hy)
    exact hOS x ⟨hx, connectedComponentIn_subset S y₀ hy⟩
  · exact absurd hy₀ (h (mem_connectedComponentIn (hS hy₀)))

end PieceRange

section PieceOpen

variable {ℓ : ℝ} {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  (A : Torus × ℝ → U) (a₁ : ℝ)

theorem exists_open_portPieceMap_low (hsrc : e.source = halfCollarSource) (ha₁ : a₁ < 1)
    (ha₁ℓ : a₁ ≤ ℓ) (q : Torus × Icc (0 : ℝ) ℓ) (hq : q.2.1 < a₁) :
    ∃ O : Set C.Carrier, IsOpen O ∧ (portPieceMap e A a₁ q).val ∈ O ∧
      O ⊆ range fun q => (portPieceMap (ℓ := ℓ) e A a₁ q).val := by
  set W : Set (Torus × EuclideanHalfSpace 1) := {r | r.2.val 0 < a₁} with hW
  have hWo : IsOpen W := isOpen_Iio.preimage
    (Manifold.contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd)
  have hWs : W ⊆ e.source := by
    intro r hr
    rw [hsrc]
    exact lt_trans hr ha₁
  refine ⟨Subtype.val '' (e '' W), U.isOpen.isOpenMap_subtype_val _
    (e.toOpenPartialHomeomorph.isOpen_image_of_subset_source hWo hWs), ?_, ?_⟩
  · rw [portPieceMap_of_lt e A a₁ hq]
    refine ⟨_, ⟨(q.1, Manifold.halfSpaceOneLift q.2.1), ?_, rfl⟩, rfl⟩
    change max q.2.1 0 < a₁
    rw [max_eq_left q.2.2.1]
    exact hq
  · rintro y ⟨z, ⟨r, hr, rfl⟩, rfl⟩
    have hr0 : 0 ≤ r.2.val 0 := r.2.2
    refine ⟨(r.1, ⟨r.2.val 0, hr0, (le_of_lt hr).trans ha₁ℓ⟩), ?_⟩
    change (portPieceMap e A a₁ (r.1, ⟨r.2.val 0, hr0, (le_of_lt hr).trans ha₁ℓ⟩)).val = (e r).val
    rw [portPieceMap_of_lt e A a₁ (q := (r.1, ⟨r.2.val 0, hr0, (le_of_lt hr).trans ha₁ℓ⟩)) hr]
    have h1 : (r.1, Manifold.halfSpaceOneLift (r.2.val 0)) = r := by
      refine Prod.ext rfl ?_
      rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift _ hr0]
      exact GC.GraphManifold.halfPoint_coord_eq _
    rw [h1]

theorem finrank_torusLine :
    Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  simp [Module.finrank_prod]

theorem exists_open_portPieceMap_high {a : ℝ} (ha : 0 < a)
    (hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s))
    (hA : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ A)
    (hAinj : ∀ q, Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model A q))
    (hAint : ∀ p s, a < s → C.model.IsInteriorPoint (A (p, s))) {g : U → ℝ}
    (hAabove : ∀ p s, a < s → ℓ < s → ℓ < g (A (p, s)))
    (q : Torus × Icc (0 : ℝ) ℓ) (hq : a < q.2.1) :
    ∃ O : Set C.Carrier, IsOpen O ∧ (portPieceMap e A a₁ q).val ∈ O ∧
      O ∩ {y | ∃ h : y ∈ U, g ⟨y, h⟩ ≤ ℓ} ⊆
        range fun q => (portPieceMap (ℓ := ℓ) e A a₁ q).val := by
  set N : Set (Torus × ℝ) := univ ×ˢ Ioi a with hN
  have hNo : IsOpen N := isOpen_univ.prod isOpen_Ioi
  have hqN : (q.1, q.2.1) ∈ N := ⟨mem_univ _, hq⟩
  have h1 : A '' N ∈ 𝓝 (A (q.1, q.2.1)) :=
    image_mem_nhds_of_mfderiv_injective hA BoundarylessManifold.isInteriorPoint
      (hAint q.1 q.2.1 hq) (hAinj _) finrank_torusLine (hNo.mem_nhds hqN)
  have h2 : Subtype.val '' (A '' N) ∈ 𝓝 (A (q.1, q.2.1)).val :=
    U.isOpen.isOpenMap_subtype_val.image_mem_nhds h1
  refine ⟨interior (Subtype.val '' (A '' N)), isOpen_interior, ?_, ?_⟩
  · rw [portPieceMap_of_gt e A a₁ hagree hq]
    exact mem_interior_iff_mem_nhds.mpr h2
  · rintro y ⟨hyO, hy, hyg⟩
    obtain ⟨z, ⟨r, hr, rfl⟩, rfl⟩ := interior_subset hyO
    have hz : (⟨(A r).val, hy⟩ : U) = A r := rfl
    rw [hz] at hyg
    have hrℓ : r.2 ≤ ℓ := by
      by_contra h
      exact absurd hyg (not_le.mpr (hAabove r.1 r.2 hr.2 (not_le.mp h)))
    have hr0 : 0 ≤ r.2 := ha.le.trans (le_of_lt hr.2)
    refine ⟨(r.1, ⟨r.2, hr0, hrℓ⟩), ?_⟩
    change (portPieceMap e A a₁ (r.1, ⟨r.2, hr0, hrℓ⟩)).val = (A r).val
    rw [portPieceMap_of_gt e A a₁ hagree (show a < r.2 from hr.2)]

end PieceOpen

section TopIdentity

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  {F : CircleFibration C U} (D : BaseMorseData F.base)
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞} (L : LiftedBicollar F c)
  (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
  (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s)

include hc hcf in
theorem flow_eq_liftFlow {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}
    (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y) {w : ℝ}
    (hwL : w < L.width) (hκw : D.κ * w < D.level 0)
    (hYX : ∀ x θ s, F.projection x = c (θ, s) → |s| ≤ w / 2 →
      portHeight F D x ∈ Icc (D.level 0 - D.κ * w / 2) (D.level 0 + D.κ * w / 2) →
        Y x = liftGenerator L x)
    {y : U} {θ : Circle} (hy : F.projection y = c (θ, 0)) {t : ℝ} (ht : |t| < w / 2) :
    Φ t y = L.flow t y := by
  have hκ := D.κ_pos
  have hw : 0 < w := by
    have := abs_nonneg t
    linarith
  have hproj : ∀ t' ∈ Ioo (-(w / 2)) (w / 2), F.projection (L.flow t' y) = c (θ, t') := by
    intro t' ht'
    rw [L.projection_flow, hy, L.baseFlow_apply θ 0 t' (by rw [abs_zero]; exact L.width_pos)
      (by rw [zero_add, abs_lt]; constructor <;> linarith [ht'.1, ht'.2]), zero_add]
  have hlt1 : ∀ t' ∈ Ioo (-(w / 2)) (w / 2), -1 < t' ∧ t' < 1 := fun t' ht' =>
    L.lt_one_of_lt_width hc (by rw [abs_lt]; constructor <;> linarith [ht'.1, ht'.2])
  have hheight : ∀ t' ∈ Ioo (-(w / 2)) (w / 2),
      portHeight F D (L.flow t' y) = D.level 0 + D.κ * t' := by
    intro t' ht'
    unfold portHeight
    rw [hproj t' ht', hcf θ t' (hlt1 t' ht').1 (hlt1 t' ht').2]
  have hcurve : IsMIntegralCurveOn (fun t' => L.flow t' y) Y (Ioo (-(w / 2)) (w / 2)) := by
    intro t' ht'
    have h1 := isMIntegralCurve_liftFlow L y t'
    have h2 : Y (L.flow t' y) = liftGenerator L (L.flow t' y) := by
      refine hYX _ θ t' (hproj t' ht') (by rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2])
        ?_
      rw [hheight t' ht']
      constructor <;> nlinarith [ht'.1, ht'.2]
    rw [← h2] at h1
    exact h1.hasMFDerivWithinAt
  have hint : ∀ t' ∈ Ioo (-(w / 2)) (w / 2), C.model.IsInteriorPoint (L.flow t' y) := by
    intro t' ht'
    apply isInteriorPoint_of_portHeight_pos F D
    rw [hheight t' ht']
    nlinarith [ht'.1, ht'.2]
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := 0) ⟨by linarith, by linarith⟩
    hint (hY.of_le (by simp)) hcurve ((hΦY y).isMIntegralCurveOn _)
    (by simp only [L.flow_zero, hΦ0])
  exact (heq (abs_lt.mp ht)).symm

include hc hcf in
theorem forall_projection_eq_of_level {γ : Torus → U} (hγ : Continuous γ)
    (hγu : ∀ p, portHeight F D (γ p) = D.level 0) {p₀ : Torus} {θ₀ : Circle}
    (hp₀ : F.projection (γ p₀) = c (θ₀, 0)) (p : Torus) :
    ∃ θ, F.projection (γ p) = c (θ, 0) := by
  have hcomp : IsCompact (c '' (univ ×ˢ {(0 : ℝ)})) := by
    refine (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
      (c.toOpenPartialHomeomorph.continuousOn.mono ?_)
    rintro ⟨θ, s⟩ ⟨-, hs⟩
    have hs0 : s = 0 := hs
    change _ ∈ c.source
    rw [hc]
    change -1 < s ∧ s < 1
    rw [hs0]
    constructor <;> norm_num
  set O₁ : Set U := F.projection ⁻¹' c.target with hO₁
  set O₂ : Set U := (F.projection ⁻¹' (c '' (univ ×ˢ {(0 : ℝ)})))ᶜ with hO₂
  have hO₁o : IsOpen O₁ := c.open_target.preimage F.smooth.continuous
  have hO₂o : IsOpen O₂ := (hcomp.isClosed.preimage F.smooth.continuous).isOpen_compl
  have hsplit : ∀ q, γ q ∈ O₁ → ∃ θ, F.projection (γ q) = c (θ, 0) := by
    intro q hq
    set z' := c.symm (F.projection (γ q)) with hz'
    have h1 : z' ∈ c.source := c.map_target hq
    rw [hc] at h1
    have h2 : c z' = F.projection (γ q) := c.right_inv hq
    have h4 : D.f (c z') = D.level 0 + D.κ * z'.2 := hcf z'.1 z'.2 h1.1 h1.2
    have h5 : D.f (c z') = D.level 0 := by
      rw [h2]
      exact hγu q
    have h6 : z'.2 = 0 := by
      have := D.κ_pos
      have h7 : D.κ * z'.2 = 0 := by linarith
      rcases mul_eq_zero.mp h7 with h8 | h8
      · linarith
      · exact h8
    refine ⟨z'.1, ?_⟩
    rw [← h2]
    congr 1
    exact Prod.ext rfl h6
  have hconn : IsPreconnected (range γ) := isPreconnected_range hγ
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn O₁ O₂ hO₁o hO₂o
    (by
      rintro y ⟨q, rfl⟩
      by_cases h : γ q ∈ O₂
      · exact Or.inr h
      · left
        have h1 : F.projection (γ q) ∈ c '' (univ ×ˢ {(0 : ℝ)}) := not_not.mp h
        obtain ⟨r, hr, hr'⟩ := h1
        change F.projection (γ q) ∈ c.target
        rw [← hr']
        apply c.map_source
        rw [hc]
        obtain ⟨-, hr2⟩ := hr
        have hr0 : r.2 = 0 := hr2
        change -1 < r.2 ∧ r.2 < 1
        rw [hr0]
        constructor <;> norm_num)
    (by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨q, rfl⟩ h1 h2
      obtain ⟨θ, hθ⟩ := hsplit q h1
      exact h2 ⟨(θ, 0), ⟨mem_univ _, rfl⟩, hθ.symm⟩) with h | h
  · exact hsplit p (h ⟨p, rfl⟩)
  · exact absurd ⟨(θ₀, 0), ⟨mem_univ _, rfl⟩, hp₀.symm⟩ (h ⟨p₀, rfl⟩)

end TopIdentity

section PortArrival

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
  {F : CircleFibration C U} (D : BaseMorseData F.base)

theorem exists_rate_lower_bound {Y : (x : U) → TangentSpace C.model x}
    (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
    {α β : ℝ} (hpos : ∀ x, portHeight F D x ∈ Icc α β → 0 < heightRate F D x (Y x)) :
    ∃ ε > 0, ∀ x, portHeight F D x ∈ Icc α β → ε ≤ heightRate F D x (Y x) := by
  have hK := isCompact_portHeight F D α β
  have hcont : ContinuousOn (fun x => heightRate F D x (Y x)) univ :=
    continuousOn_mfderiv_apply isOpen_univ (contMDiff_portHeight F D).contMDiffOn Y
      hY.continuous.continuousOn
  rcases eq_empty_or_nonempty {x : U | portHeight F D x ∈ Icc α β} with h | h
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    have hx' : x ∈ {x : U | portHeight F D x ∈ Icc α β} := hx
    rw [h] at hx'
    exact hx'.elim
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn h (hcont.mono (subset_univ _))
    exact ⟨_, hpos x₀ hx₀, fun x hx => hmin hx⟩

theorem exists_portArrival (hsrc : e.source = halfCollarSource)
    {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}
    (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
    (hΦs : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y)
    {a a₁ b μ w ν : ℝ} (ha : 0 < a) (h2a : 2 * a < a₁) (ha₁b : a₁ < b) (hb1 : b < 1)
    (hYray : ∀ p s, a < s → s < b →
      Y (e (p, Manifold.halfSpaceOneLift s)) =
        collarNormalField e (e (p, Manifold.halfSpaceOneLift s)))
    (hint : ∀ p s, a < s → s < b → C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)))
    (hr0 : ∀ x, 0 ≤ heightRate F D x (Y x)) (hμ : 0 < μ) (hμℓ : μ < D.level 0 / 4)
    (hw : 0 < w) (hκw : D.κ * w ≤ D.level 0 / 4) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hμ₁ : ∀ p, μ ≤ portHeight F D (e (p, Manifold.halfSpaceOneLift a₁)))
    (hlow0 : ∀ p, portHeight F D (e (p, Manifold.halfSpaceOneLift (2 * a))) < μ)
    (hrband : ∀ x, portHeight F D x ∈ Ioo (D.level 0 - D.κ * (w / 2)) (D.level 0 + D.κ * (w / 2)) →
      heightRate F D x (Y x) = D.κ)
    (hrslow : ∀ x, portHeight F D x ∈ Icc (D.level 0 / 4) (D.level 0 - D.κ * w) →
      heightRate F D x (Y x) ≤ ν)
    (hrpos : ∀ x, portHeight F D x ∈ Icc μ (D.level 0) → 0 < heightRate F D x (Y x)) :
    ∃ T : Torus → ℝ, ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ T ∧ (∀ p, D.level 0 ≤ T p) ∧
      (∀ p, portHeight F D (Φ (T p) (e (p, Manifold.halfSpaceOneLift (2 * a)))) = D.level 0) ∧
      (∀ p t, portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))) ≤ D.level 0 ↔
        t ≤ T p) ∧
      (∀ p t, portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))) < D.level 0 ↔
        t < T p) := by
  have hℓ := D.two_κ_lt_level
  have hκ := D.κ_pos
  have hmono := monotone_height_flow F D hΦY hr0
  have hd : ∀ p t, HasDerivAt (fun t => portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift
      (2 * a))))) (heightRate F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))))
        (Y (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))))) t :=
    fun p t => hasDerivAt_height_flow F D hΦY _ t
  obtain ⟨ε, hε, hεr⟩ := exists_rate_lower_bound D hY hrpos
  have hray₁ : ∀ p, Φ (a₁ - 2 * a) (e (p, Manifold.halfSpaceOneLift (2 * a))) =
      e (p, Manifold.halfSpaceOneLift a₁) := fun p => by
    rw [portFlow_ray e hsrc hY hΦ0 hΦY hb1 hYray hint ha (by linarith) p
      ⟨by linarith, by linarith⟩]
    congr 3
    ring
  have hex : ∀ p, ∃ T, 0 ≤ T ∧
      portHeight F D (Φ T (e (p, Manifold.halfSpaceOneLift (2 * a)))) = D.level 0 := by
    intro p
    refine exists_arrival (hd p) (hmono _) hε (by linarith) (t₁ := a₁ - 2 * a) ?_
      (fun t ht => hεr _ ht) ?_ (by linarith)
    · rw [hray₁ p]
      exact hμ₁ p
    · rw [hΦ0]
      linarith [hlow0 p]
  choose T hT0 hT using hex
  have hband' : ∀ p t, portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))) ∈
      Ioo (D.level 0 - D.κ * (w / 2)) (D.level 0 + D.κ * (w / 2)) →
      heightRate F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))))
        (Y (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))))) = D.κ :=
    fun p t ht => hrband _ ht
  have hchar := fun p => arrival_char (hd p) (hmono _) hκ (by positivity : 0 < w / 2)
    (hband' p) (hT p)
  have hTℓ : ∀ p, D.level 0 ≤ T p := by
    intro p
    have h1 := le_arrival (hd p) (hmono _) hν (α := D.level 0 / 4)
      (β := D.level 0 - D.κ * w) (T := T p) (by linarith) (by
        rw [hΦ0]
        linarith [hlow0 p])
      (by
        rw [hT p]
        linarith [mul_pos hκ hw]) (hT0 p) (fun t ht => hrslow _ ht)
    have h2 : D.level 0 ≤ (D.level 0 - D.κ * w - D.level 0 / 4) / ν := by
      rw [le_div_iff₀ hν]
      nlinarith
    linarith
  refine ⟨T, ?_, hTℓ, hT, fun p => (hchar p).2.1, fun p => (hchar p).2.2⟩
  exact contMDiff_arrival (contMDiff_portFlowMap e hsrc hΦs (b := 2 * a) (by linarith))
    (contMDiff_portHeight F D) (fun p t => hd p t) hκ (by positivity : 0 < w / 2)
    (fun p t ht => hband' p t ht) (fun p => (hchar p).2.1) (fun p => (hchar p).2.2) hT

end PortArrival

section PortPiece

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def collarRegion (F : CircleFibration C U) (D : BaseMorseData F.base)
    (c₀ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞) :
    Set C.Carrier :=
  connectedComponentIn {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}
    (c₀ (1, halfZero))

def topPoint {B : CompactSurface} (D : BaseMorseData B) [Fact (0 < D.level 0)] :
    Icc (0 : ℝ) (D.level 0) :=
  ⟨D.level 0, (Fact.out : 0 < D.level 0).le, le_rfl⟩

theorem exists_portPiece
    (e : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) U ∞)
    (hsrc : e.source = halfCollarSource) {F : CircleFibration C U} (D : BaseMorseData F.base)
    [Fact (0 < D.level 0)]
    {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞} (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s)
    (L : LiftedBicollar F c) {Y : (x : U) → TangentSpace C.model x} {Φ : ℝ → U → U}
    (hY : ContMDiff C.model C.model.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle C.model U)))
    (hΦs : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ t (Φ s x) = Φ (s + t) x)
    (hΦY : ∀ x, IsMIntegralCurve (fun t => Φ t x) Y)
    {a a₁ b μ w : ℝ} (ha : 0 < a) (h2a : 2 * a < a₁) (ha₁b : a₁ < b)
    (hb4 : b < D.level 0 / 4) (hb1 : b < 1) (hw : 0 < w) (hκw : D.κ * w ≤ D.level 0 / 4)
    (hYray : ∀ p s, a < s → s < b →
      Y (e (p, Manifold.halfSpaceOneLift s)) =
        collarNormalField e (e (p, Manifold.halfSpaceOneLift s)))
    (hpos : ∀ p s, 0 < s → s ≤ b → 0 < portHeight F D (e (p, Manifold.halfSpaceOneLift s)))
    (hlow : ∀ p s, 0 ≤ s → s ≤ b →
      portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < D.level 0 / 4)
    (hμ₁ : ∀ p, μ ≤ portHeight F D (e (p, Manifold.halfSpaceOneLift a₁)))
    (hμ₂ : ∀ p s, 0 ≤ s → s ≤ 2 * a → portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < μ)
    (hr0 : ∀ x, 0 ≤ heightRate F D x (Y x))
    (hYX : ∀ x θ s, F.projection x = c (θ, s) → |s| ≤ w / 2 →
      portHeight F D x ∈ Icc (D.level 0 - D.κ * w / 2) (D.level 0 + D.κ * w / 2) →
        Y x = liftGenerator L x)
    {T : Torus → ℝ} (hTs : ContMDiff torusModel 𝓘(ℝ, ℝ) ∞ T) (hTℓ : ∀ p, D.level 0 ≤ T p)
    (hT : ∀ p, portHeight F D (Φ (T p) (e (p, Manifold.halfSpaceOneLift (2 * a)))) = D.level 0)
    (hchar : ∀ p t, portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))) ≤
      D.level 0 ↔ t ≤ T p)
    (hchar' : ∀ p t, portHeight F D (Φ t (e (p, Manifold.halfSpaceOneLift (2 * a)))) <
      D.level 0 ↔ t < T p)
    (hwL : w < L.width)
    (htie : ∃ (θ₀ : Circle) (x : U), F.projection x = c (θ₀, 0) ∧
      x.val ∈ connectedComponentIn {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}
        (e (1, halfZero)).val) :
    ∃ δ > 0, ∃ K : Torus × Icc (0 : ℝ) (D.level 0) → U,
      ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (fun q => (K q).val) ∧
      Function.Injective K ∧
      (∀ q, Function.Bijective
        (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q)) ∧
      range (fun q => (K q).val) =
        connectedComponentIn {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}
          (e (1, halfZero)).val ∧
      (∀ p s, s.1 < δ → K (p, s) = e (p, Manifold.halfSpaceOneLift s.1)) ∧
      ∀ p s, D.level 0 - δ < s.1 → K (p, s) = L.flow (s.1 - D.level 0) (K (p, topPoint D)) := by
  have hℓ := D.two_κ_lt_level
  have hκ := D.κ_pos
  have hℓpos : 0 < D.level 0 := by linarith
  have hab : 2 * a < b := by linarith
  have hint : ∀ p s, a < s → s < b →
      C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)) := fun p s h1 h2 =>
    isInteriorPoint_of_portHeight_pos F D (hpos p s (by linarith) h2.le)
  have hGs := contMDiff_portFlowMap e hsrc hΦs (b := 2 * a) (by linarith)
  have hGd := injective_mfderiv_portFlowMap e hsrc hY hΦs hΦ0 hΦadd hΦY hb1 hYray hint ha hab
  have hmono := monotone_height_flow F D hΦY hr0
  have hGi := injective_portFlowMap e hsrc hY hΦ0 hΦadd hΦY hb1 hYray hint ha hab hmono h2a
    ha₁b hμ₁ (fun p => hμ₂ p (2 * a) (by linarith) le_rfl)
  have hray : ∀ p t, t ∈ Ioo (-a) (b - 2 * a) →
      Φ t (e (p, Manifold.halfSpaceOneLift (2 * a))) =
        e (p, Manifold.halfSpaceOneLift (2 * a + t)) := fun p t ht =>
    portFlow_ray e hsrc hY hΦ0 hΦY hb1 hYray hint ha hab p ht
  have hs01 : b < 3 * D.level 0 / 4 := by linarith
  set τ := portTime a (D.level 0) b (3 * D.level 0 / 4) T with hτ
  have hτs : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ τ := contMDiff_portTime _ _ _ _ hTs
  have hτmono : ∀ p, StrictMono (fun s => τ (p, s)) := fun p =>
    strictMono_portTime hs01 (by linarith [hTℓ p])
  have hτlow : ∀ p s, s ≤ b → τ (p, s) = s - 2 * a := fun p s hs => portTime_of_le hs01 T p hs
  have hτhigh : ∀ p s, 3 * D.level 0 / 4 ≤ s → τ (p, s) = s - D.level 0 + T p :=
    fun p s hs => portTime_of_ge hs01 T p hs
  set A : Torus × ℝ → U := fun q => Φ (τ q) (e (q.1, Manifold.halfSpaceOneLift (2 * a)))
    with hA
  have hAs : ContMDiff (torusModel.prod 𝓘(ℝ, ℝ)) C.model ∞ A :=
    hGs.comp (contMDiff_fst.prodMk hτs)
  have hAd : ∀ q, Function.Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) C.model A q) :=
    injective_mfderiv_reparam hGs hGd hτs fun p s =>
      ⟨_, (lt_of_lt_of_le one_pos (one_le_deriv_portTime hs01 (by linarith [hTℓ p]) s)).ne',
        hasDerivAt_portTime a (D.level 0) b (3 * D.level 0 / 4) T p s⟩
  have hagree : ∀ p s, a < s → s < a₁ → A (p, s) = e (p, Manifold.halfSpaceOneLift s) := by
    intro p s h1 h2
    change Φ (τ (p, s)) (e (p, Manifold.halfSpaceOneLift (2 * a))) = _
    rw [hτlow p s (by linarith), hray p (s - 2 * a) ⟨by linarith, by linarith⟩]
    congr 3
    ring
  have hAinj : ∀ p p' s s', a < s → a < s' → A (p, s) = A (p', s') → p = p' ∧ s = s' := by
    intro p p' s s' hs hs' h
    have h1 := hGi (a₁ := (p, τ (p, s))) (a₂ := (p', τ (p', s'))) h
    have h2 : p = p' := congrArg Prod.fst h1
    subst h2
    exact ⟨rfl, (hτmono p).injective (congrArg Prod.snd h1)⟩
  have hhigh : ∀ p s, a₁ ≤ s → μ ≤ portHeight F D (A (p, s)) := by
    intro p s hs
    have h1 : τ (p, a₁) ≤ τ (p, s) := (hτmono p).monotone hs
    rw [hτlow p a₁ ha₁b.le] at h1
    have h2 := hmono (e (p, Manifold.halfSpaceOneLift (2 * a))) h1
    simp only at h2
    rw [hray p (a₁ - 2 * a) ⟨by linarith, by linarith⟩,
      show 2 * a + (a₁ - 2 * a) = a₁ by ring] at h2
    exact (hμ₁ p).trans h2
  have hAle : ∀ p s, s ≤ D.level 0 → portHeight F D (A (p, s)) ≤ D.level 0 := by
    intro p s hs
    have h1 : τ (p, s) ≤ τ (p, D.level 0) := (hτmono p).monotone hs
    rw [hτhigh p (D.level 0) (by linarith)] at h1
    exact (hchar p _).mpr (by linarith)
  have hAlt : ∀ p s, s < D.level 0 → portHeight F D (A (p, s)) < D.level 0 := by
    intro p s hs
    have h1 : τ (p, s) < τ (p, D.level 0) := hτmono p hs
    rw [hτhigh p (D.level 0) (by linarith)] at h1
    exact (hchar' p _).mpr (by linarith)
  have hAabove : ∀ p s, a < s → D.level 0 < s → D.level 0 < portHeight F D (A (p, s)) := by
    intro p s hsa hs
    by_contra h
    have h1 := (hchar p (τ (p, s))).mp (not_lt.mp h)
    rw [hτhigh p s (by linarith)] at h1
    linarith
  have hAint : ∀ p s, a < s → C.model.IsInteriorPoint (A (p, s)) := by
    intro p s hs
    apply isInteriorPoint_of_portHeight_pos F D
    have h1 : τ (p, a) < τ (p, s) := hτmono p hs
    rw [hτlow p a (by linarith)] at h1
    set t' := min (τ (p, s)) (a₁ - 2 * a) with ht'
    have h2 : t' ≤ τ (p, s) := min_le_left _ _
    have h3 : t' ≤ a₁ - 2 * a := min_le_right _ _
    have h4 : -a < t' := lt_min (by linarith) (by linarith)
    have h5 := hmono (e (p, Manifold.halfSpaceOneLift (2 * a))) h2
    simp only at h5
    rw [hray p t' ⟨h4, by linarith⟩] at h5
    exact lt_of_lt_of_le (hpos p _ (by linarith) (by linarith)) h5
  set K := portPieceMap (ℓ := D.level 0) e A a₁ with hK
  have hKs := contMDiff_portPieceMap (ℓ := D.level 0) e A a₁ hsrc (by linarith : a < a₁)
    (by linarith) hAs hagree
  have hKi := injective_portPieceMap (ℓ := D.level 0) e A a₁ hsrc (by linarith : a < a₁)
    (by linarith) hagree hAinj (g := portHeight F D) (fun p s h1 h2 => hμ₂ p s h1 (by linarith))
    hhigh
  have hKd := injective_mfderiv_portPieceMap (ℓ := D.level 0) e A a₁ hsrc (by linarith : a < a₁)
    (by linarith) hAs hAd hagree
  have hKval : ∀ q, mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q =
      mfderiv (torusModel.prod (𝓡∂ 1)) C.model K q := fun q =>
    DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U K q
  have hKle : ∀ q, portHeight F D (K q) ≤ D.level 0 := by
    intro q
    rcases lt_or_ge q.2.1 a₁ with hq | hq
    · rw [hK, portPieceMap_of_lt e A a₁ hq]
      linarith [hlow q.1 q.2.1 q.2.2.1 (by linarith)]
    · rw [hK, portPieceMap_of_gt e A a₁ hagree (by linarith : a < q.2.1)]
      exact hAle q.1 q.2.1 q.2.2.2
  have hKlt : ∀ q, q.2.1 < D.level 0 → portHeight F D (K q) < D.level 0 := by
    intro q hq'
    rcases lt_or_ge q.2.1 a₁ with hq | hq
    · rw [hK, portPieceMap_of_lt e A a₁ hq]
      linarith [hlow q.1 q.2.1 q.2.2.1 (by linarith)]
    · rw [hK, portPieceMap_of_gt e A a₁ hagree (by linarith : a < q.2.1)]
      exact hAlt q.1 q.2.1 hq'
  have hKtop : ∀ p, K (p, topPoint D) = Φ (T p) (e (p, Manifold.halfSpaceOneLift (2 * a))) := by
    intro p
    rw [hK, portPieceMap_of_gt e A a₁ hagree (show a < (topPoint D).1 by
      change a < D.level 0
      linarith)]
    change Φ (τ (p, D.level 0)) _ = _
    rw [hτhigh p (D.level 0) (by linarith), sub_self, zero_add]
  have : ConnectedSpace (Icc (0 : ℝ) (D.level 0)) :=
    Subtype.connectedSpace (isConnected_Icc hℓpos.le)
  have hrange : range (fun q => (K q).val) =
      connectedComponentIn {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}
        (e (1, halfZero)).val := by
    refine range_eq_connectedComponentIn (continuous_subtype_val.comp hKs.continuous) ?_ ?_ ?_
    · refine ⟨((1 : Torus), ⟨0, le_rfl, hℓpos.le⟩), ?_⟩
      change (K ((1 : Torus), ⟨0, le_rfl, hℓpos.le⟩)).val = _
      rw [hK, portPieceMap_of_lt e A a₁ (show ((⟨0, le_rfl, hℓpos.le⟩ : Icc (0 : ℝ) (D.level 0)) :
        ℝ) < a₁ by change (0 : ℝ) < a₁; linarith)]
      change (e (1, Manifold.halfSpaceOneLift 0)).val = _
      rw [halfSpaceOneLift_zero]
    · rintro y ⟨q, rfl⟩
      exact ⟨(K q).2, hKle q⟩
    · intro q
      rcases lt_or_ge q.2.1 a₁ with hq | hq
      · obtain ⟨O, hO, hqO, hOK⟩ := exists_open_portPieceMap_low (ℓ := D.level 0) e A a₁ hsrc
          (by linarith) (by linarith) q hq
        exact ⟨O, hO, hqO, fun y hy => hOK hy.1⟩
      · exact exists_open_portPieceMap_high (ℓ := D.level 0) e A a₁ ha hagree hAs hAd hAint
          (g := portHeight F D) hAabove q (by linarith)
  obtain ⟨θ₀, x, hxπ, hxR⟩ := htie
  rw [← hrange] at hxR
  obtain ⟨q₀, hq₀⟩ := hxR
  have hq₀' : K q₀ = x := Subtype.ext hq₀
  have hxu : portHeight F D x = D.level 0 := by
    unfold portHeight
    rw [hxπ, hcf θ₀ 0 (by norm_num) (by norm_num), mul_zero, add_zero]
  have hq₀ℓ : q₀.2 = topPoint D := by
    apply Subtype.ext
    by_contra hne
    have h1 : q₀.2.1 < D.level 0 := lt_of_le_of_ne q₀.2.2.2 hne
    have h2 := hKlt q₀ h1
    rw [hq₀', hxu] at h2
    exact lt_irrefl _ h2
  have hγc : Continuous (fun p => Φ (T p) (e (p, Manifold.halfSpaceOneLift (2 * a)))) :=
    (hGs.comp (contMDiff_id.prodMk hTs)).continuous
  have hγπ : F.projection (Φ (T q₀.1) (e (q₀.1, Manifold.halfSpaceOneLift (2 * a)))) =
      c (θ₀, 0) := by
    rw [← hxπ, ← hq₀', ← hKtop q₀.1]
    congr 2
    exact Prod.ext rfl hq₀ℓ.symm
  have hover := forall_projection_eq_of_level D hc hcf hγc hT hγπ
  refine ⟨min (w / 2) (min a₁ (D.level 0 / 4)), lt_min (by positivity)
    (lt_min (by linarith) (by positivity)), K,
    contMDiff_subtype_val.comp hKs, hKi, fun q => ?_, hrange, fun p s hs => ?_,
      fun p s hs => ?_⟩
  · rw [hKval q]
    exact bijective_of_injective_tangent _ (hKd q)
  · rw [hK]
    exact portPieceMap_of_lt e A a₁ (lt_of_lt_of_le hs ((min_le_right _ _).trans
      (min_le_left _ _)))
  · have hδ : min (w / 2) (min a₁ (D.level 0 / 4)) ≤ D.level 0 / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hs1 : D.level 0 - D.level 0 / 4 < s.1 := by linarith
    rw [hK, portPieceMap_of_gt e A a₁ hagree (by linarith : a < s.1), ← hK, hKtop p]
    change Φ (τ (p, s.1)) _ = _
    rw [hτhigh p s.1 (by linarith)]
    obtain ⟨θ, hθ⟩ := hover p
    have h1 : |s.1 - D.level 0| < w / 2 := by
      rw [abs_lt]
      constructor
      · linarith [min_le_left (w / 2) (min a₁ (D.level 0 / 4))]
      · linarith [s.2.2]
    rw [← flow_eq_liftFlow D L hc hcf hY hΦ0 hΦY hwL (by linarith) hYX hθ h1, hΦadd]
    congr 1
    ring

end PortPiece

section OldPortCollarPiece

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem exists_oldPortCollarPiece (F : CircleFibration C U) (D : BaseMorseData F.base)
    [Fact (0 < D.level 0)]
    (c₀ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hsrc : c₀.source = halfCollarSource) (hb : ∀ t, C.model.IsBoundaryPoint (c₀ (t, halfZero)))
    (hown : c₀.target ⊆ U)
    (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
      F.base.Carrier ∞) (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level 0 + D.κ * s)
    (htie : ∃ (θ₀ : Circle) (x : U), F.projection x = c (θ₀, 0) ∧ x.val ∈ collarRegion F D c₀)
    (L : LiftedBicollar F c) :
    ∃ δ > 0, ∃ K : Torus × Icc (0 : ℝ) (D.level 0) → U,
      ContMDiff (torusModel.prod (𝓡∂ 1)) C.model ∞ (fun q => (K q).val) ∧
      Function.Injective K ∧
      (∀ q, Function.Bijective
        (mfderiv (torusModel.prod (𝓡∂ 1)) C.model (fun q => (K q).val) q)) ∧
      range (fun q => (K q).val) = collarRegion F D c₀ ∧
      (∀ p s, s.1 < δ → (K (p, s)).val = c₀ (p, halfPoint s.1 s.2.1)) ∧
      ∀ p s, D.level 0 - δ < s.1 → K (p, s) = L.flow (s.1 - D.level 0) (K (p, topPoint D)) := by
  set e := portCollar c₀ hsrc hown with he
  have hesrc : e.source = halfCollarSource := (portCollar_source c₀ hsrc hown).trans hsrc
  have heval : ∀ q, q ∈ c₀.source → (e q).val = c₀ q := fun q hq =>
    portCollar_apply_val c₀ hsrc hown hq
  have hzero : ∀ t : Torus, (t, halfZero) ∈ c₀.source := fun t => by
    rw [hsrc]
    change (0 : ℝ) < 1
    norm_num
  have hbe : ∀ t, C.model.IsBoundaryPoint (e (t, halfZero)).val := fun t => by
    rw [heval _ (hzero t)]
    exact hb t
  have hℓ := D.two_κ_lt_level
  have hκ := D.κ_pos
  have hℓpos : 0 < D.level 0 := by linarith
  obtain ⟨a₀, ha₀, ha₀1, ha₀ℓ, hcol⟩ := exists_portCollarWidth e F D hesrc hbe hℓpos
  have hrate : ∀ t s, 0 ≤ s → s ≤ a₀ → 0 < heightRate F D (e (t, Manifold.halfSpaceOneLift s))
      (collarNormalField e (e (t, Manifold.halfSpaceOneLift s))) := fun t s h1 h2 =>
    (hcol t s h1 h2).1
  have hlow₀ : ∀ t s, 0 ≤ s → s ≤ a₀ →
      portHeight F D (e (t, Manifold.halfSpaceOneLift s)) < D.level 0 / 4 := fun t s h1 h2 =>
    (hcol t s h1 h2).2
  obtain ⟨μ, hμ, hμ₁, a', ha', hμ₂⟩ := exists_portSeparation e F D hesrc hbe (a₁ := a₀ / 4)
    (by positivity) (by linarith) ha₀1 hrate
  set a := min (a' / 2) (a₀ / 16) with hadef
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have ha1 : a ≤ a' / 2 := min_le_left _ _
  have ha2 : a ≤ a₀ / 16 := min_le_right _ _
  set M := (a₀ / 2) / a with hM
  have hMa : M * a = a₀ / 2 := div_mul_cancel₀ _ ha.ne'
  set w := min (L.width / 2) (min (1 / 2) (D.level 0 / (4 * D.κ))) with hwdef
  set ν := min D.κ (1 / 2) with hνdef
  have hw : 0 < w := lt_min (by linarith [L.width_pos]) (lt_min (by norm_num) (by positivity))
  have hwL : w < L.width := lt_of_le_of_lt (min_le_left _ _) (by linarith [L.width_pos])
  have hw1 : w < 1 :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hκw : D.κ * w ≤ D.level 0 / 4 := by
    have h1 : w ≤ D.level 0 / (4 * D.κ) := (min_le_right _ _).trans (min_le_right _ _)
    calc D.κ * w ≤ D.κ * (D.level 0 / (4 * D.κ)) := mul_le_mul_of_nonneg_left h1 hκ.le
      _ = D.level 0 / 4 := by
        field_simp
  have hν : 0 < ν := lt_min hκ (by norm_num)
  have hνκ : ν ≤ D.κ := min_le_left _ _
  have hν2 : ν ≤ 1 / 2 := min_le_right _ _
  have hμℓ : μ < D.level 0 / 4 :=
    lt_of_le_of_lt (hμ₁ 1) (hlow₀ 1 (a₀ / 4) (by positivity) (by linarith))
  have hposray : ∀ p s, 0 < s → s ≤ a₀ →
      0 < portHeight F D (e (p, Manifold.halfSpaceOneLift s)) := by
    intro p s hs hsa
    have hmono := strictMonoOn_portRay e hesrc (contMDiff_portHeight F D) p ha₀1
      (fun s' h1 h2 => hrate p s' h1.le h2.le)
    have h := hmono ⟨le_rfl, ha₀.le⟩ ⟨hs.le, hsa⟩ hs
    simp only at h
    rw [halfSpaceOneLift_zero, portHeight_collar_zero e F D hbe] at h
    exact h
  obtain ⟨V₀, hV₀s, hV₀⟩ := exists_unitField_of_isCompact (contMDiff_portHeight F D)
    (isCompact_portHeight F D (μ / 2) (D.level 0 + D.κ * w))
    (fun x hx => isInteriorPoint_of_portHeight_pos F D (by
      have h1 : μ / 2 ≤ portHeight F D x := hx.1
      linarith))
    (fun x hx => mfderiv_portHeight_ne_zero F D (by
      have h1 : portHeight F D x ≤ D.level 0 + D.κ * w := hx.2
      nlinarith))
  have hV₀' : ∀ x, portHeight F D x ∈ Icc (μ / 2) (D.level 0 + D.κ * w) →
      heightRate F D x (V₀ x) = 1 := fun x hx => hV₀ x hx
  have hMa' : M * a + a / 2 < 1 := by
    rw [hMa]
    linarith
  have hMa₀ : M * a + a / 2 ≤ a₀ := by
    rw [hMa]
    linarith
  have hμℓw : μ / 2 ≤ D.level 0 - D.κ * w := by linarith
  set Y := portVectorField e F D L a M μ ν w V₀ with hYdef
  have hY := contMDiff_portVectorField e F D L (μ := μ) (ν := ν) hesrc hc ha hMa' hw hw1 hV₀s
  have hYsupp := tsupport_portVectorField e F D L (V₀ := V₀) (ν := ν) hesrc ha hMa' hμ hw hμℓw
    (fun p s h1 h2 => hposray p s (by linarith) (by linarith))
  obtain ⟨Φ, hΦs, hΦ0, hΦadd, hΦY⟩ := exists_flow_of_tsupport_interior Y hY hYsupp.1 hYsupp.2
  have hr0 := heightRate_portVectorField_nonneg e F D L hc hcf hw hwL hμ hμℓw hV₀' ha hMa₀
    hrate hν.le hνκ
  have hrhigh : ∀ x, D.level 0 / 4 ≤ portHeight F D x →
      heightRate F D x (Y x) = slopeProfile μ ν D.κ (D.level 0) w (portHeight F D x) :=
    fun x hx => heightRate_portVectorField_of_high e F D L hc hcf hw hwL hμ hμℓw hV₀' ha hMa₀
      hlow₀ hx
  have hrpos : ∀ x, portHeight F D x ∈ Icc μ (D.level 0) → 0 < heightRate F D x (Y x) :=
    fun x hx => heightRate_portVectorField_pos e F D L hc hcf hw hwL hμ hμℓw hV₀' ha hMa₀
      hrate hν hνκ hx
  have hrband : ∀ x, portHeight F D x ∈
      Ioo (D.level 0 - D.κ * (w / 2)) (D.level 0 + D.κ * (w / 2)) →
      heightRate F D x (Y x) = D.κ := fun x hx => by
    rw [hrhigh x (by linarith [hx.1])]
    exact slopeProfile_eq_band hμ (by linarith) (mul_pos hκ hw) (by linarith [hx.1])
      (by linarith [hx.2])
  have hrslow : ∀ x, portHeight F D x ∈ Icc (D.level 0 / 4) (D.level 0 - D.κ * w) →
      heightRate F D x (Y x) ≤ ν := fun x hx => by
    rw [hrhigh x hx.1]
    exact slopeProfile_le_slow hν.le (mul_pos hκ hw) hx.2
  have hYray : ∀ p s, a < s → s < a₀ / 2 →
      Y (e (p, Manifold.halfSpaceOneLift s)) =
        collarNormalField e (e (p, Manifold.halfSpaceOneLift s)) := fun p s h1 h2 =>
    portVectorField_ray e F D L hesrc ha p h1.le (by rw [hMa]; exact h2.le) (by linarith)
  have hint : ∀ p s, a < s → s < a₀ / 2 →
      C.model.IsInteriorPoint (e (p, Manifold.halfSpaceOneLift s)) := fun p s h1 h2 =>
    isInteriorPoint_of_portHeight_pos F D (hposray p s (by linarith) (by linarith))
  have hYX : ∀ x θ s, F.projection x = c (θ, s) → |s| ≤ w / 2 →
      portHeight F D x ∈ Icc (D.level 0 - D.κ * w / 2) (D.level 0 + D.κ * w / 2) →
        Y x = liftGenerator L x := fun x θ s hx hs hu =>
    portVectorField_eq_liftGenerator e F D L hc hw hw1 ha hMa₀ hlow₀ hμ (by linarith)
      (by linarith) hx hs hu
  have hμ₂' : ∀ p s, 0 ≤ s → s ≤ 2 * a →
      portHeight F D (e (p, Manifold.halfSpaceOneLift s)) < μ := fun p s h1 h2 =>
    hμ₂ p s h1 (by linarith)
  obtain ⟨T, hTs, hTℓ, hT, hchar, hchar'⟩ := exists_portArrival e D hesrc hY hΦs hΦ0 hΦY ha
    (a₁ := a₀ / 4) (b := a₀ / 2) (by linarith) (by linarith) (by linarith) hYray hint hr0 hμ hμℓ
    hw hκw hν hν2 hμ₁ (fun p => hμ₂' p (2 * a) (by linarith) le_rfl) hrband hrslow hrpos
  have htie' : ∃ (θ₀ : Circle) (x : U), F.projection x = c (θ₀, 0) ∧
      x.val ∈ connectedComponentIn {y | ∃ h : y ∈ U, D.f (F.projection ⟨y, h⟩) ≤ D.level 0}
        (e (1, halfZero)).val := by
    obtain ⟨θ₀, x, h1, h2⟩ := htie
    refine ⟨θ₀, x, h1, ?_⟩
    rw [heval _ (hzero 1)]
    exact h2
  obtain ⟨δ, hδ, K, h1, h2, h3, h4, h5, h6⟩ := exists_portPiece e hesrc D hc hcf L hY hΦs hΦ0
    hΦadd hΦY ha (a₁ := a₀ / 4) (b := a₀ / 2) (by linarith) (by linarith) (by linarith)
    (by linarith) hw hκw hYray (fun p s h1 h2 => hposray p s h1 (by linarith))
    (fun p s h1 h2 => hlow₀ p s h1 (by linarith)) hμ₁ hμ₂' hr0 hYX hTs hTℓ hT hchar hchar' hwL
    htie'
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), K, h1, h2, h3, ?_, fun p s hs => ?_,
    fun p s hs => h6 p s (lt_of_le_of_lt (by linarith [min_le_left δ (1 / 2)]) hs)⟩
  · rw [h4, heval _ (hzero 1)]
    rfl
  · have hs1 : s.1 < 1 / 2 := lt_of_lt_of_le hs (min_le_right _ _)
    rw [h5 p s (lt_of_lt_of_le hs (min_le_left _ _)),
      heval _ (by rw [hsrc]; change max s.1 0 < 1; exact max_lt (by linarith) one_pos),
      GC.GraphManifold.halfPoint_eq_halfSpaceOneLift]

end OldPortCollarPiece

end GC.Seifert
