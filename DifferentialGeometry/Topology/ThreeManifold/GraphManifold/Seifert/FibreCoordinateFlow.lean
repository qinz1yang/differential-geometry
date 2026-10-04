import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# Lifted collar flows and test instances of the fibre-coordinate gluing

Chapter 6, lane MD4 (second file; `SF/FibreCoordinate.lean` is frozen).

`CircleFibration.exists_liftFlow` builds a `LiftedBicollar F c` for every bicollar `c` with
`S¹ × [-R, R]` in its source (width `R / 8`, reach `R`). The base field is `(0, bump(s))` on
`S¹ × ℝ` (`collarField`), supported in `|s| ≤ R / 2`; its flow (`collarFlowZ`) is the
translation `(θ, s) ↦ (θ, s + t)` while `|s|, |s + t| < R / 8` (`collarFlowZ_apply`, uniqueness of
integral curves). The total space over `c.target` consists of interior points
(`isInteriorPoint_of_mem_target`, `FibreCoordinate.isInteriorPoint`), so it is a boundaryless
manifold for the interior atlas (`CollarTotal`, `collarTotalEquiv`). There `c.symm ∘ π` is a
submersion (`surjective_mfderiv_collarMap`, from `CircleFibration.surjective_mfderiv_projection`),
the field lifts with compact support (`exists_smoothDerivativeLift_of_surjective`,
`isCompact_collarMap_preimage`), the lifted and base flows are related
(`compactSupportFlowDiffeomorph_map_of_mfderiv_eq`), and the lifted flow, extended by the identity
outside `π⁻¹ (c.target)` (`collarLift`), is jointly smooth (`contMDiff_collarLift`), a group in
the time (`collarLift_zero`, `collarLift_add`), covers the base flow (`projection_collarLift`) and
is the identity off `π⁻¹ (c (S¹ × [-R, R]))`. The two compactly supported flows of the tree agree
by definition (`compactSupportFlowDiffeomorph_eq_compactSupportFlow`, `rfl`).

Test instances of `FibreCoordinate.glue`: one simply connected overlap
(`glue_of_isSimplyConnected`) and two trivialisation charts of `F` made positive
(`exists_glue_trivializationCharts`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

section LiftFlow

theorem FibreCoordinate.isInteriorPoint {F : CircleFibration C U}
    {V : TopologicalSpace.Opens F.base.Carrier} (τ : FibreCoordinate F V)
    (x : TopologicalSpace.Opens.comap F.projection V)
    (hx : (SurfaceModel.model F.base.kind).IsInteriorPoint (F.projection x.val)) :
    C.model.IsInteriorPoint x.val := by
  have hfst : (SurfaceModel.model F.base.kind).IsInteriorPoint (τ.toDiffeo x).1 := by
    rw [ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val, τ.fst_eq]
    exact hx
  have h1 : ((SurfaceModel.model F.base.kind).prod (𝓡 1)).IsInteriorPoint (τ.toDiffeo x) := by
    have hmem : τ.toDiffeo x ∈ ((SurfaceModel.model F.base.kind).prod (𝓡 1)).interior
        (V × Circle) := by
      rw [ModelWithCorners.interior_prod]
      exact ⟨hfst, BoundarylessManifold.isInteriorPoint⟩
    exact hmem
  exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
    (((τ.toDiffeo.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mpr h1)

theorem CircleFibration.isInteriorPoint_of_projection (F : CircleFibration C U) {x : U}
    (hx : (SurfaceModel.model F.base.kind).IsInteriorPoint (F.projection x)) :
    C.model.IsInteriorPoint x :=
  (FibreCoordinate.ofTrivialization F (F.projection x)).isInteriorPoint
    ⟨x, F.mem_neighborhood (F.projection x)⟩ hx

theorem CircleFibration.surjective_mfderiv_projection (F : CircleFibration C U) (x : U) :
    Function.Surjective (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection x) := by
  set τ := FibreCoordinate.ofTrivialization F (F.projection x)
  set N := F.neighborhood (F.projection x)
  set x' : TopologicalSpace.Opens.comap F.projection N := ⟨x, F.mem_neighborhood _⟩
  intro w
  obtain ⟨v, hv⟩ := (τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) x').surjective
    ((w, 0) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
  refine ⟨v, ?_⟩
  have hπ : MDifferentiableAt C.model (SurfaceModel.model F.base.kind) F.projection x :=
    F.smooth.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt C.model C.model
      (Subtype.val : TopologicalSpace.Opens.comap F.projection N → U) x' :=
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)) x'
  have h1 := mfderiv_comp_apply x' hπ hval v
  rw [mfderiv_subtype_val_apply] at h1
  have hvf : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) (Subtype.val ∘ Prod.fst : N × Circle → F.base.Carrier)
      (τ.toDiffeo x') :=
    (((contMDiff_subtype_val (n := ∞)).comp contMDiff_fst).mdifferentiable (by simp)) _
  have hτ : MDifferentiableAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      τ.toDiffeo x' := (τ.toDiffeo.contMDiff.mdifferentiable (by simp)) x'
  have h2 := mfderiv_comp_apply x' hvf hτ v
  have hcomp : (Subtype.val ∘ Prod.fst) ∘ τ.toDiffeo =
      (F.projection ∘ Subtype.val : TopologicalSpace.Opens.comap F.projection N →
        F.base.Carrier) := funext fun y => τ.fst_eq y
  have hv' : mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ.toDiffeo x' v =
      ((w, 0) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) := hv
  have h3 : mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) (Subtype.val ∘ Prod.fst : N × Circle → F.base.Carrier)
      (τ.toDiffeo x') ((w, 0) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = w := by
    have h4 := mfderiv_comp_apply (τ.toDiffeo x')
      (((contMDiff_subtype_val (n := ∞) (I := SurfaceModel.model F.base.kind)
        (U := N)).mdifferentiable (by simp)) (τ.toDiffeo x').1)
      (mdifferentiableAt_fst (I := SurfaceModel.model F.base.kind) (I' := 𝓡 1))
      ((w, 0) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
    refine h4.trans ?_
    rw [mfderiv_fst, mfderiv_subtype_val_apply]
    rfl
  rw [hcomp, hv', h3] at h2
  rw [← h1]
  exact h2


variable {F : CircleFibration C U}
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞}

theorem isInteriorPoint_of_mem_target {b : F.base.Carrier} (hb : b ∈ c.target) :
    (SurfaceModel.model F.base.kind).IsInteriorPoint b := by
  have hs : c.symm b ∈ c.source := c.toPartialEquiv.map_target hb
  have h := ((PartialDiffeomorph.isLocalDiffeomorphAt (I := (𝓡 1).prod 𝓘(ℝ, ℝ))
    (J := SurfaceModel.model F.base.kind) (n := ∞) c hs).isInteriorPoint_iff (by simp)).mp
    BoundarylessManifold.isInteriorPoint
  have e : c (c.symm b) = b := c.toPartialEquiv.right_inv hb
  change (SurfaceModel.model F.base.kind).IsInteriorPoint (c (c.symm b)) at h
  rwa [e] at h

def collarOpens (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) : TopologicalSpace.Opens F.base.Carrier :=
  ⟨c.target, c.open_target⟩

instance boundarylessManifold_collar :
    BoundarylessManifold C.model (TopologicalSpace.Opens.comap F.projection (collarOpens c)) where
  isInteriorPoint' x := ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr
    (CircleFibration.isInteriorPoint_of_projection F (isInteriorPoint_of_mem_target x.2))

variable (F c) in
def CollarTotal : Type u := TopologicalSpace.Opens.comap F.projection (collarOpens c)

instance : TopologicalSpace (CollarTotal F c) :=
  inferInstanceAs (TopologicalSpace (TopologicalSpace.Opens.comap F.projection (collarOpens c)))

instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (CollarTotal F c) :=
  DifferentialGeometry.Manifold.interiorChartedSpace C.model ∞
    (M := TopologicalSpace.Opens.comap F.projection (collarOpens c))

instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (CollarTotal F c) :=
  DifferentialGeometry.Manifold.interiorIsManifold C.model ∞
    (M := TopologicalSpace.Opens.comap F.projection (collarOpens c))

instance : T2Space (CollarTotal F c) :=
  inferInstanceAs (T2Space (TopologicalSpace.Opens.comap F.projection (collarOpens c)))

instance : SigmaCompactSpace (CollarTotal F c) := by
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have : LocallyCompactSpace (TopologicalSpace.Opens.comap F.projection (collarOpens c)) :=
    (TopologicalSpace.Opens.comap F.projection (collarOpens c)).isOpen.locallyCompactSpace
  exact inferInstanceAs
    (SigmaCompactSpace (TopologicalSpace.Opens.comap F.projection (collarOpens c)))

variable (F c) in
def collarTotalEquiv : TopologicalSpace.Opens.comap F.projection (collarOpens c)
    ≃ₘ⟮C.model, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ CollarTotal F c :=
  DifferentialGeometry.Manifold.interiorAtlasDiffeomorph C.model ∞

variable (F c) in
def collarMap (y : CollarTotal F c) : Circle × ℝ :=
  c.symm (F.projection ((collarTotalEquiv F c).symm y).val)

theorem collarMap_eq (y : CollarTotal F c) :
    c (collarMap F c y) = F.projection ((collarTotalEquiv F c).symm y).val :=
  c.toPartialEquiv.right_inv ((collarTotalEquiv F c).symm y).2

theorem contMDiff_collarBase :
    ContMDiff C.model ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : TopologicalSpace.Opens.comap F.projection (collarOpens c) =>
        c.symm (F.projection x.val)) :=
  c.symm.contMDiffOn.comp_contMDiff (F.smooth.comp contMDiff_subtype_val) fun x => x.2

theorem contMDiff_collarMap :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (collarMap F c) :=
  contMDiff_collarBase.comp (collarTotalEquiv F c).symm.contMDiff

theorem surjective_mfderiv_collarMap (y : CollarTotal F c) :
    Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (collarMap F c) y) := by
  set x := (collarTotalEquiv F c).symm y
  have hb : F.projection x.val ∈ c.target := x.2
  have hloc : IsLocalDiffeomorphAt (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      c.symm (F.projection x.val) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (I := SurfaceModel.model F.base.kind)
      (J := (𝓡 1).prod 𝓘(ℝ, ℝ)) (n := ∞) c.symm hb
  have hcs : MDifferentiableAt (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ))
      c.symm (F.projection x.val) := hloc.mdifferentiableAt (by simp)
  have hπ : MDifferentiableAt C.model (SurfaceModel.model F.base.kind) F.projection x.val :=
    F.smooth.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt C.model C.model
      (Subtype.val : TopologicalSpace.Opens.comap F.projection (collarOpens c) → U) x :=
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)) x
  have he : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C.model
      (collarTotalEquiv F c).symm y :=
    ((collarTotalEquiv F c).symm.contMDiff.mdifferentiable (by simp)) y
  intro w
  obtain ⟨w₁, hw₁⟩ := (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective w
  obtain ⟨w₂, hw₂⟩ := CircleFibration.surjective_mfderiv_projection F x.val w₁
  obtain ⟨w₃, hw₃⟩ := ((collarTotalEquiv F c).symm.mfderivToContinuousLinearEquiv
    (by simp) y).surjective w₂
  refine ⟨w₃, ?_⟩
  have hw₃' : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C.model (collarTotalEquiv F c).symm y w₃
      = w₂ := hw₃
  have hw₁' : mfderiv (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) c.symm
      (F.projection x.val) w₁ = w := hw₁
  have key : ∀ v, mfderiv C.model ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((c.symm ∘ F.projection) ∘ Subtype.val)
      x v = mfderiv (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) c.symm
        (F.projection x.val) (mfderiv C.model (SurfaceModel.model F.base.kind) F.projection
          x.val v) := fun v => by
    rw [mfderiv_comp_apply x (hcs.comp x.val hπ) hval, mfderiv_subtype_val_apply]
    exact mfderiv_comp_apply x.val hcs hπ v
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
    (((c.symm ∘ F.projection) ∘ Subtype.val) ∘ (collarTotalEquiv F c).symm) y w₃ = w
  rw [mfderiv_comp_apply y ((hcs.comp x.val hπ).comp x hval) he, hw₃']
  exact (key w₂).trans (by rw [hw₂, hw₁'])

open AnnulusStraightening in
theorem contDiff_collarBump (ε : ℝ) : ContDiff ℝ ∞ (collarBump ε) :=
  (contDiff_cutoff _ _).mul ((contDiff_cutoff _ _).comp contDiff_neg)

open AnnulusStraightening in
theorem collarBump_of_abs_le {ε s : ℝ} (hε : 0 < ε) (hs : |s| ≤ ε / 4) : collarBump ε s = 1 := by
  have h1 : cutoff (-(ε / 2)) (-(ε / 4)) s = 1 :=
    cutoff_of_ge (by linarith) (by linarith [neg_abs_le s])
  have h2 : cutoff (-(ε / 2)) (-(ε / 4)) (-s) = 1 :=
    cutoff_of_ge (by linarith) (by linarith [le_abs_self s])
  rw [collarBump, h1, h2, mul_one]

open AnnulusStraightening in
theorem collarBump_of_le_abs {ε s : ℝ} (hε : 0 < ε) (hs : ε / 2 ≤ |s|) : collarBump ε s = 0 := by
  rcases le_abs.mp hs with h | h
  · rw [collarBump,
      cutoff_of_le (s₁ := -(ε / 2)) (by linarith) (show -s ≤ -(ε / 2) by linarith), mul_zero]
  · rw [collarBump, cutoff_of_le (s₁ := -(ε / 2)) (by linarith)
      (show s ≤ -(ε / 2) by linarith), zero_mul]

def collarField (R : ℝ) (p : Circle × ℝ) : TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ)) p :=
  ((0 : EuclideanSpace ℝ (Fin 1)), collarBump R p.2)

theorem contMDiff_collarField (R : ℝ) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, collarField R p⟩ : TangentBundle ((𝓡 1).prod 𝓘(ℝ, ℝ)) (Circle × ℝ))) := by
  have hρ : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : Circle × ℝ => collarBump R p.2) :=
    (contDiff_collarBump R).contMDiff.comp contMDiff_snd
  have hR : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun p : Circle × ℝ => (⟨p.2, collarBump R p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro p
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiff_snd p, ?_⟩
    convert hρ p using 1
    simp
  have hT : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1).tangent ∞
      (fun p : Circle × ℝ => (⟨p.1, 0⟩ : TangentBundle (𝓡 1) Circle)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 1) : Circle → Type)).comp contMDiff_fst
  exact contMDiff_equivTangentBundleProd_symm.comp (hT.prodMk hR)

theorem collarField_eq_zero {R : ℝ} (hR : 0 < R) {p : Circle × ℝ} (hp : R / 2 ≤ |p.2|) :
    collarField R p = 0 := by
  rw [collarField, collarBump_of_le_abs hR hp]
  rfl

theorem tsupport_collarField {R : ℝ} (hR : 0 < R) :
    tsupport (collarField R) ⊆ univ ×ˢ Icc (-(R / 2)) (R / 2) := by
  refine closure_minimal ?_ (isClosed_univ.prod isClosed_Icc)
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  by_contra h
  have h' : R / 2 ≤ |p.2| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  exact hp (collarField_eq_zero hR h')

theorem isCompact_tsupport_collarField {R : ℝ} (hR : 0 < R) :
    IsCompact (tsupport (collarField R)) :=
  (isCompact_univ.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_collarField hR)

def collarFlowZ {R : ℝ} (hR : 0 < R) (t : ℝ) : (Circle × ℝ) ≃ₘ⟮(𝓡 1).prod 𝓘(ℝ, ℝ),
    (𝓡 1).prod 𝓘(ℝ, ℝ)⟯ (Circle × ℝ) :=
  DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph (collarField R)
    (contMDiff_collarField R) (isCompact_tsupport_collarField hR) t

theorem collarFlowZ_eq_self {R : ℝ} (hR : 0 < R) {p : Circle × ℝ} (hp : R / 2 ≤ |p.2|)
    (t : ℝ) : collarFlowZ hR t p = p := by
  rw [collarFlowZ, DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_apply]
  exact DifferentialGeometry.Analysis.ODE.curveAt_eq_self_of_eq_zero _
    ((contMDiff_collarField R).of_le (by norm_num)) _ (collarField_eq_zero hR hp) t

theorem collarFlowZ_apply {R : ℝ} (hR : 0 < R) {θ : Circle} {s t : ℝ} (hs : |s| < R / 8)
    (hst : |s + t| < R / 8) : collarFlowZ hR t (θ, s) = (θ, s + t) := by
  have hab : ∀ u ∈ Ioo (-(R / 8) - s) (R / 8 - s), |s + u| < R / 8 := fun u hu => by
    have h1 := hu.1
    have h2 := hu.2
    rw [abs_lt]
    constructor <;> linarith
  have h0 : (0 : ℝ) ∈ Ioo (-(R / 8) - s) (R / 8 - s) := by
    have h1 := abs_lt.mp hs
    constructor <;> linarith [h1.1, h1.2]
  have ht : t ∈ Ioo (-(R / 8) - s) (R / 8 - s) := by
    have h1 := abs_lt.mp hst
    constructor <;> linarith [h1.1, h1.2]
  have hγ : IsMIntegralCurveOn (fun u : ℝ => ((θ, s + u) : Circle × ℝ)) (collarField R)
      (Ioo (-(R / 8) - s) (R / 8 - s)) := by
    intro u hu
    have hd : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (fun u : ℝ => ((θ, s + u) : Circle × ℝ)) u
        ((0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).prod (ContinuousLinearMap.toSpanSingleton ℝ 1)) :=
      (hasMFDerivAt_const θ u).prodMk
        (((hasDerivAt_id u).const_add s).hasFDerivAt.hasMFDerivAt)
    refine (hd.congr_mfderiv ?_).hasMFDerivWithinAt
    have hb : collarBump R (s + u) = 1 := collarBump_of_abs_le hR (by linarith [hab u hu])
    refine ContinuousLinearMap.ext_ring ?_
    change ((0 : EuclideanSpace ℝ (Fin 1)), (1 : ℝ) • (1 : ℝ)) =
      (1 : ℝ) • (((0 : EuclideanSpace ℝ (Fin 1)), collarBump R (s + u)) :
        EuclideanSpace ℝ (Fin 1) × ℝ)
    rw [hb, one_smul, one_smul]
  have hγ' : IsMIntegralCurveOn (fun u => collarFlowZ hR u (θ, s)) (collarField R)
      (Ioo (-(R / 8) - s) (R / 8 - s)) :=
    (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ _).isMIntegralCurveOn _
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0
    ((contMDiff_collarField R).of_le (by norm_num)) hγ hγ' (by
      rw [add_zero, collarFlowZ,
        DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_zero]
      rfl)
  exact (heq ht).symm

theorem compactSupportFlowDiffeomorph_eq_compactSupportFlow {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞ (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) (t : ℝ) (x : M) :
    DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph v hv hsupp t x =
      Diffeomorph.compactSupportFlow v hv hsupp t x :=
  rfl

theorem isCompact_collarMap_preimage {R : ℝ} (hsrc : ∀ θ s, |s| ≤ R → (θ, s) ∈ c.source) :
    IsCompact (collarMap F c ⁻¹' (univ ×ˢ Icc (-(R / 2)) (R / 2))) := by
  have hA : univ ×ˢ Icc (-(R / 2)) (R / 2) ⊆ c.source := by
    rintro ⟨θ, s⟩ ⟨-, hs⟩
    refine hsrc θ s ?_
    have h := abs_le.mpr ⟨hs.1, hs.2⟩
    have hR : 0 ≤ R := by linarith [abs_nonneg s, hs.1, hs.2]
    linarith
  have hK : IsCompact (c '' (univ ×ˢ Icc (-(R / 2)) (R / 2))) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (c.contMDiffOn.continuousOn.mono hA)
  have hKu := CircleFibration.isCompact_preimage F hK.isClosed
  have hsub : F.projection ⁻¹' (c '' (univ ×ˢ Icc (-(R / 2)) (R / 2))) ⊆
      range (Subtype.val : TopologicalSpace.Opens.comap F.projection (collarOpens c) → U) := by
    rintro x ⟨q, hq, hqx⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    change F.projection x ∈ c.target
    rw [← hqx]
    exact c.toPartialEquiv.map_source (hA hq)
  have hKc : IsCompact ((Subtype.val : TopologicalSpace.Opens.comap F.projection
      (collarOpens c) → U) ⁻¹' (F.projection ⁻¹' (c '' (univ ×ˢ Icc (-(R / 2)) (R / 2))))) :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).mpr hKu
  refine (hKc.image (collarTotalEquiv F c).continuous).of_isClosed_subset
    ((isClosed_univ.prod isClosed_Icc).preimage contMDiff_collarMap.continuous) ?_
  intro y hy
  refine ⟨(collarTotalEquiv F c).symm y, ?_, (collarTotalEquiv F c).apply_symm_apply y⟩
  change F.projection ((collarTotalEquiv F c).symm y).val ∈
    c '' (univ ×ˢ Icc (-(R / 2)) (R / 2))
  rw [← collarMap_eq]
  exact mem_image_of_mem _ hy

section CollarLift

variable {X : (y : CollarTotal F c) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) y}
  (hX : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)).tangent ∞
    (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (CollarTotal F c))))
  (hXc : IsCompact (tsupport X))

variable (X) in
open scoped Classical in
def collarLift (r : ℝ) (x : U) : U :=
  if hx : F.projection x ∈ c.target then
    ((collarTotalEquiv F c).symm
      (DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc r
        (collarTotalEquiv F c ⟨x, hx⟩))).val
  else x

theorem collarLift_of_mem {r : ℝ} {x : U} (hx : F.projection x ∈ c.target) :
    collarLift X hX hXc r x = ((collarTotalEquiv F c).symm
      (DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc r
        (collarTotalEquiv F c ⟨x, hx⟩))).val :=
  dite_eq_left hx

theorem collarLift_of_not_mem {r : ℝ} {x : U} (hx : F.projection x ∉ c.target) :
    collarLift X hX hXc r x = x :=
  dite_eq_right hx

theorem flowX_eq_self {y : CollarTotal F c} (hy : y ∉ tsupport X) (r : ℝ) :
    DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc r y = y := by
  rw [DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_apply]
  exact DifferentialGeometry.Analysis.ODE.curveAt_eq_self_of_not_mem_tsupport X hX _ hy r

theorem projection_collarLift_mem {r : ℝ} {x : U} (hx : F.projection x ∈ c.target) :
    F.projection (collarLift X hX hXc r x) ∈ c.target := by
  rw [collarLift_of_mem hX hXc hx]
  exact ((collarTotalEquiv F c).symm _).2

theorem collarLift_zero (x : U) : collarLift X hX hXc 0 x = x := by
  by_cases hx : F.projection x ∈ c.target
  · rw [collarLift_of_mem hX hXc hx,
      DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_zero]
    change ((collarTotalEquiv F c).symm (collarTotalEquiv F c ⟨x, hx⟩)).val = x
    rw [Diffeomorph.symm_apply_apply]
  · exact collarLift_of_not_mem hX hXc hx

theorem collarLift_add (s t : ℝ) (x : U) :
    collarLift X hX hXc (s + t) x = collarLift X hX hXc s (collarLift X hX hXc t x) := by
  by_cases hx : F.projection x ∈ c.target
  · have hm := projection_collarLift_mem hX hXc (r := t) hx
    have e : (⟨collarLift X hX hXc t x, hm⟩ : TopologicalSpace.Opens.comap F.projection
        (collarOpens c)) = (collarTotalEquiv F c).symm
          (DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc t
            (collarTotalEquiv F c ⟨x, hx⟩)) := Subtype.ext (collarLift_of_mem hX hXc hx)
    rw [collarLift_of_mem hX hXc hx, collarLift_of_mem hX hXc hm, e,
      Diffeomorph.apply_symm_apply, add_comm,
      ← DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_trans]
    rfl
  · rw [collarLift_of_not_mem hX hXc hx, collarLift_of_not_mem hX hXc hx,
      collarLift_of_not_mem hX hXc hx]

variable (X) in
def collarLiftCore : Set U :=
  Subtype.val '' ((collarTotalEquiv F c).symm '' tsupport X)

include hXc in
theorem isClosed_collarLiftCore : IsClosed (collarLiftCore (F := F) (c := c) X) :=
  ((hXc.image (collarTotalEquiv F c).symm.continuous).image continuous_subtype_val).isClosed

theorem projection_mem_of_mem_core {x : U} (hx : x ∈ collarLiftCore (F := F) (c := c) X) :
    F.projection x ∈ c.target := by
  obtain ⟨x', -, rfl⟩ := hx
  exact x'.2

theorem collarLift_eq_self {x : U} (hx : x ∉ collarLiftCore (F := F) (c := c) X) (r : ℝ) :
    collarLift X hX hXc r x = x := by
  by_cases hπ : F.projection x ∈ c.target
  · have hy : collarTotalEquiv F c ⟨x, hπ⟩ ∉ tsupport X := fun h =>
      hx ⟨⟨x, hπ⟩, ⟨_, h, (collarTotalEquiv F c).symm_apply_apply _⟩, rfl⟩
    rw [collarLift_of_mem hX hXc hπ, flowX_eq_self hX hXc hy, Diffeomorph.symm_apply_apply]
  · exact collarLift_of_not_mem hX hXc hπ

theorem contMDiff_collarLift :
    ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞
      (fun p : ℝ × U => collarLift X hX hXc p.1 p.2) := by
  rintro ⟨r₀, x₀⟩
  by_cases hx₀ : F.projection x₀ ∈ c.target
  · let O := TopologicalSpace.Opens.comap F.projection (collarOpens c)
    let W : TopologicalSpace.Opens (ℝ × U) := ⟨univ ×ˢ (O : Set U), isOpen_univ.prod O.isOpen⟩
    have hjoint : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (fun p : ℝ × CollarTotal F c =>
          DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc p.1
            p.2) :=
      DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport X hX hXc
    have hWO : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun w : W => (⟨w.val.2, w.2.2⟩ : O)) :=
      (ContMDiff.subtypeVal_comp_iff O _).mp (contMDiff_snd.comp contMDiff_subtype_val)
    have hin : ContMDiff (𝓘(ℝ, ℝ).prod C.model)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
        (fun w : W => (w.val.1, collarTotalEquiv F c ⟨w.val.2, w.2.2⟩)) :=
      (contMDiff_fst.comp contMDiff_subtype_val).prodMk
        ((collarTotalEquiv F c).contMDiff.comp hWO)
    have hg : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun w : W =>
        collarLift X hX hXc w.val.1 w.val.2) := by
      have h := contMDiff_subtype_val.comp ((collarTotalEquiv F c).symm.contMDiff.comp
        (hjoint.comp hin))
      refine h.congr fun w => ?_
      exact collarLift_of_mem hX hXc (r := w.val.1) w.2.2
    exact (contMDiffAt_subtype_iff (U := W) (f := fun p : ℝ × U => collarLift X hX hXc p.1 p.2)
      (x := ⟨(r₀, x₀), mem_univ _, hx₀⟩)).mp (hg ⟨(r₀, x₀), mem_univ _, hx₀⟩)
  · have hK : x₀ ∉ collarLiftCore (F := F) (c := c) X := fun h =>
      hx₀ (projection_mem_of_mem_core h)
    have hn : (univ ×ˢ (collarLiftCore (F := F) (c := c) X)ᶜ : Set (ℝ × U)) ∈ 𝓝 (r₀, x₀) :=
      (isOpen_univ.prod (isClosed_collarLiftCore hXc).isOpen_compl).mem_nhds ⟨mem_univ _, hK⟩
    refine contMDiff_snd.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hn] with p hp
    exact collarLift_eq_self hX hXc hp.2 p.1

def collarBase {R : ℝ} (hR : 0 < R) (r : ℝ) (b : F.base.Carrier) : F.base.Carrier := by
  classical
  exact if b ∈ c.target then c (collarFlowZ hR r (c.symm b)) else b

theorem projection_collarLift {R : ℝ} (hR : 0 < R)
    (hrel : ∀ t y, collarMap F c
      (DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X hX hXc t y) =
        collarFlowZ hR t (collarMap F c y)) (r : ℝ) (x : U) :
    F.projection (collarLift X hX hXc r x) = collarBase (c := c) hR r (F.projection x) := by
  by_cases hx : F.projection x ∈ c.target
  · rw [collarLift_of_mem hX hXc hx, ← collarMap_eq, hrel, collarBase, ite_eq_left hx]
    have e : collarMap F c (collarTotalEquiv F c ⟨x, hx⟩) = c.symm (F.projection x) := by
      change c.symm (F.projection ((collarTotalEquiv F c).symm
        (collarTotalEquiv F c ⟨x, hx⟩)).val) = c.symm (F.projection x)
      rw [Diffeomorph.symm_apply_apply]
    rw [e]
  · rw [collarLift_of_not_mem hX hXc hx, collarBase, ite_eq_right hx]

end CollarLift

theorem CircleFibration.exists_liftFlow (F : CircleFibration C U)
    (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞) {R : ℝ} (hR : 0 < R)
    (hsrc : ∀ θ s, |s| ≤ R → (θ, s) ∈ c.source) :
    ∃ L : LiftedBicollar F c, L.width = R / 8 ∧ L.reach = R := by
  obtain ⟨X, hrel, hsupp⟩ :=
    DifferentialGeometry.Topology.Ehresmann.exists_smoothDerivativeLift_of_surjective
      (collarMap F c) contMDiff_collarMap surjective_mfderiv_collarMap (collarField R)
      (contMDiff_collarField R)
  have hXc : IsCompact (tsupport X) :=
    (isCompact_collarMap_preimage hsrc).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans (preimage_mono (tsupport_collarField hR)))
  have hflow : ∀ t y, collarMap F c
      (DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph X X.contMDiff hXc t
        y) = collarFlowZ hR t (collarMap F c y) := fun t y =>
    DifferentialGeometry.Topology.Ehresmann.compactSupportFlowDiffeomorph_map_of_mfderiv_eq
      (collarMap F c) (contMDiff_collarMap.of_le (by norm_num)) X X.contMDiff hXc (collarField R)
      (contMDiff_collarField R) (isCompact_tsupport_collarField hR) hrel t y
  have hsm := contMDiff_collarLift X.contMDiff hXc
  have hsm1 : ∀ r : ℝ, ContMDiff C.model C.model ∞ (collarLift X X.contMDiff hXc r) :=
    fun r => hsm.comp (contMDiff_const.prodMk contMDiff_id)
  have hinv : ∀ r x, collarLift X X.contMDiff hXc (-r) (collarLift X X.contMDiff hXc r x) = x :=
    fun r x => by rw [← collarLift_add, neg_add_cancel, collarLift_zero]
  have hinv' : ∀ r x, collarLift X X.contMDiff hXc r (collarLift X X.contMDiff hXc (-r) x) = x :=
    fun r x => by rw [← collarLift_add, add_neg_cancel, collarLift_zero]
  have hsrc' : ∀ θ s, |s| < R / 8 → (θ, s) ∈ c.source := fun θ s hs =>
    hsrc θ s (by linarith)
  let Φ : ℝ → (U ≃ₘ⟮C.model, C.model⟯ U) := fun r =>
    { toFun := collarLift X X.contMDiff hXc r
      invFun := collarLift X X.contMDiff hXc (-r)
      left_inv := hinv r
      right_inv := hinv' r
      contMDiff_toFun := hsm1 r
      contMDiff_invFun := hsm1 (-r) }
  refine ⟨{ flow := Φ
            smooth := hsm
            flow_zero := collarLift_zero X.contMDiff hXc
            flow_add := collarLift_add X.contMDiff hXc
            baseFlow := collarBase hR
            projection_flow := projection_collarLift X.contMDiff hXc hR hflow
            width := R / 8
            width_pos := by positivity
            reach := R
            width_lt_reach := by linarith
            mem_source := hsrc
            baseFlow_apply := fun θ s r hs hsr => ?_
            baseFlow_eq_self := fun r b hb => ?_
            flow_eq_self := fun r x hx => ?_ }, rfl, rfl⟩
  · have hm := hsrc' θ s hs
    have e : c.symm (c (θ, s)) = (θ, s) := c.toPartialEquiv.left_inv hm
    rw [collarBase, ite_eq_left (c.toPartialEquiv.map_source hm)]
    change c (collarFlowZ hR r (c.symm (c (θ, s)))) = c (θ, s + r)
    rw [e, collarFlowZ_apply hR hs hsr]
  · by_cases hbt : b ∈ c.target
    · have hb' : R < |(c.symm b).2| := by
        by_contra h
        exact hb (c.symm b).1 (c.symm b).2 (not_lt.mp h) (c.toPartialEquiv.right_inv hbt).symm
      rw [collarBase, ite_eq_left hbt, collarFlowZ_eq_self hR (by linarith) r]
      exact c.toPartialEquiv.right_inv hbt
    · rw [collarBase, ite_eq_right hbt]
  · refine collarLift_eq_self X.contMDiff hXc ?_ r
    rintro ⟨x', hx', rfl⟩
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyA := tsupport_collarField hR (hsupp hy)
    have he : c (collarMap F c y) = F.projection ((collarTotalEquiv F c).symm y).val :=
      collarMap_eq y
    exact hx (collarMap F c y).1 (collarMap F c y).2
      (abs_le.mpr ⟨by linarith [hyA.2.1], by linarith [hyA.2.2]⟩) he.symm

end LiftFlow

section GlueInstances

variable {F : CircleFibration C U} {V₁ V₂ : TopologicalSpace.Opens F.base.Carrier}

theorem FibreCoordinate.glue_of_isSimplyConnected (τ₁ : FibreCoordinate F V₁)
    (τ₂ : FibreCoordinate F V₂)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (h₁ : τ₁.IsPositive (o.restrictOpen V₁)) (h₂ : τ₂.IsPositive (o.restrictOpen V₂))
    (ℓ : F.base.Carrier → ℝ) (hℓ : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ ℓ)
    (hℓ01 : ∀ b, 0 ≤ ℓ b ∧ ℓ b ≤ 1)
    (h₀ : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0) (h₁' : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1)
    (hsc : IsSimplyConnected ((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) :
      Set F.base.Carrier)) :
    ∃ τ : FibreCoordinate F (V₁ ⊔ V₂), τ.IsPositive (o.restrictOpen (V₁ ⊔ V₂)) ∧
      (∀ x : U, ℓ (F.projection x) = 0 → F.projection x ∈ V₁ → τ.angle x = τ₁.angle x) ∧
      (∀ x : U, ℓ (F.projection x) = 1 → F.projection x ∈ V₂ → τ.angle x = τ₂.angle x) := by
  obtain ⟨τ, hτ, hz, ho, -, -⟩ := τ₁.glue τ₂ o h₁ h₂ ℓ hℓ hℓ01 h₀ h₁'
    ⟨{V₁ ⊓ V₂}, le_antisymm (le_iSup₂_of_le (V₁ ⊓ V₂) (Finset.mem_singleton_self _) le_rfl)
      (iSup₂_le fun O' hO' => (Finset.mem_singleton.mp hO').le), by simp, by simpa using hsc⟩
  exact ⟨τ, hτ, hz, ho⟩

theorem FibreCoordinate.exists_glue_trivializationCharts
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (b₁ b₂ : F.base.Carrier) (hV₁ : V₁ ≤ F.neighborhood b₁) (hV₂ : V₂ ≤ F.neighborhood b₂)
    [ConnectedSpace V₁] [ConnectedSpace V₂]
    (ℓ : F.base.Carrier → ℝ) (hℓ : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ ℓ)
    (hℓ01 : ∀ b, 0 ≤ ℓ b ∧ ℓ b ≤ 1)
    (h₀ : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0) (h₁' : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1)
    (hsc : IsSimplyConnected ((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) :
      Set F.base.Carrier)) :
    ∃ τ : FibreCoordinate F (V₁ ⊔ V₂), τ.IsPositive (o.restrictOpen (V₁ ⊔ V₂)) ∧
      (∀ x : U, ℓ (F.projection x) = 0 → F.projection x ∈ V₁ →
        τ.angle x = (ofTrivialization F b₁).angle x ∨
          τ.angle x = ((ofTrivialization F b₁).angle x)⁻¹) ∧
      (∀ x : U, ℓ (F.projection x) = 1 → F.projection x ∈ V₂ →
        τ.angle x = (ofTrivialization F b₂).angle x ∨
          τ.angle x = ((ofTrivialization F b₂).angle x)⁻¹) := by
  obtain ⟨τ₁, hp₁, he₁⟩ := ((ofTrivialization F b₁).restrict hV₁).exists_isPositive
    (o.restrictOpen V₁)
  obtain ⟨τ₂, hp₂, he₂⟩ := ((ofTrivialization F b₂).restrict hV₂).exists_isPositive
    (o.restrictOpen V₂)
  obtain ⟨τ, hτ, hz, ho⟩ := τ₁.glue_of_isSimplyConnected τ₂ o hp₁ hp₂ ℓ hℓ hℓ01 h₀ h₁' hsc
  have key : ∀ {b : F.base.Carrier} {V : TopologicalSpace.Opens F.base.Carrier}
      (hV : V ≤ F.neighborhood b) (τ' : FibreCoordinate F V)
      (he : τ' = (ofTrivialization F b).restrict hV ∨
        τ' = ((ofTrivialization F b).restrict hV).conj)
      (x : U) (hx : F.projection x ∈ V),
      τ'.angle x = (ofTrivialization F b).angle x ∨
        τ'.angle x = ((ofTrivialization F b).angle x)⁻¹ := by
    intro b V hV τ' he x hx
    rcases he with rfl | rfl
    · exact Or.inl (angle_restrict _ hV x hx)
    · exact Or.inr (by rw [angle_conj _ x hx, angle_restrict _ hV x hx])
  refine ⟨τ, hτ, fun x h0 hx => ?_, fun x h1 hx => ?_⟩
  · rw [hz x h0 hx]
    exact key hV₁ τ₁ he₁ x hx
  · rw [ho x h1 hx]
    exact key hV₂ τ₂ he₂ x hx

end GlueInstances

end GC.Seifert
