import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothQuotient
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Morse.CriticalPoint

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.HorosphereProjection

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open BusemannCocycle (poConfFactor)
open Busemann (busemann horosphere)

section

variable {n : ℕ} (hn : 1 ≤ n) (P : Subgroup (PO n 1)) (ξ : BoundaryH n)
  (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
    poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ)

local notation "Q" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)
local notation "π" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))

theorem mem_image_horosphere_iff_quotientBusemann_eq (q : Q) :
    q ∈ π '' horosphere ξ c ↔ quotientBusemann hn P ξ hhor q = c := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · induction q using Quotient.inductionOn with
    | _ p => exact fun hp => ⟨p, hp, rfl⟩

private def quotientHorosphereLevelHomeomorph :
    (π '' horosphere ξ c) ≃ₜ {q : Q // quotientBusemann hn P ξ hhor q = c} where
  toFun q := ⟨q.val, (mem_image_horosphere_iff_quotientBusemann_eq hn P ξ hhor c q).mp q.property⟩
  invFun q := ⟨q.val, (mem_image_horosphere_iff_quotientBusemann_eq hn P ξ hhor c q).mpr q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem mem_image_open_horoball_iff_quotientBusemann_lt (q : Q) :
    q ∈ π '' {p : HUpper n | busemann ξ p < c} ↔ quotientBusemann hn P ξ hhor q < c := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · induction q using Quotient.inductionOn with
    | _ p => exact fun hp => ⟨p, hp, rfl⟩

def quotientOpenHoroball : TopologicalSpace.Opens Q where
  carrier := π '' {p : HUpper n | busemann ξ p < c}
  is_open' := by
    have he : π '' {p : HUpper n | busemann ξ p < c} =
        {q : Q | quotientBusemann hn P ξ hhor q < c} :=
      Set.ext (mem_image_open_horoball_iff_quotientBusemann_lt hn P ξ hhor c)
    rw [he]
    exact isOpen_lt (continuous_quotientBusemann hn P ξ hhor) continuous_const

@[simp] theorem mem_quotientOpenHoroball (q : Q) :
    q ∈ quotientOpenHoroball hn P ξ hhor c ↔ quotientBusemann hn P ξ hhor q < c :=
  mem_image_open_horoball_iff_quotientBusemann_lt hn P ξ hhor c q

end

variable {m : ℕ} (P : Subgroup (PO (m + 1) 1))

private local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction (Nat.le_add_left 1 m) P

private local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

private local instance :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ P (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable [ProperlyDiscontinuousSMul P (HUpper (m + 1))]
  [IsCancelSMul P (HUpper (m + 1))]
  (ξ : BoundaryH (m + 1))
  (hhor : ∀ γ : P, (poBoundaryMulAction (Nat.le_add_left 1 m)).smul (γ : PO (m + 1) 1) ξ = ξ ∧
    poConfFactor (Nat.le_add_left 1 m) (γ : PO (m + 1) 1) ξ = 1) (c : ℝ)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "L" => PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)
local notation "J" => ModelWithCorners.transContinuousLinearEquiv I L
local notation "Q" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "S" => (π '' horosphere ξ c)
local notation "B" => quotientBusemann (Nat.le_add_left 1 m) P ξ hhor

private theorem contMDiff_quotientBusemann_model : ContMDiff J 𝓘(ℝ, ℝ) ∞ B :=
  (L).contMDiff_transContinuousLinearEquiv_left.mpr (contMDiff_quotientBusemann P ξ hhor ∞)

private theorem quotientBusemann_model_regular (q : Q) : mfderiv J 𝓘(ℝ, ℝ) B q ≠ 0 := by
  intro hz
  exact mfderiv_quotientBusemann_ne_zero P ξ hhor q
    ((DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L B q).mp hz)

@[instance_reducible] def quotientHorosphereChartedSpace : ChartedSpace (Fin m → ℝ) S := by
  let _ := Manifold.RegularLevel.levelChartedSpace J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  exact Manifold.Homeomorph.pullbackChartedSpace
    (quotientHorosphereLevelHomeomorph (Nat.le_add_left 1 m) P ξ hhor c)

theorem isManifold_quotient_horosphere :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    IsManifold K ∞ S := by
  let _ := Manifold.RegularLevel.levelChartedSpace J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  let _ := Manifold.RegularLevel.levelIsManifold J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  exact Manifold.Homeomorph.instIsManifoldPullback
    (quotientHorosphereLevelHomeomorph (Nat.le_add_left 1 m) P ξ hhor c)

theorem contMDiff_quotient_horosphere_inclusion :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    ContMDiff K I ∞ (Subtype.val : S → Q) := by
  let _ := Manifold.RegularLevel.levelChartedSpace J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  let _ := Manifold.RegularLevel.levelIsManifold J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  have hi := Manifold.RegularLevel.contMDiff_level_inclusion J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  have he := Manifold.Homeomorph.contMDiff_pullback («I» := K) (n := ∞)
    (quotientHorosphereLevelHomeomorph (Nat.le_add_left 1 m) P ξ hhor c)
  exact (L).contMDiff_transContinuousLinearEquiv_right.mp (hi.comp he)

theorem contMDiff_quotient_horosphere_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {X : Type*} [TopologicalSpace X]
    [ChartedSpace H X] {IX : ModelWithCorners ℝ E H}
    {f : X → Q} (hf : ContMDiff IX I ∞ f) (hfS : ∀ x, f x ∈ S) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    ContMDiff IX K ∞ (fun x => (⟨f x, hfS x⟩ : S)) := by
  let _ := Manifold.RegularLevel.levelChartedSpace J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  let _ := Manifold.RegularLevel.levelIsManifold J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  have hF := Manifold.RegularLevel.contMDiff_level_factor J (a := c)
    (contMDiff_quotientBusemann_model P ξ hhor)
    (fun q _ => quotientBusemann_model_regular P ξ hhor q)
    ((L).contMDiff_transContinuousLinearEquiv_right.mpr hf)
    (fun x => (mem_image_horosphere_iff_quotientBusemann_eq (Nat.le_add_left 1 m) P ξ hhor c (f x)).mp (hfS x))
  have he := Manifold.Homeomorph.contMDiff_symm_pullback («I» := K) (n := ∞)
    (quotientHorosphereLevelHomeomorph (Nat.le_add_left 1 m) P ξ hhor c)
  exact he.comp hF

def quotientHorosphereDiffeomorph :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    Q ≃ₘ⟮I, (K).prod 𝓘(ℝ, ℝ)⟯ S × ℝ := by
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  let e := quotientHorosphereHomeomorph (Nat.le_add_left 1 m) P ξ hhor c
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hR : ContMDiff I I ∞ (fun q : Q => (e q).1.val) :=
      contMDiff_quotient_retract P ξ hhor c ∞
    have hfirst := contMDiff_quotient_horosphere_factor P ξ hhor c hR
      (fun q => (e q).1.property)
    have hsecond : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q : Q => (e q).2) :=
      contMDiff_const.sub (contMDiff_quotientBusemann P ξ hhor ∞)
    exact hfirst.prodMk hsecond
  · have hp : ContMDiff ((K).prod 𝓘(ℝ, ℝ)) ((I).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : S × ℝ => (z.1.val, z.2)) :=
      ((contMDiff_quotient_horosphere_inclusion P ξ hhor c).comp contMDiff_fst).prodMk
        contMDiff_snd
    exact (contMDiff_quotientRay P ξ (fun γ => (hhor γ).1) ∞).comp hp

theorem quotientHorosphereDiffeomorph_toHomeomorph :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    (quotientHorosphereDiffeomorph P ξ hhor c).toHomeomorph =
      quotientHorosphereHomeomorph (Nat.le_add_left 1 m) P ξ hhor c := rfl

@[simp] theorem quotientHorosphereDiffeomorph_apply_mk (p : HUpper (m + 1)) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    quotientHorosphereDiffeomorph P ξ hhor c (π p) =
      (⟨π (retract ξ c p), ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩⟩,
        c - busemann ξ p) := rfl

theorem quotientHorosphereDiffeomorph_symm_apply_mk (p : HUpper (m + 1))
    (hp : p ∈ horosphere ξ c) (t : ℝ) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    (quotientHorosphereDiffeomorph P ξ hhor c).symm
      (⟨π p, ⟨p, hp, rfl⟩⟩, t) = π (AsymptoticRays.rayTo p ξ t) := rfl

local notation "T" => (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi)
local notation "U" => quotientOpenHoroball (Nat.le_add_left 1 m) P ξ hhor c

def quotientOpenHoroballDiffeomorph :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    U ≃ₘ⟮I, (K).prod 𝓘(ℝ, ℝ)⟯ S × T := by
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  let e := quotientHorosphereDiffeomorph P ξ hhor c
  refine
    { toFun := fun q => ((e q.val).1, ⟨(e q.val).2, ?_⟩)
      invFun := fun z => ⟨e.symm (z.1, z.2.val), ?_⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · change 0 < c - B q.val
    exact sub_pos.mpr ((mem_quotientOpenHoroball (Nat.le_add_left 1 m) P ξ hhor c q.val).mp q.property)
  · apply (mem_quotientOpenHoroball (Nat.le_add_left 1 m) P ξ hhor c _).mpr
    have he := congrArg Prod.snd (e.apply_symm_apply (z.1, z.2.val))
    change c - B (e.symm (z.1, z.2.val)) = z.2.val at he
    have ht : 0 < z.2.val := z.2.property
    linarith
  · intro q
    apply Subtype.ext
    exact e.symm_apply_apply q.val
  · intro z
    apply Prod.ext
    · change (e (e.symm (z.1, z.2.val))).1 = z.1
      exact congrArg Prod.fst (e.apply_symm_apply (z.1, z.2.val))
    · apply Subtype.ext
      change (e (e.symm (z.1, z.2.val))).2 = z.2.val
      exact congrArg Prod.snd (e.apply_symm_apply (z.1, z.2.val))
  · have hs : ContMDiff I ((K).prod 𝓘(ℝ, ℝ)) ∞ (fun q : U => e q.val) :=
      e.contMDiff.comp contMDiff_subtype_val
    apply hs.fst.prodMk
    apply (Manifold.contMDiff_subtypeVal_comp_iff T _).mp
    exact hs.snd
  · apply (Manifold.contMDiff_subtypeVal_comp_iff U _).mp
    have hs : ContMDiff ((K).prod 𝓘(ℝ, ℝ)) ((K).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : S × T => (z.1, z.2.val)) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    exact e.symm.contMDiff.comp hs

theorem quotientOpenHoroballDiffeomorph_apply (q : U) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    ((quotientOpenHoroballDiffeomorph P ξ hhor c q).1,
      (quotientOpenHoroballDiffeomorph P ξ hhor c q).2.val) =
        quotientHorosphereHomeomorph (Nat.le_add_left 1 m) P ξ hhor c q.val := rfl

@[simp] theorem quotientOpenHoroballDiffeomorph_apply_mk (p : HUpper (m + 1))
    (hp : busemann ξ p < c) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    quotientOpenHoroballDiffeomorph P ξ hhor c ⟨π p, ⟨p, hp, rfl⟩⟩ =
      (⟨π (retract ξ c p), ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩⟩,
        ⟨c - busemann ξ p, sub_pos.mpr hp⟩) := rfl

theorem quotientOpenHoroballDiffeomorph_symm_apply_mk (p : HUpper (m + 1))
    (hp : p ∈ horosphere ξ c) (t : T) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    ((quotientOpenHoroballDiffeomorph P ξ hhor c).symm
      (⟨π p, ⟨p, hp, rfl⟩⟩, t)).val = π (AsymptoticRays.rayTo p ξ t.val) := rfl

@[simp] theorem quotientOpenHoroballDiffeomorph_depth (q : U) :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    (quotientOpenHoroballDiffeomorph P ξ hhor c q).2.val = c - B q.val := rfl

end DifferentialGeometry.HorosphereProjection
