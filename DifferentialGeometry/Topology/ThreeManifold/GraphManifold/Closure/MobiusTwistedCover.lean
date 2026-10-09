import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MobiusRegularCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus

/-!
# Circle-fibration descent through an actual twisted Möbius double cover

The base two-sheet cover and local trivializations are derived from actual smooth
cover maps. The fibre involution is inversion, and no target trivialization is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

universe u

abbrev MobiusCoverBase := Circle × unitInterval

abbrev mobiusCoverBaseModel := (𝓡 1).prod (𝓡∂ 1)

abbrev mobiusTwistedCoverModel := mobiusCoverBaseModel.prod (𝓡 1)

def mobiusTwistedBaseDeck (p : MobiusCoverBase) : MobiusCoverBase :=
  (-p.1, unitInterval.symm p.2)

def mobiusTwistedDeck (p : MobiusCoverBase × Circle) : MobiusCoverBase × Circle :=
  (mobiusTwistedBaseDeck p.1, p.2⁻¹)

private theorem mobiusTwistedBaseDeck_ne (p : MobiusCoverBase) :
    mobiusTwistedBaseDeck p ≠ p := by
  intro h
  have hz := congrArg (fun q : MobiusCoverBase => (q.1 : ℂ)) h
  change -(p.1 : ℂ) = (p.1 : ℂ) at hz
  have hzero : (p.1 : ℂ) = 0 := by linear_combination -(1 / 2 : ℂ) * hz
  exact Circle.coe_ne_zero p.1 hzero

theorem mobiusRegularBaseParam_eq_iff (p q : MobiusCoverBase) :
    mobiusRegularBaseParam.{u} p = mobiusRegularBaseParam.{u} q ↔
      q = p ∨ q = mobiusTwistedBaseDeck p := by
  constructor
  · intro h
    have hs := congrArg (fun x : mobiusSurface.{u}.Carrier => mobiusSq x.val.down) h
    have hv := congrArg (fun x : mobiusSurface.{u}.Carrier => mobiusVec x.val.down) h
    have hs' : (p.1 : ℂ) ^ 2 = (q.1 : ℂ) ^ 2 := by
      change (Circle.exp (2 * Complex.arg (p.1 : ℂ)) : ℂ) =
        (Circle.exp (2 * Complex.arg (q.1 : ℂ)) : ℂ) at hs
      simpa only [← circleExp_sq, Circle.exp_arg] using hs
    change mobiusVec (mobiusBandCover (p.1, 2 * (p.2 : ℝ) - 1)) =
      mobiusVec (mobiusBandCover (q.1, 2 * (q.2 : ℝ) - 1)) at hv
    rw [mobiusVec_cover, mobiusVec_cover, Complex.real_smul, Complex.real_smul] at hv
    have hpq : ((q.1 : ℂ) - (p.1 : ℂ)) * ((q.1 : ℂ) + (p.1 : ℂ)) = 0 := by
      linear_combination -hs'
    rcases mul_eq_zero.mp hpq with he | he
    · have hz : q.1 = p.1 := Circle.ext (sub_eq_zero.mp he)
      left
      refine Prod.ext hz (Subtype.ext ?_)
      rw [hz] at hv
      have hh := mul_right_cancel₀ (Circle.coe_ne_zero p.1) hv
      have hh' := congrArg Complex.re hh
      simp only [Complex.ofReal_re] at hh'
      linarith
    · have hz : q.1 = -p.1 := Circle.ext (eq_neg_of_add_eq_zero_left he)
      right
      refine Prod.ext hz (Subtype.ext ?_)
      rw [hz, Circle.coe_neg, mul_neg] at hv
      have hh : ((2 * (p.2 : ℝ) - 1 : ℝ) : ℂ) =
          -((2 * (q.2 : ℝ) - 1 : ℝ) : ℂ) := by
        apply mul_right_cancel₀ (Circle.coe_ne_zero p.1)
        simpa only [neg_mul] using hv
      have hh' := congrArg Complex.re hh
      simp only [Complex.ofReal_re, Complex.neg_re] at hh'
      change (q.2 : ℝ) = 1 - (p.2 : ℝ)
      linarith
  · rintro (rfl | rfl)
    · rfl
    · exact (mobiusRegularBaseParam_deck p).symm

private theorem isLocalDiffeomorph_circleExp :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp := by
  let D := (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 (1 / (2 * Real.pi)) (by positivity))).toDiffeomorph
  have he : AnnulusStraightening.cexp ∘ D = Circle.exp := by
    funext t
    rw [Function.comp_apply, AnnulusStraightening.cexp_eq]
    change Circle.exp (2 * Real.pi * ((1 / (2 * Real.pi)) * t)) = Circle.exp t
    congr 1
    field_simp
  rw [← he]
  exact DifferentialGeometry.isLocalDiffeomorph_comp
    AnnulusStraightening.isLocalDiffeomorph_cexp D.isLocalDiffeomorph

private theorem isLocalDiffeomorph_mobiusBandCover :
    IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusBandCover := by
  intro p
  let q := (Complex.arg (p.1 : ℂ), p.2)
  have hE := (isLocalDiffeomorph_circleExp.prodMap
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph) q
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hE
  have hP : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (mobiusBandCover ∘ Prod.map Circle.exp id) q := by
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.Eventually.of_forall (fun a : ℝ × ℝ => mobiusBandCover_exp a.1 a.2))
    exact isLocalDiffeomorph_mobiusProj q
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp hP hE
  simpa only [q, Prod.map_apply, id_eq, Circle.exp_arg] using h

private def mobiusBaseIntervalCoordinates (p : MobiusCoverBase) : Circle × ℝ :=
  (p.1, 2 * (p.2 : ℝ) - 1)

private theorem contMDiff_mobiusBaseIntervalCoordinates :
    ContMDiff mobiusCoverBaseModel ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      mobiusBaseIntervalCoordinates :=
  contMDiff_fst.prodMk
    ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).sub contMDiff_const)

private theorem mobiusIntervalCoordinates_norm (p : Circle × ℝ)
    (h : mobiusWidth (mobiusBandCover p) ≤ 1) :
    (p.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
  rw [mobiusWidth_cover] at h
  have hsq := sq_le_one_iff_abs_le_one p.2 |>.mp h
  rw [abs_le] at hsq
  constructor <;> linarith [hsq.1, hsq.2]

theorem isLocalDiffeomorph_mobiusRegularBaseParam :
    IsLocalDiffeomorph mobiusCoverBaseModel (SurfaceModel.model mobiusSurface.{u}.kind)
      ∞ mobiusRegularBaseParam.{u} := by
  intro p
  let : ChartedSpace (EuclideanHalfSpace 2) mobiusSurface.{u}.Carrier :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 2) mobiusSet.{u})
  let A : Circle × ℝ → MobiusLift.{u} := fun q => ULift.up (mobiusBandCover q)
  have hA : IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ A :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (uliftDiffeomorph 𝓘(ℝ, ℝ × ℝ) MobiusBand).isLocalDiffeomorph
      isLocalDiffeomorph_mobiusBandCover
  obtain ⟨γ, hpγ, hEq⟩ := hA (mobiusBaseIntervalCoordinates p)
  let V : TopologicalSpace.Opens mobiusSurface.{u}.Carrier :=
    ⟨Subtype.val ⁻¹' γ.target, γ.open_target.preimage continuous_subtype_val⟩
  have hright (w : V) : A (γ.symm w.val.val) = w.val.val :=
    (hEq (γ.toPartialEquiv.map_target w.property)).trans
      (γ.toPartialEquiv.right_inv w.property)
  have hbound (w : V) : ((γ.symm w.val.val).2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    apply mobiusIntervalCoordinates_norm
    have h := w.val.property
    change mobiusWidth w.val.val.down ≤ 1 at h
    rwa [← hright w] at h
  let R : mobiusSurface.{u}.Carrier → MobiusCoverBase := fun w =>
    ((γ.symm w.val).1, Set.projIcc 0 1 zero_le_one (((γ.symm w.val).2 + 1) / 2))
  have hraw : ContMDiff (SurfaceModel.model mobiusSurface.{u}.kind)
      ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (fun w : V => γ.symm w.val.val) := by
    change ContMDiff (𝓡∂ 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun w : V => γ.symm w.val.val)
    exact γ.symm.contMDiffOn.comp_contMDiff
      (mobiusAtlas.contMDiff_subtype_val.comp contMDiff_subtype_val)
      (fun w => w.property)
  have hreal : ContMDiff (SurfaceModel.model mobiusSurface.{u}.kind)
      𝓘(ℝ, ℝ) ∞ (fun w : V => ((γ.symm w.val.val).2 + 1) / 2) :=
    ((contMDiff_snd.comp hraw).add contMDiff_const).div₀ contMDiff_const
      (fun w => by norm_num)
  have hinterval : ContMDiff (SurfaceModel.model mobiusSurface.{u}.kind) (𝓡∂ 1) ∞
      (fun w : V => (R w.val).2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨(continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
      hreal.continuous, ?_⟩
    convert hreal using 1
    funext w
    exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (hbound w))
  have hRsmooth : ContMDiff (SurfaceModel.model mobiusSurface.{u}.kind)
      mobiusCoverBaseModel ∞ (fun w : V => R w.val) :=
    (contMDiff_fst.comp hraw).prodMk hinterval
  have hRi (w : V) : mobiusBaseIntervalCoordinates (R w.val) = γ.symm w.val.val := by
    apply Prod.ext
    · rfl
    change 2 * (Set.projIcc 0 1 zero_le_one (((γ.symm w.val.val).2 + 1) / 2) : ℝ) - 1 = _
    rw [Set.projIcc_of_mem zero_le_one (hbound w)]
    ring
  let Φ : PartialDiffeomorph mobiusCoverBaseModel
      (SurfaceModel.model mobiusSurface.{u}.kind) MobiusCoverBase mobiusSurface.{u}.Carrier ∞ :=
    { toFun := mobiusRegularBaseParam
      invFun := R
      source := mobiusBaseIntervalCoordinates ⁻¹' γ.source
      target := V
      map_source' := by
        intro q hq
        change A (mobiusBaseIntervalCoordinates q) ∈ γ.target
        rw [hEq hq]
        exact γ.toPartialEquiv.map_source hq
      map_target' := by
        intro w hw
        change mobiusBaseIntervalCoordinates (R w) ∈ γ.source
        rw [hRi ⟨w, hw⟩]
        exact γ.toPartialEquiv.map_target hw
      left_inv' := by
        intro q hq
        change ((γ.symm (A (mobiusBaseIntervalCoordinates q))).1,
          Set.projIcc 0 1 zero_le_one
            (((γ.symm (A (mobiusBaseIntervalCoordinates q))).2 + 1) / 2)) = q
        rw [hEq hq]
        have hc : γ.symm.toPartialEquiv (γ.toPartialEquiv
            (mobiusBaseIntervalCoordinates q)) = mobiusBaseIntervalCoordinates q :=
          γ.toPartialEquiv.left_inv hq
        rw [hc]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change (Set.projIcc 0 1 zero_le_one ((2 * (q.2 : ℝ) - 1 + 1) / 2) : ℝ) = _
          rw [show (2 * (q.2 : ℝ) - 1 + 1) / 2 = q.2 by ring, Set.projIcc_val]
      right_inv' := by
        intro w hw
        apply Subtype.ext
        change A (mobiusBaseIntervalCoordinates (R w)) = w.val
        rw [hRi ⟨w, hw⟩]
        exact hright ⟨w, hw⟩
      open_source := γ.open_source.preimage contMDiff_mobiusBaseIntervalCoordinates.continuous
      open_target := V.isOpen
      contMDiffOn_toFun := contMDiff_mobiusRegularBaseParam.contMDiffOn
      contMDiffOn_invFun := by
        intro w hw
        have h := hRsmooth.contMDiffAt (x := (⟨w, hw⟩ : V))
        exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt }
  exact ⟨Φ, hpγ, fun q hq => rfl⟩

section Descent

variable {C : CompactCarrier.{u}}
  (Ψ : MobiusCoverBase × Circle → C.Carrier) (honto : Function.Surjective Ψ)
  (hrel : ∀ p q, Ψ p = Ψ q ↔ q = p ∨ q = mobiusTwistedDeck p)

private def twistedCoverProjection : C.Carrier → mobiusSurface.{u}.Carrier :=
  fun c => mobiusRegularBaseParam (Function.surjInv honto c).1

include hrel

private theorem twistedCoverProjection_apply (p : MobiusCoverBase × Circle) :
    twistedCoverProjection Ψ honto (Ψ p) = mobiusRegularBaseParam p.1 := by
  change mobiusRegularBaseParam (Function.surjInv honto (Ψ p)).1 = _
  rcases (hrel p (Function.surjInv honto (Ψ p))).mp
      (Function.surjInv_eq honto (Ψ p)).symm with he | he
  · rw [he]
  · rw [he]
    exact mobiusRegularBaseParam_deck p.1

private theorem contMDiff_twistedCoverProjection
    (hl : IsLocalDiffeomorph mobiusTwistedCoverModel C.model ∞ Ψ) :
    ContMDiff C.model (SurfaceModel.model mobiusSurface.{u}.kind) ∞
      (twistedCoverProjection Ψ honto) := by
  have hcomp : ContMDiff mobiusTwistedCoverModel
      (SurfaceModel.model mobiusSurface.{u}.kind) ∞
      (twistedCoverProjection Ψ honto ∘ Ψ) := by
    convert contMDiff_mobiusRegularBaseParam.comp contMDiff_fst using 1
    funext p
    exact twistedCoverProjection_apply Ψ honto hrel p
  intro c
  obtain ⟨p, rfl⟩ := honto c
  exact (hl p).contMDiffAt_of_comp hcomp.contMDiffAt

private def twistedCoverProjectionMap
    (hl : IsLocalDiffeomorph mobiusTwistedCoverModel C.model ∞ Ψ) :
    C((⊤ : TopologicalSpace.Opens C.Carrier), mobiusSurface.{u}.Carrier) :=
  ⟨fun c => twistedCoverProjection Ψ honto c.val,
    (contMDiff_twistedCoverProjection Ψ honto hrel hl).continuous.comp continuous_subtype_val⟩

private theorem exists_twistedCoverTrivialization
    (hl : IsLocalDiffeomorph mobiusTwistedCoverModel C.model ∞ Ψ)
    (b : mobiusSurface.{u}.Carrier) :
    ∃ V : TopologicalSpace.Opens mobiusSurface.{u}.Carrier, b ∈ V ∧
    ∃ e : ↥(TopologicalSpace.Opens.comap (twistedCoverProjectionMap Ψ honto hrel hl) V)
        ≃ₘ⟮C.model, (SurfaceModel.model mobiusSurface.{u}.kind).prod (𝓡 1)⟯ (V × Circle),
      ∀ x, (e x).1.val = (twistedCoverProjectionMap Ψ honto hrel hl) x.val := by
  let a := Function.surjInv mobiusRegularBaseParam_surjective b
  have ha : mobiusRegularBaseParam a = b := Function.surjInv_eq _ b
  let hπ := isLocalDiffeomorph_mobiusRegularBaseParam a
  let V : TopologicalSpace.Opens mobiusSurface.{u}.Carrier :=
    ⟨hπ.localInverse.source, hπ.localInverse.open_source⟩
  have hb : b ∈ V := ha ▸ hπ.localInverse_mem_source
  let α : V → MobiusCoverBase := fun v => hπ.localInverse v.val
  have hα : IsLocalDiffeomorph (SurfaceModel.model mobiusSurface.{u}.kind)
      mobiusCoverBaseModel ∞ α :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open V
      (fun v => hπ.localInverse.isLocalDiffeomorphAt _ _ ∞ v.property)
  have hαbase (v : V) : mobiusRegularBaseParam (α v) = v.val :=
    hπ.localInverse_right_inv v.property
  let P := twistedCoverProjectionMap Ψ honto hrel hl
  let W := TopologicalSpace.Opens.comap P V
  let f : V × Circle → C.Carrier := fun q => Ψ (α q.1, q.2)
  have hf : IsLocalDiffeomorph
      ((SurfaceModel.model mobiusSurface.{u}.kind).prod (𝓡 1)) C.model ∞ f :=
    DifferentialGeometry.isLocalDiffeomorph_comp hl
      (hα.prodMap (Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph)
  have hfP (q : V × Circle) : twistedCoverProjection Ψ honto (f q) = q.1.val :=
    (twistedCoverProjection_apply Ψ honto hrel (α q.1, q.2)).trans (hαbase q.1)
  let fU : V × Circle → (⊤ : TopologicalSpace.Opens C.Carrier) :=
    fun q => ⟨f q, mem_univ (f q)⟩
  have hfW (q : V × Circle) : fU q ∈ W := by
    change twistedCoverProjection Ψ honto (f q) ∈ V
    rw [hfP q]
    exact q.1.property
  let E : V × Circle → W := fun q => ⟨fU q, hfW q⟩
  have hE : IsLocalDiffeomorph
      ((SurfaceModel.model mobiusSurface.{u}.kind).prod (𝓡 1)) C.model ∞ E := by
    intro q
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hfW
      (DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
        (fun r => mem_univ (f r)) (hf q))
  have hEinj : Function.Injective E := by
    intro q r he
    have hc := congrArg (fun w : W => w.val.val) he
    rcases (hrel (α q.1, q.2) (α r.1, r.2)).mp hc with hs | hs
    · have hsbase : α r.1 = α q.1 :=
        congrArg (fun p : MobiusCoverBase × Circle => p.1) hs
      apply Prod.ext
      · apply Subtype.ext
        exact (hαbase q.1).symm.trans
          ((congrArg mobiusRegularBaseParam hsbase.symm).trans (hαbase r.1))
      · exact (congrArg (fun p : MobiusCoverBase × Circle => p.2) hs).symm
    · have hsbase : α r.1 = mobiusTwistedBaseDeck (α q.1) :=
        congrArg (fun p : MobiusCoverBase × Circle => p.1) hs
      have hqr : r.1 = q.1 := by
        apply Subtype.ext
        exact (hαbase r.1).symm.trans
          ((congrArg mobiusRegularBaseParam hsbase).trans
            ((mobiusRegularBaseParam_deck (α q.1)).trans (hαbase q.1)))
      have hfix : mobiusTwistedBaseDeck (α q.1) = α q.1 :=
        hsbase.symm.trans (congrArg α hqr)
      exact False.elim (mobiusTwistedBaseDeck_ne (α q.1) hfix)
  have hEsurj : Function.Surjective E := by
    intro w
    obtain ⟨p, hp⟩ := honto w.val.val
    have hpb : mobiusRegularBaseParam p.1 ∈ V := by
      rw [← twistedCoverProjection_apply Ψ honto hrel p, hp]
      exact w.property
    let v : V := ⟨mobiusRegularBaseParam p.1, hpb⟩
    have hπeq : mobiusRegularBaseParam p.1 = mobiusRegularBaseParam (α v) :=
      (hαbase v).symm
    rcases (mobiusRegularBaseParam_eq_iff p.1 (α v)).mp hπeq with hs | hs
    · refine ⟨(v, p.2), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change Ψ (α v, p.2) = w.val.val
      rw [hs]
      exact hp
    · refine ⟨(v, p.2⁻¹), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change Ψ (α v, p.2⁻¹) = w.val.val
      rw [hs]
      exact ((hrel p (mobiusTwistedDeck p)).mpr (Or.inr rfl)).symm.trans hp
  let D := hE.diffeomorphOfBijective ⟨hEinj, hEsurj⟩
  refine ⟨V, hb, D.symm, ?_⟩
  intro x
  have h := hfP (D.symm x)
  have he : f (D.symm x) = x.val.val :=
    congrArg (fun w : W => w.val.val) (D.apply_symm_apply x)
  rw [he] at h
  exact h.symm

end Descent

theorem exists_circleFibration_of_mobiusCover
    (C : CompactCarrier.{u})
    (Ψ : (Circle × unitInterval) × Circle → C.Carrier)
    (hl : IsLocalDiffeomorph (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model ∞ Ψ)
    (honto : Function.Surjective Ψ)
    (hrel : ∀ p q, Ψ p = Ψ q ↔ q = p ∨ q = mobiusTwistedDeck p) :
    ∃ F : CircleFibration C ⊤, ∃ hbase : F.base = mobiusSurface.{u},
      ∀ p, hbase ▸ F.projection ⟨Ψ p, Set.mem_univ (Ψ p)⟩ =
        mobiusRegularBaseParam.{u} p.1 := by
  choose V hV e he using exists_twistedCoverTrivialization Ψ honto hrel hl
  let P := twistedCoverProjectionMap Ψ honto hrel hl
  have hPonto : Function.Surjective P := by
    intro b
    let a := Function.surjInv mobiusRegularBaseParam_surjective b
    refine ⟨⟨Ψ (a, 1), mem_univ (Ψ (a, 1))⟩, ?_⟩
    exact (twistedCoverProjection_apply Ψ honto hrel (a, 1)).trans
      (Function.surjInv_eq mobiusRegularBaseParam_surjective b)
  let F : CircleFibration C ⊤ :=
    { base := mobiusSurface
      projection := P
      surjective := hPonto
      smooth := (contMDiff_twistedCoverProjection Ψ honto hrel hl).comp contMDiff_subtype_val
      neighborhood := V
      mem_neighborhood := hV
      trivialization := e
      projection_trivialization := he }
  exact ⟨F, rfl, fun p => twistedCoverProjection_apply Ψ honto hrel p⟩

end GC.GraphManifold
