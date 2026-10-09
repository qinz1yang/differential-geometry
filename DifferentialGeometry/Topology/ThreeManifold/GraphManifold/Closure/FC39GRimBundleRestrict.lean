import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# FC39 GROUP G, RIMBOX R1: the row circle bundle restricted to an open set of its base

External draft 58 §三 R1, lead disposition D58-4 (lane FC39-G-RIMBOX, suffix `_GRIM`). The final
circle region of the adapted edge–rim data has base an open set `U ⊆ Pr.globalFaces.base`, domain
the WHOLE circle preimage of `U`, projection the restricted projection and the restricted
trivializations; the link to the row bundle is `ι = Subtype.val`. This file builds the bundle part
of that restriction for an arbitrary `CircleBundle` and an arbitrary open `O` of its base (the same
construction as the circle-region version `CircleRegion.restrictBase`,
`AssemblySphereRecCircle.lean:129–300`, which only reads the bundle fields):

* `CircleBundle.restrictDomain_GRIM`, `restrictProj_GRIM` (smooth, a submersion),
  `restrictNeighborhood_GRIM`, `restrictTrivialization_GRIM` (with
  `restrictProjection_trivialization_GRIM`);
* the link facts for `ι = Subtype.val`: `restrictDomain_eq_GRIM` (`CircleRestrictionLink.domain_eq`),
  `restrictProj_eq_GRIM` (`proj_eq`), `isOpenEmbedding_val_GRIM`, `contMDiff_val_GRIM`,
  `mfderiv_val_bijective_GRIM` (`ι_isOpenEmbedding`, `ι_smooth`, `ι_mfderiv`);
* `tube_restrict_GRIM`: the saturated preimage of a base set inside `O` is unchanged (this gives
  `CircleRestrictionLink.region_eq` once the cornered base is the preimage of `C₁ ⊆ O`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

namespace CircleBundle

variable (R : CircleBundle W)

/-! ## The restricted domain and projection -/

/-- The saturated domain over an open set `O` of the base. -/
def restrictDomain_GRIM (O : TopologicalSpace.Opens R.Base) : TopologicalSpace.Opens W.Carrier :=
  ⟨{x | ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O}, by
    have hset : {x | ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O} =
        Subtype.val '' (R.proj ⁻¹' (O : Set R.Base)) := by
      ext x
      constructor
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
    rw [hset]
    exact R.domain.isOpen.isOpenMap_subtype_val _ (O.isOpen.preimage R.proj.continuous)⟩

variable {R} in
theorem mem_restrictDomain_GRIM {O : TopologicalSpace.Opens R.Base} {x : W.Carrier} :
    x ∈ R.restrictDomain_GRIM O ↔ ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O :=
  Iff.rfl

theorem restrictDomain_le_GRIM (O : TopologicalSpace.Opens R.Base) :
    R.restrictDomain_GRIM O ≤ R.domain :=
  fun _ hx => hx.fst

/-- The projection over the open set `O`. -/
def restrictProj_GRIM (O : TopologicalSpace.Opens R.Base) : C(R.restrictDomain_GRIM O, O) where
  toFun x :=
    ⟨R.proj (TopologicalSpace.Opens.inclusion (R.restrictDomain_le_GRIM O) x), x.2.snd⟩
  continuous_toFun :=
    (R.proj.continuous.comp (continuous_inclusion (R.restrictDomain_le_GRIM O))).subtype_mk _

theorem restrictProj_val_GRIM (O : TopologicalSpace.Opens R.Base)
    (x : R.restrictDomain_GRIM O) :
    (R.restrictProj_GRIM O x : R.Base) =
      R.proj (TopologicalSpace.Opens.inclusion (R.restrictDomain_le_GRIM O) x) :=
  rfl

theorem contMDiff_restrictProj_GRIM (O : TopologicalSpace.Opens R.Base) :
    ContMDiff W.model (𝓡 2) ∞ (R.restrictProj_GRIM O) :=
  (ContMDiff.subtypeVal_comp_iff O _).mp
    (R.proj_smooth.comp (contMDiff_inclusion (R.restrictDomain_le_GRIM O)))

theorem mfderiv_restrictProj_GRIM (O : TopologicalSpace.Opens R.Base)
    (x : R.restrictDomain_GRIM O) :
    mfderiv W.model (𝓡 2) (R.restrictProj_GRIM O) x =
      mfderiv W.model (𝓡 2) R.proj
        (TopologicalSpace.Opens.inclusion (R.restrictDomain_le_GRIM O) x) := by
  rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp O (R.restrictProj_GRIM O) x]
  change mfderiv W.model (𝓡 2)
    (R.proj ∘ TopologicalSpace.Opens.inclusion (R.restrictDomain_le_GRIM O)) x = _
  rw [mfderiv_comp x (R.proj_smooth.mdifferentiableAt (by simp))
    ((contMDiff_inclusion (R.restrictDomain_le_GRIM O)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)),
    DifferentialGeometry.mfderiv_opens_incl]
  rfl

/-- The restricted projection is a submersion. -/
theorem restrictProj_submersion_GRIM (O : TopologicalSpace.Opens R.Base)
    (x : R.restrictDomain_GRIM O) :
    Surjective (mfderiv W.model (𝓡 2) (R.restrictProj_GRIM O) x) := by
  rw [R.mfderiv_restrictProj_GRIM O x]
  exact R.proj_submersion _

/-! ## The restricted trivializations -/

/-- The base neighbourhoods over `O`. -/
def restrictNeighborhood_GRIM (O : TopologicalSpace.Opens R.Base) (b : O) :
    TopologicalSpace.Opens O :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (R.neighborhood b.val)

theorem mem_restrictNeighborhood_GRIM (O : TopologicalSpace.Opens R.Base) (b : O) :
    b ∈ R.restrictNeighborhood_GRIM O b :=
  R.mem_neighborhood b.val

section Triv

variable (O : TopologicalSpace.Opens R.Base) (b : O)

/-- The old trivialization domain point of a point of the restricted trivialization domain. -/
def restrictTrivIn_GRIM
    (x : TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b)) :
    TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) :=
  ⟨TopologicalSpace.Opens.inclusion (R.restrictDomain_le_GRIM O) x.val, x.2⟩

theorem trivialization_fst_val_GRIM
    (a : TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val)) :
    ((R.trivialization b.val a).1).val = R.proj a.val :=
  R.projection_trivialization b.val a

/-- The restricted trivialization, forward map. -/
def restrictTrivFun_GRIM
    (x : TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b)) :
    R.restrictNeighborhood_GRIM O b × Circle :=
  (⟨⟨((R.trivialization b.val (R.restrictTrivIn_GRIM O b x)).1).val, by
      rw [R.trivialization_fst_val_GRIM]
      exact x.val.2.snd⟩, ((R.trivialization b.val (R.restrictTrivIn_GRIM O b x)).1).2⟩,
    (R.trivialization b.val (R.restrictTrivIn_GRIM O b x)).2)

/-- The restricted trivialization, inverse map. -/
def restrictTrivInv_GRIM (y : R.restrictNeighborhood_GRIM O b × Circle) :
    TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b) :=
  let a := (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)
  have ha : R.proj a.val = y.1.val.val := by
    rw [← R.trivialization_fst_val_GRIM, Diffeomorph.apply_symm_apply]
  ⟨⟨a.val.val, a.val.2, by
      change R.proj a.val ∈ O
      rw [ha]
      exact y.1.val.2⟩, by
    change R.proj a.val ∈ R.neighborhood b.val
    rw [ha]
    exact y.1.2⟩

theorem restrictTrivInv_in_GRIM (y : R.restrictNeighborhood_GRIM O b × Circle) :
    R.restrictTrivIn_GRIM O b (R.restrictTrivInv_GRIM O b y) =
      (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2) :=
  rfl

theorem restrictTrivFun_in_GRIM
    (x : TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b)) :
    (R.trivialization b.val).symm
        (⟨(R.restrictTrivFun_GRIM O b x).1.val.val, (R.restrictTrivFun_GRIM O b x).1.2⟩,
          (R.restrictTrivFun_GRIM O b x).2) = R.restrictTrivIn_GRIM O b x := by
  rw [show (⟨(R.restrictTrivFun_GRIM O b x).1.val.val, (R.restrictTrivFun_GRIM O b x).1.2⟩,
      (R.restrictTrivFun_GRIM O b x).2) = R.trivialization b.val (R.restrictTrivIn_GRIM O b x)
      from rfl,
    Diffeomorph.symm_apply_apply]

theorem contMDiff_restrictTrivIn_GRIM :
    ContMDiff W.model W.model ∞ (R.restrictTrivIn_GRIM O b) := by
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model W.model ∞
      (fun x : TopologicalSpace.Opens.comap (R.restrictProj_GRIM O)
          (R.restrictNeighborhood_GRIM O b) => (x.val.val : W.Carrier)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  exact h

theorem contMDiff_restrictTrivFun_GRIM :
    ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞ (R.restrictTrivFun_GRIM O b) := by
  have hT : ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞
      (fun x => R.trivialization b.val (R.restrictTrivIn_GRIM O b x)) :=
    (R.trivialization b.val).contMDiff.comp (R.contMDiff_restrictTrivIn_GRIM O b)
  refine ContMDiff.prodMk ?_ (contMDiff_snd.comp hT)
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model (𝓡 2) ∞
      (fun x => ((R.trivialization b.val (R.restrictTrivIn_GRIM O b x)).1 : R.Base)) :=
    contMDiff_subtype_val.comp (contMDiff_fst.comp hT)
  exact h

theorem contMDiff_restrictTrivInv_GRIM :
    ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞ (R.restrictTrivInv_GRIM O b) := by
  have hin : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun y : R.restrictNeighborhood_GRIM O b × Circle =>
        ((⟨y.1.val.val, y.1.2⟩ : R.neighborhood b.val), y.2)) := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (contMDiff_subtype_val.comp contMDiff_subtype_val).comp contMDiff_fst
  have hT : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.restrictNeighborhood_GRIM O b × Circle =>
        (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)) :=
    (R.trivialization b.val).symm.contMDiff.comp hin
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.restrictNeighborhood_GRIM O b × Circle =>
        (((R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)).val.val : W.Carrier)) :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).comp hT
  exact h

/-- **The restricted trivialization.** -/
def restrictTrivialization_GRIM :
    TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b)
      ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (R.restrictNeighborhood_GRIM O b × Circle) where
  toFun := R.restrictTrivFun_GRIM O b
  invFun := R.restrictTrivInv_GRIM O b
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun a : TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) =>
      a.val.val) (R.restrictTrivFun_in_GRIM O b x)
    exact h
  right_inv y := by
    have h := Diffeomorph.apply_symm_apply (R.trivialization b.val) (⟨y.1.val.val, y.1.2⟩, y.2)
    rw [← R.restrictTrivInv_in_GRIM O b y] at h
    rcases y with ⟨⟨⟨c, hcO⟩, hc⟩, θ⟩
    simp only [Prod.ext_iff] at h
    refine Prod.ext ?_ h.2
    apply Subtype.ext
    apply Subtype.ext
    have h3 := congrArg Subtype.val h.1
    exact h3
  contMDiff_toFun := R.contMDiff_restrictTrivFun_GRIM O b
  contMDiff_invFun := R.contMDiff_restrictTrivInv_GRIM O b

/-- The restricted trivialization lies over the restricted projection. -/
theorem restrictProjection_trivialization_GRIM
    (x : TopologicalSpace.Opens.comap (R.restrictProj_GRIM O) (R.restrictNeighborhood_GRIM O b)) :
    ((R.restrictTrivialization_GRIM O b x).1).val = R.restrictProj_GRIM O x.val := by
  apply Subtype.ext
  change ((R.trivialization b.val (R.restrictTrivIn_GRIM O b x)).1).val = _
  rw [R.trivialization_fst_val_GRIM]
  rfl

end Triv

/-! ## The link facts for `ι = Subtype.val` -/

/-- `CircleRestrictionLink.domain_eq` for the restriction. -/
theorem restrictDomain_eq_GRIM (O : TopologicalSpace.Opens R.Base) :
    (R.restrictDomain_GRIM O : Set W.Carrier) =
      Subtype.val '' {x : R.domain | R.proj x ∈ range (Subtype.val : O → R.Base)} := by
  ext x
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, ⟨⟨_, hx⟩, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [← hc]
    exact c.2

/-- `CircleRestrictionLink.proj_eq` for the restriction. -/
theorem restrictProj_eq_GRIM (O : TopologicalSpace.Opens R.Base) (x : R.restrictDomain_GRIM O) :
    ∃ hx : (x : W.Carrier) ∈ R.domain,
      R.proj ⟨x, hx⟩ = ((R.restrictProj_GRIM O x : O) : R.Base) :=
  ⟨x.2.fst, rfl⟩

/-- `CircleRestrictionLink.ι_isOpenEmbedding` for `ι = Subtype.val`. -/
theorem isOpenEmbedding_val_GRIM (O : TopologicalSpace.Opens R.Base) :
    Topology.IsOpenEmbedding (Subtype.val : O → R.Base) :=
  O.isOpen.isOpenEmbedding_subtypeVal

/-- `CircleRestrictionLink.ι_smooth` for `ι = Subtype.val`. -/
theorem contMDiff_val_GRIM (O : TopologicalSpace.Opens R.Base) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : O → R.Base) :=
  contMDiff_subtype_val

/-- `CircleRestrictionLink.ι_mfderiv` for `ι = Subtype.val`. -/
theorem mfderiv_val_bijective_GRIM (O : TopologicalSpace.Opens R.Base) (c : O) :
    Bijective (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : O → R.Base) c) := by
  rw [DifferentialGeometry.mfderiv_subtype_val O c]
  exact bijective_id

/-- **The saturated preimage of a base set inside `O` is unchanged by the restriction.** -/
theorem tube_restrict_GRIM (O : TopologicalSpace.Opens R.Base) {A : Set R.Base}
    (hA : A ⊆ O) :
    Subtype.val '' ((R.restrictProj_GRIM O) ⁻¹' (Subtype.val ⁻¹' A : Set O)) = R.tube A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, R.restrictDomain_le_GRIM O y.2⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, y.2, hA hy⟩, hy, rfl⟩

/-- The circle region of the row bundle is the saturated preimage of the restricted `C₁`
(`CircleRestrictionLink.region_eq` once the cornered base is `val⁻¹ C₁`). -/
theorem region_restrict_GRIM (O : TopologicalSpace.Opens R.Base) (hC : R.cbase ⊆ O) :
    Subtype.val '' ((R.restrictProj_GRIM O) ⁻¹' (Subtype.val ⁻¹' R.cbase : Set O)) =
      R.region :=
  R.tube_restrict_GRIM O hC

end CircleBundle

end GC.GraphManifold.Assembly.FC39P0
