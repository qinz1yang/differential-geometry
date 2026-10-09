import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesEdge74

/-!
# Draft 74, G5 step 3a: the trivializations of a circle bundle over the stage restricted to `V`

Lane S-JUNCTIONS2 (suffix `_JN74`). For a `CircleBundle R` and an open set `V` of its base, the
trivialization of `R` over the neighbourhood `N_b = val⁻¹ (R.neighborhood b)` of `b : ↥V` restricted
to the stage `StageProj74.ofCircleBundle74 R` restricted to `V` (parent `restrictParent V`, map
`restrictProj V`): the same construction as `restrictTrivialization_GRIM` (lane FC39-G-RIMBOX), for
the stage-style restricted parent used by `CircleCutFacts74`.
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

variable (R : CircleBundle W) (V : TopologicalSpace.Opens R.Base) (b : V)

/-- The base neighbourhood of `b` over `V`. -/
def stageNeighborhood_JN74 : TopologicalSpace.Opens V :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (R.neighborhood b.val)

theorem mem_stageNeighborhood_JN74 : b ∈ R.stageNeighborhood_JN74 V b :=
  R.mem_neighborhood b.val

/-- The old trivialization domain point of a point of the restricted trivialization domain. -/
def stageTrivIn_JN74
    (x : TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b)) :
    TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) :=
  ⟨TopologicalSpace.Opens.inclusion ((StageProj74.ofCircleBundle74 R).restrictParent_le V) x.val,
    x.2⟩

/-- The restricted trivialization, forward map. -/
def stageTrivFun_JN74
    (x : TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b)) : R.stageNeighborhood_JN74 V b × Circle :=
  (⟨⟨((R.trivialization b.val (R.stageTrivIn_JN74 V b x)).1).val, by
      rw [R.projection_trivialization b.val (R.stageTrivIn_JN74 V b x)]
      exact ((StageProj74.ofCircleBundle74 R).exists_of_mem_restrictParent x.val.2).2⟩,
    ((R.trivialization b.val (R.stageTrivIn_JN74 V b x)).1).2⟩,
    (R.trivialization b.val (R.stageTrivIn_JN74 V b x)).2)

/-- The restricted trivialization, inverse map. -/
def stageTrivInv_JN74 (y : R.stageNeighborhood_JN74 V b × Circle) :
    TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b) :=
  let a := (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)
  have ha : R.proj a.val = y.1.val.val := by
    rw [← R.projection_trivialization b.val, Diffeomorph.apply_symm_apply]
  ⟨⟨a.val.val, (StageProj74.ofCircleBundle74 R).mem_restrictParent_of a.val.2 (by
      change R.proj a.val ∈ V
      rw [ha]
      exact y.1.val.2)⟩, by
    change R.proj a.val ∈ R.neighborhood b.val
    rw [ha]
    exact y.1.2⟩

theorem stageTrivInv_in_JN74 (y : R.stageNeighborhood_JN74 V b × Circle) :
    R.stageTrivIn_JN74 V b (R.stageTrivInv_JN74 V b y) =
      (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2) :=
  rfl

theorem stageTrivFun_in_JN74
    (x : TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b)) :
    (R.trivialization b.val).symm
        (⟨(R.stageTrivFun_JN74 V b x).1.val.val, (R.stageTrivFun_JN74 V b x).1.2⟩,
          (R.stageTrivFun_JN74 V b x).2) = R.stageTrivIn_JN74 V b x := by
  rw [show (⟨(R.stageTrivFun_JN74 V b x).1.val.val, (R.stageTrivFun_JN74 V b x).1.2⟩,
      (R.stageTrivFun_JN74 V b x).2) = R.trivialization b.val (R.stageTrivIn_JN74 V b x)
      from rfl,
    Diffeomorph.symm_apply_apply]

theorem contMDiff_stageTrivIn_JN74 :
    ContMDiff W.model W.model ∞ (R.stageTrivIn_JN74 V b) := by
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model W.model ∞
      (fun x : TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
          (R.stageNeighborhood_JN74 V b) => (x.val.val : W.Carrier)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  exact h

theorem contMDiff_stageTrivFun_JN74 :
    ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞ (R.stageTrivFun_JN74 V b) := by
  have hT : ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞
      (fun x => R.trivialization b.val (R.stageTrivIn_JN74 V b x)) :=
    (R.trivialization b.val).contMDiff.comp (R.contMDiff_stageTrivIn_JN74 V b)
  refine ContMDiff.prodMk ?_ (contMDiff_snd.comp hT)
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model (𝓡 2) ∞
      (fun x => ((R.trivialization b.val (R.stageTrivIn_JN74 V b x)).1 : R.Base)) :=
    contMDiff_subtype_val.comp (contMDiff_fst.comp hT)
  exact h

theorem contMDiff_stageTrivInv_JN74 :
    ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞ (R.stageTrivInv_JN74 V b) := by
  have hin : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun y : R.stageNeighborhood_JN74 V b × Circle =>
        ((⟨y.1.val.val, y.1.2⟩ : R.neighborhood b.val), y.2)) := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (contMDiff_subtype_val.comp contMDiff_subtype_val).comp contMDiff_fst
  have hT : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.stageNeighborhood_JN74 V b × Circle =>
        (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)) :=
    (R.trivialization b.val).symm.contMDiff.comp hin
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.stageNeighborhood_JN74 V b × Circle =>
        (((R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)).val.val : W.Carrier)) :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).comp hT
  exact h

/-- **The restricted trivialization** over the stage restricted to `V`. -/
def stageTrivialization_JN74 :
    TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b)
      ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (R.stageNeighborhood_JN74 V b × Circle) where
  toFun := R.stageTrivFun_JN74 V b
  invFun := R.stageTrivInv_JN74 V b
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun a : TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) =>
      a.val.val) (R.stageTrivFun_in_JN74 V b x)
    exact h
  right_inv y := by
    have h := Diffeomorph.apply_symm_apply (R.trivialization b.val) (⟨y.1.val.val, y.1.2⟩, y.2)
    rw [← R.stageTrivInv_in_JN74 V b y] at h
    rcases y with ⟨⟨⟨c, hcO⟩, hc⟩, θ⟩
    simp only [Prod.ext_iff] at h
    refine Prod.ext ?_ h.2
    apply Subtype.ext
    apply Subtype.ext
    have h3 := congrArg Subtype.val h.1
    exact h3
  contMDiff_toFun := R.contMDiff_stageTrivFun_JN74 V b
  contMDiff_invFun := R.contMDiff_stageTrivInv_JN74 V b

/-- The restricted trivialization lies over the restricted projection. -/
theorem stageProjection_trivialization_JN74
    (x : TopologicalSpace.Opens.comap ((StageProj74.ofCircleBundle74 R).restrictProj V)
      (R.stageNeighborhood_JN74 V b)) :
    ((R.stageTrivialization_JN74 V b x).1).val =
      (StageProj74.ofCircleBundle74 R).restrictProj V x.val := by
  apply Subtype.ext
  change ((R.trivialization b.val (R.stageTrivIn_JN74 V b x)).1).val = _
  rw [R.projection_trivialization b.val]
  rfl

end CircleBundle

end GC.GraphManifold.Assembly.FC39P0
