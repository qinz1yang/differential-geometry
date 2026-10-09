import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageU74

/-!
# Restricting a smooth stage to an open base; components along an embedding (O-CL0, G2 kernel)

Lane O-CL0 (`_OCL`), G2 kernel. Draft 74 §1.3 / D74-11 / D74-13: the rows' stage bases are the
GOOD open bases, and the whole-fibre identification `StageIdent_LND74` (with its `parent_pre`
clause: every point over the base lies in the parent) holds after restricting a stage whose parent
is `ψ(U)` to an open base `V` all of whose fibres lie in `U`.

* `StageProj74.restrictStage_OCL Q V`: the stage `Q` restricted to the open base `V` — base `↥V`,
  parent `Q.restrictParent V` (the whole `Q`-preimage of `V`), projection `Q.restrictProj V`
  (smooth, submersion: lane S-JUNCTIONS's `restrictProj_smooth / _submersion`);
* **`stageIdent_restrict_OCL`**: from `StageIdentU_LND74 ψ Q q ι U` (parent `= ψ(U)`) and the
  localization `q p ∈ ι(V) → p ∈ U`, the restricted stage is identified with `q` through
  `ι ∘ val` in the strong sense `StageIdent_LND74` (whole fibres);
* `image_connectedComponentIn_OCL`: an embedding carries `connectedComponentIn S x` onto
  `connectedComponentIn (ι '' S) (ι x)`;
* **`actualComponentEquiv_OCL ι hι S`**: `ActualComponent S ≃ ActualComponent (ι '' S)` with
  `ι '' c = e c` (the slim components of the cut choice on the stage base and on the block space);
  `actualComponentEquivOfEq_OCL` for equal sets.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u v w

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

namespace StageProj74

variable {k : ℕ}

/-- **The stage restricted to an open base** `V`: base `↥V`, the whole `Q`-preimage of `V` as
parent, the restricted projection. -/
def restrictStage_OCL (Q : StageProj74 W k) (V : TopologicalSpace.Opens Q.Base) :
    StageProj74 W k where
  Base := V
  parent := Q.restrictParent V
  parent_interior := fun _ hx => Q.parent_interior (Q.restrictParent_le V hx)
  proj := Q.restrictProj V
  proj_smooth := Q.restrictProj_smooth V
  proj_submersion := Q.restrictProj_submersion V

@[simp] theorem restrictStage_parent_OCL (Q : StageProj74 W k) (V : TopologicalSpace.Opens Q.Base) :
    (Q.restrictStage_OCL V).parent = Q.restrictParent V :=
  rfl

end StageProj74

section Ident

variable {X : Type v} {Bs : Type w} [TopologicalSpace Bs] {k : ℕ}

/-- **Whole-fibre identification of a restricted stage**: if the parent of `Q` is `ψ(U)`
(`StageIdentU_LND74`) and every point of `X` over `ι(V)` lies in `U`, then the stage restricted to
`V` is identified with `q` through `ι ∘ val` with the whole-fibre clause. -/
theorem stageIdent_restrict_OCL {ψ : X ≃ W.Carrier} {Q : StageProj74 W k} {q : X → Bs}
    {ι : Q.Base → Bs} {U : Set X} (h : StageIdentU_LND74 ψ Q q ι U)
    (V : TopologicalSpace.Opens Q.Base) (hU : ∀ p, q p ∈ ι '' (V : Set Q.Base) → p ∈ U) :
    StageIdent_LND74 ψ (Q.restrictStage_OCL V) q (fun b : V => ι b) where
  emb := h.emb.comp Topology.IsEmbedding.subtypeVal
  proj_eq := fun x => h.proj_eq (Q.restrictIncl V x)
  parent_pre := fun p hp => by
    obtain ⟨b, hb⟩ := hp
    let b' : V := b
    have hb' : ι b'.1 = q p := hb
    have hpU : p ∈ U := hU p ⟨b'.1, b'.2, hb'⟩
    have hpar : ψ p ∈ (Q.parent : Set W.Carrier) := by
      rw [h.parent_eq]
      exact mem_image_of_mem _ hpU
    refine Q.mem_restrictParent_of hpar ?_
    have h1 := h.proj_eq ⟨ψ p, hpar⟩
    rw [ψ.symm_apply_apply] at h1
    have h2 : Q.proj ⟨ψ p, hpar⟩ = b'.1 := h.emb.injective (h1.trans hb'.symm)
    rw [h2]
    exact b'.2

end Ident

section Components

variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

/-- An embedding carries the component of `S` through `x` onto the component of `ι '' S` through
`ι x`. -/
theorem image_connectedComponentIn_OCL {ι : Y → Z} (hι : Topology.IsEmbedding ι) {S : Set Y}
    {x : Y} (hx : x ∈ S) :
    ι '' connectedComponentIn S x = connectedComponentIn (ι '' S) (ι x) := by
  refine (hι.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  set C' := connectedComponentIn (ι '' S) (ι x)
  have hC'S : C' ⊆ ι '' S := connectedComponentIn_subset _ _
  have hC'r : C' ⊆ range ι := hC'S.trans (image_subset_range _ _)
  have hpre : IsPreconnected (ι ⁻¹' C') := by
    rw [← hι.isInducing.isPreconnected_image, image_preimage_eq_of_subset hC'r]
    exact isPreconnected_connectedComponentIn
  have hsub : ι ⁻¹' C' ⊆ S := fun y hy => by
    obtain ⟨z, hz, hzy⟩ := hC'S hy
    rw [← hι.injective hzy]
    exact hz
  have hxC : x ∈ ι ⁻¹' C' :=
    mem_connectedComponentIn (mem_image_of_mem ι hx)
  have h := hpre.subset_connectedComponentIn hxC hsub
  intro z hz
  obtain ⟨y, -, rfl⟩ := hC'r hz
  exact mem_image_of_mem ι (h hz)

/-- **Actual components along an embedding**: `ActualComponent S ≃ ActualComponent (ι '' S)`,
the image of a component being the corresponding component. -/
def actualComponentEquiv_OCL (ι : Y → Z) (hι : Topology.IsEmbedding ι) (S : Set Y) :
    ActualComponent S ≃ ActualComponent (ι '' S) where
  toFun c := ⟨ι '' c.1, by
    obtain ⟨x, hx, hc⟩ := c.2
    exact ⟨ι x, mem_image_of_mem ι hx, by rw [hc]; exact image_connectedComponentIn_OCL hι hx⟩⟩
  invFun c := ⟨ι ⁻¹' c.1, by
    obtain ⟨z, ⟨x, hx, rfl⟩, hc⟩ := c.2
    refine ⟨x, hx, ?_⟩
    rw [hc, ← image_connectedComponentIn_OCL hι hx, preimage_image_eq _ hι.injective]⟩
  left_inv c := Subtype.ext (preimage_image_eq _ hι.injective)
  right_inv c := by
    apply Subtype.ext
    change ι '' (ι ⁻¹' c.1) = c.1
    obtain ⟨z, ⟨x, hx, rfl⟩, hc⟩ := c.2
    refine image_preimage_eq_of_subset ?_
    rw [hc]
    exact (connectedComponentIn_subset _ _).trans (image_subset_range _ _)

@[simp] theorem actualComponentEquiv_OCL_apply (ι : Y → Z) (hι : Topology.IsEmbedding ι)
    (S : Set Y) (c : ActualComponent S) : (actualComponentEquiv_OCL ι hι S c).1 = ι '' c.1 :=
  rfl

/-- Actual components of equal sets. -/
def actualComponentEquivOfEq_OCL {S S' : Set Y} (h : S = S') :
    ActualComponent S ≃ ActualComponent S' :=
  h ▸ Equiv.refl _

@[simp] theorem actualComponentEquivOfEq_OCL_val {S S' : Set Y} (h : S = S')
    (c : ActualComponent S) : (actualComponentEquivOfEq_OCL h c).1 = c.1 := by
  subst h
  rfl

end Components

end GC.GraphManifold.Assembly.FC39P0
