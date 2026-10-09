import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportPorts74

/-!
# Draft 74, D74-6: transport of the cusp cores (onto the transported ports)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G21 (second file). `CuspCores.mapCarrier74 e C :
CuspCores W₁ (E.transport74 e)`: pieces `e ∘ (piece b).map` with the same product structure and
model faces, cusp functions `cuspFn b ∘ e⁻¹`, near sets `e(near b)`; the ports, the external ends,
the owned collars, the closure condition, regularity and the internal / sublevel identities are
carried by `e` (the target boundary tori are the transported ones, D74-6).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- A pulled-back function is regular at `z` where the original is regular at `e⁻¹ z`. -/
theorem mfderiv_comp_symm_ne_zero_at_R74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {f : W₀.Carrier → ℝ} {z : W₁.Carrier}
    (hf : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ) f (e.symm z))
    (hz : mfderiv W₀.model 𝓘(ℝ, ℝ) f (e.symm z) ≠ 0) :
    mfderiv W₁.model 𝓘(ℝ, ℝ) (f ∘ e.symm) z ≠ 0 := by
  have he : MDifferentiableAt W₁.model W₀.model e.symm z := e.symm.mdifferentiable (by simp) _
  rw [mfderiv_comp z hf he]
  intro h0
  apply hz
  ext v
  obtain ⟨u, rfl⟩ := (mfderiv_diffeo_bijective_R74 e.symm z).2 v
  exact congrArg (fun L => L u) h0

/-- Points of `e(N)` where the pulled-back function satisfies `Q` are the image. -/
theorem image_setOf_R74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (N : Set W₀.Carrier) (f : W₀.Carrier → ℝ) (Q : ℝ → Prop) :
    {x | x ∈ e '' N ∧ Q ((f ∘ e.symm) x)} = e '' {y | y ∈ N ∧ Q (f y)} := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hq⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    change Q (f (e.symm (e y))) at hq
    rwa [e.symm_apply_apply] at hq
  · rintro ⟨y, ⟨hy, hq⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    change Q (f (e.symm (e y)))
    rwa [e.symm_apply_apply]

/-- **The cusp cores transported along `e`**, onto the transported boundary tori. -/
def CuspCores.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} (C : CuspCores W₀ E) : CuspCores W₁ (E.transport74 e) where
  ports := E.transport74_ports e C.ports
  piece b := (C.piece b).mapCarrier74 e
  product b := C.product b
  external_end b t := by
    change e ((C.piece b).map (C.product b (t, iccEnd false))) = e (E.torusMap b t)
    rw [C.external_end b t]
  collar_owned b := by
    rw [E.transport74_target, PieceEmbedding.range_mapCarrier74]
    exact image_mono (C.collar_owned b)
  collar_closure_off b := by
    rw [E.transport74_target, ← image_closure_R74 e]
    change Disjoint (e '' closure (E.collar b).target)
      (range (e ∘ fun t => (C.piece b).map (C.product b (t, iccEnd true))))
    rw [range_comp]
    exact (disjoint_image_iff e.injective).mpr (C.collar_closure_off b)
  disjoint b b' hbb' := by
    change Disjoint (range ((C.piece b).mapCarrier74 e).map)
      (range ((C.piece b').mapCarrier74 e).map)
    rw [PieceEmbedding.range_mapCarrier74, PieceEmbedding.range_mapCarrier74]
    exact (disjoint_image_iff e.injective).mpr (C.disjoint hbb')
  cuspFn b := C.cuspFn b ∘ e.symm
  near b := ⟨e '' C.near b, e.toHomeomorph.isOpenMap _ (C.near b).isOpen⟩
  near_interior b := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono (C.near_interior b)
  fn_smooth b := (C.fn_smooth b).comp e.symm.contMDiff.contMDiffOn fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    change e.symm (e y) ∈ C.near b
    rw [e.symm_apply_apply]
    exact hy
  fn_regular b x hx h0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hy0 : C.cuspFn b y = 0 := by
      change C.cuspFn b (e.symm (e y)) = 0 at h0
      rwa [e.symm_apply_apply] at h0
    have hd : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ) (C.cuspFn b) y :=
      ((C.fn_smooth b y hy).contMDiffAt ((C.near b).isOpen.mem_nhds hy)).mdifferentiableAt
        (by simp)
    refine mfderiv_comp_symm_ne_zero_at_R74 e ?_ ?_
    · rw [e.symm_apply_apply]
      exact hd
    · rw [e.symm_apply_apply]
      exact C.fn_regular b y hy hy0
  internal_eq b := by
    change range (e ∘ fun t => (C.piece b).map (C.product b (t, iccEnd true))) =
      {x | x ∈ e '' C.near b ∧ (C.cuspFn b ∘ e.symm) x = 0}
    rw [range_comp, C.internal_eq b]
    exact (image_setOf_R74 e _ (C.cuspFn b) (fun r => r = 0)).symm
  near_eq b := by
    change range ((C.piece b).mapCarrier74 e).map ∩ e '' C.near b = _
    rw [PieceEmbedding.range_mapCarrier74, ← image_inter (f := (e : W₀.Carrier → W₁.Carrier))
      e.injective, C.near_eq b]
    exact (image_setOf_R74 e _ (C.cuspFn b) (fun r => r ≤ 0)).symm
  internalModelFace b := C.internalModelFace b
  internalModelFace_eq b := C.internalModelFace_eq b
  externalModelFace b := C.externalModelFace b
  externalModelFace_eq b := C.externalModelFace_eq b
  modelFace_cases b := C.modelFace_cases b

/-- The transported cusp cores have the transported ranges and cusp functions. -/
theorem CuspCores.mapCarrier74_range (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} (C : CuspCores W₀ E) (b : Fin n) :
    range ((C.mapCarrier74 e).piece b).map = e '' range (C.piece b).map ∧
      (C.mapCarrier74 e).cuspFn b = C.cuspFn b ∘ e.symm :=
  ⟨PieceEmbedding.range_mapCarrier74 e (C.piece b), rfl⟩

end GC.GraphManifold.Assembly.FC39P0
