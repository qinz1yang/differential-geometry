import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Topology

namespace VectorBundle

section ScalarMultiplication

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

theorem continuous_totalSpace_smul :
    Continuous (fun q : 𝕜 × TotalSpace F V =>
      (⟨q.2.proj, q.1 • q.2.snd⟩ : TotalSpace F V)) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  have hb : Continuous (fun q : 𝕜 × TotalSpace F V => q.2.proj) :=
    (FiberBundle.continuous_proj F V).comp continuous_snd
  refine ⟨hb.continuousAt, ?_⟩
  let e := trivializationAt F V q₀.2.proj
  have he : q₀.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt F V q₀.2.proj
  have hc : ContinuousAt (fun q : 𝕜 × TotalSpace F V => (e q.2).2) q₀ :=
    ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr he)).comp
      continuous_snd.continuousAt).snd
  apply (continuous_fst.continuousAt.smul hc).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with q hq
  exact (e.linear 𝕜 hq).map_smul q.1 q.2.snd

end ScalarMultiplication

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def zeroSectionHomotopy :
    ContinuousMap.Homotopy
      (⟨fun z : TotalSpace F V => (⟨z.proj, 0⟩ : TotalSpace F V),
        (Bundle.Trivialization.continuous_zeroSection ℝ).comp
          (FiberBundle.continuous_proj F V)⟩ : C(TotalSpace F V, TotalSpace F V))
      (ContinuousMap.id (TotalSpace F V)) where
  toFun q := ⟨q.2.proj, (q.1 : ℝ) • q.2.snd⟩
  continuous_toFun :=
    (continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left z := by
    change (⟨z.proj, (0 : ℝ) • z.snd⟩ : TotalSpace F V) = ⟨z.proj, 0⟩
    rw [zero_smul]
  map_one_left z := by
    change (⟨z.proj, (1 : ℝ) • z.snd⟩ : TotalSpace F V) = z
    rw [one_smul]

end VectorBundle
