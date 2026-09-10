/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Covering.Section
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set Topology

universe u v

namespace DifferentialGeometry.Topology

structure BoolCocycle (ι : Type u) (B : Type v) [TopologicalSpace B] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  parity : ι → ι → B → Bool
  parity_self : ∀ i, ∀ x ∈ baseSet i, parity i i x = false
  continuousOn_parity : ∀ i j, ContinuousOn (parity i j) (baseSet i ∩ baseSet j)
  parity_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k,
    Bool.xor (parity i j x) (parity j k x) = parity i k x

namespace BoolCocycle

variable {ι : Type u} {B : Type v} [TopologicalSpace B] (C : BoolCocycle ι B)

def toFiberBundleCore : FiberBundleCore ι B Bool where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_at
  coordChange i j x side := Bool.xor side (C.parity i j x)
  coordChange_self i x hx side := by simp [C.parity_self i x hx]
  continuousOn_coordChange i j := by
    let overlap : Set (B × Bool) := (C.baseSet i ∩ C.baseSet j) ×ˢ univ
    have hparity : ContinuousOn
        (fun p : B × Bool ↦ C.parity i j p.1) overlap :=
      (C.continuousOn_parity i j).comp continuousOn_fst fun _ hp ↦ hp.1
    have hpair : ContinuousOn
        (fun p : B × Bool ↦ (p.2, C.parity i j p.1)) overlap :=
      continuousOn_snd.prodMk hparity
    have hxor : Continuous (fun p : Bool × Bool ↦ Bool.xor p.1 p.2) :=
      continuous_of_discreteTopology
    exact hxor.comp_continuousOn hpair
  coordChange_comp i j k x hx side := by
    rw [Bool.xor_assoc, C.parity_comp i j k x hx]

noncomputable def sectionCoord
    (s : C(B, C.toFiberBundleCore.TotalSpace))
    (hs : Function.RightInverse s C.toFiberBundleCore.proj)
    (i : ι) : C(C.baseSet i, Bool) where
  toFun x := ((C.toFiberBundleCore.localTriv i) (s x.1)).2
  continuous_toFun := by
    apply continuous_snd.comp
    apply (C.toFiberBundleCore.localTriv i).continuousOn_toFun.comp_continuous
      (s.continuous.comp continuous_subtype_val)
    intro x
    change (s x).1 ∈ C.baseSet i
    rw [show (s x).1 = x by exact hs x]
    exact x.2

theorem sectionCoord_change
    (s : C(B, C.toFiberBundleCore.TotalSpace))
    (hs : Function.RightInverse s C.toFiberBundleCore.proj)
    (i j : ι) (x : B) (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j) :
    C.sectionCoord s hs j ⟨x, hxj⟩ =
      Bool.xor (C.sectionCoord s hs i ⟨x, hxi⟩) (C.parity i j x) := by
  change ((C.toFiberBundleCore.localTriv j) (s x)).2 =
    Bool.xor ((C.toFiberBundleCore.localTriv i) (s x)).2 (C.parity i j x)
  rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
  let side : Bool := (s x).2
  change Bool.xor side (C.parity (C.indexAt (s x).1) j (s x).1) =
    Bool.xor (Bool.xor side (C.parity (C.indexAt (s x).1) i (s x).1))
      (C.parity i j x)
  rw [show (s x).1 = x by exact hs x]
  rw [Bool.xor_assoc, C.parity_comp]
  exact ⟨⟨C.mem_baseSet_at x, hxi⟩, hxj⟩

theorem isLocallyConstant_sectionCoord
    (s : C(B, C.toFiberBundleCore.TotalSpace))
    (hs : Function.RightInverse s C.toFiberBundleCore.proj)
    (i : ι) : IsLocallyConstant (C.sectionCoord s hs i) := by
  exact (IsLocallyConstant.iff_continuous _).2 (C.sectionCoord s hs i).continuous

structure Coorientation where
  coord : ∀ i, C(C.baseSet i, Bool)
  coord_change : ∀ i j x (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j),
    coord j ⟨x, hxj⟩ = Bool.xor (coord i ⟨x, hxi⟩) (C.parity i j x)

noncomputable def coorientationOfSection
    (s : C(B, C.toFiberBundleCore.TotalSpace))
    (hs : Function.RightInverse s C.toFiberBundleCore.proj) : C.Coorientation where
  coord := C.sectionCoord s hs
  coord_change := C.sectionCoord_change s hs

namespace Coorientation

variable (O : C.Coorientation)

def reorientedParity (i j : ι) (x : B)
    (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j) : Bool :=
  Bool.xor (Bool.xor (O.coord i ⟨x, hxi⟩) (C.parity i j x))
    (O.coord j ⟨x, hxj⟩)

theorem reorientedParity_eq_false (i j : ι) (x : B)
    (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j) :
    reorientedParity C O i j x hxi hxj = false := by
  rw [reorientedParity, ← O.coord_change i j x hxi hxj]
  exact Bool.xor_self _

end Coorientation

theorem isCoveringMap_proj : IsCoveringMap C.toFiberBundleCore.proj := by
  exact FiberBundle.isCoveringMap

theorem exists_continuous_section
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (b₀ : B) (side₀ : Bool) :
    ∃ s : C(B, C.toFiberBundleCore.TotalSpace),
      Function.RightInverse s C.toFiberBundleCore.proj := by
  exact exists_continuous_section_of_isCoveringMap_of_simplyConnected
    C.isCoveringMap_proj b₀ ⟨b₀, side₀⟩ rfl

theorem nonempty_coorientation
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (b₀ : B) (side₀ : Bool) : Nonempty C.Coorientation := by
  obtain ⟨s, hs⟩ := C.exists_continuous_section b₀ side₀
  exact ⟨C.coorientationOfSection s hs⟩

end BoolCocycle

end DifferentialGeometry.Topology
