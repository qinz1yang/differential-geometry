import DifferentialGeometry.Bundle.Orientation.Cover
import DifferentialGeometry.Bundle.Orientation.Basic
import DifferentialGeometry.Topology.Covering.Sections



noncomputable section
open Set Bundle
open scoped Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {B F J : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

attribute [local instance] orientationTopology
local instance : DiscreteTopology (Orientation ℝ F (Fin n)) := ⟨rfl⟩

theorem orientationCore_localTriv (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (i : J) (x : B) (hx : x ∈ Z.baseSet i)
    (o : Orientation ℝ (Z.Fiber x) (Fin n)) :
    ((orientationCore Z hdim).localTriv i ⟨x, o⟩).2 =
      Orientation.map (Fin n) ((Z.localTriv i).continuousLinearEquivAt ℝ x hx).toLinearEquiv o := by
  change Orientation.map (Fin n)
    ((Z.localTriv (Z.indexAt x)).coordChangeL ℝ (Z.localTriv i) x).toLinearEquiv o = _
  congr 2
  apply LinearEquiv.ext
  intro v
  change (Z.localTriv (Z.indexAt x)).coordChangeL ℝ (Z.localTriv i) x v =
    (Z.localTriv i).continuousLinearEquivAt ℝ x hx v
  rw [Z.localTriv_coordChange_eq (Z.indexAt x) i ⟨Z.mem_baseSet_at x, hx⟩]
  rw [(Z.localTriv i).coe_continuousLinearEquivAt_eq (R := ℝ) hx,
    Z.localTriv_continuousLinearMapAt hx]
  rfl


theorem compatibleOrientation_of_section (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (s : C(B, (orientationCore Z hdim).TotalSpace))
    (hs : Function.RightInverse s (orientationCore Z hdim).proj) :
    IsCompatibleOrientation (F := F) Z.Fiber (fun x => (s x).2) := by
  intro x
  let t := (orientationCore Z hdim).localTrivAt x
  have hxsource : s x ∈ t.source := by
    change (s x).1 ∈ Z.baseSet (Z.indexAt x)
    have hsp : (s x).1 = x := hs x
    rw [hsp]
    exact Z.mem_baseSet_at x
  have hcont : ContinuousAt (fun y => (t (s y)).2) x :=
    (t.continuousAt hxsource).snd.comp s.continuous.continuousAt
  have heq : ∀ᶠ y in 𝓝 x, (t (s y)).2 = (t (s x)).2 :=
    hcont.eventually (isOpen_discrete {((t (s x)).2)} |>.mem_nhds rfl)
  let U := Z.baseSet (Z.indexAt x) ∩ {y | (t (s y)).2 = (t (s x)).2}
  have hUx : U ∈ 𝓝 x :=
    Filter.inter_mem ((Z.isOpen_baseSet _).mem_nhds (Z.mem_baseSet_at x)) heq
  refine ⟨trivializationAt F Z.Fiber x, inferInstance, U, hUx,
    (fun y hy => hy.1), (t (s x)).2, ?_⟩
  intro y hy
  have hsy : s y = ⟨y, (s y).2⟩ := by
    cases h : s y with
    | mk b o =>
      have hb : b = y := by simpa [h] using hs y
      subst b
      rfl
  have hybase : y ∈ Z.baseSet (Z.indexAt x) := hy.1
  exact (orientationCore_localTriv Z hdim (Z.indexAt x) y hybase (s y).2).symm.trans
    (by change (t ⟨y, (s y).2⟩).2 = _; rw [← hsy]; exact hy.2)

theorem exists_compatible_orientation_of_simply_connected
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (Z : VectorBundleCore ℝ B F J) (hdim : Module.finrank ℝ F = n) :
    ∃ o : ∀ x, Orientation ℝ (Z.Fiber x) (Fin n), IsCompatibleOrientation (F := F) Z.Fiber o := by
  let b : B := Classical.choice inferInstance
  let basis : Module.Basis (Fin n) ℝ F :=
    (Module.finBasis ℝ F).reindex (finCongr hdim)
  obtain ⟨s, ⟨_, hs⟩, _⟩ := DifferentialGeometry.Topology.Covering.exists_unique_section
    (orientationCore_isCoveringMap Z hdim) b ⟨b, basis.orientation⟩ rfl
  exact ⟨fun x => (s x).2, compatibleOrientation_of_section Z hdim s hs⟩

end DifferentialGeometry.VectorBundle
