import DifferentialGeometry.Bundle.Orientation.Section



noncomputable section
open Bundle Set Filter
open scoped Topology

namespace DifferentialGeometry.VectorBundle

variable {n : ℕ} {B E J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] orientationTopology
local instance compatibleSectionDiscreteTopology : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

theorem continuous_section_of_compatibleOrientation (Z : VectorBundleCore ℝ B E J)
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x, Orientation ℝ (Z.Fiber x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) Z.Fiber o) :
    Continuous (fun x => (⟨x, o x⟩ : (orientationCore Z hdim).TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨t, ht, U, hUx, hU, p, hp⟩ := ho x
  obtain ⟨i, rfl⟩ := ht.out
  let T := (orientationCore Z hdim).localTriv i
  let e := T.toOpenPartialHomeomorph
  have hx : (x, p) ∈ e.target := ⟨hU (mem_of_mem_nhds hUx), mem_univ _⟩
  have hc : ContinuousAt (fun y : B => e.symm (y, p)) x :=
    ContinuousAt.comp (f := fun y : B => (y, p)) (x := x)
      (e.symm.continuousAt hx) (continuous_id.prodMk continuous_const).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hUx] with y hy
  have hv : T (⟨y, o y⟩ : (orientationCore Z hdim).TotalSpace) = (y, p) := by
    apply Prod.ext
    · rfl
    · exact (orientationCore_localTriv Z hdim i y (hU hy) (o y)).trans (hp y hy)
  change (⟨y, o y⟩ : (orientationCore Z hdim).TotalSpace) = e.symm (y, p)
  rw [← hv]
  exact (e.left_inv (show (⟨y, o y⟩ : (orientationCore Z hdim).TotalSpace) ∈ e.source from
    hU hy)).symm

end DifferentialGeometry.VectorBundle
