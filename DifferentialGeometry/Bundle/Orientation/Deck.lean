import DifferentialGeometry.Bundle.Orientation.Cover

noncomputable section
open Set Bundle
open scoped Topology

namespace DifferentialGeometry.VectorBundle

variable {n : ℕ} {B F J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
attribute [local instance] orientationTopology
local instance : DiscreteTopology (Orientation ℝ F (Fin n)) := ⟨rfl⟩


def orientationDeck (Z : VectorBundleCore ℝ B F J) (hdim : Module.finrank ℝ F = n)
    (z : (orientationCore Z hdim).TotalSpace) : (orientationCore Z hdim).TotalSpace :=
  ⟨z.proj, @Neg.neg (Orientation ℝ F (Fin n)) inferInstance z.snd⟩

theorem orientationDeck_involutive (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) : Function.Involutive (orientationDeck Z hdim) := by
  rintro ⟨x, o⟩
  exact congrArg (fun q : Orientation ℝ F (Fin n) =>
    (⟨x, q⟩ : (orientationCore Z hdim).TotalSpace))
    (@neg_neg (Orientation ℝ F (Fin n)) inferInstance o)

theorem orientationDeck_ne_self (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (z : (orientationCore Z hdim).TotalSpace) :
    orientationDeck Z hdim z ≠ z := by
  intro h
  have hh := congrArg (fun w : (orientationCore Z hdim).TotalSpace =>
    (w.snd : Orientation ℝ F (Fin n))) h
  exact Module.Ray.ne_neg_self z.snd hh.symm


theorem orientationDeck_chart (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (i : J) (z : (orientationCore Z hdim).TotalSpace) :
    ((orientationCore Z hdim).localTriv i (orientationDeck Z hdim z)).2 =
      -((orientationCore Z hdim).localTriv i z).2 := by
  change Orientation.map (Fin n) _ (@Neg.neg (Orientation ℝ F (Fin n)) inferInstance z.snd) =
    -(Orientation.map (Fin n) _ z.snd)
  exact Orientation.map_neg _ _

theorem orientationDeck_continuous (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) : Continuous (orientationDeck Z hdim) := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [_root_.FiberBundle.continuousAt_totalSpace (Orientation ℝ F (Fin n))]
  refine ⟨(orientationCore_isCoveringMap Z hdim).continuous.continuousAt, ?_⟩
  let t := (orientationCore Z hdim).localTrivAt z.proj
  have ht : ContinuousAt (fun w : (orientationCore Z hdim).TotalSpace => (t w).2) z :=
    (t.continuousAt (_root_.FiberBundle.mem_trivializationAt_proj_source)).snd
  have hn : Continuous (fun o : Orientation ℝ F (Fin n) => -o) := continuous_of_discreteTopology
  convert hn.continuousAt.comp ht using 1
  ext w
  exact orientationDeck_chart Z hdim (Z.indexAt z.proj) w

end DifferentialGeometry.VectorBundle
