import DifferentialGeometry.Topology.Homotopy.SphereClasses
import DifferentialGeometry.Topology.Homotopy.BasedMap



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



theorem genLoopSphereHomeomorph_natural (n : ℕ) (f : C(X, Y))
    (x : X) (y : Y) (hf : f x = y) (Γ : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n y (genLoopBasedMap f x y hf Γ)).val =
      f.comp (genLoopSphereHomeomorph n x Γ).val := by
  ext z
  obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
  rw [genLoopSphereHomeomorph_projection, ContinuousMap.comp_apply,
    genLoopSphereHomeomorph_projection]
  rfl


def freeSpherePostcompose (n : ℕ) (f : C(X, Y)) :
    ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y) :=
  ZerothHomotopy.lift (fun Γ => ZerothHomotopy.mk (f.comp Γ))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (continuous_postcomp f)))

@[simp] theorem freeSpherePostcompose_mk (n : ℕ) (f : C(X, Y))
    (Γ : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSpherePostcompose n f (ZerothHomotopy.mk Γ) = ZerothHomotopy.mk (f.comp Γ) := rfl


theorem homotopyGroupToFreeSphere_natural (n : ℕ) (f : C(X, Y))
    (x : X) (y : Y) (hf : f x = y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n y (homotopyGroupBasedMap f x y hf a) =
      freeSpherePostcompose n f (homotopyGroupToFreeSphere n x a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg ZerothHomotopy.mk (genLoopSphereHomeomorph_natural n f x y hf Γ)



theorem homotopyGroupToFreeSphere_ne_constant_iff [SimplyConnectedSpace X]
    (n : ℕ) (x : X) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n x a ≠ ZerothHomotopy.mk (ContinuousMap.const _ x) ↔ a ≠ 1 := by
  rw [← homotopyGroupToFreeSphere_one n x]
  exact not_congr (homotopyGroupToFreeSphere_injective n x).eq_iff

end DifferentialGeometry.Topology
