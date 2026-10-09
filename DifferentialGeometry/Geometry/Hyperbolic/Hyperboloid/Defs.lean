import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

namespace DifferentialGeometry

structure Hyperboloid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  time : ℝ
  space : E
  time_pos : 0 < time
  time_sq_sub_inner_self : time ^ 2 - inner ℝ space space = 1

namespace Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem time_sq (x : Hyperboloid E) : x.time ^ 2 = 1 + ‖x.space‖ ^ 2 := by
  have h := x.time_sq_sub_inner_self
  rw [real_inner_self_eq_norm_sq] at h
  linarith

theorem time_eq_sqrt (x : Hyperboloid E) : x.time = Real.sqrt (1 + ‖x.space‖ ^ 2) := by
  rw [← x.time_sq, Real.sqrt_sq x.time_pos.le]

@[ext] theorem ext {x y : Hyperboloid E} (h : x.space = y.space) : x = y := by
  have ht : x.time = y.time := by rw [x.time_eq_sqrt, y.time_eq_sqrt, h]
  cases x
  cases y
  cases h
  cases ht
  rfl

def ofSpace (x : E) : Hyperboloid E where
  time := Real.sqrt (1 + ‖x‖ ^ 2)
  space := x
  time_pos := Real.sqrt_pos.2 (by positivity)
  time_sq_sub_inner_self := by
    rw [Real.sq_sqrt (by positivity), real_inner_self_eq_norm_sq]
    ring

@[simp] theorem space_ofSpace (x : E) : (ofSpace x).space = x := rfl

@[simp] theorem time_ofSpace (x : E) : (ofSpace x).time = Real.sqrt (1 + ‖x‖ ^ 2) := rfl

@[simp] theorem ofSpace_space (x : Hyperboloid E) : ofSpace x.space = x := by
  ext
  rfl

def spaceEquiv : Hyperboloid E ≃ E where
  toFun := space
  invFun := ofSpace
  left_inv := ofSpace_space
  right_inv := space_ofSpace

@[simp] theorem spaceEquiv_apply (x : Hyperboloid E) : spaceEquiv x = x.space := rfl

@[simp] theorem spaceEquiv_symm_apply (x : E) : spaceEquiv.symm x = ofSpace x := rfl

instance : TopologicalSpace (Hyperboloid E) :=
  TopologicalSpace.induced (fun x : Hyperboloid E => (x.time, x.space)) inferInstance

theorem continuous_time : Continuous (time : Hyperboloid E → ℝ) :=
  continuous_fst.comp (continuous_induced_dom (f := fun x : Hyperboloid E => (x.time, x.space)))

theorem continuous_space : Continuous (space : Hyperboloid E → E) :=
  continuous_snd.comp (continuous_induced_dom (f := fun x : Hyperboloid E => (x.time, x.space)))

theorem continuous_ofSpace : Continuous (ofSpace : E → Hyperboloid E) := by
  apply continuous_induced_rng.2
  exact ((continuous_const.add (continuous_norm.pow 2)).sqrt).prodMk continuous_id

def spaceHomeomorph : Hyperboloid E ≃ₜ E where
  toEquiv := spaceEquiv
  continuous_toFun := continuous_space
  continuous_invFun := continuous_ofSpace

@[simp] theorem spaceHomeomorph_apply (x : Hyperboloid E) : spaceHomeomorph x = x.space := rfl

@[simp] theorem spaceHomeomorph_symm_apply (x : E) : spaceHomeomorph.symm x = ofSpace x := rfl

def origin : Hyperboloid E := ofSpace 0

@[simp] theorem origin_time : (origin : Hyperboloid E).time = 1 := by simp [origin]

@[simp] theorem origin_space : (origin : Hyperboloid E).space = 0 := rfl

instance : Inhabited (Hyperboloid E) := ⟨origin⟩

end Hyperboloid

end DifferentialGeometry
