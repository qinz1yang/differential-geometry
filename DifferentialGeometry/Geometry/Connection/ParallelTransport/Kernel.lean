import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantCone
import DifferentialGeometry.Tensor.Alternating.Contraction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

structure LinearIsometryKernelIntertwining
    (V W : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (source : V →L[ℝ] V) (target : W →L[ℝ] W) where
  map : V ≃ₗᵢ[ℝ] W
  intertwining :
    map.toLinearMap.comp source.toLinearMap =
      target.toLinearMap.comp map.toLinearMap

namespace LinearIsometryKernelIntertwining

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {source : V →L[ℝ] V} {target : W →L[ℝ] W}

theorem map_ker_eq_ker (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.ker = target.ker := by
  apply le_antisymm
  · rintro y ⟨v, hv, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L v) h.intertwining
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hv] at hz
    simpa using hz.symm
  · intro y hy
    let v : V := h.map.symm y
    have hv : source.toLinearMap v = 0 := by
      apply h.map.injective
      have hmapv : h.map v = y := by simp [v]
      calc
        h.map (source v) = target (h.map v) := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun L : V →ₗ[ℝ] W => L v) h.intertwining
        _ = target y := by rw [hmapv]
        _ = 0 := LinearMap.mem_ker.mp hy
        _ = h.map 0 := by simp
    exact ⟨v, hv, by simp [v]⟩

theorem finrank_ker_eq (h : LinearIsometryKernelIntertwining V W source target) :
    Module.finrank ℝ source.ker = Module.finrank ℝ target.ker := by
  rw [← h.map_ker_eq_ker]
  exact (Submodule.equivMapOfInjective h.map.toLinearMap h.map.injective source.ker).finrank_eq

theorem map_range_eq_range (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.range = target.range := by
  apply le_antisymm
  · rintro y ⟨v, ⟨z, rfl⟩, rfl⟩
    refine ⟨h.map z, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h.intertwining
    simpa [LinearMap.comp_apply] using hz.symm
  · intro y hy
    rcases hy with ⟨w, rfl⟩
    let z : V := h.map.symm w
    refine ⟨source z, ⟨z, rfl⟩, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h.intertwining
    simpa [z, LinearMap.comp_apply] using hz

end LinearIsometryKernelIntertwining

universe uX uF

variable {X : Type uX} (V : X → Type uF)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def IsParallelSubmoduleFamily
    (P : LinearIsometricTransport V)
    (S : ∀ x, Submodule ℝ (V x)) : Prop :=
  ∀ x y, Submodule.map (P.transport x y).toLinearMap (S x) = S y

namespace IsParallelSubmoduleFamily

variable {P : LinearIsometricTransport V} {S : ∀ x, Submodule ℝ (V x)}

theorem map_transport (h : IsParallelSubmoduleFamily V P S) (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (S x) = S y :=
  h x y

theorem transport_mem_iff (h : IsParallelSubmoduleFamily V P S)
    (x y : X) (v : V x) : P.transport x y v ∈ S y ↔ v ∈ S x := by
  rw [← h x y]
  constructor
  · rintro ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport x y).injective
      change P.transport x y w = P.transport x y v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

end IsParallelSubmoduleFamily

def IsParallelAlternatingSubmoduleFamily
    (P : LinearIsometricTransport V)
    (K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)) : Prop :=
  ∀ x y,
    Submodule.map
      (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ
        (P.transport x y).toLinearEquiv).toLinearMap (K x) = K y

namespace IsParallelAlternatingSubmoduleFamily

variable {P : LinearIsometricTransport V}
  {K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)}

theorem contractionAnnihilator
    (h : IsParallelAlternatingSubmoduleFamily V P K) :
    IsParallelSubmoduleFamily V P
      (fun x => AlternatingMap.contractionAnnihilator (K x)) := by
  intro x y
  have hback :
      Submodule.map
          (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ
            (P.transport x y).symm.toLinearEquiv).toLinearMap (K y) =
        K x := by
    simpa [P.transport_symm V x y] using h y x
  change Submodule.map (P.transport x y).toLinearMap
      (AlternatingMap.contractionAnnihilator (K x)) =
    AlternatingMap.contractionAnnihilator (K y)
  rw [← hback]
  exact AlternatingMap.map_contractionAnnihilator_compLinearEquiv
    (K y) (P.transport x y).toLinearEquiv

end IsParallelAlternatingSubmoduleFamily

structure UhlenbeckKernelTransfer (base : X)
    (fixedOperator : V base →L[ℝ] V base)
    (physicalOperator : ∀ x, V x →L[ℝ] V x)
    (P : LinearIsometricTransport V) where
  baseIntertwining : ∀ x,
    (P.transport base x).toLinearMap.comp fixedOperator.toLinearMap =
      (physicalOperator x).toLinearMap.comp (P.transport base x).toLinearMap
  pathIntertwining : ∀ x y,
    (P.transport x y).toLinearMap.comp (physicalOperator x).toLinearMap =
      (physicalOperator y).toLinearMap.comp (P.transport x y).toLinearMap

namespace UhlenbeckKernelTransfer

variable {base : X} {fixedOperator : V base →L[ℝ] V base}
  {physicalOperator : ∀ x, V x →L[ℝ] V x} {P : LinearIsometricTransport V}

theorem fixed_kernel_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Submodule.map (P.transport base x).toLinearMap fixedOperator.ker =
      (physicalOperator x).ker := by
  exact LinearIsometryKernelIntertwining.map_ker_eq_ker
    { map := P.transport base x, intertwining := h.baseIntertwining x }

theorem physical_kernel_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).ker =
      (physicalOperator y).ker := by
  exact LinearIsometryKernelIntertwining.map_ker_eq_ker
      { map := P.transport x y, intertwining := h.pathIntertwining x y }

theorem fixed_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Submodule.map (P.transport base x).toLinearMap fixedOperator.range =
      (physicalOperator x).range := by
  exact LinearIsometryKernelIntertwining.map_range_eq_range
    { map := P.transport base x, intertwining := h.baseIntertwining x }

theorem physical_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).range =
      (physicalOperator y).range := by
  exact LinearIsometryKernelIntertwining.map_range_eq_range
    { map := P.transport x y, intertwining := h.pathIntertwining x y }

theorem physical_kernel_finrank_eq (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Module.finrank ℝ fixedOperator.ker = Module.finrank ℝ (physicalOperator x).ker := by
  exact LinearIsometryKernelIntertwining.finrank_ker_eq
    { map := P.transport base x, intertwining := h.baseIntertwining x }

theorem physical_range_finrank_eq (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Module.finrank ℝ fixedOperator.range =
      Module.finrank ℝ (physicalOperator x).range := by
  calc
    Module.finrank ℝ fixedOperator.range =
        Module.finrank ℝ (Submodule.map (P.transport base x).toLinearMap fixedOperator.range) := by
      exact (Submodule.equivMapOfInjective (P.transport base x).toLinearMap
        (P.transport base x).injective fixedOperator.range).finrank_eq
    _ = Module.finrank ℝ (physicalOperator x).range := by
      exact congrArg (fun S : Submodule ℝ (V x) => Module.finrank ℝ S)
        (fixed_range_transport (V := V) h x)

theorem physical_kernel_is_parallel
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P) :
    IsParallelSubmoduleFamily V P (fun x => (physicalOperator x).ker) := by
  intro x y
  exact physical_kernel_transport (V := V) h x y

theorem fixed_kernel_mem_iff_physical
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) (v : V base) :
    P.transport base x v ∈ (physicalOperator x).ker ↔ v ∈ fixedOperator.ker := by
  constructor
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.ker := by
      rw [fixed_kernel_transport (V := V) h x]
      exact hv
    rcases hv' with ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport base x).injective
      change P.transport base x w = P.transport base x v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.ker :=
      ⟨v, hv, rfl⟩
    rw [fixed_kernel_transport (V := V) h x] at hv'
    exact hv'

theorem fixed_range_mem_iff_physical
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) (v : V base) :
    P.transport base x v ∈ (physicalOperator x).range ↔
      v ∈ fixedOperator.range := by
  constructor
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.range := by
      rw [fixed_range_transport (V := V) h x]
      exact hv
    rcases hv' with ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport base x).injective
      change P.transport base x w = P.transport base x v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.range :=
      ⟨v, hv, rfl⟩
    rw [fixed_range_transport (V := V) h x] at hv'
    exact hv'

end UhlenbeckKernelTransfer

end DifferentialGeometry.Geometry.Connection
