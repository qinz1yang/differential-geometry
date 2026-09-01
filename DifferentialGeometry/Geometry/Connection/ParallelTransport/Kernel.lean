import DifferentialGeometry.Bundle.SmoothSubbundle.Range
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantCone
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Endpoint
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.Contraction
import DifferentialGeometry.Tensor.Alternating.ContractionSubbundle

set_option autoImplicit false

noncomputable section

namespace LinearEquiv

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {source : V →ₗ[ℝ] V} {target : W →ₗ[ℝ] W}

private theorem map_ker_eq_ker_of_intertwining (e : V ≃ₗ[ℝ] W)
    (h : e.toLinearMap.comp source =
      target.comp e.toLinearMap) :
    Submodule.map e.toLinearMap source.ker = target.ker := by
  apply le_antisymm
  · rintro y ⟨v, hv, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L v) h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hv] at hz
    simpa using hz.symm
  · intro y hy
    let v : V := e.symm y
    have hv : source v = 0 := by
      apply e.injective
      have hmapv : e v = y := by simp [v]
      calc
        e (source v) = target (e v) := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun L : V →ₗ[ℝ] W => L v) h
        _ = target y := by rw [hmapv]
        _ = 0 := LinearMap.mem_ker.mp hy
        _ = e 0 := by simp
    exact ⟨v, hv, by simp [v]⟩

private theorem map_range_eq_range_of_intertwining (e : V ≃ₗ[ℝ] W)
    (h : e.toLinearMap.comp source =
      target.comp e.toLinearMap) :
    Submodule.map e.toLinearMap source.range = target.range := by
  apply le_antisymm
  · rintro y ⟨v, ⟨z, rfl⟩, rfl⟩
    refine ⟨e z, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h
    simpa [LinearMap.comp_apply] using hz.symm
  · intro y hy
    rcases hy with ⟨w, rfl⟩
    let z : V := e.symm w
    refine ⟨source z, ⟨z, rfl⟩, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h
    simpa [z, LinearMap.comp_apply] using hz

end LinearEquiv

namespace DifferentialGeometry.Geometry.Connection

structure LinearIsometryKernelIntertwining
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (source : V →L[ℝ] V) (target : W →L[ℝ] W) where
  map : V ≃ₗᵢ[ℝ] W
  intertwining :
    map.toLinearMap.comp source.toLinearMap =
      target.toLinearMap.comp map.toLinearMap

namespace LinearIsometryKernelIntertwining

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {source : V →L[ℝ] V} {target : W →L[ℝ] W}

theorem map_ker_eq_ker (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.ker = target.ker := by
  exact h.map.toLinearEquiv.map_ker_eq_ker_of_intertwining h.intertwining

theorem finrank_ker_eq (h : LinearIsometryKernelIntertwining V W source target) :
    Module.finrank ℝ source.ker = Module.finrank ℝ target.ker := by
  rw [← h.map_ker_eq_ker]
  exact (Submodule.equivMapOfInjective h.map.toLinearMap h.map.injective source.ker).finrank_eq

theorem map_range_eq_range (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.range = target.range := by
  exact h.map.toLinearEquiv.map_range_eq_range_of_intertwining h.intertwining

end LinearIsometryKernelIntertwining

universe uX uF

variable {X : Type uX} (V : X → Type uF)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def IsTransportInvariantSubmoduleFamily
    (P : LinearIsometricTransport V)
    (S : ∀ x, Submodule ℝ (V x)) : Prop :=
  ∀ x y, Submodule.map (P.transport x y).toLinearMap (S x) = S y

namespace IsTransportInvariantSubmoduleFamily

variable {P : LinearIsometricTransport V} {S : ∀ x, Submodule ℝ (V x)}

theorem map_transport (h : IsTransportInvariantSubmoduleFamily V P S) (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (S x) = S y :=
  h x y

theorem transport_mem_iff (h : IsTransportInvariantSubmoduleFamily V P S)
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

end IsTransportInvariantSubmoduleFamily

def IsTransportInvariantAlternatingSubmoduleFamily
    (P : LinearIsometricTransport V)
    (K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)) : Prop :=
  ∀ x y,
    Submodule.map
      (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ
        (P.transport x y).toLinearEquiv).toLinearMap (K x) = K y

namespace IsTransportInvariantAlternatingSubmoduleFamily

variable {P : LinearIsometricTransport V}
  {K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)}

theorem contractionAnnihilator
    (h : IsTransportInvariantAlternatingSubmoduleFamily V P K) :
    IsTransportInvariantSubmoduleFamily V P
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

end IsTransportInvariantAlternatingSubmoduleFamily

def IsTransportInvariantContinuousAlternatingSubmoduleFamily
    (P : LinearIsometricTransport V)
    (K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→L[ℝ] ℝ)) : Prop :=
  ∀ x y,
    Submodule.map
      ((P.transport x y).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
        (ι := Fin 2)).toLinearMap (K x) = K y

namespace IsTransportInvariantContinuousAlternatingSubmoduleFamily

variable {P : LinearIsometricTransport V}
  {K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→L[ℝ] ℝ)}

theorem contractionAnnihilator
    (h : IsTransportInvariantContinuousAlternatingSubmoduleFamily V P K) :
    IsTransportInvariantSubmoduleFamily V P
      (fun x => ContinuousAlternatingMap.contractionAnnihilator (K x)) := by
  intro x y
  have hback :
      Submodule.map
          ((P.transport x y).symm.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
            (ι := Fin 2)).toLinearMap (K y) =
        K x := by
    simpa [P.transport_symm V x y] using h y x
  change Submodule.map (P.transport x y).toLinearMap
      (ContinuousAlternatingMap.contractionAnnihilator (K x)) =
    ContinuousAlternatingMap.contractionAnnihilator (K y)
  rw [← hback]
  exact ContinuousAlternatingMap.map_contractionAnnihilator_compContinuousLinearEquiv
    (K y) (P.transport x y).toContinuousLinearEquiv

end IsTransportInvariantContinuousAlternatingSubmoduleFamily

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
  exact (P.transport base x).toLinearEquiv.map_ker_eq_ker_of_intertwining
    (h.baseIntertwining x)

theorem physical_kernel_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).ker =
      (physicalOperator y).ker := by
  exact (P.transport x y).toLinearEquiv.map_ker_eq_ker_of_intertwining
    (h.pathIntertwining x y)

theorem fixed_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Submodule.map (P.transport base x).toLinearMap fixedOperator.range =
      (physicalOperator x).range := by
  exact (P.transport base x).toLinearEquiv.map_range_eq_range_of_intertwining
    (h.baseIntertwining x)

theorem physical_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).range =
      (physicalOperator y).range := by
  exact (P.transport x y).toLinearEquiv.map_range_eq_range_of_intertwining
    (h.pathIntertwining x y)

theorem physical_kernel_finrank_eq (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Module.finrank ℝ fixedOperator.ker = Module.finrank ℝ (physicalOperator x).ker := by
  calc
    Module.finrank ℝ fixedOperator.ker =
        Module.finrank ℝ (Submodule.map (P.transport base x).toLinearMap fixedOperator.ker) := by
      exact (Submodule.equivMapOfInjective (P.transport base x).toLinearMap
        (P.transport base x).injective fixedOperator.ker).finrank_eq
    _ = Module.finrank ℝ (physicalOperator x).ker := by
      exact congrArg (fun S : Submodule ℝ (V x) => Module.finrank ℝ S)
        (fixed_kernel_transport (V := V) h x)

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

theorem physical_kernel_is_transport_invariant
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P) :
    IsTransportInvariantSubmoduleFamily V P (fun x => (physicalOperator x).ker) := by
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

universe uE uH uM

section LeviCivitaParallel

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

local instance tangentT2Space (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (TangentSpace I) x

local instance tangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance tangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

local instance tangentSmoothVectorBundle :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have h : IsManifold I ∞ M := inferInstance
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle (I := I) (M := M)

def IsParallelSubmoduleFamily [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ∀ x : M, Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b),
    Submodule.map
      (Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab).toLinearMap (S (γ a)) = S (γ b)

namespace IsParallelSubmoduleFamily

theorem map_parallelTransportBetween [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    Submodule.map
      (Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab).toLinearMap (S (γ a)) = S (γ b) :=
  h γ hγ hab

theorem parallelTransportBetween_mem_iff [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) {v : TangentSpace I (γ a)} :
    Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab v ∈ S (γ b) ↔ v ∈ S (γ a) := by
  rw [← h γ hγ hab]
  simp

end IsParallelSubmoduleFamily

def IsParallelContinuousAlternatingSubmoduleFamily [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (K : ∀ x : M,
      Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)) : Prop :=
  ∀ (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b),
    let e := (Riemannian.Variation.parallelTransportLinearEquivBetween
      (I := I) g γ hγ hab).toContinuousLinearEquiv
    Submodule.map
      (e.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap
        (K (γ a)) = K (γ b)

namespace IsParallelContinuousAlternatingSubmoduleFamily

theorem contractionAnnihilator [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {K : ∀ x : M,
      Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)}
    (h : IsParallelContinuousAlternatingSubmoduleFamily g K) :
    IsParallelSubmoduleFamily g
      (fun x => ContinuousAlternatingMap.contractionAnnihilator (K x)) := by
  intro γ hγ a b hab
  let e := (Riemannian.Variation.parallelTransportLinearEquivBetween
    (I := I) g γ hγ hab).toContinuousLinearEquiv
  change Submodule.map e.toLinearMap
      (ContinuousAlternatingMap.contractionAnnihilator (K (γ a))) =
    ContinuousAlternatingMap.contractionAnnihilator (K (γ b))
  exact ContinuousAlternatingMap.map_contractionAnnihilator_of_map_eq
    (K (γ a)) (K (γ b)) e (h γ hγ hab)

end IsParallelContinuousAlternatingSubmoduleFamily

theorem exists_smooth_parallel_contractionAnnihilator_range [I.Boundaryless]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : ∀ x : M,
      (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
        TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)
    (hA : ContMDiff I
      (I.prod 𝓘(ℝ,
        (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk'
        ((E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) x (A x)))
    (hrange : ∀ x, Module.finrank ℝ (A x).range = 1)
    (hparallel : IsParallelContinuousAlternatingSubmoduleFamily
      g (fun x => (A x).range)) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      (∀ x, S.fiber x =
        ContinuousAlternatingMap.contractionAnnihilator (A x).range) ∧
      IsParallelSubmoduleFamily g S.fiber := by
  let basis := Module.finBasis ℝ E
  let _ : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) basis)
      |>.finiteDimensional_of_finite
  let R := ContMDiffVectorSubbundle.range A hA 1 hrange
  obtain ⟨S, hSrank, hSfiber⟩ :=
    ContinuousAlternatingMap.exists_smooth_contractionAnnihilator
      (I := I) (M := M) (F := E) (V := TangentSpace I)
      (fiberBundle := tangentFiberBundle (I := I) (M := M))
      (vectorBundle := tangentVectorBundle (I := I) (M := M))
      (smoothVectorBundle := tangentSmoothVectorBundle (I := I) (M := M))
      hE R rfl
  refine ⟨S, hSrank, ?_, ?_⟩
  · intro x
    simpa [R] using hSfiber x
  · intro γ hγ a b hab
    rw [hSfiber (γ a), hSfiber (γ b)]
    simpa [R] using hparallel.contractionAnnihilator γ hγ hab

end LeviCivitaParallel

end DifferentialGeometry.Geometry.Connection
