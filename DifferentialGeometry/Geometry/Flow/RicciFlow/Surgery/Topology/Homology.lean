import DifferentialGeometry.Topology.ThreeManifold.LocalOrientationRealization

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable (X : Type u) [TopologicalSpace X]
variable {X} {Y : Type u} [TopologicalSpace Y]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
variable {o : TangentOrientationSection M} {x : M}

theorem localOrientationClass_generator (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) := by
  sorry

variable [hT2 : T2Space M] [hCompact : CompactSpace M]
include hT2 hCompact

theorem exists_unique_fundamentalClass (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  let uliftChart := (Homeomorph.ulift (X := ThreeSpace)).symm.toOpenPartialHomeomorph
  let : ChartedSpace (ULift.{u} ThreeSpace) M :=
    { atlas := (fun e : OpenPartialHomeomorph M ThreeSpace => e.trans uliftChart) ''
        atlas ThreeSpace M
      chartAt := fun x => (chartAt ThreeSpace x).trans uliftChart
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source ThreeSpace x, trivial⟩
      chart_mem_atlas := fun x => ⟨chartAt ThreeSpace x, chart_mem_atlas ThreeSpace x, rfl⟩ }
  exact DifferentialGeometry.Topology.exists_unique_absolute_class_of_locally_realized_family
    (E := ULift.{u} ThreeSpace) 3
    (by rw [(ULift.moduleEquiv (R := ℝ) (M := ThreeSpace)).finrank_eq]; simp)
    (localOrientationClass o) (localOrientationClass_locally_realized o)

def fundamentalClass (o : TangentOrientationSection M) : IntegralHomology M 3 :=
  Classical.choose (exists_unique_fundamentalClass o)

theorem fundamentalClass_local (o : TangentOrientationSection M) (x : M) :
    absoluteToRelative M ({x}ᶜ) 3 (fundamentalClass o) = localOrientationClass o x :=
  (Classical.choose_spec (exists_unique_fundamentalClass o)).1 x

variable [hConnected : ConnectedSpace M]
include hConnected


theorem fundamentalClass_generator (o : TangentOrientationSection M) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) := by
  sorry

omit hT2 hCompact hConnected in
theorem exists_unique_fundamentalClass_of_exists (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x)
    (hinj : ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  obtain ⟨x, hx⟩ := hinj
  exact hx (by rw [hz, hz'])

omit hConnected in
theorem fundamentalClass_generator_of (o : TangentOrientationSection M) (x : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x))
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) := by
  let A : IntegralHomology M 3 →ₗ[ℤ] LocalIntegralHomology M x 3 :=
    (absoluteToRelative M ({x}ᶜ) 3).hom
  have hA : ∀ z : ℤ, A (z • fundamentalClass o) = z • localOrientationClass o x := by
    intro z
    rw [map_zsmul, fundamentalClass_local]
  constructor
  · intro a b hab
    apply hlocal.injective
    have h := congrArg A hab
    rwa [hA, hA] at h
  · intro w
    obtain ⟨z, hz⟩ := hlocal.surjective (A w)
    exact ⟨z, hinj (hA z ▸ hz)⟩

def fundamentalClassEquiv (o : TangentOrientationSection M) :
    ℤ ≃ₗ[ℤ] IntegralHomology M 3 :=
  (AddEquiv.ofBijective
    ({ toFun := fun z : ℤ => z • fundamentalClass o
       map_zero' := zero_zsmul (fundamentalClass o)
       map_add' := fun z w => add_zsmul (fundamentalClass o) z w } :
      ℤ →+ IntegralHomology M 3)
    (fundamentalClass_generator o)).toIntLinearEquiv

@[simp] theorem fundamentalClassEquiv_one (o : TangentOrientationSection M) :
    fundamentalClassEquiv o 1 = fundamentalClass o := by
  change (1 : ℤ) • fundamentalClass o = fundamentalClass o
  exact one_smul ℤ (fundamentalClass o)

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N] [ConnectedSpace N]

def orientedDegree (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) : ℤ :=
  Classical.choose ((fundamentalClass_generator oN).surjective
    (integralHomologyMap 3 f (fundamentalClass oM)))

omit hConnected in
theorem orientedDegree_spec (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) :
    integralHomologyMap 3 f (fundamentalClass oM) =
      orientedDegree oM oN f • fundamentalClass oN :=
  (Classical.choose_spec ((fundamentalClass_generator oN).surjective
    (integralHomologyMap 3 f (fundamentalClass oM)))).symm

omit hConnected in
theorem orientedDegree_eq_iff (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) (d : ℤ) :
    orientedDegree oM oN f = d ↔
      integralHomologyMap 3 f (fundamentalClass oM) = d • fundamentalClass oN := by
  rw [orientedDegree_spec]
  exact (fundamentalClass_generator oN).injective.eq_iff.symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
