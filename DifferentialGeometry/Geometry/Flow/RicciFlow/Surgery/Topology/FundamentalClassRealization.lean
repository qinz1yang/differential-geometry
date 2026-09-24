import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def existsFundamentalClassAt (o : TangentOrientationSection M) (x : M) : Prop :=
  ∃ z : IntegralHomology M 3, absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

def localClassRealizationLocallyConstant (o : TangentOrientationSection M) : Prop :=
  ∀ (z : IntegralHomology M 3) (x : M), ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, (absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y ↔
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x)

theorem existsFundamentalClassAt_iff_mem_range (o : TangentOrientationSection M) (x : M) :
    existsFundamentalClassAt o x ↔
      localOrientationClass o x ∈ Set.range (absoluteToRelative M ({x}ᶜ) 3) :=
  Iff.rfl

theorem exists_fundamentalClassAt_iff_surjective (o : TangentOrientationSection M) (x : M)
    (hgen : Function.Surjective (fun z : ℤ => z • localOrientationClass o x)) :
    existsFundamentalClassAt o x ↔ Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) := by
  constructor
  · rintro ⟨z, hz⟩ w
    obtain ⟨m, hm⟩ := hgen w
    exact ⟨m • z, by rw [map_zsmul, hz]; exact hm⟩
  · intro h
    exact h (localOrientationClass o x)

theorem existsFundamentalClassAt_of_forall (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) (x : M) :
    existsFundamentalClassAt o x :=
  ⟨h.choose, h.choose_spec x⟩

theorem finite_realization_of_forall (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) (F : Finset M) :
    ∃ z : IntegralHomology M 3, ∀ x ∈ F,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  ⟨h.choose, fun x _ => h.choose_spec x⟩

variable [ConnectedSpace M]

theorem exists_fundamentalClass_of_local_realization_at (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) (h : existsFundamentalClassAt o x₀) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h
  let S : Set M := {x | absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hconst⟩ := hprop z x
    exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy => (hconst y hy).mpr hx
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hconst⟩ := hprop z x
    exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy hyS => hx ((hconst y hy).mp hyS)
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨x₀, hz⟩
  refine ⟨z, fun x => ?_⟩
  have : x ∈ S := by rw [hSuniv]; trivial
  exact this

theorem exists_fundamentalClass_of_local_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : ∀ x : M, existsFundamentalClassAt o x) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_fundamentalClass_of_local_realization_at o hprop x₀ (h x₀)

theorem exists_fundamentalClass_of_finite_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : ∀ F : Finset M, ∃ z : IntegralHomology M 3, ∀ x ∈ F,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h {x₀}
  exact exists_fundamentalClass_of_local_realization_at o hprop x₀
    ⟨z, hz x₀ (Finset.mem_singleton_self x₀)⟩

theorem finite_realization_iff_existsFundamentalClassAt (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) :
    (∀ F : Finset M, ∃ z : IntegralHomology M 3, ∀ x ∈ F,
        absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) ↔
      existsFundamentalClassAt o x₀ := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h {x₀}
    exact ⟨z, hz x₀ (Finset.mem_singleton_self x₀)⟩
  · intro h
    exact finite_realization_of_forall o
      (exists_fundamentalClass_of_local_realization_at o hprop x₀ h)

theorem exists_unique_fundamentalClass_of_local_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) (h : existsFundamentalClassAt o x₀)
    (hinj : Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_exists o
    (exists_fundamentalClass_of_local_realization_at o hprop x₀ h) ⟨x₀, hinj⟩

omit [ConnectedSpace M] in
theorem exists_unique_fundamentalClass_of_exists_of_subsingleton [T2Space M] [CompactSpace M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hsub : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
  exists_unique_fundamentalClass_of_exists o h
    ⟨x, absoluteToRelative_compl_singleton_injective_of_subsingleton x hsub⟩

omit [ConnectedSpace M] in
theorem fundamentalClass_generator_of_subsingleton [T2Space M] [CompactSpace M]
    (o : TangentOrientationSection M) (x : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x))
    (hsub : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) :=
  fundamentalClass_generator_of o x hlocal
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x hsub)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
