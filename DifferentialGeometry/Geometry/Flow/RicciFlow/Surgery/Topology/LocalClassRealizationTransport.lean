import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationLocality

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def localClassTransport (o : TangentOrientationSection M) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
    ∃ e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ M, e x = y ∧
      (⟨e, e.continuous⟩ : C(M, M)).Homotopic (ContinuousMap.id M) ∧
      relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, M)) ({x}ᶜ) ({e x}ᶜ)
        (fun _ hp hp' => hp (e.injective hp')) (localOrientationClass o x) =
          localOrientationClass o (e x)

theorem localClassRealizationLocallyConstant_of_localClassTransport
    (o : TangentOrientationSection M) (h : localClassTransport o) :
    localClassRealizationLocallyConstant o := by
  intro z x
  obtain ⟨U, hU, hxU, hloc⟩ := h x
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  obtain ⟨e, hex, hhom, hcrux⟩ := hloc y hy
  subst hex
  have hmapsTo : Set.MapsTo (⟨e, e.continuous⟩ : C(M, M)) ({x}ᶜ : Set M) ({e x}ᶜ : Set M) :=
    fun p hp hp' => hp (e.injective hp')
  have hmapsTo' : Set.MapsTo e.symm ({e x}ᶜ : Set M) ({x}ᶜ : Set M) :=
    fun p hp hp' => hp (by
      have h1 : e.symm p = x := hp'
      calc p = e (e.symm p) := (e.apply_symm_apply p).symm
        _ = e x := by rw [h1])
  have hinj : Function.Injective
      (relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, M)) ({x}ᶜ) ({e x}ᶜ) hmapsTo).hom :=
    DifferentialGeometry.Topology.injective_integralRelativeHomologyMap_of_homeomorph 3
      e.toHomeomorph hmapsTo hmapsTo'
  have hA : (relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, M)) ({x}ᶜ) ({e x}ᶜ) hmapsTo)
      (absoluteToRelative M ({x}ᶜ) 3 z) = absoluteToRelative M ({e x}ᶜ) 3 z := by
    have hnat := absoluteToRelative_naturality 3 (⟨e, e.continuous⟩ : C(M, M))
      ({x}ᶜ) ({e x}ᶜ) hmapsTo
    have happ := congrArg
      (fun k : IntegralHomology M 3 ⟶ LocalIntegralHomology M (e x) 3 => k z) hnat
    simp only [ModuleCat.comp_apply] at happ
    rw [happ, integralHomologyMap_self_eq_of_homotopic_id (⟨e, e.continuous⟩ : C(M, M)) hhom z]
  have hlc : (relativeIntegralHomologyMap 3 (⟨e, e.continuous⟩ : C(M, M)) ({x}ᶜ) ({e x}ᶜ) hmapsTo)
      (localOrientationClass o x) = localOrientationClass o (e x) := hcrux
  constructor
  · intro hyz
    exact hinj (by rw [hA, hlc]; exact hyz)
  · intro hxz
    rw [← hA, hxz, hlc]

theorem localClassTransport_of_localOrientationPreservingSelfDiffeomorphismTransitive
    (o : TangentOrientationSection M)
    (h : localOrientationPreservingSelfDiffeomorphismTransitive o) :
    localClassTransport o := by
  intro x
  obtain ⟨U, hU, hxU, hloc⟩ := h x
  exact ⟨U, hU, hxU, fun y hy => by
    obtain ⟨e, hex, heo, hhom⟩ := hloc y hy
    exact ⟨e, hex, hhom, localOrientationClass_natural_diffeomorph o o e heo x⟩⟩

def realizationSet (o : TangentOrientationSection M) (z : IntegralHomology M 3) : Set M :=
  fun x => absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

theorem localClassRealizationLocallyConstant_iff_forall_isClopen
    (o : TangentOrientationSection M) :
    localClassRealizationLocallyConstant o ↔
      ∀ z : IntegralHomology M 3, IsClopen (realizationSet o z) := by
  constructor
  · intro h z
    refine ⟨?_, ?_⟩
    · refine isOpen_compl_iff.mp ?_
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨U, hU, hxU, hconst⟩ := h z x
      exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy hyS => hx ((hconst y hy).mp hyS)
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨U, hU, hxU, hconst⟩ := h z x
      exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy => (hconst y hy).mpr hx
  · intro h z x
    by_cases hx : (realizationSet o z) x
    · exact ⟨realizationSet o z, (h z).2, hx, fun y hy => ⟨fun _ => hx, fun _ => hy⟩⟩
    · exact ⟨(realizationSet o z)ᶜ, (h z).1.isOpen_compl, hx,
        fun y hy => ⟨fun hy' => absurd hy' hy, fun hxc => absurd hxc hx⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant_of_localClassTransport,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassTransport_of_localOrientationPreservingSelfDiffeomorphismTransitive,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant_iff_forall_isClopen] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
