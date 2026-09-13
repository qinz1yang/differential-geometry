import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OrientationDegree
import DifferentialGeometry.Topology.Homology.LocalizationTransport

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

def localOrientationPreservingSelfDiffeomorphismTransitive (o : TangentOrientationSection M) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
    ∃ e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ M, e x = y ∧
      PreservesTangentOrientation o o e ∧
      (⟨e, e.continuous⟩ : C(M, M)).Homotopic (ContinuousMap.id M)

theorem preservesTangentOrientation_refl (o : TangentOrientationSection M) :
    PreservesTangentOrientation o o (Diffeomorph.refl ThreeModel M ∞) := by
  constructor
  · exact contMDiff_id
  · intro x
    have hd : mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x
        = ContinuousLinearMap.id ℝ (TangentSpace ThreeModel x) := mfderiv_id
    have hbij : Function.Bijective
        (mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x) :=
      hd ▸ Function.bijective_id
    refine ⟨hbij, ?_⟩
    unfold PreservesTangentOrientationAt
    have he : LinearEquiv.ofBijective
        (mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x).toLinearMap hbij
        = LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
      ext v
      change mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x v = v
      rw [hd]
      rfl
    have hm := congrArg (fun e : TangentSpace ThreeModel x ≃ₗ[ℝ] TangentSpace ThreeModel x =>
      Orientation.map (Fin 3) e (o.orientation x)) he
    have hr := congrArg (fun e : Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) ≃
      Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) => e (o.orientation x))
      (Orientation.map_refl (R := ℝ) (M := TangentSpace ThreeModel x) (Fin 3))
    exact hm.trans hr

theorem exists_orientationPreservingSelfDiffeomorphism_eq_self (o : TangentOrientationSection M)
    (x : M) :
    ∃ e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ M, e x = x ∧
      PreservesTangentOrientation o o e ∧
      (⟨e, e.continuous⟩ : C(M, M)).Homotopic (ContinuousMap.id M) :=
  ⟨Diffeomorph.refl ThreeModel M ∞, rfl, preservesTangentOrientation_refl o,
    ContinuousMap.Homotopic.refl _⟩

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem integralHomologyMap_self_eq_of_homotopic_id {X : Type u} [TopologicalSpace X]
    (f : C(X, X)) (hf : f.Homotopic (ContinuousMap.id X)) (z : IntegralHomology X 3) :
    integralHomologyMap 3 f z = z := by
  have h := integralHomologyMap_eq_of_homotopic (X := X) (Y := X) hf
  rw [h]
  simp only [integralHomologyMap, TopCat.ofHom_id]
  rw [CategoryTheory.Functor.map_id (integralHomologyFunctor 3) (TopCat.of X)]
  exact ModuleCat.id_apply (IntegralHomology X 3) z

theorem localClassRealizationLocallyConstant_of_localOrientationPreservingSelfDiffeomorphismTransitive
    (o : TangentOrientationSection M)
    (h : localOrientationPreservingSelfDiffeomorphismTransitive o) :
    localClassRealizationLocallyConstant o := by
  intro z x
  obtain ⟨U, hU, hxU, hloc⟩ := h x
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  obtain ⟨e, hex, heo, hhom⟩ := hloc y hy
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
      (localOrientationClass o x) = localOrientationClass o (e x) :=
    localOrientationClass_natural_diffeomorph o o e heo x
  constructor
  · intro hyz
    exact hinj (by rw [hA, hlc]; exact hyz)
  · intro hxz
    rw [← hA, hxz, hlc]

theorem exists_unique_fundamentalClass_of_subsingleton_punctured_of_localOrientationPreservingSelfDiffeomorphismTransitive
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (h : localOrientationPreservingSelfDiffeomorphismTransitive o) (x₀ : M)
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o
    (localClassRealizationLocallyConstant_of_localOrientationPreservingSelfDiffeomorphismTransitive o h)
    x₀ h₂ h₃

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
