import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width

variable {Q : Type*} [TopologicalSpace Q]


def constantContractibleLoops : C(Q, ContractibleContinuousLoop Q) :=
  ⟨fun q => ⟨constantLoops q, isContractibleLoop_constant q⟩,
    constantLoops.continuous.subtype_mk _⟩

def IsEssentialFamilyClass (ξ : FreeContractibleSphereClass Q) : Prop :=
  ∀ f : C(Sphere 2, Q), FreeHomotopyClass.mk (constantContractibleLoops.comp f) ≠ ξ

theorem not_isEssentialFamilyClass_constant (f : C(Sphere 2, Q)) :
    ¬ IsEssentialFamilyClass (FreeHomotopyClass.mk (constantContractibleLoops.comp f)) := by
  intro h
  exact h f rfl

theorem isEssentialFamilyClass_of_pi2_zero
    (hpi2 : ∀ q : Q, Subsingleton (HomotopyGroup (Fin 2) Q q))
    (ξ : FreeContractibleSphereClass Q)
    (hnonnull : ∀ q : Q, ξ ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2)
        (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q))) :
    IsEssentialFamilyClass ξ := by
  intro f hf
  obtain ⟨q, hq⟩ := sphereFamily_homotopic_const_of_pi2_subsingleton hpi2 f
  have hconst : ContinuousMap.Homotopic (constantContractibleLoops.comp f)
      (ContinuousMap.const (Sphere 2)
        (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q)) := by
    exact (ContinuousMap.Homotopic.refl constantContractibleLoops).comp hq
  exact hnonnull q (hf.symm.trans ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hconst))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H Q] [IsManifold I ∞ Q]
    [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]

include hT2 hCompact hConnected hBoundary

theorem rfs_essential_short_family (g : SmoothRiemannianMetric I Q) :
    ∃ sigma K : ℝ, 0 < sigma ∧ 0 ≤ K ∧
      (∀ (ξ : FreeContractibleSphereClass Q), IsEssentialFamilyClass ξ →
        ∀ Γ : RegularRepresentative (I := I) ξ,
          ∀ ell : ℝ, 0 < ell → ell ≤ sigma →
            ∃ p : Sphere 2, ell ≤ loopLength g (Γ.1 p).1.toContinuousLoop) ∧
      (∀ (γ : ContractibleRegularLoop (I := I) (Q := Q)) (ell : ℝ),
        0 < ell → ell ≤ sigma → loopLength g γ.1.toContinuousLoop < ell →
          regularLeastArea g γ ≤ K * ell ^ 2) := by
  classical
  obtain ⟨sigma, K, hsigma, hK, hfill, hcontract, _⟩ := rfs_short_loop_fillings.{0} g
  refine ⟨sigma, K, hsigma, hK, ?_, ?_⟩
  · intro ξ hξ Γ ell _hell hellsigma
    by_contra hnone
    have hshort : ∀ k, loopLength g (Γ.1 k).1.toContinuousLoop < sigma := by
      intro k
      exact (lt_of_not_ge (fun hk => hnone ⟨k, hk⟩)).trans_le hellsigma
    obtain ⟨F, hzero, hone⟩ := hcontract (Sphere 2) Γ.1 hshort
    let i : C(ContractibleRegularLoop (I := I) (Q := Q), RegularLoop I Q) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let f : C(Sphere 2, Q) := loopEvaluation.comp (regularLoopInclusion.comp (i.comp Γ.1))
    have hhom : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
        (constantContractibleLoops.comp f) := by
      refine ⟨{
        toFun := fun p => contractibleRegularLoopInclusion (F p)
        continuous_toFun := contractibleRegularLoopInclusion.continuous.comp F.continuous
        map_zero_left := ?_
        map_one_left := ?_ }⟩
      · intro k
        exact congrArg contractibleRegularLoopInclusion (hzero k)
      · intro k
        have h := congrArg contractibleRegularLoopInclusion (hone k)
        convert! h using 1
    exact hξ f (((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhom).symm.trans Γ.2)
  · intro γ ell hell hellsigma hshort
    obtain ⟨u, hu⟩ := hfill γ.1.toContinuousLoop (γ.1.isLipschitz g)
      (hshort.trans_le hellsigma)
    have hsq : loopLength g γ.1.toContinuousLoop ^ 2 ≤ ell ^ 2 := by
      nlinarith [loopLength_nonneg g γ.1.toContinuousLoop]
    exact (leastArea_le_competitor g γ.1.toContinuousLoop γ.2
      (γ.1.isLipschitz g) u).trans
      (hu.trans (mul_le_mul_of_nonneg_left hsq hK))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
