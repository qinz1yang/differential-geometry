import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass

noncomputable section

universe u

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q]

theorem regularRepresentative_smooth_exists (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∃ Γ : RegularRepresentative (I := I) ξ, HasContinuousSmoothLoopJets e Γ.1 := by
  classical
  obtain ⟨Γ⟩ := regularRepresentative_nonempty (I := I) ξ
  let i : C(ContractibleRegularLoop (I := I) (Q := Q), RegularLoop I Q) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let Γr : C(Sphere 2, RegularLoop I Q) := i.comp Γ.1
  obtain ⟨_, _, hsmooth⟩ := rfs_loop_smoothing g e
  obtain ⟨ε₀, hε₀, S, hjets, _, hhom, _, _⟩ :=
    hsmooth (Sphere 2) (regularLoopInclusion.comp Γr)
  let ε := ε₀ / 2
  have hε : ε ∈ Ioo (0 : ℝ) ε₀ := ⟨half_pos hε₀, half_lt_self hε₀⟩
  obtain ⟨F, _, hF⟩ := hhom ε hε
  have hctr (k : Sphere 2) : IsContractibleLoop (S ε k).toContinuousLoop := by
    have h := hF k (Γ.1 k).2 1
    exact Eq.mp (congrArg IsContractibleLoop (F.apply_one k)) h
  let T : RegularFamily (I := I) (Q := Q) (Sphere 2) :=
    ⟨fun k => ⟨S ε k, hctr k⟩, (S ε).continuous.subtype_mk _⟩
  have hhomT : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
      (contractibleRegularLoopInclusion.comp T) := by
    refine ⟨{
      toFun := fun p => ⟨F p, hF p.2 (Γ.1 p.2).2 p.1⟩
      continuous_toFun := (map_continuous F).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro k
      apply Subtype.ext
      exact F.apply_zero k
    · intro k
      apply Subtype.ext
      exact F.apply_one k
  have hclass : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp T) = ξ :=
    ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhomT).symm.trans Γ.2
  refine ⟨⟨T, hclass⟩, ?_⟩
  simpa only [HasContinuousSmoothLoopJets, HasContinuousSmoothJets, T,
    ContinuousMap.coe_mk] using hjets ε hε

theorem regularClass_existsUnique (ξ : FreeContractibleSphereClass Q) :
    ∃! ξ₁ : FreeHomotopyClass (Sphere 2) (ContractibleRegularLoop (I := I) (Q := Q)),
      FreeHomotopyClass.map contractibleRegularLoopInclusion ξ₁ = ξ := by
  have hb := rfs_regular_class_correspondence (I := I) (Q := Q)
  obtain ⟨ξ₁, hξ₁⟩ := hb.surjective ξ
  exact ⟨ξ₁, hξ₁, fun ξ₂ hξ₂ => hb.injective (hξ₂.trans hξ₁.symm)⟩

section Canonical

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]

theorem canonical_regularClass_existsUnique (g : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) {N : ℕ}
    (e : SmoothLoopEmbedding (I := ThreeModel) (Q := M) N) :
    ∃! ξ : FreeHomotopyClass (Sphere 2) (ContractibleRegularLoop (I := ThreeModel) (Q := M)),
      FreeHomotopyClass.map contractibleRegularLoopInclusion ξ = positiveFreeContractibleClass o ∧
      (∀ q : M, ξ ≠ FreeHomotopyClass.mk
        (ContinuousMap.const (Sphere 2) (constantContractibleRegularLoop (I := ThreeModel) q))) ∧
      ∃ Γ : RegularFamily (I := ThreeModel) (Q := M) (Sphere 2),
        FreeHomotopyClass.mk Γ = ξ ∧ HasContinuousSmoothLoopJets e Γ := by
  classical
  obtain ⟨ξ, hξ, huniq⟩ := regularClass_existsUnique (I := ThreeModel) (positiveFreeContractibleClass o)
  obtain ⟨Γ, hΓ⟩ := regularRepresentative_smooth_exists g (positiveFreeContractibleClass o) e
  have hΓclass : FreeHomotopyClass.mk Γ.1 = ξ := huniq _ Γ.2
  refine ⟨ξ, ⟨hξ, ?_, Γ.1, hΓclass, hΓ⟩, fun η hη => huniq η hη.1⟩
  intro q hq
  apply positiveFreeContractibleClass_nontrivial o q
  exact hξ.symm.trans (congrArg
    (FreeHomotopyClass.map (X := Sphere 2) contractibleRegularLoopInclusion) hq)

end Canonical

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
