import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Covering.Smooth.Manifold

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]

def loopShift
    (g : Path.Homotopic.Quotient (default : X) default)
    (p : UniversalCover X) : UniversalCover X :=
  ⟨p.1, g.trans p.2⟩

theorem loopShift_preim
    (g : Path.Homotopic.Quotient (default : X) default)
    (p : UniversalCover X)
    (U : Set X) :
    loopShift g ⁻¹' basicOpen p U =
      basicOpen (loopShift g.symm p) U := by
  rcases p with ⟨px, pp⟩
  ext q
  rcases q with ⟨qx, qp⟩
  constructor
  · rintro ⟨η, hη, hq⟩
    change Path px qx at η
    change g.trans qp =
      pp.trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change qp =
      (g.symm.trans pp).trans (Path.Homotopic.Quotient.mk η)
    rw [Path.Homotopic.Quotient.trans_assoc, ← hq,
      ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  · rintro ⟨η, hη, hq⟩
    change Path px qx at η
    change qp =
      (g.symm.trans pp).trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change g.trans qp =
      pp.trans (Path.Homotopic.Quotient.mk η)
    rw [hq, ← Path.Homotopic.Quotient.trans_assoc,
      ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans]

theorem loopShift_cont
    [LocallyPathConnectedSpace X]
    (g : Path.Homotopic.Quotient (default : X) default) :
    Continuous (loopShift g) := by
  rw [(basis_assemble (X := X)).continuous_iff]
  rintro _ ⟨p, U, hU, hp, rfl⟩
  rw [loopShift_preim]
  exact TopologicalSpace.GenerateOpen.basic _
    ⟨loopShift g.symm p, U, hU, hp, rfl⟩

def deckAct
    (g : FundamentalGroup X (default : X))
    (p : UniversalCover X) : UniversalCover X :=
  loopShift (FundamentalGroup.toPath g⁻¹) p

instance deckMulAction :
    MulAction (FundamentalGroup X (default : X)) (UniversalCover X) where
  smul := deckAct
  one_smul p := by
    change deckAct 1 p = p
    refine Sigma.ext (x := deckAct 1 p) (y := p) rfl ?_
    change HEq
      ((Path.Homotopic.Quotient.refl default).trans p.2) p.2
    exact heq_of_eq (Path.Homotopic.Quotient.refl_trans p.2)
  mul_smul g h p := by
    change deckAct (g * h) p = deckAct g (deckAct h p)
    refine Sigma.ext
      (x := deckAct (g * h) p) (y := deckAct g (deckAct h p)) rfl ?_
    simp only [deckAct, loopShift, mul_inv_rev]
    exact heq_of_eq
      (Path.Homotopic.Quotient.trans_assoc
        (FundamentalGroup.toPath g⁻¹)
        (FundamentalGroup.toPath h⁻¹) p.2)

@[simp]
theorem proj_deckAct
    (g : FundamentalGroup X (default : X)) (p : UniversalCover X) :
    proj (g • p) = proj p :=
  rfl

theorem proj_eq_iff_smul
    (p q : UniversalCover X) :
    proj p = proj q ↔
      ∃ g : FundamentalGroup X (default : X), g • p = q := by
  constructor
  · intro hpq
    rcases p with ⟨x, a⟩
    rcases q with ⟨y, b⟩
    change x = y at hpq
    subst y
    refine ⟨(FundamentalGroup.fromPath (b.trans a.symm))⁻¹, ?_⟩
    refine Sigma.ext
      (x := deckAct (FundamentalGroup.fromPath (b.trans a.symm))⁻¹
        (⟨x, a⟩ : UniversalCover X))
      (y := (⟨x, b⟩ : UniversalCover X)) rfl ?_
    simp only [deckAct, inv_inv, FundamentalGroup.toPath,
      FundamentalGroup.fromPath, loopShift]
    rw [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  · rintro ⟨g, rfl⟩
    exact proj_deckAct g p

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] in
omit [T2Space M]
  [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem contMDiff_of_proj_eq
    {f : UniversalCover M → UniversalCover M}
    (hf : Continuous f)
    (hproj : ∀ x, proj (f x) = proj x) :
    ContMDiff I I ∞ f := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hf.continuousAt, ?_⟩
  have hcharts :
      (extChartAt I (f x) : UniversalCover M → E) ∘ f =
        extChartAt I x := by
    funext y
    simp only [Function.comp_apply]
    rw [extChartAt_proj_eq (I := I) (f x) (f y),
      extChartAt_proj_eq (I := I) x y, hproj x, hproj y]
  rw [hcharts]
  exact contMDiffAt_extChartAt

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M]
  [T2Space M]
  [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem deckAct_contMDiff
    (g : FundamentalGroup M (default : M)) :
    ContMDiff I I ∞ (fun p : UniversalCover M => g • p) :=
  contMDiff_of_proj_eq (loopShift_cont (FundamentalGroup.toPath g⁻¹))
    (proj_deckAct g)

noncomputable def deckDiffeo
    (g : FundamentalGroup M (default : M)) :
    Diffeomorph I I (UniversalCover M) (UniversalCover M) ∞ where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := deckAct_contMDiff g
  contMDiff_invFun := by
    change ContMDiff I I ∞ (fun p : UniversalCover M => g⁻¹ • p)
    exact deckAct_contMDiff g⁻¹

end Smooth

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
