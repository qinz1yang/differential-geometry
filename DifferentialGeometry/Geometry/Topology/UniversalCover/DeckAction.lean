import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Geometry.Topology.UniversalCover.Manifold

/-!
# Deck transformations of the path-space universal cover

The fundamental group acts on the path-space model of the universal cover by
prefixing the represented path with a loop.  The inverse in `deckAct` accounts
for Mathlib's composition-order convention for multiplication in an endomorphism
group, so this is a left action.

The action preserves the projection, and its orbits are exactly the fibres of
the projection.  On a smooth manifold every action map is a diffeomorphism.
-/

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]

/-- Prefix the path represented by a universal-cover point with a loop at the
chosen base point. -/
def loopShift
    (g : Path.Homotopic.Quotient (default : X) default)
    (p : UniversalCover X) : UniversalCover X :=
  ⟨p.1, g.trans p.2⟩

/-- The inverse image of a slice-topology basic open under a loop shift is the
basic open based at the oppositely shifted point. -/
theorem loopShift_preim
    (g : Path.Homotopic.Quotient (default : X) default)
    (p : UniversalCover X)
    (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U) :
    loopShift g ⁻¹' basicOpen p U hU hp =
      basicOpen (loopShift g.symm p) U hU hp := by
  ext q
  constructor
  · rintro ⟨η, hη, hq⟩
    change g.trans q.2 =
      p.2.trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change q.2 =
      (g.symm.trans p.2).trans (Path.Homotopic.Quotient.mk η)
    calc
      q.2 = (Path.Homotopic.Quotient.refl default).trans q.2 :=
        (Path.Homotopic.Quotient.refl_trans q.2).symm
      _ = (g.symm.trans g).trans q.2 := by
        rw [Path.Homotopic.Quotient.symm_trans]
      _ = g.symm.trans (g.trans q.2) :=
        Path.Homotopic.Quotient.trans_assoc g.symm g q.2
      _ = g.symm.trans
          (p.2.trans (Path.Homotopic.Quotient.mk η)) :=
        congrArg (fun z => g.symm.trans z) hq
      _ = (g.symm.trans p.2).trans
          (Path.Homotopic.Quotient.mk η) :=
        (Path.Homotopic.Quotient.trans_assoc g.symm p.2 _).symm
  · rintro ⟨η, hη, hq⟩
    change q.2 =
      (g.symm.trans p.2).trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change g.trans q.2 =
      p.2.trans (Path.Homotopic.Quotient.mk η)
    calc
      g.trans q.2 =
          g.trans ((g.symm.trans p.2).trans
            (Path.Homotopic.Quotient.mk η)) := by rw [hq]
      _ = (g.trans (g.symm.trans p.2)).trans
          (Path.Homotopic.Quotient.mk η) :=
        (Path.Homotopic.Quotient.trans_assoc g _ _).symm
      _ = ((g.trans g.symm).trans p.2).trans
          (Path.Homotopic.Quotient.mk η) := by
        rw [← Path.Homotopic.Quotient.trans_assoc]
      _ = p.2.trans (Path.Homotopic.Quotient.mk η) := by
        rw [Path.Homotopic.Quotient.trans_symm,
          Path.Homotopic.Quotient.refl_trans]

/-- Prefixing by a fixed loop is continuous for the slice topology. -/
theorem loopShift_cont
    [LocPathConnectedSpace X]
    (g : Path.Homotopic.Quotient (default : X) default) :
    Continuous (loopShift g) := by
  rw [(basis_assemble (X := X)).continuous_iff]
  rintro _ ⟨p, U, hU, hp, rfl⟩
  rw [loopShift_preim]
  exact TopologicalSpace.GenerateOpen.basic _
    ⟨loopShift g.symm p, U, hU, hp, rfl⟩

/-- The fundamental-group action on the path-space universal cover. -/
def deckAct
    (g : FundamentalGroup X (default : X))
    (p : UniversalCover X) : UniversalCover X :=
  loopShift (FundamentalGroup.toPath g⁻¹) p

/-- The left action of the fundamental group by deck transformations. -/
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

/-- A deck transformation preserves the universal-cover projection. -/
@[simp]
theorem proj_deckAct
    (g : FundamentalGroup X (default : X)) (p : UniversalCover X) :
    proj (g • p) = proj p :=
  rfl

/-- Two universal-cover points have the same projection exactly when one is a
fundamental-group translate of the other. -/
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
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] in
/-- A continuous self-map of the universal cover that preserves the projection
is smooth. -/
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] in
/-- Every fundamental-group deck transformation is smooth. -/
theorem deckAct_contMDiff
    (g : FundamentalGroup M (default : M)) :
    ContMDiff I I ∞ (fun p : UniversalCover M => g • p) :=
  contMDiff_of_proj_eq (loopShift_cont (FundamentalGroup.toPath g⁻¹))
    (proj_deckAct g)

/-- The diffeomorphism of the universal cover induced by a fundamental-group
element. -/
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
