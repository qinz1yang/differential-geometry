import DifferentialGeometry.Topology.FundamentalGroup.Product

set_option autoImplicit false
noncomputable section
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem fundamentalGroup_mapOfEq_comp (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z} (hf : f x = y) (hg : g y = z) :
    FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) =
      (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) := by
  ext a
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
    simp only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl

theorem fundamentalGroup_mapOfEq_prodMk (f : C(X, Y)) (g : C(X, Z))
    {x : X} {y : Y} {z : Z} (hf : f x = y) (hg : g x = z)
    (a : FundamentalGroup X x) :
    fundamentalGroupProdEquiv y z
      (FundamentalGroup.mapOfEq (f.prodMk g) (show (f.prodMk g) x = (y, z) from Prod.ext hf hg) a) =
        (FundamentalGroup.mapOfEq f hf a, FundamentalGroup.mapOfEq g hg a) := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalGroupProdEquiv_apply]
    apply Prod.ext <;>
      simp only [Path.Homotopic.projLeft, Path.Homotopic.projRight,
        FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast] <;>
      apply congrArg Path.Homotopic.Quotient.mk <;> ext t <;> rfl

end DifferentialGeometry.Topology
