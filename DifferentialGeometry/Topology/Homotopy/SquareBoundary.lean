import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps



noncomputable section

open Set Function ContinuousMap
open scoped Topology unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]



theorem square_boundary_homotopic {a b c d : X}
    (bottom : Path a b) (top : Path c d) (left : Path a c) (right : Path b d)
    (F : C(I × I, X))
    (hbottom : ∀ s, F (0, s) = bottom s) (htop : ∀ s, F (1, s) = top s)
    (hleft : ∀ t, F (t, 0) = left t) (hright : ∀ t, F (t, 1) = right t) :
    (bottom.trans right).Homotopic (left.trans top) := by
  let p₁ : Path ((0, 0) : I × I) (1, 1) :=
    .prod (.trans (.refl _) .id) (.trans .id (.refl _))
  let p₂ : Path ((0, 0) : I × I) (1, 1) :=
    .prod (.trans .id (.refl _)) (.trans (.refl _) .id)
  let H : p₁.Homotopy p₂ :=
    Path.Homotopic.prodHomotopy (.trans (.reflTrans _) (.symm <| .transRefl _))
      (.trans (.transRefl _) (.symm <| .reflTrans _))
  have ha : a = F (0, 0) := (hbottom 0 |>.trans bottom.source).symm
  have hd : d = F (1, 1) := (htop 1 |>.trans top.target).symm
  refine ⟨((H.map F).pathCast ha hd).cast ?_ ?_⟩
  · ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, p₁, Path.prod_coe,
      Path.trans_apply, Path.refl_apply]
    split_ifs <;> simp only [hbottom, hright] <;> rfl
  · ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, p₂, Path.prod_coe,
      Path.trans_apply, Path.refl_apply]
    split_ifs <;> simp only [hleft, htop] <;> rfl

end DifferentialGeometry.Topology
