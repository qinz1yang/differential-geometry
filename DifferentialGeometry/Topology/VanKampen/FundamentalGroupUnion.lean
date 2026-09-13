import DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology.VanKampen

variable {X : Type u} [TopologicalSpace X]

private noncomputable def amalgamatedProductCollapse
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [Subsingleton (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))]
    [Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2))] :
    Monoid.PushoutI (fundamentalGroupAmalgamation U V x₀ hx₀) →*
      FundamentalGroup U (leftBasepoint U x₀ hx₀.1) :=
  Monoid.PushoutI.lift
    (fun i => match i with
      | false => MonoidHom.id _
      | true => 1)
    (1 : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀) →*
      FundamentalGroup U (leftBasepoint U x₀ hx₀.1))
    (by intro i; exact Subsingleton.elim _ _)

private theorem amalgamatedProductCollapse_comp_of_false
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [Subsingleton (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))]
    [Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2))] :
    (amalgamatedProductCollapse U V x₀ hx₀).comp
        (Monoid.PushoutI.of
          (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false) =
      MonoidHom.id _ := by
  ext g
  simp [amalgamatedProductCollapse]

private theorem of_false_comp_amalgamatedProductCollapse
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [Subsingleton (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))]
    [Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2))] :
    (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false).comp
        (amalgamatedProductCollapse U V x₀ hx₀) =
      MonoidHom.id _ := by
  refine Monoid.PushoutI.hom_ext_nonempty
    (φ := fundamentalGroupAmalgamation U V x₀ hx₀) ?_
  intro i
  cases i with
  | false =>
    rw [MonoidHom.comp_assoc, amalgamatedProductCollapse_comp_of_false,
      MonoidHom.comp_id, MonoidHom.id_comp]
  | true =>
    have hcollapse : (amalgamatedProductCollapse U V x₀ hx₀).comp
        (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x₀ hx₀) true) =
        1 := Subsingleton.elim _ _
    rw [MonoidHom.comp_assoc, hcollapse, MonoidHom.id_comp]
    exact Subsingleton.elim _ _

private noncomputable def amalgamatedProductEquivLeft
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [Subsingleton (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))]
    [Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2))] :
    Monoid.PushoutI (fundamentalGroupAmalgamation U V x₀ hx₀) ≃*
      FundamentalGroup U (leftBasepoint U x₀ hx₀.1) :=
  MonoidHom.toMulEquiv
    (amalgamatedProductCollapse U V x₀ hx₀)
    (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false)
    (of_false_comp_amalgamatedProductCollapse U V x₀ hx₀)
    (amalgamatedProductCollapse_comp_of_false U V x₀ hx₀)

noncomputable def fundamentalGroupEquivOfOpenCover
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup X x₀ ≃* FundamentalGroup U (leftBasepoint U x₀ hx₀.1) :=
  (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).symm.trans
    (amalgamatedProductEquivLeft U V x₀ hx₀)

theorem subsingleton_fundamentalGroup_of_open_cover
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))]
    (h : Subsingleton (FundamentalGroup U (leftBasepoint U x₀ hx₀.1))) :
    Subsingleton (FundamentalGroup X x₀) :=
  (fundamentalGroupEquivOfOpenCover U V hU hV hcover x₀ hx₀).subsingleton

end DifferentialGeometry.Topology.VanKampen
