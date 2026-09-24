import DifferentialGeometry.Topology.Homology.RelativeMaps

namespace DifferentialGeometry.Topology

open Set

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralSingularHomologyMap_eq_of_relativeHomologyMap_eq
    (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B)
    (a : integralSingularHomology n X) (b : integralSingularHomology n Y)
    (μ : integralRelativeHomology n A) (ν : integralRelativeHomology n B)
    (ha : integralAbsoluteToRelative n A a = μ)
    (hb : integralAbsoluteToRelative n B b = ν)
    (hlocal : integralRelativeHomologyMap n f hf μ = ν)
    (hinj : Function.Injective (integralAbsoluteToRelative n B)) :
    integralSingularHomologyMap n f a = b := by
  apply hinj
  have hnat := LinearMap.congr_fun (integralAbsoluteToRelative_natural n f hf) a
  simpa only [LinearMap.comp_apply, ha, hb, hlocal] using hnat

theorem integralSingularHomologyMap_eq_of_singleton_fiber
    (n : ℕ) (f : C(X, Y)) {x : X} {y : Y} (hf : f ⁻¹' {y} = {x})
    (a : integralSingularHomology n X) (b : integralSingularHomology n Y)
    (μ : integralRelativeHomology n ({x}ᶜ : Set X))
    (ν : integralRelativeHomology n ({y}ᶜ : Set Y))
    (ha : integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ)
    (hb : integralAbsoluteToRelative n ({y}ᶜ : Set Y) b = ν)
    (hlocal : integralRelativeHomologyMap n f
      (show MapsTo f ({x}ᶜ) ({y}ᶜ) from fun _ hz hzy => hz (hf ▸ hzy)) μ = ν)
    (hinj : Function.Injective (integralAbsoluteToRelative n ({y}ᶜ : Set Y))) :
    integralSingularHomologyMap n f a = b :=
  integralSingularHomologyMap_eq_of_relativeHomologyMap_eq n f
    (show MapsTo f ({x}ᶜ) ({y}ᶜ) from fun _ hz hzy => hz (hf ▸ hzy))
    a b μ ν ha hb hlocal hinj

end DifferentialGeometry.Topology
