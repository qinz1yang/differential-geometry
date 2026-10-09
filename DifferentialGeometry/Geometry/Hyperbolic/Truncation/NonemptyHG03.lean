import DifferentialGeometry.Geometry.Hyperbolic.Truncation.UniformizationHG03
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.PeripheralLatticeHG03
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.OrientationHG03

/-!
# HG03 无条件 producer（O-HG-HG03 G4，后缀 `_HG03`）

`nonempty_hyperbolicTruncation_HG03 : ∀ H : FiniteVolumeHyperbolicModel.{u},
Nonempty (HyperbolicTruncation H)` —— ch12 D-R3-20 的显式输入 `hHG03` 的逐字形状。
组装：G2 `exists_truncation_of_peripheral_HG03`（uniformization 已消）的前提 (P) 由
G3a `peripheral_lattice_of_det_pos_HG03`（free action + 正 det ⇒ 周边群 = 平移格）与
G3b `det_pos_of_orientation_HG03`（`H.orientation` ⇒ 正 det）给出。
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- HG03：每个有限体积、截面曲率 −1/4、完备、定向的双曲 3-流形模型都有 `HyperbolicTruncation`。 -/
theorem nonempty_hyperbolicTruncation_HG03 :
    ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H) := by
  intro H
  refine exists_truncation_of_peripheral_HG03 H ?_
  intro Γ _ _ _ hcov e he ξ hξ
  exact peripheral_lattice_of_det_pos_HG03 Γ hcov
    (fun a δ hδ f hf => det_pos_of_orientation_HG03 H Γ e he a δ hδ f hf) ξ hξ

/-- consumer：与 ch12 binder `hHG03` 的类型逐字相等（`type_of%`）。 -/
example : type_of% @nonempty_hyperbolicTruncation_HG03.{u} =
    (∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H)) := rfl

/-- consumer：每个模型的 cusp 个数 = end 个数（S-HG-INTAKE G1 的 `endCount_eq_count`）。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) : ∃ Tr : HyperbolicTruncation H,
    DifferentialGeometry.Geometry.Topology.endCount H.Carrier = (Tr.count : ℕ∞) := by
  obtain ⟨Tr⟩ := nonempty_hyperbolicTruncation_HG03 H
  exact ⟨Tr, Tr.endCount_eq_count⟩

end DifferentialGeometry.Geometry.Hyperbolic
