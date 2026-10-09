import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegions

/-!
# Consumer of the G3 intake (S-HG-INTAKE, suffix `_HGI`)

Local finiteness of the thin regions of a discrete subgroup of `PO 3 1`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.ProjectiveOrthogonalGroup

theorem locallyFinite_thinRegion_three_HGI (Γ : Subgroup (PO 3 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) :
    LocallyFinite (OrbifoldThinRegions.thinRegion (by norm_num : 1 ≤ 3) Γ r) :=
  OrbifoldThinRegions.locallyFinite_thinRegion (by norm_num) Γ hΓ r
