import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus
import DifferentialGeometry.Topology.Collar.SingleSheet

/-!
# Consumers of the F-e collar statements (E1, E2 delta, E4)

* every collar of a nearly cuspidal boundary has compact level slabs `3 ≤ z ≤ 97` (BCP01: each
  level slab is compactly contained in the collar);
* for every collar of a nearly cuspidal boundary, a smooth height with positive vertical
  derivative on `1 < z < 99` whose level `c` meets every vertical and lies in the collar has a
  level that is a smooth embedded torus (BCP01, level tori);
* a local homeomorphism from the torus onto a connected Hausdorff space is surjective (BCP03).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- Every collar of a nearly cuspidal boundary has compact level slabs `3 ≤ z ≤ 97`. -/
theorem NearlyCuspidalBoundary.isCompact_collar_slab {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) :
    IsCompact ((B.collar i).toFun '' {p : CuspHalfSpace | 3 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 97}) :=
  (B.collar i).isCompact_image_band (by norm_num [cuspDepth])

/-- Level tori in the collars of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_diffeomorph_level_torus {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {c : ℝ}
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo (1 : ℝ) 99,
      0 < deriv (fun s : ℝ => η ((B.collar i).toFun (x, halfSpaceOneLift s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo (1 : ℝ) 99,
      η ((B.collar i).toFun (x, halfSpaceOneLift s)) = c)
    (hlevel : ∀ y, η y = c →
      ∃ x : Torus, ∃ s ∈ Ioo (1 : ℝ) 99, (B.collar i).toFun (x, halfSpaceOneLift s) = y) :
    ∃ cs : ChartedSpace (Topology.Morse.MorseModel 2) {y : W.Carrier // η y = c},
      letI := cs
      IsManifold 𝓘(ℝ, Topology.Morse.MorseModel 2) ∞ {y : W.Carrier // η y = c} ∧
      ContMDiff 𝓘(ℝ, Topology.Morse.MorseModel 2) W.model ∞
        (Subtype.val : {y : W.Carrier // η y = c} → W.Carrier) ∧
      Nonempty ({y : W.Carrier // η y = c} ≃ₘ⟮𝓘(ℝ, Topology.Morse.MorseModel 2), torusModel⟯
        Torus) :=
  (B.collar i).exists_diffeomorph_level_torus hη (by norm_num) (by norm_num [cuspDepth]) hvert
    hcross hlevel

/-- A local homeomorphism from the torus onto a connected Hausdorff space is surjective (the
covering half of BCP03's sheet count). -/
theorem torus_surjective_of_isLocalHomeomorph {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [PreconnectedSpace Y] {p : Torus → Y} (hp : IsLocalHomeomorph p) : Surjective p :=
  Topology.surjective_of_isLocalHomeomorph_of_compactSpace hp

end DifferentialGeometry.Geometry.Collapse
