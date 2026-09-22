/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain

/-!
# A producer skeleton for annuli between essential polygons on a solid torus

The endpoint is the existing `Moise286`, with the ambient closure of each actual connected
component and the original two polygon labels. Moise, printed p. 204 (PDF p. 214), first uses
Theorem 28.3 to put the finite polygon family in standard position. He then recognizes bands
crossing the cylindrical diagram, excludes a Mobius band using orientability, and treats the
latitudinal case separately.

This skeleton proposes a stronger common product-coordinate formulation of the first step.
It is not the literal statement of Theorem 28.3. Producing the boundary PL torus chart and
simultaneously straightening all essential polygons to distinct fibers is the main geometric
obligation. The chart concerns the boundary only; an extension over the solid torus is not
asserted. A proof must establish the parallelization without using `Moise286`, and must justify
the use of the frozen no-PL-disk hypothesis, rather than assume a surface classification.

Leaves, both owned by the PL surface lane:
* `exists_product_coordinates_for_disjoint_essential_polygons`: simultaneous boundary
  coordinates and distinct labeled fibers for the whole finite family; UNREVIEWED.
* `exists_annulus_parametrization_of_product_circle_cut`: recognize a component of the product
  model cut along finitely many fibers, with the precise two endpoint images; UNREVIEWED.

The second leaf has no solid-torus or essential-polygon hypotheses. Its remaining work is to
find the two neighboring marked points on the second PL circle, identify the product component,
and transport its ambient closure. `n > 1` and injectivity of the marking prevent one circle
from being used for both ends. The indices are not presumed to be in cyclic order. Both PL
circles and all marked points are tied to the single coordinate map supplied by the first leaf.

Existing inputs inspected: `CircleArcs.lean` supplies
`exists_arc_decomposition_of_isPLSphere_one`, with PL arcs between two specified points.
`IsPLHomeomorphOn.prodMap` and `IsPLHomeomorphOn.image_closure` supply product and closure
transport.
`AnnulusCylinder` already recognizes an interval cylindrical diagram as an annulus, with
orientability excluding the twisted case. No replacement for that classification is introduced.
`AnnulusComplement`, `AnnulusComponents`, `SurfaceAnnulusComplement` and `SurfaceCircleComplement`
provide collars, surface complements and component control, but not simultaneous polygon
coordinates or the finite-cut endpoint parameterization. `TorusMeridian` provides an embedded
example, not a producer for every combinatorial solid torus.

Joint fixture: UNTESTED. A proposed nondegenerate instance is the square solid torus
`1 <= max (abs x) (abs y) <= 3`, `abs z <= 1`, with the two rectangular meridians in `y = 0`
on the positive and negative x sides. The shared PL product chart, combinatorial-solid-torus
witness and no-disk witnesses have not been formalized. In particular, this description is not
a joint satisfiability certificate. The `n = 2` case and endpoint labels require review.

The assembly is proved from the two leaves. Its transitive axiom closure still contains
`sorryAx`; the named input remains open until both reviewed producers are proved in real modules.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_product_coordinates_for_disjoint_essential_polygons
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) {n : ℕ} (G : Fin n → Set E3)
    (hn : 1 < n) (hG : ∀ i, IsPLSphere 1 (G i)) (hGS : ∀ i, G i ⊆ frontier S)
    (hdisj : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hess : ∀ i, ¬ ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
        G i = r '' stdSimplexBoundary 2) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3) (q : Fin n → E3),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier S) ∧
      (∀ i, q i ∈ Q) ∧ Function.Injective q ∧ ∀ i, G i = f '' (J ×ˢ {q i}) := by
  sorry

theorem exists_annulus_parametrization_of_product_circle_cut
    {J Q X : Set E3} (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : E3 × E3 → E3} (hf : IsPLHomeomorphOn f (J ×ˢ Q) X)
    {n : ℕ} (hn : 1 < n) (q : Fin n → E3) (hq : ∀ i, q i ∈ Q)
    (hinj : Function.Injective q) {x : E3}
    (hx : x ∈ X \ (⋃ i, f '' (J ×ˢ {q i}))) :
    ∃ i j : Fin n, i ≠ j ∧ ∃ ρ : E3 × ℝ → E3,
      IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1)
        (closure (connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) x)) ∧
      f '' (J ×ˢ {q i}) = ρ '' (J ×ˢ {(0 : ℝ)}) ∧
      f '' (J ×ˢ {q j}) = ρ '' (J ×ˢ {(1 : ℝ)}) := by
  sorry

theorem moise286 : Moise286 := by
  classical
  intro S hS n G hn hG hGS hdisj hess x hx
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G hn hG hGS hdisj hess
  have hG_eq : G = fun i => f '' (J ×ˢ {q i}) := funext hfamily
  rw [hG_eq] at hx ⊢
  obtain ⟨i, j, hij, ρ, hρ, hzero, hone⟩ :=
    exists_annulus_parametrization_of_product_circle_cut hJ hQ hf hn q hq hinj hx
  exact ⟨i, j, hij, J, ρ, hJ, hρ, hzero, hone⟩

end DifferentialGeometry.Topology.PiecewiseLinear
