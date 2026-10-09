import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLowerDistance

/-!
# Lower distortion of a cusp collar with one endpoint in the collar (statement V.2)

For a cusp embedding `e : CuspEmbedding W g K δ X`, a height `z₀` and `a` with `z₀ + a < 100`
(the slab may contain the boundary `z = 0`), and `p` with `|z(p) - z₀| ≤ a/2`:

* `CuspEmbedding.exists_preimage_frozen_le_riemannianEDistOf`: every point `y` with
  `d_g(e p, y) < √(1 - δ) a / 2` is `y = e p'` for a point `p'` of the cusp domain with
  `|z(p') - z₀| < a`, and
  `√(1 - δ) e^{-a/2} √((z' - z)² + e^{-z₀} d_q(t, t')²) ≤ d_g(e p, y)`.

Only ONE endpoint is assumed in the half-width slab: the other one is located by the slab first
exit (`CuspEmbedding.exists_slab_lift_of_pathELength_lt`) along one almost minimizing curve, and
every further competitor ends at the same preimage (injectivity on the cusp domain). This is the
form used for balls centred near the boundary (`z₀ = 0`, `a = 4/100`), whose points can reach
heights beyond `a/2`. The proof follows `CuspEmbedding.frozen_le_riemannianEDistOf` (lane B-5a),
whose suppliers are imported, not repeated.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **One-endpoint lower distortion.** If `|z(p) - z₀| ≤ a/2`, `z₀ + a < 100` and
`d_g(e p, y) < √(1 - δ) a / 2`, then `y = e p'` with `p'` in the cusp domain, `|z(p') - z₀| < a`,
and `d_g(e p, y) ≥ √(1 - δ) e^{-a/2} √((z' - z)² + e^{-z₀} d_q(t, t')²)`. -/
theorem CuspEmbedding.exists_preimage_frozen_le_riemannianEDistOf {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} {y : W.Carrier} {z₀ a : ℝ}
    (hup : z₀ + a < cuspDepth) (hp : |p.2.val 0 - z₀| ≤ a / 2)
    (hd : riemannianEDistOf g (e.toFun p) y < ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) :
    ∃ p' ∈ cuspDomain, |p'.2.val 0 - z₀| < a ∧ e.toFun p' = y ∧
      ENNReal.ofReal (Real.sqrt (1 - δ) * (Real.exp (-a / 2) *
          Real.sqrt ((p'.2.val 0 - p.2.val 0) ^ 2 +
            Real.exp (-z₀) * (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) ≤
        riemannianEDistOf g (e.toFun p) y := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  have hpd : p ∈ cuspDomain := lt_of_le_of_lt (by have := abs_le.mp hp; linarith) hup
  -- the preimage of `y`, from one almost minimizing curve
  have hd' : Manifold.riemannianEDist W.model (e.toFun p) y <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2)) := hd
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hd'
  obtain ⟨c, -, hcd, hce⟩ := e.exists_slab_lift_of_pathELength_lt hγ hup hp hγ0 hlen
  have hc1 := hcd 1 ⟨zero_le_one, le_rfl⟩
  have hc1y : e.toFun (c 1) = y := (hce 1 ⟨zero_le_one, le_rfl⟩).trans hγ1
  refine ⟨c 1, hc1.1, hc1.2, hc1y, ?_⟩
  -- the lower bound, along every competitor
  refine le_of_forall_gt fun r hr => ?_
  have hr' : riemannianEDistOf g (e.toFun p) y <
      min r (ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) := lt_min hr hd
  change Manifold.riemannianEDist W.model (e.toFun p) y < _ at hr'
  obtain ⟨σ, hσ0, hσ1, hσ, hσlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr'
  obtain ⟨c', hc', hc'd, hc'e⟩ := e.exists_slab_lift_of_pathELength_lt hσ hup hp hσ0
    (hσlen.trans_le (min_le_right _ _))
  have hc'0 : c' 0 = p := e.injOn_cuspDomain (hc'd 0 ⟨le_rfl, zero_le_one⟩).1 hpd
    ((hc'e 0 ⟨le_rfl, zero_le_one⟩).trans hσ0)
  have hc'1 : c' 1 = c 1 := e.injOn_cuspDomain (hc'd 1 ⟨zero_le_one, le_rfl⟩).1 hc1.1
    ((hc'e 1 ⟨zero_le_one, le_rfl⟩).trans (hσ1.trans hc1y.symm))
  have hlow := e.frozen_le_pathELength_comp hc' (fun t ht => (hc'd t ht).1)
    (fun t ht => (hc'd t ht).2.le)
  rw [hc'0, hc'1] at hlow
  calc _ ≤ pathELength W.model (e.toFun ∘ c') 0 1 := hlow
    _ = pathELength W.model σ 0 1 := pathELength_congr fun t ht => hc'e t ht
    _ < min r _ := hσlen
    _ ≤ r := min_le_left _ _

end DifferentialGeometry.Geometry.Collapse
