import DifferentialGeometry.Geometry.Metric.Approximation.BoundedDiameterLimit
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# LFR16, metric part: the bounded factor is compact AND connected

Blueprint 207A, LFR16 (`lem:collapse-finite-compact-factor`, A:26159–26203), second paragraph of
the proof: AC50's limit `W` of the actual residual factors is compact with `diam W ≤ D`
(`exists_compact_factor_of_approximate_products`, already in the tree), and it is connected
because the limit `Y` is connected and the projection `ℝ × W → W` is continuous and onto.

Connectedness of `Y` is derived, not assumed: a pointed limit of spaces with arbitrarily short
curves (`hcurves`, the length-space input of W3-F1) has arbitrarily short curves
(`PointedGHConverges.arbitrarily_short_curves`), hence is path connected.

The surface clause of LFR16 (the factor is a closed orientable `C^{K-1}` surface) needs LFR11's
differentiable part and is not proved here.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

/-- A nonempty metric space in which any two points are joined by continuous curves on the unit
interval is path connected. -/
theorem pathConnectedSpace_of_curves {Y : Type*} [MetricSpace Y] [Nonempty Y]
    (hcurves : ∀ a b : Y, ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b) :
    PathConnectedSpace Y := by
  refine ⟨inferInstance, fun a b => ?_⟩
  obtain ⟨c, hc, h0, h1⟩ := hcurves a b
  exact ⟨⟨⟨c, hc⟩, h0, h1⟩⟩

/-- The second factor of a connected space isometric to an `ℓ²` product with nonempty first
factor is connected. -/
theorem connectedSpace_l2_product_factor {Y E W : Type*} [MetricSpace Y] [MetricSpace E]
    [MetricSpace W] [ConnectedSpace Y] [Nonempty E] (e : Y ≃ᵢ WithLp 2 (E × W)) :
    ConnectedSpace W := by
  obtain ⟨a⟩ := ‹Nonempty E›
  have hLip : LipschitzWith 1 (fun y : Y => (e y).snd) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul]
    exact (WithLp.dist_snd_le (e x) (e y)).trans (e.dist_eq x y).le
  refine Function.Surjective.connectedSpace (f := fun y : Y => (e y).snd) (fun w => ?_)
    hLip.continuous
  refine ⟨e.symm (WithLp.toLp 2 (a, w)), ?_⟩
  simp

namespace PointedGHConverges

universe u v w z
variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {Y : Type v} [MetricSpace Y]
variable {p : ∀ n, X n} {q : Y} {D : ℝ}

/-- A pointed limit of spaces with arbitrarily short curves is connected. -/
theorem connectedSpace_of_short_curves (h : PointedGHConverges p q)
    (hcurves : ∀ n, ∀ a b : X n, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) :
    ConnectedSpace Y := by
  have : Nonempty Y := ⟨q⟩
  have hY := h.arbitrarily_short_curves hcurves
  have : PathConnectedSpace Y := pathConnectedSpace_of_curves fun a b => by
    obtain ⟨c, hc, h0, h1, -⟩ := hY a b 1 one_pos
    exact ⟨c, hc, h0, h1⟩
  infer_instance

variable {E : Type w} {Z : ℕ → Type z} [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [ProperSpace E] [ProperSpace Y]
variable {a : E} {b : ∀ i, Z i} {δ : ℕ → ℝ}

/-- **LFR16, metric part (kernel).** For a pointed limit `Y` of spaces with arbitrarily short
curves and Kleiner–Lott approximations of the sources by `E × Z i` with errors tending to zero and
`diam Z i ≤ D` uniformly, a subsequence has a factor limit `W` that is compact, connected, of
diameter at most `D`, with `Y ≃ᵢ E × W` pointed. -/
theorem exists_connected_compact_factor_of_approximate_products
    (h : PointedGHConverges p q)
    (hcurves : ∀ n, ∀ a b : X n, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        CompactSpace W ∧ ConnectedSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) := by
  obtain ⟨W, m, w, φ, hφ, hp, hc, hcpt, hdiam, hb, hx, e, he⟩ :=
    h.exists_compact_factor_of_approximate_products f hδ hD
  let := m
  have : ConnectedSpace Y := h.connectedSpace_of_short_curves hcurves
  have : Nonempty E := ⟨a⟩
  exact ⟨W, m, w, φ, hφ, hp, hc, hcpt, connectedSpace_l2_product_factor e, hdiam, hb, hx, e, he⟩

end PointedGHConverges

end GC.MetricGeometry
