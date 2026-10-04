import DifferentialGeometry.Geometry.Comparison.Volume.AllCentreSeedVolume

/-!
# Consumer of A13: the `hvol` shape of the local flow-limit theorem

`exists_pointed_local_flow_limits_of_local_solutions` (`RF/Compactness/Limits/LocalPointedFlowLimit.lean`)
takes `hvol : ∀ r R, 0 < r → r < R → ∀ C ≥ 0, ∃ a κ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a⁴ C² ≤ 1 ∧ …`.
Following the review (§8): choose a small positive radius `a` with `r + a ≤ R` and `a⁴ C² ≤ 1`,
then apply A13 on the comparison ball of radius `max r r₀`.  The curvature buffer is an input,
per radius (`Λ ρ` on `B(p, 3ρ)`); `a` and `κ` are chosen before the manifold.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- The `hvol` shape from a seed volume and per-radius sectional buffers, uniformly over closed
three-manifolds. -/
theorem exists_hvol_shape_of_seed {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w) (Λ : ℝ → ℝ)
    (hΛ : ∀ ρ, 0 ≤ Λ ρ) :
    ∀ r R' : ℝ, 0 < r → r < R' → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
        ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
          [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
          (g : SmoothRiemannianMetric ThreeModel X) (p : X),
          ENNReal.ofReal (w * r₀ ^ 3) ≤
              Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p r₀) →
          (∀ y ∈ riemannianBallOf g p (3 * max r r₀),
            SectionalBoundedBelowAt g y (-Λ (max r r₀))) →
          ∀ x ∈ riemannianClosedBallOf g p r,
            ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
              Integral.Measure.riemannianVolumeMeasure ThreeModel X g
                (riemannianBallOf g x a) := by
  intro r R' hr hrR' C hC
  let a : ℝ := min (min (R' - r) 1) (min (1 / (C + 1)) (max r r₀))
  have hC1 : 0 < C + 1 := by linarith
  have ha : 0 < a := by
    have h1 : 0 < R' - r := by linarith
    have h2 : 0 < 1 / (C + 1) := by positivity
    have h3 : 0 < max r r₀ := lt_max_of_lt_left hr
    exact lt_min (lt_min h1 one_pos) (lt_min h2 h3)
  have haR' : a ≤ R' - r := (min_le_left _ _).trans (min_le_left _ _)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have haC : a ≤ 1 / (C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have haR : a ≤ max r r₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hR : r₀ ≤ max r r₀ := le_max_right _ _
  obtain ⟨κ, hκ, hvol⟩ := A13_all_centre_volume_of_seed.{u} hr₀ hw (hΛ (max r r₀)) hR ha haR
  refine ⟨a, κ, ha, hκ, by linarith, ?_, ?_⟩
  · have hac : a * C ≤ 1 := by
      have h := (le_div_iff₀ hC1).mp haC
      nlinarith
    have hac0 : 0 ≤ a * C := mul_nonneg ha.le hC
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    calc a ^ 4 * C ^ 2 = (a * C) ^ 2 * a ^ 2 := by ring
      _ ≤ 1 * 1 := by
          apply mul_le_mul _ ha2 (by positivity) zero_le_one
          nlinarith
      _ = 1 := by norm_num
  · intro X _ _ _ _ _ g p hseed hsec x hx
    rw [finrank_euclideanSpace_fin]
    exact hvol X g p hseed hsec x (riemannianClosedBallOf_mono g p (le_max_left r r₀) hx)

end FILL910
