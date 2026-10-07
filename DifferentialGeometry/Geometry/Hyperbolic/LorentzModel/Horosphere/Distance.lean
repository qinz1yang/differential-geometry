import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Diameter

noncomputable section

open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.HorosphereProjection

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open AsymptoticRays (rayTo dist_rayTo_self)
open Busemann (busemann horosphere)

variable {n : ℕ} {M : Type*} [PseudoEMetricSpace M]

theorem edist_le_ediam_horosphere_add_busemann_sub
    (ξ : BoundaryH n) (p : HUpper n → M) {L : ℝ≥0} (hp : LipschitzWith L p)
    (x y : HUpper n) :
    edist (p x) (p y) ≤ Metric.ediam (p '' horosphere ξ (busemann ξ x)) +
      L * ENNReal.ofReal |busemann ξ y - busemann ξ x| := by
  let z := rayTo y ξ (busemann ξ y - busemann ξ x)
  have hz : z ∈ horosphere ξ (busemann ξ x) := by
    change busemann ξ (rayTo y ξ (busemann ξ y - busemann ξ x)) = busemann ξ x
    rw [busemann_rayTo]
    ring
  have hx : x ∈ horosphere ξ (busemann ξ x) := rfl
  have hhor := Metric.edist_le_ediam_of_mem (Set.mem_image_of_mem p hx) (Set.mem_image_of_mem p hz)
  have hray := hp y z
  rw [edist_dist, dist_rayTo_self] at hray
  have htriangle := edist_triangle (p x) (p z) (p y)
  rw [edist_comm (p z) (p y)] at htriangle
  exact htriangle.trans (add_le_add hhor hray)

theorem edist_le_add_of_ediam_horosphere_le
    (ξ : BoundaryH n) (p : HUpper n → M) {L : ℝ≥0} (hp : LipschitzWith L p)
    (x y : HUpper n) {D H : ℝ≥0∞}
    (hdiam : Metric.ediam (p '' horosphere ξ (busemann ξ x)) ≤ D)
    (hheight : L * ENNReal.ofReal |busemann ξ y - busemann ξ x| ≤ H) :
    edist (p x) (p y) ≤ D + H :=
  (edist_le_ediam_horosphere_add_busemann_sub ξ p hp x y).trans (add_le_add hdiam hheight)

theorem eventually_edist_le_of_busemann_eq
    (hn : 1 ≤ n) (P : Subgroup (ProjectiveOrthogonalGroup.PO n 1)) (ξ : BoundaryH n) (c : ℝ)
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : ProjectiveOrthogonalGroup.PO n 1) ξ = ξ ∧
      BusemannCocycle.poConfFactor hn (γ : ProjectiveOrthogonalGroup.PO n 1) ξ = 1)
    (hcompact : IsCompact ((Quotient.mk
      (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))) '' horosphere ξ c))
    (p : HUpper n → M) {L : ℝ≥0} (hp : LipschitzWith L p)
    (hinv : ∀ (γ : P) (x : HUpper n), p ((HyperbolicAction.poMulAction hn).smul
      (γ : ProjectiveOrthogonalGroup.PO n 1) x) = p x)
    {D : ℝ≥0∞} (hD : 0 < D) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ x y : HUpper n, busemann ξ x = c - t →
      edist (p x) (p y) ≤ D + L * ENNReal.ofReal |busemann ξ y - busemann ξ x| := by
  have hdecay := tendsto_ediam_image_horosphere hn P ξ c hhor hcompact p hp hinv
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hdecay D hD] with t ht
  intro x y hx
  have hd : Metric.ediam (p '' horosphere ξ (busemann ξ x)) ≤ D := by rwa [hx]
  exact edist_le_add_of_ediam_horosphere_le ξ p hp x y hd le_rfl

end DifferentialGeometry.HorosphereProjection
