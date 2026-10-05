import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircleApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedSTG
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedApplications

/-!
# EDP06's collar → circle step on the staged final family (`3βc ≤ β 2` discharged)

Lane C14-STG. Consumer of `exists_c14d_staged_assignment_STG`: lane C14-EDP6's binding
`eventually_edp06_collar_circle_EDP6` needs, besides LC20's tail, a scale in LC02's window at a
volume `w < w₀(Λ)` and the parameter facts `β 3 ≤ ϑ₃`, `3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1`. The
staged assignment provides all of them on the SAME family `LocalChartPacketsC14D` it produces:

* `edp06StagedRq_STG`: EDP06's staged request `w ≤ w₀(Λ)/2` (stage 7, read at `C14PreLip`, where
  `Λ` is fixed; `w₀` is the threshold of `eventually_edp06_collar_circle_EDP6` at `Λ₀ = Λ`);
* `exists_c14d_staged_edp06_STG`: for every STG record `Rq`, ONE admissible prefix meeting `Rq`
  with `3βc ≤ β 2`, such that on every standing sequence every late member carries a family
  `LocalChartPacketsC14D` with these parameters on which EDP06's band at every edge centre is
  two-stratum and lies in a circle chart (`‖η_a(x)‖ < 2(1 + γ)`);
* `c14RowsRqSTG_STG`: the delivered rows SGP03 / EGP04 / TCP03 in the STG contract (their `β₂`
  request reads only `C14Tol`); `C14PreFinal.rows_meets_STG`: a prefix meeting it meets the three
  rows' records, so `exists_c14d_staged_edp06_STG _ _ _ _ t c14RowsRqSTG_STG` puts the three rows
  and EDP06 on ONE assignment.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### EDP06's staged request -/

/-- **EDP06's volume threshold at the prefix's `Λ`**: the `w₀` of
`eventually_edp06_collar_circle_EDP6` at `Λ₀ = Λ` (LC20's tail with LC02's window). -/
def edp06w₀_STG (p : C14PreLip) : ℝ :=
  (eventually_edp06_collar_circle_EDP6 p.Λ_pos).choose

/-- EDP06's volume threshold is positive. -/
theorem edp06w₀_pos_STG (p : C14PreLip) : 0 < edp06w₀_STG p :=
  (eventually_edp06_collar_circle_EDP6 p.Λ_pos).choose_spec.1

/-- **EDP06's staged requests**: `w ≤ w₀(Λ)/2` (stage 7, at `C14PreLip`); every other request
trivial. (`3βc ≤ β 2` is built into `exists_c14d_staged_assignment_STG`.) -/
def edp06StagedRq_STG : C14StagedRequestsSTG :=
  { C14StagedRequestsSTG.trivial with
    w := fun p => edp06w₀_STG p / 2
    w_pos := fun p => half_pos (edp06w₀_pos_STG p) }

/-! ### EDP06 on the staged final family -/

/-- **EDP06's collar → circle step on ONE staged assignment of the final family** (lane C14-STG;
lane C14-EDP6's request `3βc ≤ β 2` discharged by `exists_c14d_staged_assignment_STG`): for the
external tolerances `t` and every STG record `Rq` there is ONE admissible prefix `P` meeting `Rq`
with `3βc ≤ β 2` such that, for every standing sequence, with the joint zero output `V ≥ T`,
`δ < δ'` and `Lmax := c14Lmax (Rq.inf edp06StagedRq_STG).toC14 P V` (above `400V` and `Rq`'s
`Lmax` request), every late member carries a family `LocalChartPacketsC14D` with exactly these
parameters on which every point of EDP06's band at an edge centre is two-stratum and lies at
distance `< 2ρ(a)` from a circle centre `a` with `‖η_a(x)‖ < 2(1 + γ)`. -/
theorem exists_c14d_staged_edp06_STG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequestsSTG) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
      ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        400 * V < c14Lmax (Rq.inf edp06StagedRq_STG).toC14 P V ∧
        Rq.Lmax P V ≤ c14Lmax (Rq.inf edp06StagedRq_STG).toC14 P V ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        ∃ L : LocalChartPacketsC14D (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc
          (c14Lmax (Rq.inf edp06StagedRq_STG).toC14 P V) P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz,
        ∀ h : ℝ, h ≤ 1 / 1000 → ∀ j (hj : j ∈ L.edge.centres) (x : X i),
        dist x j < 100 * P.Δ * ρ j →
        (let c := L.edge.chart j hj
         let hMc : CompleteSpace (X i) := complete_of_compact
         letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
         letI := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
         letI : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
           radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
         letI : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
           radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
         letI : CompleteSpace (X i) :=
           ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
         |c.coord x| < 401 / 100 * P.Δ) →
        |L.edge.smoothing x / ρ x - 4 * P.Δ| < h →
        x ∈ scaledSplittingStratum.{0, 0} ρ hρpos P.β 2 ∧
          ∃ a, ∃ ha : a ∈ L.circle.centres, dist x a < 2 * ρ a ∧
            (let c := L.circle.chart a ha
             letI := (mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))
             ‖c.coord x‖ < 2 * (1 + P.γ)) := by
  obtain ⟨P, hPt, hM, h3, h⟩ :=
    exists_c14d_staged_assignment_STG K hK A hA t (Rq.inf edp06StagedRq_STG)
  rw [C14StagedRequestsSTG.toC14_inf] at hM
  refine ⟨P, hPt, hM.inf_left, h3, ?_⟩
  intro X mX _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', h400, hL, hev⟩ := h X g hmetric α hα hstand hder hor
  have hw2 : P.w ≤ edp06w₀_STG P.toC14PreLip / 2 := hM.inf_right.w_le
  have hw : P.w < edp06w₀_STG P.toC14PreLip := by
    have := edp06w₀_pos_STG P.toC14PreLip
    linarith
  have htail := (eventually_edp06_collar_circle_EDP6 P.Λ_pos).choose_spec.2 P.w P.w_pos hw
    P.w_lt_pi X g hmetric α hα hstand
  refine ⟨V, hTV, δ, hδ, hδδ', h400,
    (C14StagedRequests.inf_Lmax_left Rq.toC14 edp06StagedRq_STG.toC14 P V).trans hL, ?_⟩
  filter_upwards [hev, htail] with i hi hti
  obtain ⟨ρ, hρ, hwin, ⟨L⟩⟩ := hi
  refine ⟨ρ, hρ, hwin, L, ?_⟩
  exact hti ρ hρ (fun p => ⟨(hwin p).1.le, (hwin p).2.le⟩) P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s
    P.b' P.s' P.ε P.γc P.βc _ P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz P.β_three.le h3
    (by rw [P.β_two]; exact P.β₂_lt.trans (by norm_num)) P.γ_pos.le (by linarith [P.Δ_gt6])
    L.toLocalChartPacketsC14

/-! ### The delivered rows in the STG contract -/

/-- **The delivered rows' common `β₂` request read early** (at `C14PreGcSTG`): SGP03's and EGP04's
are trivial, TCP03's reads only `C14Tol`. -/
def c14RowsEarlyβ₂_STG (p : C14PreGcSTG) : ℝ :=
  min 1 (min 1 (min (tcp03η₂_FAM2b p.toC14Tol) (tcp03σ_FAM2b p.toC14Tol / 3)))

/-- The rows' early `β₂` request is positive. -/
theorem c14RowsEarlyβ₂_pos_STG (p : C14PreGcSTG) : 0 < c14RowsEarlyβ₂_STG p := by
  have := tcp03η₂_pos_FAM2b p.toC14Tol
  have := tcp03σ_pos_FAM2b p.toC14Tol
  unfold c14RowsEarlyβ₂_STG
  positivity

/-- The rows' early `β₂` request is `c14RowsRq_FAM2b`'s, read through `C14PreCollar`. -/
theorem c14RowsEarlyβ₂_le_STG (q : C14PreCollar) :
    c14RowsEarlyβ₂_STG q.toGc_STG ≤ c14RowsRq_FAM2b.β₂ q :=
  le_rfl

/-- **The rows SGP03 / EGP04 / TCP03 in the STG contract**: `c14RowsRq_FAM2b` with its `β₂` request
read at `C14PreGcSTG`. -/
def c14RowsRqSTG_STG : C14StagedRequestsSTG :=
  c14RowsRq_FAM2b.withEarlyβ₂_STG c14RowsEarlyβ₂_STG c14RowsEarlyβ₂_pos_STG

/-- A prefix meeting the STG rows record meets SGP03's, EGP04's and TCP03's staged requests (so
`C14PreFinal.sgp03_FAM2b`, `.egp04_FAM2b`, `.tcp03_FAM2b` apply to it). -/
theorem C14PreFinal.rows_meets_STG {P : C14PreFinal} (h : c14RowsRqSTG_STG.toC14.Meets P) :
    sgp03StagedRq_FAM2b.Meets P ∧ egp04StagedRq_FAM2b.Meets P ∧ tcp03StagedRq_FAM2b.Meets P := by
  have hM := C14StagedRequests.Meets.of_withEarlyβ₂_STG c14RowsEarlyβ₂_le_STG h
  exact ⟨hM.inf_left, hM.inf_right.inf_left, hM.inf_right.inf_right⟩

end DifferentialGeometry.Geometry.Collapse
