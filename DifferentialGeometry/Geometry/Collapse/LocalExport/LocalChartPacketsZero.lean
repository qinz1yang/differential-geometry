import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidual

/-!
# LC87 with LC73's zero shell clauses on the SAME zero family (`LocalChartPacketsZ`)

Blueprint 207B, SGP02 (B:4473–4480: "LC73/LCP04 give an actual `(1, β₁)`-splitting there whose
real coordinate is EXACTLY `d(p₀,·) − d(p₀,p_i)` in reference units"), TCP02 (B:5362), TCP03
(B:5430: "LC73 at EVERY `x ∈ D_i`"), EGP03; blueprint 207A, LC73
(`thm:collapse-prescribed-annular-adapted`, A:24318).

`LocalChartPacketsZ … ζ Λz` extends `LocalChartPacketsR` (no delivered structure is edited) by the
two zero shell clauses that LPA05 (`lpa05_selected_zero_packets_with_local_comparison`) proves on
the SAME zero family and that the R producer drops:
* `zero_shell_split` (X82 / LC70): at every point `q` of the CLOSED shell `r/10 ≤ d(c, q) ≤ 10r`
  of a selected zero ball, an actual Kleiner–Lott `(1, β₁)`-splitting of `(X, ρ(q)⁻¹ d, q)` whose
  real coordinate is EXACTLY `ρ(q)⁻¹ (d(c, ·) − d(c, q))`;
* `zero_adapted` (LC73): at every such `q` and every ratio `λ ≥ Λz`, the prescribed function
  `λ (η_c − η_c(q))` of the ORIGINAL radial function is adapted of quality `ζ` (in
  `λ² r⁻² g`) to an actual splitting with real coordinate `λ (d(c, ·) − d(c, q))` (in `r⁻¹ d`).
The fields are LPA05's fourth and fifth clauses verbatim. `ZeroModelFamily` does not store them
("LC80 item 3 … is not stored here") and the packets do not record `RadialConeData` of their cones,
so they cannot be re-derived from `LocalChartPacketsR`.

Producer: `eventually_nonempty_localChartPacketsZ` (LocalChartPacketsZeroProducer).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The final family with LC73's zero shell clauses** (SGP02 (R0), TCP02 (TR0), EGP03 (ER0)
and the zero blocks of SGP03/TCP03/EGP04): a `LocalChartPacketsR` whose zero family carries, at
every point `q` of the closed shell of every selected zero ball, X82's splitting with real
coordinate exactly `ρ(q)⁻¹ (d(c, ·) − d(c, q))`, and LC73's adapted coordinate of quality `ζ` for
every ratio `λ ≥ Λz`. -/
structure LocalChartPacketsZ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
    extends
      LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    where
  /-- X82 (LC70) at every point of the closed shell of every selected zero ball. -/
  zero_shell_split : ∀ c (hc : c ∈ zero.centres), ∀ q, (zero.zero c hc).radius / 10 ≤ dist c q →
    dist c q ≤ 10 * (zero.zero c hc).radius →
    ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
      ∃ (z : Zf) (F : @KleinerLottApprox X
        (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
        (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
        q (WithLp.toLp 2 (0, z)) (β 1)),
        ∀ x : X, (@KleinerLottApprox.toFun X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
          (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
          q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
          (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))
  /-- LC73 at every point of the closed shell of every selected zero ball, every ratio `λ ≥ Λz`. -/
  zero_adapted : ∀ c (hc : c ∈ zero.centres), ∀ q, (zero.zero c hc).radius / 10 ≤ dist c q →
    dist c q ≤ 10 * (zero.zero c hc).radius →
    ∀ (lam : ℝ) (hlam : 0 < lam), Λz ≤ lam →
    let R := (zero.zero c hc).radius
    let hR : 0 < R := (zero.zero c hc).radius_pos
    let η := (zero.zero c hc).radial
    let mr := mX.rescale R⁻¹ (inv_pos.mpr hR)
    let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX) g
      hmetric hR
    let := mr.rescale lam hlam
    letI := (mr.rescale_completeSpace_iff lam hlam).mpr
      ((mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
        (@complete_of_compact X mX.toUniformSpace _))
    letI := radialScaledBundle gr lam hlam
    letI := radialScaledContinuous gr lam hlam
    letI := radialScaledManifold (m := mr) gr hmr lam hlam
    let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
    let ψ := fun x => lam * (η x - η q)
    ∃ hEnorm : IsMetricNorm h,
      ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
        ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
        (∀ x, (κ.toFun x).fst = lam *
          (@dist X mr.toDist c x - @dist X mr.toDist c q)) ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
        (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
        (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
        ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
          ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
          intrinsicGeodesic h hEnorm x u (dist x y) = y →
          |mvfderiv (I := I3) ψ x u -
            ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ

end DifferentialGeometry.Geometry.Collapse
