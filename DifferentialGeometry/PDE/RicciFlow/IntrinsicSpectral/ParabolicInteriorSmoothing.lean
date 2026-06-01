import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DuhamelSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

/-!
# Parabolic interior smoothing: the all-orders spectral bootstrap

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
inhomogeneous heat equation `∂_t u = Δ_∇ u + f`, `u(0) = 0`, has the
`L²`-maximal-regularity solution field
`maximalRegularitySolField a hT f` (file `MaximalRegularity/Operator.lean`),
which gains *two* spatial Sobolev derivatives over the forcing `f`: its
eigen-coordinate masses at order `c + 2` are dominated by `(1 + T)²` times the
forcing masses at order `c` (`weighted_solModeCoeff_le`, uniform across the
spectrum).

The Ricci–DeTurck flow is a quasilinear parabolic equation
`∂_t u = Δ_∇ u + N(u)` whose nonlinearity `N` is **first-order**: it loses
exactly one spatial derivative (`N : H^{b+1} → Hᵇ`, zero principal symbol —
see `DeTurckPrincipalPartMatch.lean`).  Feeding such a solution into the
two-derivative-gain smoothing produces a genuine **net gain of one spatial
order per step**:

  forcing `∈ L²(Hᶜ)`  (= `N(u)`, with `u ∈ L²(H^{c+1})`, `N` first-order)
    ⟹ solution `∈ L²(H^{c+2})`   (two-derivative gain),

so `c + 1 ↦ c + 2`.  Iterating from the base regularity `b = a + 1` reaches
*every* spatial Sobolev order.  This is the **parabolic interior smoothing**
mechanism: a solution that is initially only `L²` in time at the base scale
becomes spatially smooth (lands in `Hˢ` for every `σ`) in the interior `t > 0`,
regardless of how rough the data is within the base scale.

## The mass-level abstraction

The analytic heart is the iteration of the spectral two-derivative gain against
the first-order loss of the nonlinearity, carried out at the level of the
eigen-coordinate **mass families**

  `forcingMass f c i = (1 + λᵢ)ᶜ · ‖timeModeCoeff f i‖²`,
  `solFieldMass f c i = (1 + λᵢ)ᶜ · ‖solModeCoeff hT f i‖²`.

The two-derivative gain is the per-mode bound
`solFieldMass f (c + 2) i ≤ (1 + T)² · forcingMass f c i`, summed over the
spectrum.  The first-order loss of `N` is encoded honestly, **without
circularity**, as a hypothesis controlling the forcing masses at order `c` by
the *solution* masses at order `c + 1`: this is the statement
`‖N(u)‖_{Hᶜ} ≲ ‖u‖_{H^{c+1}}` integrated in time, and it is genuinely a property
of the *operator* `N`, not the conclusion of the bootstrap.

## Main results

* `forcingMass`, `solFieldMass` — the per-mode mass families.
* `solFieldMass_summable_of_forcingMass_summable` — **the one-step
  two-derivative gain**: summable forcing masses at order `c` ⟹ summable
  solution-field masses at order `c + 2`.
* `solFieldMass_summable_succ` — **the net one-order bootstrap step**: given the
  first-order coupling (forcing masses at order `c` controlled by solution
  masses at order `c + 1`), summable solution masses at order `c + 1` ⟹
  summable solution masses at order `c + 2`.
* `solFieldMass_summable_bootstrap` — **the all-orders bootstrap**: iterating the
  step, summable solution masses at the base order `b` ⟹ summable solution
  masses at every order `b + n`, `n : ℕ`.
* `solField_into_all_tensorHs_interior` — **the headline interior-smoothing
  statement (L²-in-time)**: the maximal-regularity solution field of a
  first-order-coupled forcing lands in `Hˢ` for *every* `σ ≥ 0`, in the
  `L²`-in-time sense — the precise statement that `u ∈ L²((0,T]; ⋂_σ Hˢ)`.

## Sign convention

Geometer convention `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; resolvent
`(1 − Δ_∇)⁻¹`, eigenvalues `λᵢ ≥ 0`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ} {T : ℝ}

/-- The per-mode **forcing mass** at spatial Sobolev order `c`:
`(1 + λᵢ)ᶜ · ‖timeModeCoeff f i‖²`, the `i`-th contribution to the squared
`L²([0,T]; Hᶜ)` norm of the forcing field `f`. -/
def forcingMass (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorSobolevWeight (I := I) (M := M) i c *
    ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2

/-- The per-mode **solution-field mass** at spatial Sobolev order `c`:
`(1 + λᵢ)ᶜ · ‖solModeCoeff hT f i‖²`, the `i`-th contribution to the squared
`L²([0,T]; Hᶜ)` norm of the Duhamel solution field of forcing `f`.  Here
`solModeCoeff hT f i = perModeConvL2 λᵢ (timeModeCoeff f i)` is the `i`-th
eigen-coordinate of the solution. -/
def solFieldMass (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorSobolevWeight (I := I) (M := M) i c *
    ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2

lemma forcingMass_nonneg (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (c : ℝ) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ forcingMass (I := I) (M := M) f c i :=
  mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) (sq_nonneg _)

lemma solFieldMass_nonneg (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ solFieldMass (I := I) (M := M) hT f c i :=
  mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) (sq_nonneg _)

/-- **The per-mode two-derivative gain.**  For `0 ≤ T`,

  `solFieldMass f (c + 2) i ≤ (1 + T)² · forcingMass f c i`

at every eigen-index `i`.  This is `weighted_solModeCoeff_le` with the order `a`
of the forcing relabelled `c`. -/
theorem solFieldMass_le_forcingMass (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    solFieldMass (I := I) (M := M) hT f (c + 2) i ≤
      (1 + T) ^ 2 * forcingMass (I := I) (M := M) f c i := by
  have hbound :
      tensorSobolevWeight (I := I) (M := M) i (c + 2) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
        (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i c *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
    have h := weighted_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
    have hperMode := one_add_lambda_mul_norm_solModeCoeff_le (I := I) (M := M)
      (a := a) hT f i
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i c
    have hsol_nn : 0 ≤ ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
      norm_nonneg _
    have hweight_split :
        tensorSobolevWeight (I := I) (M := M) i (c + 2) =
          tensorSobolevWeight (I := I) (M := M) i c * (1 + lam) ^ 2 := by
      rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def,
        Real.rpow_add hbase_pos,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    have hsq : ((1 + lam) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2 ≤
        ((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
      have hlhs_nn : 0 ≤ (1 + lam) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
        mul_nonneg hbase_pos.le hsol_nn
      have hrhs_nn : 0 ≤ (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [hperMode, hlhs_nn, hrhs_nn]
    calc tensorSobolevWeight (I := I) (M := M) i (c + 2) *
            ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
        = tensorSobolevWeight (I := I) (M := M) i c *
            (((1 + lam) *
              ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2) := by
          rw [hweight_split]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
            (((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hwc_nn
      _ = (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i c *
            ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring
  simpa [solFieldMass, forcingMass] using hbound

/-- **The one-step two-derivative gain.**  If the forcing masses at spatial
order `c` are summable (the forcing lies in `L²([0,T]; Hᶜ)`), then the
solution-field masses at order `c + 2` are summable (the solution lies in
`L²([0,T]; H^{c+2})`).  The two-derivative-gain bound dominates the solution
masses by `(1 + T)²` times the (summable) forcing masses, mode by mode. -/
theorem solFieldMass_summable_of_forcingMass_summable (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (hf : Summable (forcingMass (I := I) (M := M) f c)) :
    Summable (solFieldMass (I := I) (M := M) hT f (c + 2)) := by
  refine Summable.of_nonneg_of_le
    (fun i => solFieldMass_nonneg (I := I) (M := M) hT f (c + 2) i)
    (fun i => solFieldMass_le_forcingMass (I := I) (M := M) hT f c i)
    (hf.mul_left ((1 + T) ^ 2))

/-- **The net one-order bootstrap step.**  Suppose the forcing `f` and the
solution-field of `f` are coupled by the first-order loss of the nonlinearity:
for every order `d`, if the solution masses at order `d + 1` are summable then
the forcing masses at order `d` are summable (`hcouple`).  Then, given that the
solution masses at order `c + 1` are summable, the solution masses at order
`c + 2` are summable.

`hcouple` honestly encodes `‖N(u)‖_{Hᵈ} ≲ ‖u‖_{H^{d+1}}` integrated in time; it
controls the *forcing* by the *solution* one order higher, and is not the
conclusion (which is about solution masses two orders higher). -/
theorem solFieldMass_summable_succ (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hc : Summable (solFieldMass (I := I) (M := M) hT f (c + 1))) :
    Summable (solFieldMass (I := I) (M := M) hT f (c + 2)) :=
  solFieldMass_summable_of_forcingMass_summable (I := I) (M := M) hT f c
    (hcouple c hc)

/-- **The all-orders interior-smoothing bootstrap (mass level).**  Suppose:

* `hcouple` — the first-order coupling: solution masses summable at order
  `d + 1` ⟹ forcing masses summable at order `d`, for every `d`;
* `hbase` — the base regularity: the solution masses are summable at order `b`.

Then the solution masses are summable at *every* order `b + n`, `n : ℕ`.

The proof is induction on `n`: the base case is `hbase`, and the step is the net
one-order gain `solFieldMass_summable_succ` applied at `c = b + n − 1` (so that
`c + 1 = b + n` is the inductive hypothesis and `c + 2 = b + n + 1` is the
goal). -/
theorem solFieldMass_summable_bootstrap (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ n : ℕ, Summable (solFieldMass (I := I) (M := M) hT f (b + n)) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ k ih =>
    have hstep := solFieldMass_summable_succ (I := I) (M := M) hT f (b + k - 1)
      hcouple
    have hrw1 : (b + (k : ℝ) - 1) + 1 = b + (k : ℝ) := by ring
    have hrw2 : (b + (k : ℝ) - 1) + 2 = b + ((k : ℕ) + 1 : ℕ) := by push_cast; ring
    rw [hrw1] at hstep
    rw [hrw2] at hstep
    exact hstep ih

/-- **The all-orders interior-smoothing bootstrap, every real order.**  Under
the same hypotheses as `solFieldMass_summable_bootstrap`, the solution masses
are summable at *every* real order `σ` (not merely the integer-spaced
`b + n`): given any `σ`, choose `n` with `b + n ≥ σ` and dominate the
order-`σ` masses by the order-`(b + n)` masses using `(1 + λᵢ)^σ ≤
(1 + λᵢ)^{b+n}` (the weight is `≥ 1` and the exponent is larger). -/
theorem solFieldMass_summable_all (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ σ : ℝ, Summable (solFieldMass (I := I) (M := M) hT f σ) := by
  intro σ
  obtain ⟨n, hn⟩ := exists_nat_ge (σ - b)
  have hσ_le : σ ≤ b + n := by linarith
  have hgain := solFieldMass_summable_bootstrap (I := I) (M := M) hT f
    hcouple hbase n
  refine Summable.of_nonneg_of_le
    (fun i => solFieldMass_nonneg (I := I) (M := M) hT f σ i)
    (fun i => ?_) hgain
  have hbase_ge : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  have hwle : tensorSobolevWeight (I := I) (M := M) i σ ≤
      tensorSobolevWeight (I := I) (M := M) i (b + n) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge hσ_le
  simpa only [solFieldMass] using
    mul_le_mul_of_nonneg_right hwle (sq_nonneg _)

/-- The order-`σ` solution-field synthesised from the per-mode solution
coordinates `i ↦ solModeCoeff hT f i`, available once the order-`σ` masses are
summable.  This is the maximal-regularity solution field of `f`, viewed at
spatial Sobolev scale `σ`. -/
def solFieldAtOrder (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (_hσ : Summable (solFieldMass (I := I) (M := M) hT f σ)) :
    timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  timeL2OfModes (I := I) (M := M) (σ := σ)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT f i)

/-- The `i`-th eigen-coordinate of `solFieldAtOrder` is the solution coordinate
`solModeCoeff hT f i`, the same family at every order `σ`. -/
theorem solFieldAtOrder_timeModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (hσ : Summable (solFieldMass (I := I) (M := M) hT f σ))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (solFieldAtOrder (I := I) (M := M) hT f σ hσ) i =
      solModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := σ)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT f i) hσ i

/-- **Parabolic interior smoothing (L²-in-time, the headline).**  Let `f` be a
forcing field coupled to its own Duhamel solution by the first-order loss of a
subcritical nonlinearity (`hcouple`: solution masses at order `d + 1` summable
⟹ forcing masses at order `d` summable, for every `d`), and suppose the
solution has base regularity `b` (`hbase`: solution masses summable at order
`b`).

Then for *every* spatial Sobolev order `σ` there is a genuine time-`L²` field
`v ∈ L²([0,T]; Hˢ)` whose eigen-coordinate family is the solution coordinate
family `i ↦ solModeCoeff hT f i` — the *same* family at every order.  This is
the precise statement that the maximal-regularity solution lies in
`L²((0,T]; Hˢ)` for every `σ`, i.e. in the spatial smooth subspace `⋂_σ Hˢ`,
in the interior `t > 0`.

The bootstrap `solFieldMass_summable_all` supplies the order-`σ` summability
unconditionally from the base regularity and the first-order coupling; the
synthesis `timeL2OfModes` then packages it as an honest field. -/
theorem solField_into_all_tensorHs_interior (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ σ : ℝ,
      ∃ v : timeL2 (tensorHs (I := I) (M := M) g r s σ) T,
        ∀ i, timeModeCoeff (I := I) (M := M) v i =
          solModeCoeff (I := I) (M := M) (a := a) hT f i :=
  fun σ =>
    let hσ := solFieldMass_summable_all (I := I) (M := M) hT f hcouple hbase σ
    ⟨solFieldAtOrder (I := I) (M := M) hT f σ hσ,
      solFieldAtOrder_timeModeCoeff (I := I) (M := M) hT f σ hσ⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
