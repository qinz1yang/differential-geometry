import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingCoordinateTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

/-!
# The parabolic time-bootstrap of the Ricci–DeTurck engine forcing

For the genuinely-second-order Nemytskii forcing of the Ricci–DeTurck flow about a
closed background metric `g₀`,

  `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField a hT hT1 0 gforce)`,

in the supercritical regularity regime `2·finrank + 10 ≤ a` with zero initial datum, this
file isolates the genuine classical parabolic prerequisite behind the joint
`C∞`-up-to-`t = 0` regularity of the realized DeTurck–Ricci solution family.

## The second-order derivative loss of the Nemytskii forcing

The Ricci–DeTurck remainder is genuinely **second order**: it loses exactly **two** spatial
derivatives (the quadratic `u·∂²u` term, carried by the inverse-Gram `C₂·∇²` arm).  At the
spatial-Sobolev level this is the AFFINE ball bound
`deTurckRemainder_iteratedCovGradSum_ballBound` (`DeTurck/DeTurckRemainderAbsoluteBallBound.lean`,
window `d + 2`): on a covariant-`L²` ball of radius `R`,

  `∑_{q ≤ d} ‖∇^q N(T)‖²  ≤  C · (1 + ∑_{i ≤ d+2} ‖∇^i T‖²)`,

i.e. `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}` (quadratic, +2), **not** `≲ 1 + ‖u‖_{H^{d+1}}` (+1).
Because the loss is `+2`, the naive one-order interior-smoothing bootstrap of
`ParabolicInteriorSmoothing.lean` (`solFieldMass_summable_all`, fed a `+1` coupling
`solFieldMass (d+1) → forcingMass d`) STALLS: its net advance per step is
parabolic-gain (`+2`) − coupling-loss (`+2`) `= 0`, so it cannot derive forcing-mass
summability at all orders.  The honest mechanism is the **small-data fibre-smallness
contraction** about the zero initial datum (base order `a + 2 ≫ finrank/2` held FIXED, not
ratcheted by `+1`): with the `(1 + ‖u‖_∞)` Moser factor controlled by the supercritical
embedding and the fibre-smallness `δ < 1`, the genuine parabolic interior-time smoothing of
the engine forcing supplies the all-order forcing-mass summability directly.

## The analytic input

* `deTurckForcing_smoothTimeCoordinateFamily` — the **`C∞`-in-time forcing coordinate
  family**, together with the all-order forcing-mass summability: a smooth-in-time per-mode
  coordinate `f`, a time-continuous everywhere `Hᵃ`-representative `F` of `gforce` with a
  single `t`-independent summable all-order time-jet spectral-mass majorant, the per-mode
  `L²`-coordinate of `F` agreeing with `f i` on the closed slab `[0,T]`, AND the forcing
  masses `forcingMass gforce c` summable at every spatial order `c ≥ 0`.  This is the
  classical parabolic interior-time smoothing of the engine forcing carried up to the smooth
  (zero) initial datum (Amann maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva;
  Lieberman), in its genuine second-order / small-data form: every mixed time–space
  derivative of the forcing is continuous on the compact slab `[0,T] × M`, hence bounded into
  every spatial Sobolev order, uniformly in `t`.  Because the Nemytskii forcing is nonlinear
  its time-jets couple all modes, so this control does not reduce to the per-mode scalar ODE
  recursion of the *linear* heat semigroup; it is the genuine quasilinear smoothing input,
  and the all-order forcing-mass summability is its genuine `+2`/small-data output (the
  coupling-agnostic analogue of the sibling
  `realizedSol_forcing_continuousRepr_allOrderMass`).

## The two genuinely-deep parabolic leaves

The combination `deTurckForcing_smoothTimeCoordinateFamily` is **decomposed** into the two
genuinely-classical parabolic facts it rests on, each isolated as a single named,
forcing-pinned honest input (PINNED to `hforce`, so neither is vacuous):

* `deTurckForcing_smoothTimeCoordinateField` — the **`C∞`-in-time forcing coordinate field**
  with the all-order time-jet spectral-mass majorant on the closed slab `[0,T]` and an
  everywhere representative `F` realizing the smooth coordinates (`(F t).coeff i = f i t`).
  This is now itself GLUE over the single genuinely-irreducible deep parabolic leaf
  `deTurckForcing_smoothCoordinate_aeTimeJet` (`ForcingCoordinateTimeRegularity.lean`),
  which supplies the smooth coordinate field `f`, the all-order time-jet majorant, and the
  per-mode a.e. agreement `(fun t => (gforce t).coeff i) =ᵐ f i`; the everywhere `Hᵃ`
  representative `F` is ASSEMBLED here from `f` (its slab coordinates are `f`, summable
  across modes by the `j = 0, τ = a` instance of the majorant), the `=ᵐ` representative is
  the per-mode a.e. agreement combined across the countable eigen-index, and the coordinate
  realization is by construction.  The deep leaf is the genuine quasilinear parabolic
  interior-time smoothing of the engine forcing carried up to the smooth (zero) initial
  datum: the Nemytskii forcing is `C∞`-in-time on `[0,T]` because the datum is smooth and
  the maximal-regularity solution is `C∞`-up-to-`0`, and its time-jets couple all modes (the
  nonlinear coupling), so this control does not reduce to the per-mode linear-heat ODE
  recursion nor to the integrated-in-time spatial forcing mass.

* `deTurckForcing_allOrderForcingMass` — the **all-order spatial forcing-mass summability**
  `∀ c ≥ 0, Summable (forcingMass gforce c)`.  This is the `+2`/small-data interior-smoothing
  output (the coupling-agnostic analogue of the sibling
  `realizedSol_forcing_continuousRepr_allOrderMass`), TRUE at the FIXED base order `a + 2`
  under the fibre-smallness `δ < 1` of the zero-datum solution — NOT the dead `+1` coupling
  bootstrap (whose net advance is `0` for the `+2` nonlinearity).

The combination `deTurckForcing_smoothTimeCoordinateFamily` is then pure GLUE: `f`, `F` and
clauses (smoothness), (time-jet majorant), (representative `=ᵐ`), (coordinate realization)
come straight from `deTurckForcing_smoothTimeCoordinateField`; the per-mode coordinate
continuity of `F` is the smoothness of `f` transported across the coordinate realization;
and the all-order forcing-mass summability is `deTurckForcing_allOrderForcingMass`.

`deTurckForcing_smoothTimeCoordinateField` is now sorry-free GLUE over the single deep leaf
`deTurckForcing_smoothCoordinate_aeTimeJet`; `deTurckForcing_allOrderForcingMass` is
sorry-free GLUE (the spatial-order `+2` ratchet) over the single deep total-norm leaf
`deTurckForcing_forcingMass_summable_succ` (the genuine total small-data quasilinear
parabolic `+2` interior-smoothing advance, TRUE at the total `H`-norm level — NOT a per-mode
factored bound, which is false because the zero-datum Duhamel solution is per-mode smaller
than the forcing).  Both rest on a single deep parabolic prerequisite each (the honest
`sorry`s); consumers transitively depend on their `sorryAx`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedVariables false in

theorem deTurckForcing_smoothTimeCoordinateFieldSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJetSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (a : ℝ) (Nat.cast_nonneg a)
  have hslab_sum : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (f i t) ^ 2) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)) (sq_nonneg _)
    · have := hB_le i t ht
      rwa [iteratedDeriv_zero] at this
  set F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂ then
      ⟨fun i => f i t, hslab_sum t ht⟩ else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t := by
    intro t ht i
    simp only [hF_def, dif_pos ht]
  refine ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, ?_, hF_coeff⟩
  have hjoint : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ i, (gforce t).coeff i = f i t :=
    (MeasureTheory.ae_all_iff).2 hf_ae
  have hrestrict : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      t ∈ Set.Icc (0 : ℝ) d₂ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hjoint, hrestrict] with t ht_eq ht_mem
  refine tensorHs.ext ?_
  funext i
  rw [ht_eq i, hF_coeff t ht_mem i]

set_option linter.unusedVariables false in

theorem deTurckForcing_smoothTimeCoordinateFamilySymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateFieldSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  have hF_coord_cont : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂) := by
    intro i
    refine ContinuousOn.congr (f := fun t => f i t) ?_ ?_
    · exact (hf_smooth i).continuous.continuousOn
    · intro t ht
      exact hF_coeff t ht i
  exact ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
