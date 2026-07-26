import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicRatio
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sharp pole limit of the intrinsic transverse Jacobi density

The Bishop--Gromov absolute volume bound needs the transverse Jacobi density to
be compared to the hyperbolic model with the *sharp* constant `1` (equality on
flat `ℝⁿ`).  Along `γ = intrinsicGeodesic g hEnorm p u` with speed
`ell = √(g.inner p u u)`, for a `gₓ`-orthonormal transverse frame `v` the density
ratio `curveDensity g γ V t / hypDensity (q·ell) (n-1) t` tends to `1` at the pole
`t → 0⁺`, sharpening the non-sharp `intrPoleCap` (constant `N = M₀/c`).

Route (all metric-contracted, avoiding the discontinuous raw exponential
differential): near the pole the intrinsic Jacobi density equals the chart-radial
one (`intrJacobi_raw`); the radial Gram of the frame `v` is
`t² · Vᵀ · (normalGramMatrix) · V` with `V` the change of basis to
`chartModelBasis`, whose limit at the centre is the `gₓ`-Gram of `v`, i.e. the
identity for a `gₓ`-orthonormal frame; and the model density satisfies
`hypSn q t / t → 1`.

* `curveDensity_pole` — geodesic side: `curveDensity g γ V t / t^(n-1) → 1`.
* `poleLimit` — the sharp ratio limit (part 2).
* `transDens_le_hyp` — step-(c) corollary consumed by the L6 assembly: on the
  conjugate-free window the transverse density is `≤` the model density with
  constant exactly `1` (antitone ratio + pole limit `1`).
-/

noncomputable section

open Bundle Filter Function Manifold Set Matrix
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The hyperbolic warping ratio tends to `1` at the pole: `hypSn q t / t → 1`.
The leading term of `sinh(q t)/q` is `t`, independent of the frequency `q`. -/
private lemma hypSn_div_tendsto (q : Real) :
    Tendsto (fun t => hypSn q t / t) (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hzero : hypSn q 0 = 0 := by
    by_cases hq : q = 0 <;> simp [hypSn, hq]
  have hval : hypSnDeriv q 0 = 1 := by
    by_cases hq : q = 0 <;> simp [hypSnDeriv, hq]
  have hderiv : HasDerivAt (hypSn q) (hypSnDeriv q 0) 0 := hasDerivAt_hypSn q 0
  have hslope := (hasDerivAt_iff_tendsto_slope).mp hderiv
  rw [hval] at hslope
  have hfun : slope (hypSn q) 0 = fun t => hypSn q t / t := by
    funext t
    rw [slope_def_field, hzero, sub_zero, sub_zero]
  rw [hfun] at hslope
  exact hslope.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))

/-- Model side of the pole limit: `hypDensity q d t / t^d → 1`. -/
private lemma hypDensity_div_tendsto (q : Real) (d : ℕ) :
    Tendsto (fun t => hypDensity q d t / t ^ d) (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hpow := (hypSn_div_tendsto q).pow d
  rw [one_pow] at hpow
  have hfun : (fun t : Real => hypDensity q d t / t ^ d)
      = fun t : Real => (hypSn q t / t) ^ d := by
    funext t
    simp only [hypDensity, div_pow]
  rw [hfun]
  exact hpow

/-- **Geodesic side of the sharp pole limit.**  For a `gₓ`-orthonormal transverse
frame `v`, the transverse intrinsic-Jacobi density along `γ = intrinsicGeodesic p u`
normalized by `t^(n-1)` tends to `1` at the pole. -/
theorem curveDensity_pole
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        t ^ (Module.finrank Real E - 1))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  sorry

/-- **The sharp pole limit (deliverable 2).**  For a `gₓ`-orthonormal transverse
frame `v` perpendicular to `u`, the transverse Jacobi density ratio to the
speed-scaled hyperbolic model tends to `1` at the pole.  Sharpens `intrPoleCap`
(constant `N = M₀/c`) to the exact constant `1`. -/
theorem poleLimit
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q : Real) (hq : 0 ≤ q)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        hypDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank Real E - 1) t)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hcd := curveDensity_pole (I := I) g hEnorm p u hu v hON
  have hmd := hypDensity_div_tendsto (q * Real.sqrt (g.inner p u u))
    (Module.finrank Real E - 1)
  have hcombine := hcd.div hmd one_ne_zero
  rw [div_one] at hcombine
  refine hcombine.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : Real) < t := ht
  have hpow : (0 : Real) < t ^ (Module.finrank Real E - 1) := pow_pos ht0 _
  have hmdpos : 0 < hypDensity (q * Real.sqrt (g.inner p u u))
      (Module.finrank Real E - 1) t :=
    hypDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht0
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ _ hpow.ne']

/-- **Step-(c) corollary consumed by the L6 assembly (deliverable 3).**  On the
conjugate-free window `Ioo 0 b`, under a Ricci lower bound `Ric ≥ -(n-1)q²`, the
transverse intrinsic-Jacobi density along `γ` is bounded by the speed-scaled
hyperbolic model density with constant EXACTLY `1`.  Obtained from the antitone
ratio (`intrRatioOfFrame`) and the sharp pole limit `1` (`poleLimit`): an antitone
function whose limit at the pole is `1` is `≤ 1` throughout the window. -/
theorem transDens_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      (∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      ∀ t ∈ Set.Ioo (0 : Real) b,
        curveDensity (I := I) g γ V t ≤
          hypDensity (q * ell) (Module.finrank Real E - 1) t := by
  obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p u hu
  have hperp : ∀ i, g.inner p u (v i) = 0 := by
    intro i; rw [g.symm p u (v i)]; exact hperp' i
  have hanti := intrRatioOfFrame (I := I) g hEnorm p u q b hq hd hu v hON hperp hno hRic
  have hlim := poleLimit (I := I) g hEnorm p u q hq hu v hON
  refine ⟨v, hON, hperp, ?_⟩
  intro γ V ell t ht
  have hpos : 0 < hypDensity (q * ell) (Module.finrank Real E - 1) t :=
    hypDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht.1
  have hRatioLE :
      curveDensity (I := I) g γ V t /
        hypDensity (q * ell) (Module.finrank Real E - 1) t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : Real),
        curveDensity (I := I) g γ V t /
            hypDensity (q * ell) (Module.finrank Real E - 1) t ≤
          curveDensity (I := I) g γ V s /
            hypDensity (q * ell) (Module.finrank Real E - 1) s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsb : s ∈ Set.Ioo (0 : Real) b := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsb ht hs.2.le
    exact ge_of_tendsto hlim hev
  rwa [div_le_one hpos] at hRatioLE

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
