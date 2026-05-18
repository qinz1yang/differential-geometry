import DifferentialGeometry.Geometry.Riemannian.Length.LengthFunctional
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-!
# Riemannian distance via length of piecewise-`C¹` curves

For a smooth Riemannian manifold `(M, g)` and points `p, q : M`, this file
defines the **Riemannian distance**

```
riemDist g p q = ⨅ γ ∈ {γ | IsPiecewiseC1On γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q},
                   ENNReal.ofReal (length g γ 0 1).
```

The infimum lives in `ℝ≥0∞` because there may be no admissible curve
between `p` and `q` (in that case the infimum is `⊤`).

The headline metric properties proved unconditionally in this file are:

* `riemDist_self      : riemDist g p p = 0`,
* `riemDist_comm      : riemDist g p q = riemDist g q p`.

The triangle inequality
`riemDist g p r ≤ riemDist g p q + riemDist g q r` and positivity for
`p ≠ q` are downstream developments. Positivity requires the Gauss-lemma
radial-isometry argument; the triangle inequality requires the
length-additivity identity under concatenation of piecewise-`C¹` curves,
together with a careful affine-reparametrization change-of-variable.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Distance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Length

/-! ## Admissible curves -/

/-- The set of *admissible curves* from `p` to `q`: piecewise-`C¹` curves
`γ : ℝ → M` on the unit interval `[0, 1]` with `γ 0 = p` and `γ 1 = q`. -/
def AdmissibleCurves (p q : M) : Set (ℝ → M) :=
  {γ : ℝ → M | IsPiecewiseC1On (I := I) γ (Set.Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q}

@[simp] lemma mem_admissibleCurves {p q : M} {γ : ℝ → M} :
    γ ∈ AdmissibleCurves (I := I) p q ↔
      IsPiecewiseC1On (I := I) γ (Set.Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q :=
  Iff.rfl

/-! ## Definition of `riemDist`

We use the lower Lebesgue integral `∫⁻ t in Ioc a b, ENNReal.ofReal (speed g γ t)`
as the *length-in-`ℝ≥0∞`* of a curve. This formulation is well-defined for
arbitrary speed (without integrability hypotheses), and makes additivity
over adjacent intervals unconditional via `lintegral_union`. -/

/-- The length of a curve `γ` over `[a, b]` valued in `ℝ≥0∞`, computed via the
lower Lebesgue integral of `ENNReal.ofReal (speed g γ t)` over `Ioc a b`. -/
def lengthENN (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (speed (I := I) g γ t)

@[simp] lemma lengthENN_def
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    lengthENN (I := I) g γ a b =
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (speed (I := I) g γ t) := rfl

/-- The `ℝ≥0∞`-length over a degenerate interval `[a, a]` is zero. -/
@[simp] lemma lengthENN_self
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    lengthENN (I := I) g γ a a = 0 := by
  unfold lengthENN
  simp

/-- The `ℝ≥0∞`-length of a constant curve vanishes on every interval: the
speed of `fun _ => p` is identically zero. -/
@[simp] lemma lengthENN_const
    (g : SmoothRiemannianMetric I M) (p : M) (a b : ℝ) :
    lengthENN (I := I) g (fun _ : ℝ => p) a b = 0 := by
  unfold lengthENN
  have hfun :
      (fun t : ℝ => ENNReal.ofReal (speed (I := I) g (fun _ : ℝ => p) t)) =
        (fun _ : ℝ => (0 : ℝ≥0∞)) := by
    funext t
    rw [speed_const (I := I) g p t, ENNReal.ofReal_zero]
  rw [hfun, MeasureTheory.lintegral_zero]

/-- The `ℝ≥0∞`-length is symmetric under swapping the endpoints: the integral
runs over `Ioc (min a b) (max a b)` either way. Concretely, for `a ≤ b` both
`lengthENN g γ a b` and `lengthENN g γ b a` integrate `ENNReal.ofReal (speed _)`
over the same set `Ioc a b` (the second case is `Ioc b a = ∅`). -/
lemma lengthENN_swap_of_le
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} (hab : b ≤ a) :
    lengthENN (I := I) g γ a b = 0 := by
  unfold lengthENN
  have h_empty : Set.Ioc a b = ∅ := Set.Ioc_eq_empty (not_lt.mpr hab)
  rw [h_empty]
  simp

/-- The `ℝ≥0∞`-length is unconditionally additive over adjacent intervals
`[a, b] ∪ [b, c]` for `a ≤ b ≤ c`. -/
lemma lengthENN_add_adjacent
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    lengthENN (I := I) g γ a c =
      lengthENN (I := I) g γ a b + lengthENN (I := I) g γ b c := by
  unfold lengthENN
  have h_union : Set.Ioc a c = Set.Ioc a b ∪ Set.Ioc b c :=
    (Set.Ioc_union_Ioc_eq_Ioc hab hbc).symm
  have h_disj : Disjoint (Set.Ioc a b) (Set.Ioc b c) :=
    Set.Ioc_disjoint_Ioc_of_le (le_refl b)
  rw [h_union, MeasureTheory.lintegral_union measurableSet_Ioc h_disj]

/-- ### Headline 1: the Riemannian distance.

The Riemannian distance from `p` to `q` is the infimum, taken in `ℝ≥0∞`,
of the `ℝ≥0∞`-lengths of all admissible curves. -/
def riemDist (g : SmoothRiemannianMetric I M) (p q : M) : ℝ≥0∞ :=
  ⨅ γ ∈ AdmissibleCurves (I := I) p q, lengthENN (I := I) g γ 0 1

@[simp] lemma riemDist_def (g : SmoothRiemannianMetric I M) (p q : M) :
    riemDist (I := I) g p q =
      ⨅ γ ∈ AdmissibleCurves (I := I) p q, lengthENN (I := I) g γ 0 1 :=
  rfl

/-- The Riemannian distance is bounded above by the `ℝ≥0∞`-length of any
admissible curve. -/
lemma riemDist_le_of_mem_admissibleCurves
    {g : SmoothRiemannianMetric I M} {p q : M} {γ : ℝ → M}
    (hγ : γ ∈ AdmissibleCurves (I := I) p q) :
    riemDist (I := I) g p q ≤ lengthENN (I := I) g γ 0 1 := by
  unfold riemDist
  exact iInf₂_le γ hγ

/-! ## Headline 2: reflexivity -/

/-- The constant curve at `p`, parameterized on all of `ℝ`. -/
private def constCurve (p : M) : ℝ → M := fun _ => p

private lemma constCurve_admissible (p : M) :
    constCurve (M := M) p ∈ AdmissibleCurves (I := I) p p := by
  refine ⟨?_, rfl, rfl⟩
  exact IsPiecewiseC1On.const_Icc (I := I) p (zero_le_one)

/-- The Riemannian self-distance is zero. -/
theorem riemDist_self (g : SmoothRiemannianMetric I M) (p : M) :
    riemDist (I := I) g p p = 0 := by
  have h_admissible : constCurve (M := M) p ∈ AdmissibleCurves (I := I) p p :=
    constCurve_admissible (I := I) p
  -- The `ℝ≥0∞`-length of the constant curve is zero: its speed is identically 0.
  have h_lenENN : lengthENN (I := I) g (constCurve (M := M) p) 0 1 = 0 := by
    unfold lengthENN constCurve
    -- The integrand is `ENNReal.ofReal (speed g (fun _ => p) t)` which equals 0 since
    -- `speed g (fun _ => p) t = 0`.
    have h_zero : ∀ t : ℝ, ENNReal.ofReal (speed (I := I) g (fun _ : ℝ => p) t) = 0 := by
      intro t
      rw [speed_const (I := I) g p t]
      simp
    simp only [h_zero, MeasureTheory.lintegral_const, zero_mul]
  have h_le : riemDist (I := I) g p p ≤ 0 := by
    have := riemDist_le_of_mem_admissibleCurves (I := I) (g := g)
      (γ := constCurve (M := M) p) h_admissible
    rw [h_lenENN] at this
    exact this
  exact le_antisymm h_le (zero_le _)

/-! ## Reversal of admissible curves -/

/-- The reversed curve `revCurve γ t := γ (1 - t)`. -/
def revCurve (γ : ℝ → M) : ℝ → M := fun t => γ (1 - t)

@[simp] lemma revCurve_apply (γ : ℝ → M) (t : ℝ) :
    revCurve (M := M) γ t = γ (1 - t) := rfl

@[simp] lemma revCurve_zero (γ : ℝ → M) :
    revCurve (M := M) γ 0 = γ 1 := by simp [revCurve]

@[simp] lemma revCurve_one (γ : ℝ → M) :
    revCurve (M := M) γ 1 = γ 0 := by simp [revCurve]

/-! ### Velocity of a reversed curve -/

private lemma mfderiv_one_sub (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => 1 - s) t =
      (-1 : ℝ) • (ContinuousLinearMap.id ℝ ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have h_fd : HasFDerivAt (fun s : ℝ => 1 - s)
      (ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ)) t :=
    hd.hasFDerivAt
  have hfd : fderiv ℝ (fun s : ℝ => 1 - s) t =
      ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ) := h_fd.fderiv
  rw [mfderiv_eq_fderiv, hfd]
  -- `toSpanSingleton ℝ (-1) = (-1) • id`.
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply]

private lemma velocity_revCurve_of_mdifferentiable
    {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (1 - t)) :
    Geodesic.velocity (I := I) (revCurve (M := M) γ) t =
      - (Geodesic.velocity (I := I) γ (1 - t) : TangentSpace I (γ (1 - t))) := by
  classical
  set φ : ℝ → ℝ := fun s : ℝ => 1 - s with hφ_def
  have hφ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ φ := (contMDiff_const).sub contMDiff_id
  have hφ_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t :=
    hφ_smooth.mdifferentiable (by simp [ne_eq]) t
  have h_comp_eq : γ ∘ φ = revCurve (M := M) γ := by funext s; rfl
  have h_chain : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ φ) t =
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t) :=
    mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I) (x := t)
      (by simpa [hφ_def] using hγ) hφ_md
  have h_φd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t = (-1 : ℝ) • (ContinuousLinearMap.id ℝ ℝ) :=
    mfderiv_one_sub t
  unfold Geodesic.velocity
  rw [← h_comp_eq, h_chain, h_φd]
  -- Goal: `((mfderiv γ (φ t)).comp (-1 • id)) 1 = - (mfderiv γ (1 - t)) 1`.
  change (mfderiv 𝓘(ℝ, ℝ) I γ (1 - t))
      (((-1 : ℝ) • (ContinuousLinearMap.id ℝ ℝ)) (1 : ℝ)) =
    - (mfderiv 𝓘(ℝ, ℝ) I γ (1 - t)) (1 : ℝ)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  -- Goal: `(mfderiv γ (1 - t)) ((-1 : ℝ) • (1 : ℝ)) = - (mfderiv γ (1 - t)) 1`.
  -- Use `LinearMap.map_neg`-style reasoning via `CLM.map_smul`.
  have h_smul : ((-1 : ℝ) • (1 : ℝ)) = -(1 : ℝ) := by simp
  rw [h_smul]
  -- Now `(mfderiv γ (1-t)) (-(1:ℝ)) = -(mfderiv γ (1-t)) (1:ℝ)`.
  exact map_neg _ _

private lemma innerSq_revCurve
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} (t : ℝ) :
    g.inner (revCurve (M := M) γ t)
        (Geodesic.velocity (I := I) (revCurve (M := M) γ) t)
        (Geodesic.velocity (I := I) (revCurve (M := M) γ) t) =
      g.inner (γ (1 - t))
        (Geodesic.velocity (I := I) γ (1 - t))
        (Geodesic.velocity (I := I) γ (1 - t)) := by
  classical
  have h_pt : revCurve (M := M) γ t = γ (1 - t) := rfl
  by_cases hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (1 - t)
  · have h_vel := velocity_revCurve_of_mdifferentiable (I := I) hγ
    rw [h_pt, h_vel]
    -- `g.inner _ (-v) (-v) = g.inner _ v v`.
    have h_neg1 : g.inner (γ (1 - t))
          (- (Geodesic.velocity (I := I) γ (1 - t) : TangentSpace I (γ (1 - t)))) =
        - g.inner (γ (1 - t)) (Geodesic.velocity (I := I) γ (1 - t)) := map_neg _ _
    rw [h_neg1]
    change (- g.inner (γ (1 - t)) (Geodesic.velocity (I := I) γ (1 - t)))
        (- (Geodesic.velocity (I := I) γ (1 - t) : TangentSpace I (γ (1 - t)))) =
      g.inner (γ (1 - t)) (Geodesic.velocity (I := I) γ (1 - t))
        (Geodesic.velocity (I := I) γ (1 - t))
    have h_neg_clm : ∀ (v : TangentSpace I (γ (1 - t))),
        (- g.inner (γ (1 - t)) (Geodesic.velocity (I := I) γ (1 - t))) v =
        - (g.inner (γ (1 - t)) (Geodesic.velocity (I := I) γ (1 - t))) v := by
      intro v; rfl
    rw [h_neg_clm, map_neg]
    ring
  · have h_v_γ : Geodesic.velocity (I := I) γ (1 - t) = 0 :=
      Geodesic.velocity_eq_zero_of_not_mdifferentiable (I := I) hγ
    have h_v_rev : Geodesic.velocity (I := I) (revCurve (M := M) γ) t = 0 := by
      classical
      by_contra h_nz
      have h_md_rev : MDifferentiableAt 𝓘(ℝ, ℝ) I (revCurve (M := M) γ) t := by
        by_contra h_nm
        exact h_nz (Geodesic.velocity_eq_zero_of_not_mdifferentiable (I := I) h_nm)
      have hφ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ (fun s : ℝ => 1 - s) :=
        (contMDiff_const).sub contMDiff_id
      have hφ_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => 1 - s) (1 - t) :=
        hφ_smooth.mdifferentiable (by simp [ne_eq]) (1 - t)
      have h_fun_eq : (revCurve (M := M) γ) ∘ (fun s : ℝ => 1 - s) = γ := by
        funext s; simp [revCurve]
      have h_pt' : (fun s : ℝ => 1 - s) (1 - t) = t := by ring
      have h_comp_md :=
        MDifferentiableAt.comp (g := revCurve (M := M) γ) (f := fun s : ℝ => 1 - s)
          (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I) (x := 1 - t)
          (by simpa [h_pt'] using h_md_rev) hφ_md
      rw [h_fun_eq] at h_comp_md
      exact hγ h_comp_md
    -- Both `velocity γ (1-t)` and `velocity (revCurve γ) t` are zero.
    -- Since `revCurve γ t = γ (1-t)` definitionally, both sides reduce to
    -- `g.inner (γ (1-t)) 0 0`.
    rw [h_v_γ, h_v_rev]
    -- Note: `revCurve γ t = γ (1 - t)` is definitionally `rfl`, so both sides match.
    rfl

private lemma speed_revCurve
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speed (I := I) g (revCurve (M := M) γ) t = speed (I := I) g γ (1 - t) := by
  unfold speed
  rw [show revCurve (M := M) γ t = γ (1 - t) from rfl]
  congr 1
  exact innerSq_revCurve (I := I) g (γ := γ) t

/-- Length of a reversed curve over `[0, 1]` equals the length of the original. -/
private lemma length_revCurve (g : SmoothRiemannianMetric I M) (γ : ℝ → M) :
    length (I := I) g (revCurve (M := M) γ) 0 1 = length (I := I) g γ 0 1 := by
  unfold length
  have h1 : ∫ t in (0:ℝ)..1, speed (I := I) g (revCurve (M := M) γ) t =
      ∫ t in (0:ℝ)..1, speed (I := I) g γ (1 - t) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact speed_revCurve (I := I) g γ t
  rw [h1]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (f := speed (I := I) g γ) (1 : ℝ)
  -- `h2 : ∫ x in 0..1, speed g γ (1 - x) = ∫ x in 1 - 1..1 - 0, speed g γ x`.
  -- Simplify the bounds `1 - 1 = 0`, `1 - 0 = 1`.
  simp only [sub_zero, sub_self] at h2
  exact h2

/-- `ℝ≥0∞`-length of the reversed curve equals that of the original. The
involution `t ↦ 1 - t` is measure-preserving for the Lebesgue measure
(composition of negation and translation), and maps `Ioc 0 1` ae onto itself
(differing only by the endpoints, a null set). -/
private lemma lengthENN_revCurve (g : SmoothRiemannianMetric I M) (γ : ℝ → M) :
    lengthENN (I := I) g (revCurve (M := M) γ) 0 1 =
      lengthENN (I := I) g γ 0 1 := by
  classical
  unfold lengthENN
  -- Pointwise: `speed (revCurve γ) t = speed γ (1 - t)`.
  have h_pt : ∀ t, ENNReal.ofReal (speed (I := I) g (revCurve (M := M) γ) t) =
      ENNReal.ofReal (speed (I := I) g γ (1 - t)) := fun t => by
    rw [speed_revCurve (I := I) g γ t]
  have h_eq_fn : (fun t : ℝ => ENNReal.ofReal (speed (I := I) g (revCurve γ) t)) =
      fun t => ENNReal.ofReal (speed (I := I) g γ (1 - t)) := funext h_pt
  rw [h_eq_fn]
  -- Measure-preserving involution `1 - ·` on `ℝ`.
  have h_neg : MeasureTheory.MeasurePreserving (fun s : ℝ => -s)
      (volume : MeasureTheory.Measure ℝ) volume :=
    Measure.measurePreserving_neg _
  have h_addLeft : MeasureTheory.MeasurePreserving (fun s : ℝ => (1 : ℝ) + s)
      (volume : MeasureTheory.Measure ℝ) volume :=
    measurePreserving_add_left _ _
  have h_subLeft : MeasureTheory.MeasurePreserving (fun s : ℝ => (1 : ℝ) - s)
      (volume : MeasureTheory.Measure ℝ) volume := by
    have h_func_eq : (fun s : ℝ => (1 : ℝ) - s) =
        (fun s : ℝ => 1 + s) ∘ (fun s : ℝ => -s) := by
      funext s; simp [sub_eq_add_neg]
    rw [h_func_eq]
    exact h_addLeft.comp h_neg
  have h_emb : MeasurableEmbedding (fun s : ℝ => (1 : ℝ) - s) :=
    (Homeomorph.subLeft 1).isClosedEmbedding.measurableEmbedding
  -- `Ioc 0 1` under `1 - ·` preimages to `Ico 0 1`.
  have h_preim : (fun s : ℝ => (1 : ℝ) - s) ⁻¹' Set.Ioc (0:ℝ) 1 = Set.Ico (0:ℝ) 1 := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨?_, ?_⟩ <;> linarith
  -- Apply `MeasurePreserving.setLIntegral_comp_preimage_emb`:
  -- LHS: `∫⁻ b in Ioc 0 1, ofReal (speed γ b) ∂volume`.
  -- RHS via substitution: `∫⁻ a in (1-·)⁻¹(Ioc 0 1), ofReal (speed γ (1-a)) ∂volume`
  --                     = `∫⁻ a in Ico 0 1, ofReal (speed γ (1-a)) ∂volume`.
  have h_subst :=
    h_subLeft.setLIntegral_comp_preimage_emb h_emb
      (fun u : ℝ => ENNReal.ofReal (speed (I := I) g γ u)) (Set.Ioc (0:ℝ) 1)
  rw [h_preim] at h_subst
  -- `h_subst : ∫⁻ a in Ico 0 1, ofReal (speed γ (1-a)) ∂volume =
  --             ∫⁻ b in Ioc 0 1, ofReal (speed γ b) ∂volume`.
  rw [← h_subst]
  -- Goal: `∫⁻ t in Ioc 0 1, ofReal (speed γ (1-t)) = ∫⁻ a in Ico 0 1, ofReal (speed γ (1-a))`.
  rw [show ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc 0 1)) =
    (volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1) from
    (MeasureTheory.restrict_Ico_eq_restrict_Ioc).symm]

/-- The reverse of an admissible curve from `p` to `q` is admissible from `q` to `p`. -/
private lemma admissible_revCurve {p q : M} {γ : ℝ → M}
    (hγ : γ ∈ AdmissibleCurves (I := I) p q) :
    revCurve (M := M) γ ∈ AdmissibleCurves (I := I) q p := by
  obtain ⟨hpw, hp, hq⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · exact IsPiecewiseC1On.reverse_unitInterval (I := I) hpw
  · simp [revCurve, hq]
  · simp [revCurve, hp]

/-! ## Headline 3: symmetry -/

/-- The Riemannian distance is symmetric. -/
theorem riemDist_comm (g : SmoothRiemannianMetric I M) (p q : M) :
    riemDist (I := I) g p q = riemDist (I := I) g q p := by
  suffices h : ∀ p' q' : M, riemDist (I := I) g p' q' ≤ riemDist (I := I) g q' p' by
    exact le_antisymm (h p q) (h q p)
  intro p' q'
  unfold riemDist
  refine le_iInf₂ ?_
  intro γ hγ
  have h_rev_ad : revCurve (M := M) γ ∈ AdmissibleCurves (I := I) p' q' :=
    admissible_revCurve (I := I) hγ
  have h_lenENN : lengthENN (I := I) g (revCurve (M := M) γ) 0 1 =
      lengthENN (I := I) g γ 0 1 := lengthENN_revCurve (I := I) g γ
  have h_le : (⨅ γ' ∈ AdmissibleCurves (I := I) p' q',
        lengthENN (I := I) g γ' 0 1) ≤
      lengthENN (I := I) g (revCurve (M := M) γ) 0 1 :=
    iInf₂_le _ h_rev_ad
  rw [h_lenENN] at h_le
  exact h_le

/-! ## Headline 4: triangle inequality -/

/-- Change-of-variable identity (left half): the `Ioc 0 (1/2)` lintegral of
`ofReal(speed γ (2t))` equals `1/2` times the `Ioc 0 1` lintegral of
`ofReal(speed γ)`. -/
private lemma lintegral_speed_2t_left
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) :
    ∫⁻ t in Set.Ioc (0:ℝ) (1/2), ENNReal.ofReal (speed (I := I) g γ (2 * t)) =
      ENNReal.ofReal (1/2) *
        ∫⁻ s in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (speed (I := I) g γ s) := by
  classical
  -- Set up the measurable embedding `(2·) : ℝ → ℝ`.
  have h_emb : MeasurableEmbedding (fun t : ℝ => 2 * t) :=
    (Homeomorph.mulLeft₀ (2 : ℝ) (by norm_num)).isClosedEmbedding.measurableEmbedding
  -- Preimage of `Ioc 0 1` under `(2·)` is `Ioc 0 (1/2)`.
  have h_preim : (fun t : ℝ => 2 * t) ⁻¹' Set.Ioc (0:ℝ) 1 = Set.Ioc (0:ℝ) (1/2) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  -- Map of volume: `(volume.map (2·)) = (1/2) • volume`.
  have h_map : (volume : MeasureTheory.Measure ℝ).map (fun t : ℝ => 2 * t) =
      ENNReal.ofReal (1/2) • volume := by
    have h := Real.map_volume_mul_left (a := (2:ℝ)) (by norm_num : (2:ℝ) ≠ 0)
    -- `h : Measure.map (2 * ·) volume = ofReal |2⁻¹| • volume`.
    convert h using 2
    rw [show |(2:ℝ)⁻¹| = (1/2 : ℝ) by norm_num]
  -- Apply `MeasurableEmbedding.lintegral_map` after using restrict_map.
  have h_restr : (volume.map (fun t : ℝ => 2 * t)).restrict (Set.Ioc (0:ℝ) 1) =
      (volume.restrict (Set.Ioc (0:ℝ) (1/2))).map (fun t : ℝ => 2 * t) := by
    rw [h_emb.restrict_map]
    rw [h_preim]
  -- Compute the LHS via `MeasurableEmbedding.lintegral_map`.
  calc ∫⁻ t in Set.Ioc (0:ℝ) (1/2), ENNReal.ofReal (speed (I := I) g γ (2 * t))
      = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ (2 * t))
          ∂((volume.restrict (Set.Ioc (0:ℝ) (1/2)))) := rfl
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((volume.restrict (Set.Ioc (0:ℝ) (1/2))).map (fun t : ℝ => 2 * t)) := by
          rw [h_emb.lintegral_map]
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((volume.map (fun t : ℝ => 2 * t)).restrict (Set.Ioc (0:ℝ) 1)) := by
          rw [h_restr]
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((ENNReal.ofReal (1/2) • volume).restrict (Set.Ioc (0:ℝ) 1)) := by
          rw [h_map]
    _ = ENNReal.ofReal (1/2) *
          ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (speed (I := I) g γ t) := by
          rw [MeasureTheory.Measure.restrict_smul,
            MeasureTheory.lintegral_smul_measure]
          rfl

/-- Change-of-variable identity (right half): the `Ioc (1/2) 1` lintegral of
`ofReal(speed γ (2t - 1))` equals `1/2` times the `Ioc 0 1` lintegral of
`ofReal(speed γ)`. -/
private lemma lintegral_speed_2t_minus_1_right
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) :
    ∫⁻ t in Set.Ioc ((1/2):ℝ) 1, ENNReal.ofReal (speed (I := I) g γ (2 * t - 1)) =
      ENNReal.ofReal (1/2) *
        ∫⁻ s in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (speed (I := I) g γ s) := by
  classical
  -- Embeddings.
  have h_emb_mul : MeasurableEmbedding (fun t : ℝ => 2 * t) :=
    (Homeomorph.mulLeft₀ (2 : ℝ) (by norm_num)).isClosedEmbedding.measurableEmbedding
  have h_emb_sub : MeasurableEmbedding (fun s : ℝ => s - 1) :=
    (Homeomorph.subRight 1).isClosedEmbedding.measurableEmbedding
  have h_emb : MeasurableEmbedding (fun t : ℝ => 2 * t - 1) := by
    have h_eq : (fun t : ℝ => 2 * t - 1) =
        (fun s : ℝ => s - 1) ∘ (fun t : ℝ => 2 * t) := rfl
    rw [h_eq]
    exact h_emb_sub.comp h_emb_mul
  have h_preim : (fun t : ℝ => 2 * t - 1) ⁻¹' Set.Ioc (0:ℝ) 1 =
      Set.Ioc ((1/2):ℝ) 1 := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  -- Subtraction is measure-preserving.
  have h_sub_pres : MeasureTheory.MeasurePreserving (fun s : ℝ => s - 1)
      (volume : MeasureTheory.Measure ℝ) volume :=
    measurePreserving_sub_right (volume : MeasureTheory.Measure ℝ) (1:ℝ)
  -- Volume map: `(2·) ∘ (· - 1) = 2t - 1`.
  have h_map_mul : (volume : MeasureTheory.Measure ℝ).map (fun t : ℝ => 2 * t) =
      ENNReal.ofReal (1/2) • volume := by
    have h := Real.map_volume_mul_left (a := (2:ℝ)) (by norm_num : (2:ℝ) ≠ 0)
    convert h using 2
    rw [show |(2:ℝ)⁻¹| = (1/2 : ℝ) by norm_num]
  have h_map : (volume : MeasureTheory.Measure ℝ).map (fun t : ℝ => 2 * t - 1) =
      ENNReal.ofReal (1/2) • volume := by
    have h_eq : (fun t : ℝ => 2 * t - 1) =
        (fun s : ℝ => s - 1) ∘ (fun t : ℝ => 2 * t) := rfl
    rw [h_eq]
    rw [← MeasureTheory.Measure.map_map h_sub_pres.measurable h_emb_mul.measurable]
    rw [h_map_mul, MeasureTheory.Measure.map_smul, h_sub_pres.map_eq]
  have h_restr : (volume.map (fun t : ℝ => 2 * t - 1)).restrict (Set.Ioc (0:ℝ) 1) =
      (volume.restrict (Set.Ioc ((1/2):ℝ) 1)).map (fun t : ℝ => 2 * t - 1) := by
    rw [h_emb.restrict_map, h_preim]
  calc ∫⁻ t in Set.Ioc ((1/2):ℝ) 1, ENNReal.ofReal (speed (I := I) g γ (2 * t - 1))
      = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ (2 * t - 1))
          ∂((volume.restrict (Set.Ioc ((1/2):ℝ) 1))) := rfl
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((volume.restrict (Set.Ioc ((1/2):ℝ) 1)).map
            (fun t : ℝ => 2 * t - 1)) := by rw [h_emb.lintegral_map]
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((volume.map (fun t : ℝ => 2 * t - 1)).restrict (Set.Ioc (0:ℝ) 1)) := by
          rw [h_restr]
    _ = ∫⁻ t, ENNReal.ofReal (speed (I := I) g γ t)
          ∂((ENNReal.ofReal (1/2) • volume).restrict (Set.Ioc (0:ℝ) 1)) := by
          rw [h_map]
    _ = ENNReal.ofReal (1/2) *
          ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (speed (I := I) g γ t) := by
          rw [MeasureTheory.Measure.restrict_smul,
            MeasureTheory.lintegral_smul_measure]
          rfl

/-- `ℝ≥0∞`-length of `concatHalf γ₁ γ₂` over `[0, 1]` is the sum of the
`ℝ≥0∞`-lengths of `γ₁` and `γ₂` over `[0, 1]`. -/
private lemma lengthENN_concatHalf
    (g : SmoothRiemannianMetric I M) (γ₁ γ₂ : ℝ → M) :
    lengthENN (I := I) g (concatHalf γ₁ γ₂) 0 1 =
      lengthENN (I := I) g γ₁ 0 1 + lengthENN (I := I) g γ₂ 0 1 := by
  classical
  rw [lengthENN_add_adjacent (I := I) g (concatHalf γ₁ γ₂)
    (a := (0:ℝ)) (b := (1/2)) (c := 1) (by norm_num) (by norm_num)]
  congr 1
  · -- Left half.
    unfold lengthENN
    have h_eqOn_Ioo : Set.EqOn
        (fun t : ℝ => ENNReal.ofReal (speed (I := I) g (concatHalf γ₁ γ₂) t))
        (fun t : ℝ => ENNReal.ofReal (2 * speed (I := I) g γ₁ (2 * t)))
        (Set.Ioo (0:ℝ) (1/2)) := by
      intro t ht
      rcases ht with ⟨_, h_lt⟩
      change ENNReal.ofReal (speed (I := I) g (concatHalf γ₁ γ₂) t) =
        ENNReal.ofReal (2 * speed (I := I) g γ₁ (2 * t))
      rw [Length.speed_concatHalf_eq_left (I := I) g γ₁ γ₂ h_lt,
        Length.speed_double_reparam (I := I) g γ₁ t]
    rw [show ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) (1/2))) =
      volume.restrict (Set.Ioo (0:ℝ) (1/2)) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo h_eqOn_Ioo]
    rw [show ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo (0:ℝ) (1/2))) =
      volume.restrict (Set.Ioc (0:ℝ) (1/2)) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
    -- Now: `∫⁻ t in Ioc 0 (1/2), ofReal (2 * speed γ₁ (2t)) = lengthENN γ₁ 0 1`.
    have h_factor : ∀ t : ℝ,
        ENNReal.ofReal (2 * speed (I := I) g γ₁ (2 * t)) =
          ENNReal.ofReal 2 * ENNReal.ofReal (speed (I := I) g γ₁ (2 * t)) := by
      intro t
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp_rw [h_factor]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_speed_2t_left (I := I) g γ₁]
    rw [← mul_assoc]
    -- `ofReal 2 * ofReal (1/2) = 1`.
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (2 : ℝ) * (1/2) = 1 by norm_num]
    simp
  · -- Right half — analogous.
    unfold lengthENN
    have h_eqOn_Ioo : Set.EqOn
        (fun t : ℝ => ENNReal.ofReal (speed (I := I) g (concatHalf γ₁ γ₂) t))
        (fun t : ℝ => ENNReal.ofReal (2 * speed (I := I) g γ₂ (2 * t - 1)))
        (Set.Ioo ((1/2):ℝ) 1) := by
      intro t ht
      rcases ht with ⟨h_gt, _⟩
      change ENNReal.ofReal (speed (I := I) g (concatHalf γ₁ γ₂) t) =
        ENNReal.ofReal (2 * speed (I := I) g γ₂ (2 * t - 1))
      rw [Length.speed_concatHalf_eq_right (I := I) g γ₁ γ₂ h_gt,
        Length.speed_double_shift_reparam (I := I) g γ₂ t]
    rw [show ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc ((1/2):ℝ) 1)) =
      volume.restrict (Set.Ioo ((1/2):ℝ) 1) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo h_eqOn_Ioo]
    rw [show ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo ((1/2):ℝ) 1)) =
      volume.restrict (Set.Ioc ((1/2):ℝ) 1) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
    have h_factor : ∀ t : ℝ,
        ENNReal.ofReal (2 * speed (I := I) g γ₂ (2 * t - 1)) =
          ENNReal.ofReal 2 * ENNReal.ofReal (speed (I := I) g γ₂ (2 * t - 1)) := by
      intro t
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp_rw [h_factor]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_speed_2t_minus_1_right (I := I) g γ₂]
    rw [← mul_assoc]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (2 : ℝ) * (1/2) = 1 by norm_num]
    simp

/-- ### Triangle inequality for `riemDist`.

For any three points `p, q, r : M`, `riemDist g p r ≤ riemDist g p q + riemDist g q r`.
The proof glues admissible curves via `concatHalf` and uses the unconditional
`ℝ≥0∞`-length additivity for the concatenation. -/
theorem riemDist_triangle (g : SmoothRiemannianMetric I M) (p q r : M) :
    riemDist (I := I) g p r ≤
      riemDist (I := I) g p q + riemDist (I := I) g q r := by
  classical
  unfold riemDist
  refine ENNReal.le_iInf₂_add_iInf₂ ?_
  intro γ₁ hγ₁ γ₂ hγ₂
  -- Concatenation `concatHalf γ₁ γ₂` is admissible from p to r.
  have h_concat_ad : concatHalf γ₁ γ₂ ∈ AdmissibleCurves (I := I) p r := by
    refine ⟨?_, ?_, ?_⟩
    · exact Length.isPiecewiseC1On_concatHalf (I := I) hγ₁.1 hγ₂.1
        (by rw [hγ₁.2.2, hγ₂.2.1])
    · rw [concatHalf_zero (M := M) γ₁ γ₂]; exact hγ₁.2.1
    · rw [concatHalf_one (M := M) γ₁ γ₂]; exact hγ₂.2.2
  -- Length-additivity for the concatenation.
  have h_len_eq : lengthENN (I := I) g (concatHalf γ₁ γ₂) 0 1 =
      lengthENN (I := I) g γ₁ 0 1 + lengthENN (I := I) g γ₂ 0 1 :=
    lengthENN_concatHalf (I := I) g γ₁ γ₂
  -- Bound the LHS.
  calc (⨅ γ ∈ AdmissibleCurves (I := I) p r, lengthENN (I := I) g γ 0 1)
      ≤ lengthENN (I := I) g (concatHalf γ₁ γ₂) 0 1 := iInf₂_le _ h_concat_ad
    _ = lengthENN (I := I) g γ₁ 0 1 + lengthENN (I := I) g γ₂ 0 1 := h_len_eq

end Distance
end Riemannian
end Geometry
end DifferentialGeometry

end
