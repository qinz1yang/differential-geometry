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

/-! ## Definition of `riemDist` -/

/-- ### Headline 1: the Riemannian distance.

The Riemannian distance from `p` to `q` is the infimum, taken in `ℝ≥0∞`,
of the lengths (cast via `ENNReal.ofReal`) of all admissible curves. -/
def riemDist (g : SmoothRiemannianMetric I M) (p q : M) : ℝ≥0∞ :=
  ⨅ γ ∈ AdmissibleCurves (I := I) p q, ENNReal.ofReal (length (I := I) g γ 0 1)

@[simp] lemma riemDist_def (g : SmoothRiemannianMetric I M) (p q : M) :
    riemDist (I := I) g p q =
      ⨅ γ ∈ AdmissibleCurves (I := I) p q, ENNReal.ofReal (length (I := I) g γ 0 1) :=
  rfl

/-- The Riemannian distance is bounded above by the length of any admissible curve. -/
lemma riemDist_le_of_mem_admissibleCurves
    {g : SmoothRiemannianMetric I M} {p q : M} {γ : ℝ → M}
    (hγ : γ ∈ AdmissibleCurves (I := I) p q) :
    riemDist (I := I) g p q ≤ ENNReal.ofReal (length (I := I) g γ 0 1) := by
  unfold riemDist
  exact iInf₂_le γ hγ

/-! ## Headline 2: reflexivity -/

/-- The constant curve at `p`, parameterized on all of `ℝ`. -/
private def constCurve (p : M) : ℝ → M := fun _ => p

private lemma constCurve_admissible (p : M) :
    constCurve (M := M) p ∈ AdmissibleCurves (I := I) p p := by
  refine ⟨?_, rfl, rfl⟩
  exact IsPiecewiseC1On.const (I := I) p (Set.Icc (0 : ℝ) 1)

/-- The Riemannian self-distance is zero. -/
theorem riemDist_self (g : SmoothRiemannianMetric I M) (p : M) :
    riemDist (I := I) g p p = 0 := by
  have h_admissible : constCurve (M := M) p ∈ AdmissibleCurves (I := I) p p :=
    constCurve_admissible (I := I) p
  have h_len : length (I := I) g (constCurve (M := M) p) 0 1 = 0 := by
    unfold constCurve
    exact length_const (I := I) g p 0 1
  have h_le : riemDist (I := I) g p p ≤ ENNReal.ofReal 0 := by
    have := riemDist_le_of_mem_admissibleCurves (I := I) (g := g)
      (γ := constCurve (M := M) p) h_admissible
    rw [h_len] at this
    exact this
  simpa using h_le

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
  have h_len : length (I := I) g (revCurve (M := M) γ) 0 1 = length (I := I) g γ 0 1 :=
    length_revCurve (I := I) g γ
  have h_le : (⨅ γ' ∈ AdmissibleCurves (I := I) p' q',
        ENNReal.ofReal (length (I := I) g γ' 0 1)) ≤
      ENNReal.ofReal (length (I := I) g (revCurve (M := M) γ) 0 1) :=
    iInf₂_le _ h_rev_ad
  rw [h_len] at h_le
  exact h_le

end Distance
end Riemannian
end Geometry
end DifferentialGeometry

end
