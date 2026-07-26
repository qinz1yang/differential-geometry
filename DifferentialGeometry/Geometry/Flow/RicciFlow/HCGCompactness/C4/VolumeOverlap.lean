import DifferentialGeometry.Geometry.Comparison.Volume.SegmentCount
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.VolumeComparisonBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCovering

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# A0′ `VolumeComparisonInput` producer (brick B7, sequence assembly)

This file assembles the honest producer of the unconditional-Theorem-3.9 Step A
input **A0′** (`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`).  For a bounded-geometry
pointed Riemannian sequence it packages the member-level Bishop–Gromov packing
count `segBall_card` (`Comparison/Volume/SegmentCount.lean`) as the deep
`ballMult` field of `VolumeComparisonInput`, for the supplied distance.

## Main result

* `volInput_of_bg` — from `SeqBoundedGeometry`, a supplied realized distance
  (`InjRadiusDecayInput` + `RealizesEdist`), per-member completeness and
  connectedness, and a positive cap `r0`, produces
  `{ vc : VolumeComparisonInput X // vc.dist = hd.dist }`.  The subtype equation
  discharges `MetricCompactBase.dist_eq`.  Only `hd.dist`/`hreal` are consumed;
  `hd.decay` is never used, so A0′ is independent of the CGT input.

## Transitive-`sorry` status

This file adds **no** `sorry` of its own.  `volInput_of_bg` nonetheless remains
transitively `sorry`'d through `segBall_card`'s dependence on the two intended
frontier `sorry`s in `Comparison/Volume/SegmentPolar.lean` (the manifold-valued
non-injective area inequality and its truncated polar companion).  Per plan §7,
the A0′ endpoint stays at 0% until those close (bricks B5b/B5c); this brick only
lands the assembly, whose own content is `sorry`-free.

## Ricci input

The counting theorem wants `Ric ≥ -(n-1)q²`.  With `q := n·√(bg.C 0)` this is
derived per member from the zeroth-order curvature bound
(`rm04Bound_of_seq` → `ricciLower_of_rm`, giving `Ric ≥ -(n²·C₀)`) by
antitonicity in the constant when `n ≥ 2`.  In dimension one the target constant
is `0` and antitonicity fails; there `ricciTensor` vanishes identically
(`ricci_dim1_bddBelow`, from antisymmetry of the Riemann operator on a
one-dimensional space), giving `Ric ≥ 0` outright.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]

/-! ## Dimension-one Ricci vanishing -/

section Dim1

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

/-- In dimension one the Levi-Civita Riemann operator vanishes identically: it is
antisymmetric in its first two arguments, which both lie in a one-dimensional
space and are therefore proportional. -/
theorem riemannOp_dim1_zero (h1 : Module.finrank ℝ E = 1)
    (g : SmoothRiemannianMetric I M) (x : M) (u v w : TangentSpace I x) :
    riemannOp (LeviCivita (I := I) g) x u v w = 0 := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hfr : Module.finrank ℝ (TangentSpace I x) = 1 := h1
  haveI : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; exact one_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : TangentSpace I x)
  have hspan := (finrank_eq_one_iff_of_nonzero' e he).mp hfr
  obtain ⟨a, ha⟩ := hspan u
  obtain ⟨b, hb⟩ := hspan v
  -- `R(e, e, w) = 0` from antisymmetry in the first two slots.
  have hee : riemannOp (LeviCivita (I := I) g) x e e w = 0 := by
    have hsw := riemannOp_swap (LeviCivita (I := I) g) x e e w
    have h2 : (2 : ℝ) • riemannOp (LeviCivita (I := I) g) x e e w = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsw]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [← ha, ← hb, map_smul, ContinuousLinearMap.smul_apply, map_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hee,
    smul_zero, smul_zero]

/-- In dimension one the Ricci tensor vanishes, so `Ric ≥ 0`. -/
theorem ricci_dim1_bddBelow (h1 : Module.finrank ℝ E = 1)
    (g : SmoothRiemannianMetric I M) :
    RicciBoundedBelow (I := I) g 0 := by
  intro x v
  rw [zero_mul]
  have hzero : ricciTensor (I := I) g x v v = 0 := by
    rw [ricciTensor_apply_basisSum]
    refine Finset.sum_eq_zero ?_
    intro i _
    have hz : (chartModelBasis E).repr (0 : TangentSpace I x) = 0 := map_zero _
    rw [riemannOp_dim1_zero h1 g x ((chartModelBasis E) i) v v, hz, Finsupp.zero_apply]
  rw [hzero]

end Dim1

/-! ## The sequence-level producer -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **A0′ producer.**  Uniform bounded geometry plus a supplied realized distance,
per-member completeness, and connectedness produce the Step A bounded-overlap
input for that distance.  Only `hd.dist` and `hreal` are used (`hd.decay` is not),
so the output is independent of the injectivity-radius decay input; the subtype
equation `vc.dist = hd.dist` discharges `MetricCompactBase.dist_eq`. -/
def volInput_of_bg
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (bg : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X) (hreal : hd.RealizesEdist)
    (hcpl : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (r0 : Real) (hr0 : 0 < r0) :
    { vc : VolumeComparisonInput (I := I) X // vc.dist = hd.dist } := by
  set q : ℝ := (Module.finrank ℝ E : ℝ) * Real.sqrt (bg.C 0) with hq_def
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hC0 : 0 ≤ bg.C 0 := bg.nonneg 0
  refine ⟨{ dist := hd.dist, r0 := r0, r0_pos := hr0,
            Imult := fun m => segImult (Module.finrank ℝ E) q r0 m,
            ballMult := ?_ }, rfl⟩
  intro m k α _ _ centers r hr hcap hsep z J hJz
  -- Install the member instances for `X.obj k`.
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    (X.obj k).riemBundle
  haveI : IsContinuousRiemannianBundle E (fun x : (X.obj k).M => TangentSpace I x) :=
    (X.obj k).riemBundle_cont
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  haveI : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
  letI : ConnectedSpace (X.obj k).M := hconn k
  haveI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (X.obj k) (hcpl.complete k)
  -- Per-member Ricci lower bound `Ric ≥ -(n-1)q²`.
  have hRic : RicciBoundedBelow (I := I) (X.obj k).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) := by
    by_cases hn1 : Module.finrank ℝ E = 1
    · have h0 : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2 = 0 := by
        rw [hn1]; simp
      rw [h0, neg_zero]
      exact ricci_dim1_bddBelow hn1 (X.obj k).metric
    · have hn2 : 2 ≤ Module.finrank ℝ E := by
        have h1 : 1 ≤ Module.finrank ℝ E :=
          Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        omega
      have hsrc : RicciBoundedBelow (I := I) (X.obj k).metric
          (-((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0)) :=
        ricciLower_of_rm (I := I) (X.obj k).metric
          (by simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound]
            using rm04Bound_of_seq (I := I) bg k)
      have hq2 : q ^ 2 = (Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0 := by
        rw [hq_def, mul_pow, Real.sq_sqrt hC0]
      intro x v
      have hinner : 0 ≤ (X.obj k).metric.inner x v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst hv; simp
        · exact ((X.obj k).metric.pos x v hv).le
      have hkappa : -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) ≤
          -((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0) := by
        rw [neg_le_neg_iff, hq2]
        have hone : (1 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
          have : 1 ≤ Module.finrank ℝ E - 1 := by omega
          exact_mod_cast this
        nlinarith [mul_nonneg (sq_nonneg (Module.finrank ℝ E : ℝ)) hC0]
      calc (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))
              * (X.obj k).metric.inner x v v
          ≤ (-((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0))
              * (X.obj k).metric.inner x v v :=
            mul_le_mul_of_nonneg_right hkappa hinner
        _ ≤ ricciTensor (I := I) (X.obj k).metric x v v := hsrc x v
  -- Norm bridge: the tangent enorm is `√⟨·,·⟩`.
  have hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    simpa using
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric y w
  -- Distance bridge: the supplied distance realizes `riemannianEDist`.
  have hbridge : ∀ x y : (X.obj k).M,
      riemannianEDist I x y = ENNReal.ofReal (hd.dist k x y) := by
    intro x y
    rw [← IsRiemannianManifold.out (I := I) x y]
    exact hreal.edist_eq k x y
  have hsep' : ∀ i j : α, i ≠ j →
      ENNReal.ofReal r ≤ riemannianEDist I (centers i) (centers j) := by
    intro i j hij
    rw [hbridge (centers i) (centers j)]
    exact ENNReal.ofReal_le_ofReal (hsep i j hij)
  have hJz' : ∀ j : α, j ∈ J →
      riemannianEDist I (centers j) z ≤ ENNReal.ofReal (m * r) := by
    intro j hj
    rw [hbridge (centers j) z]
    exact ENNReal.ofReal_le_ofReal (hJz j hj)
  exact segBall_card (I := I) (X.obj k).metric hEnorm hq hr0 hRic hr hcap
    centers hsep' z J hJz'

end HCGCompactness
end DifferentialGeometry
