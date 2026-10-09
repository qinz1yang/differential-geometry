import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Operator.Restriction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# P2A-24 (imported definitions, no sorry): verbatim copies of IMS03 definitions absent from this tree

Source: branch `gc/juihuichung/ims03-astra-20261005` (scanned tip `981d9a8cd`, descendant of the
brief's `dcf465959`).  Every declaration here is a verbatim copy of a **proved** declaration of that
branch (with `_P2A` suffix and the namespace `GC.LongTime.CuspP1`), so that the sorry-mirrors in
`P2AdapterImportedLemmas.lean` can state signatures literally.  No `sorry` in this file.
After the IMS03 merge, replace each by a direct reference (see
`docs/geometrization/chapter15/p2-adapter-sorries.md`).
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

/-- Source: `DifferentialGeometry/Geometry/Metric/Conformal/BarrierProfile.lean:23` (`BarrierProfile.cutoff`),
IMS03 @ 981d9a8cd; status proved (verbatim copy). -/
def cutoff_P2A (a r : ℝ) : ℝ := 1 - Real.smoothTransition (2 * r / a - 1)

/-- Source: `BarrierProfile.lean:25` (`logWeight`), proved, verbatim copy. -/
def logWeight_P2A (a r : ℝ) : ℝ := -Real.log (cutoff_P2A a r)

/-- Source: `BarrierProfile.lean:27` (`barrier`), proved, verbatim copy. -/
def barrier_P2A (a r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, (cutoff_P2A a s)⁻¹ ^ 2

/-- Source: `BarrierProfile.lean:29` (`cutoff_smooth`), proved, verbatim copy. -/
theorem cutoff_smooth_P2A (a : ℝ) : ContDiff ℝ ∞ (cutoff_P2A a) := by
  unfold cutoff_P2A
  fun_prop

/-- Source: `BarrierProfile.lean:41` (`cutoff_pos_iff`), proved, verbatim copy. -/
theorem cutoff_pos_iff_P2A {a : ℝ} (ha : 0 < a) (r : ℝ) :
    0 < cutoff_P2A a r ↔ r < a := by
  constructor
  · intro h
    by_contra hn
    have hh : 1 ≤ 2 * r / a - 1 := by
      have hh : 2 ≤ 2 * r / a := (le_div_iff₀ ha).2 (by linarith)
      linarith
    simp only [cutoff_P2A, Real.smoothTransition.one_of_one_le hh, sub_self] at h
    exact lt_irrefl _ h
  · intro hr
    have hh : 2 * r / a - 1 < 1 := by
      have hh : 2 * r / a < 2 := (div_lt_iff₀ ha).2 (by linarith)
      linarith
    exact sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one hh)

/-- Source: `BarrierProfile.lean:63` (`logWeight_smoothOn`), proved, verbatim copy. -/
theorem logWeight_smoothOn_P2A {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (logWeight_P2A a) (Iio a) :=
  ((cutoff_smooth_P2A a).contDiffOn.log
    (fun r hr => ((cutoff_pos_iff_P2A ha r).2 hr).ne')).neg

section Geometry
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- Source: `BarrierProfile.lean:178` (private `contMDiff_comp_of_contDiffOn`), proved, verbatim copy. -/
theorem contMDiff_comp_of_contDiffOn_P2A
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hmem : ∀ x, u x ∈ s) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x => f (u x)) := by
  intro x
  exact ((hf (u x) (hmem x)).contDiffAt (hs.mem_nhds (hmem x))).comp_contMDiffAt
    hu.contMDiffAt

/-- Source: `BarrierProfile.lean:219` (`profileMetric`), proved, verbatim copy.  The conformal
metric of the actual profile. -/
def profileMetric_P2A (g : SmoothRiemannianMetric I M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a) :
    SmoothRiemannianMetric I M :=
  conformalMetricOfContDiff g (fun x => logWeight_P2A a (ρ x))
    (contMDiff_comp_of_contDiffOn_P2A isOpen_Iio (logWeight_smoothOn_P2A ha) hρ hρa)

end Geometry

section PositiveDomain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- Source: `Metric/Conformal/PositiveDomain.lean:20` (private `contMDiff_neg_log_on_positive_domain`),
proved, verbatim copy. -/
theorem contMDiff_neg_log_on_positive_domain_P2A {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => -Real.log (δ (x : M))) := by
  have hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => δ (x : M)) :=
    hδ.comp contMDiff_subtype_val
  have hlog : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => Real.log (δ (x : M))) := by
    intro x
    exact (Real.contDiffAt_log.mpr ((hU x).1 x.property).ne').contMDiffAt.comp x
      hd.contMDiffAt
  exact hlog.neg

/-- Source: `Metric/Conformal/PositiveDomain.lean:35` (`canonicalPositiveDomainMetric`), proved,
verbatim copy.  The actual conformal metric on the positive domain of `δ`. -/
def canonicalPositiveDomainMetric_P2A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {δ : M → ℝ} (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x) :
    SmoothRiemannianMetric 𝓘(ℝ, E) U :=
  DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff (g.restrictOpen U)
    (fun x : U => -Real.log (δ (x : M)))
    (contMDiff_neg_log_on_positive_domain_P2A hδ U hU)

end PositiveDomain

end GC.LongTime.CuspP1
