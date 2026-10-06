import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric
import DifferentialGeometry.Geometry.Metric.CompactDerivative
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Bundle Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

/-- A positive defining function on a relatively compact open set yields a
proper logarithmic exhaustion. The ambient superlevels are closed and stay
inside the original positive domain. -/
theorem isCompact_neg_log_sublevel
    {M : Type*} [TopologicalSpace M] {δ : M → ℝ} (hδ : Continuous δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M))) {A : ℝ} (hA : 0 < A) (c : ℝ) :
    IsCompact {x : U | -Real.log (δ (x : M)) / A ≤ c} := by
  let Kc : Set M := {x | Real.exp (-A * c) ≤ δ x}
  have hKcU : Kc ⊆ (U : Set M) := by
    intro x hx
    exact (hU x).2 ((Real.exp_pos _).trans_le hx)
  have hKc : IsCompact Kc :=
    hK.of_isClosed_subset (isClosed_le continuous_const hδ)
      (hKcU.trans subset_closure)
  have hpre : IsCompact ((Subtype.val : U → M) ⁻¹' Kc) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hKc
      (by simpa only [Subtype.range_coe] using hKcU)
  convert hpre using 1
  ext x
  change (-Real.log (δ (x : M)) / A ≤ c) ↔ Real.exp (-A * c) ≤ δ (x : M)
  rw [div_le_iff₀ hA, ← Real.le_log_iff_exp_le ((hU x).1 x.property)]
  constructor <;> intro h <;> nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SecondCountableTopology M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The actual metric `δ⁻² g` on a relatively compact positive domain is
complete for its Riemannian extended distance. The domain may be disconnected
or empty, and no regular-level assumption is imposed on `δ`. -/
theorem riemannianMetricComplete_positive_domain
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M)))
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (hG : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x),
      G.inner x v w = (δ (x : M))⁻¹ ^ 2 * (g.restrictOpen U).inner x v w) :
    let : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
    DifferentialGeometry.Geometry.RiemannianMetricComplete G := by
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
  obtain ⟨C, hC⟩ := exists_metric_mfderiv_bound_on_compact g (hδ.of_le (by simp)) hK
  let A : ℝ := (C : ℝ) + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCA : (C : ℝ) ≤ A := by dsimp only [A]; linarith
  let d : U → ℝ := fun x => δ (x : M)
  have hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ d :=
    hδ.comp contMDiff_subtype_val
  have hdpos (x : U) : 0 < d x := (hU x).1 x.property
  have hlog : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => Real.log (d x)) := by
    intro x
    exact (Real.contDiffAt_log.mpr (hdpos x).ne').contMDiffAt.comp x hd.contMDiffAt
  let f : U → ℝ := fun x => -Real.log (d x) / A
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f := hlog.neg.div_const A
  have hproper (c : ℝ) : IsCompact {x : U | f x ≤ c} :=
    isCompact_neg_log_sublevel hδ.continuous U hU hK hA c
  have hbound (x : U) (v : TangentSpace 𝓘(ℝ, E) x) :
      mvfderiv (I := 𝓘(ℝ, E)) f x v * mvfderiv (I := 𝓘(ℝ, E)) f x v ≤
        G.inner x v v := by
    let a : ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) δ (x : M) v
    let q : ℝ := g.inner (x : M) v v
    have hq : 0 ≤ q := metric_inner_self_nonneg g (x : M) v
    have habs : |a| ≤ A * Real.sqrt q := by
      have hh := hC (x : M) (subset_closure x.property) v
      change ‖a‖ ≤ (C : ℝ) * Real.sqrt q at hh
      rw [Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hCA (Real.sqrt_nonneg q))
    have hquot : |a| / A ≤ Real.sqrt q := by
      apply (div_le_iff₀ hA).2
      nlinarith [habs]
    have hsq : (a / A) ^ 2 ≤ q := by
      calc
        (a / A) ^ 2 = (|a| / A) ^ 2 := by rw [div_pow, div_pow, sq_abs]
        _ ≤ (Real.sqrt q) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (abs_nonneg a) hA.le) hquot 2
        _ = q := Real.sq_sqrt hq
    have hder : mvfderiv (I := 𝓘(ℝ, E)) f x v = (-(d x)⁻¹ / A) * a := by
      have hreal : HasDerivAt (fun t : ℝ => -Real.log t / A)
          (-(d x)⁻¹ / A) (d x) :=
        ((Real.hasDerivAt_log (hdpos x).ne').neg).div_const A
      have hchain := mvfderiv_comp_apply
        (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
        (f := d) (g := fun t : ℝ => -Real.log t / A) x
        hreal.differentiableAt.mdifferentiableAt (hd.mdifferentiable (by simp) x) v
      rw [mvfderiv_real_model_eq_fderiv, hreal.hasFDerivAt.fderiv] at hchain
      let b : ℝ := NormedSpace.fromTangentSpace (d x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) d x v)
      have hb : b = a := by
        change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) d x v : ℝ) = a
        dsimp only [d, a]
        rw [DifferentialGeometry.mfderiv_restrict_open]
        rfl
      change mvfderiv (I := 𝓘(ℝ, E)) f x v = b * (-(d x)⁻¹ / A) at hchain
      calc
        mvfderiv (I := 𝓘(ℝ, E)) f x v = b * (-(d x)⁻¹ / A) := hchain
        _ = (-(d x)⁻¹ / A) * a := by rw [hb, mul_comm]
    calc
      mvfderiv (I := 𝓘(ℝ, E)) f x v * mvfderiv (I := 𝓘(ℝ, E)) f x v =
          (d x)⁻¹ ^ 2 * (a / A) ^ 2 := by rw [hder]; ring
      _ ≤ (d x)⁻¹ ^ 2 * q := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = G.inner x v v := by rw [hG]; rfl
  have hcomplete : DifferentialGeometry.RiemannianMetricComplete G :=
    DifferentialGeometry.RiemannianMetricComplete.of_properFun hproper
      (ofReal_abs_sub_le_riemannianEDistOf G f hf hbound)
  exact hcomplete.complete

end DifferentialGeometry.Geometry
