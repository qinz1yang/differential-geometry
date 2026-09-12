import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Data.EReal.Basic
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed

import DifferentialGeometry.Analysis.Sobolev.Intrinsic.SmoothEntropyNormalization
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakGradientUnique
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyCutoff
import DifferentialGeometry.Geometry.Comparison.Volume.LocalDoubling

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

structure EntropyTest (g : SmoothRiemannianMetric I M) where
  value : M → ℝ
  gradient : M → E
  value_memLp : MemLp value 2 (riemannianVolumeMeasure I M g)
  weak_gradient : HasWeakRiemannianGradLp g value gradient
  gradient_memLp : MemLp (fun x => Real.sqrt (g.inner x (gradient x) (gradient x))) 2
    (riemannianVolumeMeasure I M g)
  nonnegative : ∀ᵐ x ∂(riemannianVolumeMeasure I M g), 0 ≤ value x
  normalized : (∫ x, value x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1


def entropyValue (g : SmoothRiemannianMetric I M) (tau : ℝ) (w : EntropyTest g) : ℝ :=
  (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
      tau * metricScalarAt g x * w.value x ^ 2 -
      w.value x ^ 2 * Real.log (w.value x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) - Module.finrank ℝ E

def muSobolev (g : SmoothRiemannianMetric I M) (tau : ℝ) : EReal :=
  ⨅ w : EntropyTest g, (entropyValue g tau w : EReal)

def muSmooth (g : SmoothRiemannianMetric I M) (tau : ℝ) : EReal :=
  ⨅ (w : EntropyTest g) (_ : ContMDiff I 𝓘(ℝ, ℝ) ∞ w.value)
    (_ : ∀ x, 0 < w.value x), (entropyValue g tau w : EReal)

omit [CompleteSpace E] in
private lemma hasWeakRiemannianGradLp_gradFun_of_contMDiff [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u
      (fun x => DifferentialGeometry.Geometry.Operator.gradFun g u x) := by
  let G₀ : M → E := fun x =>
    ((DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨u, hu⟩ :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)
  have hbase : HasWeakRiemannianGradLp (I := I) (M := M) g u G₀ :=
    hasWeakRiemannianGradLp_of_smooth (I := I) (M := M)
      (DifferentialGeometry.Analysis.Sobolev.Intrinsic.hasWeakRiemannianGrad_grad_g_of_contMDiff
        (I := I) (M := M) g hu)
  refine DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp.hasWeakRiemannianGradLp_congr_ae
    (I := I) (M := M) (g := g) (u := u) (u' := u) (G := G₀)
    (G' := fun x => DifferentialGeometry.Geometry.Operator.gradFun g u x)
    (Filter.EventuallyEq.refl _ u) ?_ hbase
  filter_upwards with x
  exact DifferentialGeometry.Geometry.Operator.grad_g_apply (I := I) g ⟨u, hu⟩ x

private lemma exists_entropyTest_approx [I.Boundaryless] [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 ≤ Module.finrank ℝ E) {tau : ℝ} (htau : 0 < tau)
    (hRc : Continuous (fun x : M => metricScalarAt g x))
    (w : EntropyTest g) {eps : ℝ} (heps : 0 < eps) :
    ∃ W' : EntropyTest g, ContMDiff I 𝓘(ℝ, ℝ) ∞ W'.value ∧
      (∀ x : M, 0 < W'.value x) ∧
      entropyValue g tau W' ≤ entropyValue g tau w + eps := by
  obtain ⟨v, hv, hmass, hbound⟩ :=
    HasWeakRiemannianGradLp.exists_smooth_normalized_wform_le (I := I) (M := M)
      (g := g) hdim w.weak_gradient w.value_memLp w.gradient_memLp w.normalized
      hRc tau (by linarith : 0 < eps / 2)
  have hvgradi : Integrable (fun x => g.inner x
      (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) g v x)
      (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) g v x))
      (riemannianVolumeMeasure I M g) :=
    integrable_metric_energy_of_memLp (I := I) (M := M) g
      (DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
        (I := I) (M := M) g 2 hv)
  obtain ⟨v', hv', hv'pos, hv'mass, hbound'⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Entropy.exists_pos_wform (I := I) (M := M) g
      hv hmass hvgradi hRc (C := 0) (tau := tau) (δ := eps / 2) htau.le
      (by linarith : 0 < eps / 2)
  have hv'2 : MemLp v' 2 (riemannianVolumeMeasure I M g) :=
    (MemW1pIntrinsicLp_of_contMDiff (I := I) (M := M) g 2 hv').1
  have hgrad2 : MemLp (fun x => Real.sqrt
      (g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x))) 2
      (riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
      (I := I) (M := M) g 2 hv'
  let W' : EntropyTest g :=
    { value := v'
      gradient := fun x => DifferentialGeometry.Geometry.Operator.gradFun g v' x
      value_memLp := hv'2
      weak_gradient := hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hv'
      gradient_memLp := hgrad2
      nonnegative := Filter.Eventually.of_forall fun x => (hv'pos x).le
      normalized := hv'mass }
  refine ⟨W', hv', hv'pos, ?_⟩
  have hF' : entropyValue g tau W' =
      (∫ x, 4 * tau * g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
          (DifferentialGeometry.Geometry.Operator.gradFun g v' x) +
        tau * metricScalarAt g x * v' x ^ 2 - v' x ^ 2 * Real.log (v' x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) -
        Module.finrank ℝ E := rfl
  have hFw : entropyValue g tau w =
      (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
        tau * metricScalarAt g x * w.value x ^ 2 - w.value x ^ 2 * Real.log (w.value x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) -
        Module.finrank ℝ E := rfl
  have hb' : (∫ x, 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x) +
      tau * metricScalarAt g x * v' x ^ 2 - v' x ^ 2 * Real.log (v' x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) ≤
      (∫ x, 4 * tau * g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun g v x)
          (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
        tau * metricScalarAt g x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) + eps / 2 := by
    simpa only [zero_mul, add_zero,
      DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] using hbound'
  have hb : (∫ x, 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
      tau * metricScalarAt g x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) ≤
      (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
        tau * metricScalarAt g x * w.value x ^ 2 - w.value x ^ 2 * Real.log (w.value x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) + eps / 2 := hbound
  rw [hF', hFw]
  linarith
theorem mu_sobolev_relaxation [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    {tau : ℝ} (htau : 0 < tau) :
    (∀ w : EntropyTest g, Integrable (fun x => w.value x ^ 2 * Real.log (w.value x ^ 2))
      (riemannianVolumeMeasure I M g)) ∧ muSobolev g tau = muSmooth g tau := by
  refine ⟨?_, ?_⟩
  · intro w
    exact (show MemW1pIntrinsicLp (I := I) (M := M) g 2 w.value from
      ⟨w.value_memLp, w.gradient, w.weak_gradient, w.gradient_memLp⟩)
      |>.integrable_sq_mul_log_sq hdim
  · have hRc : Continuous (fun x : M => metricScalarAt g x) :=
      (metricScalar_smooth (I := I) (M := M) g).continuous
    have hle : muSobolev g tau ≤ muSmooth g tau := by
      unfold muSobolev muSmooth
      refine le_iInf fun w => le_iInf fun h1 => le_iInf fun h2 => ?_
      exact iInf_le (fun w : EntropyTest g => (entropyValue g tau w : EReal)) w
    by_cases hM : Nonempty M
    · have hMne : Nonempty M := hM
      have hge : muSmooth g tau ≤ muSobolev g tau := by
        unfold muSobolev muSmooth
        refine le_iInf fun w : EntropyTest g => ?_
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
        have hwlt : entropyValue g tau w < r := EReal.coe_lt_coe_iff.mp hr1
        obtain ⟨W', hW'smooth, hW'pos, hW'le⟩ :=
          exists_entropyTest_approx (I := I) (M := M) g hdim htau hRc w
            (eps := (r - entropyValue g tau w) / 2) (by linarith)
        have hW'r : entropyValue g tau W' < r := by linarith
        have hchain : (r : EReal) < (entropyValue g tau W' : EReal) :=
          lt_of_lt_of_le hr2 (le_trans (iInf_le _ W')
            (le_trans (iInf_le _ hW'smooth) (iInf_le _ hW'pos)))
        exact absurd hchain (not_lt_of_ge (EReal.coe_le_coe hW'r.le))
      exact le_antisymm hle hge
    · have hMempty : IsEmpty M := not_nonempty_iff.mp hM
      have hempty : IsEmpty (EntropyTest g) := ⟨fun w => by
        have hμ : riemannianVolumeMeasure I M g = 0 :=
          MeasureTheory.Measure.eq_zero_of_isEmpty (riemannianVolumeMeasure I M g)
        have hz : (∫ x, w.value x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 0 := by
          rw [hμ]
          simp
        have hnorm := w.normalized
        rw [hz] at hnorm
        exact zero_ne_one hnorm⟩
      have h1 : muSobolev g tau = ⊤ := by
        unfold muSobolev
        exact iInf_of_empty _
      have h2 : muSmooth g tau = ⊤ := by
        unfold muSmooth
        exact iInf_of_empty _
      rw [h1, h2]

section MuMonotoneBridge

private local instance instMeasurableSpaceBridge : MeasurableSpace M := borel M
private local instance instBorelSpaceBridge : BorelSpace M := ⟨rfl⟩

theorem entropyValue_eq_wFunctional [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {tau : ℝ} (htau : 0 < tau) (w : EntropyTest g)
    (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w.value) (hwpos : ∀ x, 0 < w.value x) :
    entropyValue g tau w =
      DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional
        (riemannianVolumeMeasure I M g) (Module.finrank ℝ E) tau
        (fun x => metricScalarAt (I := I) (M := M) g x)
        (fun x => g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun g
            (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential
              (Module.finrank ℝ E) tau (fun y => w.value y * w.value y)) x)
          (DifferentialGeometry.Geometry.Operator.gradFun g
            (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential
              (Module.finrank ℝ E) tau (fun y => w.value y * w.value y)) x))
        (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential
          (Module.finrank ℝ E) tau (fun y => w.value y * w.value y)) := by
  classical
  let : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let n : ℕ := Module.finrank ℝ E
  let μ : Measure M := riemannianVolumeMeasure I M g
  let R : M → ℝ := fun x => metricScalarAt (I := I) (M := M) g x
  let v : M → ℝ := w.value
  have hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := hw
  have hvpos : ∀ x : M, 0 < v x := hwpos
  have hRc : Continuous R := by
    simpa only [R] using (metricScalar_smooth (I := I) (M := M) g).continuous
  have hSq := DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form
    μ g n htau R hv hvpos
  simp only [DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] at hSq
  have hae : (fun x : M => (w.gradient x : TangentSpace I x)) =ᵐ[μ]
      (fun x => DifferentialGeometry.Geometry.Operator.gradFun g v x) :=
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.ae_eq
      (g := g) (u := v)
      (G := fun x : M => (w.gradient x : TangentSpace I x))
      (G' := fun x => DifferentialGeometry.Geometry.Operator.gradFun g v x)
      w.weak_gradient
      (hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hv)
      (by
        have h2 : MemLp (fun x => Real.sqrt
            (g.inner x (w.gradient x) (w.gradient x))) 2 μ := w.gradient_memLp
        exact h2.mono_exponent (by norm_num))
      (by
        have h2 : MemLp (fun x => Real.sqrt
            (g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v x)
              (DifferentialGeometry.Geometry.Operator.gradFun g v x))) 2 μ :=
          DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
            (I := I) (M := M) g 2 hv
        exact h2.mono_exponent (by norm_num))
  let I₁ : M → ℝ := fun x => 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
      tau * R x * w.value x ^ 2 - w.value x ^ 2 * Real.log (w.value x ^ 2)
  let I₂ : M → ℝ := fun x =>
      4 * tau * g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
      tau * R x * (v x * v x) - (v x * v x) * Real.log (v x * v x)
  let c : ℝ := Real.log
    (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor n tau) - (n : ℝ)
  have henergy : Continuous (fun x => g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun g v x)
      (DifferentialGeometry.Geometry.Operator.gradFun g v x)) := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨v, hv⟩)
      (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨v, hv⟩)
    exact hinner.congr (fun _ => rfl)
  have hsq : Continuous (fun x : M => v x * v x) := hv.continuous.mul hv.continuous
  have hI₂cont : Continuous I₂ := by
    have h3 : Continuous (fun x => (v x * v x) * Real.log (v x * v x)) :=
      hsq.mul (hsq.log fun x => (mul_pos (hvpos x) (hvpos x)).ne')
    have h1 : Continuous (fun x => 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)) := henergy.const_mul (4 * tau)
    have h2 : Continuous (fun x => tau * R x * (v x * v x)) :=
      (hRc.const_mul tau).mul hsq
    exact ((h1.add h2).sub h3).congr
      (fun x => by simp only [I₂, Pi.add_apply, Pi.sub_apply])
  have hI₂int : Integrable I₂ μ :=
    hI₂cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvvint : Integrable (fun x => v x * v x) μ :=
    hsq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI₁I₂ : (∫ x, I₁ x ∂μ) = ∫ x, I₂ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp only [I₁, I₂, v, hx, pow_two]
  have hvvmass : (∫ x, v x * v x ∂μ) = 1 := by
    have hchange : (∫ x, v x * v x ∂μ) =
        ∫ x, w.value x ^ 2 ∂(riemannianVolumeMeasure I M g) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [pow_two]
    rw [hchange]
    exact w.normalized
  have hI₂add : (∫ x, I₂ x + c * (v x * v x) ∂μ) =
      (∫ x, I₂ x ∂μ) + c := by
    rw [integral_add hI₂int (hvvint.const_mul c), integral_const_mul, hvvmass, mul_one]
  have hc : c = -(n : ℝ) / 2 * Real.log (4 * Real.pi * tau) - (n : ℝ) := by
    have hpref := DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor n htau
    dsimp only [c]
    rw [hpref]
  have hent : entropyValue g tau w =
      (∫ x, I₁ x ∂μ) - ((n : ℝ) / 2 * Real.log (4 * Real.pi * tau)) - (n : ℝ) := by
    simp only [entropyValue, I₁, μ, R, n]
  have hkey : entropyValue g tau w = (∫ x, I₂ x ∂μ) + c := by
    rw [hent, hI₁I₂, hc]
    ring
  rw [hkey, hSq, hI₂add]

omit [CompleteSpace E] in
theorem exists_entropyTest_of_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {v : M → ℝ} (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v)
    (hpos : ∀ x, 0 < v x)
    (hmass : (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1) :
    ∃ w : EntropyTest g, w.value = v := by
  classical
  let : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨B, hB⟩ := (isCompact_range hv.continuous.norm).bddAbove
  have hvmLp : MemLp v 2 (riemannianVolumeMeasure I M g) :=
    MemLp.of_bound hv.continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => hB ⟨x, rfl⟩)
  exact ⟨{ value := v
           gradient := fun x => DifferentialGeometry.Geometry.Operator.gradFun g v x
           value_memLp := hvmLp
           weak_gradient := hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hv
           gradient_memLp :=
             DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
               (I := I) (M := M) g 2 hv
           nonnegative := Filter.Eventually.of_forall fun x => (hpos x).le
           normalized := hmass }, rfl⟩

theorem exists_muSmooth_step [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a₀ a b : ℝ} (ha₀a : a₀ < a)
    (hab : Set.Icc a₀ b ⊆ D.regular) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ {s t theta : ℝ}, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
        t - s ≤ rho → 0 < theta →
        muSmooth (S.base.metric s) (theta + t - s) ≤ muSmooth (S.base.metric t) theta := by
  classical
  obtain ⟨rho0, hrho0, _hrho0one, hspan⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Entropy.gallim_span (I := I) (M := M) S hS hab
  let r : ℝ := min rho0 (a - a₀)
  have hr : 0 < r := lt_min hrho0 (sub_pos.mpr ha₀a)
  have hr_rho : r ≤ rho0 := min_le_left _ _
  have hr_gap : r ≤ a - a₀ := min_le_right _ _
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro s t theta hs ht hst hgap htheta
  have hqle : 0 ≤ t - s := sub_nonneg.mpr hst
  have hqlt : t - s < r := lt_of_le_of_lt hgap (half_lt_self hr)
  have hleft : a₀ ≤ t - r := by
    have : a₀ ≤ a - (a - a₀) := by linarith
    linarith [hs.1, hr_gap, this]
  refine le_iInf fun w => le_iInf fun hw => le_iInf fun hwpos => ?_
  let zeta : C^∞⟮I, M; ℝ⟯ := ⟨fun x => w.value x * w.value x, hw.mul hw⟩
  let u0 : DifferentialGeometry.Integral.L2.SmoothCcTensor (S.family.metric t) 0 0 :=
    DifferentialGeometry.Analysis.Sobolev.scalarCc (I := I) (M := M) (S.family.metric t) zeta
  have hu0 : DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0
      (n := (∞ : WithTop ℕ∞)) u0.toSection = fun x => w.value x * w.value x := by
    funext x
    exact congrFun (DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc (I := I) (M := M)
      (S.family.metric t) zeta) x
  have hinit : ∀ x : M, 0 < DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0
      (n := (∞ : WithTop ℕ∞)) u0.toSection x := by
    intro x
    rw [hu0]
    exact mul_pos (hwpos x) (hwpos x)
  obtain ⟨V, phi, ulim, hlim, hpot⟩ :=
    hspan ⟨t, hab ⟨ha₀a.le.trans ht.1, ht.2⟩⟩
      ⟨ha₀a.le.trans ht.1, ht.2⟩ r hr hr_rho hleft u0
  let G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) ℝ :=
    DifferentialGeometry.PDE.RicciFlow.Entropy.reverseFamily
      (DifferentialGeometry.PDE.RicciFlow.flowG (I := I) S) t
  let u : ℝ → M → ℝ := fun z x =>
    DifferentialGeometry.Analysis.Spectral.scalarSpecSum (I := I) (M := M)
      (S.family.metric t) (fun i z => ulim z i) z x
  have hGq : G.metric (t - s) = S.family.metric s := by
    change S.family.metric (t - (t - s)) = S.family.metric s
    have hts : t - (t - s) = s := by ring
    rw [hts]
  have hG0 : G.metric 0 = S.family.metric t := by
    change S.family.metric (t - 0) = S.family.metric t
    rw [sub_zero]
  have hposPath : ∀ z ∈ Set.Icc (0 : ℝ) r, ∀ x : M, 0 < u z x := by
    simpa only [u] using
      DifferentialGeometry.PDE.RicciFlow.Entropy.gallim_pos_on (I := I) (M := M)
        S hS hab ⟨t, hab ⟨ha₀a.le.trans ht.1, ht.2⟩⟩
        ⟨ha₀a.le.trans ht.1, ht.2⟩ hr hleft hlim hpot hinit
  have href : ∀ z ∈ Set.Icc (0 : ℝ) r, t - z ∈ D.regular := by
    intro z hz
    apply hab
    constructor
    · linarith [hz.2, hleft]
    · linarith [hz.1, ht.2]
  have hmassPath := DifferentialGeometry.PDE.RicciFlow.Entropy.heatpot_mass_on
    (I := I) (M := M) S hS ⟨t, hab ⟨ha₀a.le.trans ht.1, ht.2⟩⟩ hr hpot href
  have hqIcc : t - s ∈ Set.Icc (0 : ℝ) r := ⟨hqle, hqlt.le⟩
  have hqIco : t - s ∈ Set.Ico (0 : ℝ) r := ⟨hqle, hqlt⟩
  have hu0eval : u 0 = DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0
      (n := (∞ : WithTop ℕ∞)) u0.toSection := by
    simpa only [u] using
      DifferentialGeometry.PDE.RicciFlow.Entropy.galerkinLim_initial (I := I) (M := M) hlim
  have hvol0 : DifferentialGeometry.Integral.Measure.volumeMeasureFamily (I := I) (M := M) G 0
      = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric t) := by
    simp only [DifferentialGeometry.Integral.Measure.volumeMeasureFamily,
      DifferentialGeometry.Integral.Measure.metricFamilyForMeasure,
      DifferentialGeometry.Integral.Measure.riemannianMeasureFamily,
      hG0, SolutionOn.family_metric]
  have hmass0 : (∫ x, u 0 x ∂(DifferentialGeometry.Integral.Measure.volumeMeasureFamily
      (I := I) (M := M) G 0)) = 1 := by
    rw [hvol0, hu0eval, hu0]
    simpa only [pow_two] using w.normalized
  have hvolq : DifferentialGeometry.Integral.Measure.volumeMeasureFamily (I := I) (M := M) G (t - s)
      = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric s) := by
    have hts : t - (t - s) = s := by ring
    simp only [DifferentialGeometry.Integral.Measure.volumeMeasureFamily,
      DifferentialGeometry.Integral.Measure.metricFamilyForMeasure,
      DifferentialGeometry.Integral.Measure.riemannianMeasureFamily,
      hGq, SolutionOn.family_metric]
  have hmassq : (∫ x, u (t - s) x ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      (I := I) (M := M) (S.base.metric s))) = 1 := by
    have hm := (hmassPath (t - s) hqIcc).trans hmass0
    rwa [hvolq] at hm
  have hsmoothq : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u (t - s)) := hpot.sliceSmooth (t - s) hqIcc
  have hposq : ∀ x : M, 0 < u (t - s) x := hposPath (t - s) hqIcc
  have hsqrtDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => Real.sqrt (u (t - s) x)) := by
    have hsq : ContDiffOn ℝ ∞ Real.sqrt (Set.Ioi (0 : ℝ)) := by
      simpa only [id_eq] using
        ContDiffOn.sqrt (f := id) (s := Set.Ioi (0 : ℝ))
          (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))) (fun x hx => ne_of_gt hx)
    have hsqM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.sqrt (Set.Ioi (0 : ℝ)) :=
      (contMDiffOn_iff_contDiffOn (𝕜 := ℝ)).mpr hsq
    refine contMDiffOn_univ.mp ?_
    refine (hsqM.comp (s := Set.univ) (t := Set.Ioi (0 : ℝ))
      (contMDiffOn_univ.mpr hsmoothq) ?_).congr ?_
    · intro x _
      exact hposq x
    · intro x _
      rfl
  have hsqrtMemLp : MemLp (fun x => Real.sqrt (u (t - s) x)) 2
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric s)) := by
    let : IsFiniteMeasure (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) (S.base.metric s)) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) (S.base.metric s)
    obtain ⟨B, hB⟩ := (isCompact_range hsqrtDiff.continuous.norm).bddAbove
    exact MemLp.of_bound hsqrtDiff.continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => hB ⟨x, rfl⟩)
  have hgradMemLp : MemLp (fun x => Real.sqrt ((S.base.metric s).inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (S.base.metric s)
        (fun y => Real.sqrt (u (t - s) y)) x)
      (DifferentialGeometry.Geometry.Operator.gradFun (S.base.metric s)
        (fun y => Real.sqrt (u (t - s) y)) x))) 2
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric s)) := by
    let : IsFiniteMeasure (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) (S.base.metric s)) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) (S.base.metric s)
    have hcont : Continuous (fun x => Real.sqrt ((S.base.metric s).inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (S.base.metric s)
          (fun y => Real.sqrt (u (t - s) y)) x)
        (DifferentialGeometry.Geometry.Operator.gradFun (S.base.metric s)
          (fun y => Real.sqrt (u (t - s) y)) x))) := by
      have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
        (I := I) (M := M) (S.base.metric s)
        (DifferentialGeometry.Geometry.Operator.gradG (I := I) (S.base.metric s)
          ⟨fun y => Real.sqrt (u (t - s) y), hsqrtDiff⟩)
        (DifferentialGeometry.Geometry.Operator.gradG (I := I) (S.base.metric s)
          ⟨fun y => Real.sqrt (u (t - s) y), hsqrtDiff⟩)
      exact Real.continuous_sqrt.comp (hinner.congr (fun _ => rfl))
    obtain ⟨B, hB⟩ := (isCompact_range hcont.norm).bddAbove
    exact MemLp.of_bound hcont.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => hB ⟨x, rfl⟩)
  let ws : EntropyTest (S.base.metric s) :=
    { value := fun x => Real.sqrt (u (t - s) x)
      gradient := fun x => DifferentialGeometry.Geometry.Operator.gradFun (S.base.metric s)
        (fun y => Real.sqrt (u (t - s) y)) x
      value_memLp := hsqrtMemLp
      weak_gradient := hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hsqrtDiff
      gradient_memLp := hgradMemLp
      nonnegative := Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
      normalized := by
        have hsq_eq : (fun x => Real.sqrt (u (t - s) x) ^ 2) = u (t - s) := by
          funext x
          exact Real.sq_sqrt (hposq x).le
        rw [hsq_eq]
        exact hmassq }
  have hscalarS : (fun x => metricScalarAt (I := I) (M := M) (S.base.metric s) x) =
      S.scalar s := by
    funext x
    rw [SolutionOn.scalar_eq_metricTrace]
    rfl
  have hscalarT : (fun x => metricScalarAt (I := I) (M := M) (S.base.metric t) x) =
      S.scalar t := by
    funext x
    rw [SolutionOn.scalar_eq_metricTrace]
    rfl
  have hdensityq : (fun y => ws.value y * ws.value y) = u (t - s) := by
    funext y
    exact Real.mul_self_sqrt (hposq y).le
  have hu0fun : (fun x => DifferentialGeometry.Analysis.Spectral.scalarSpecSum (I := I) (M := M)
      (S.family.metric t) (fun i r => ulim r i) 0 x) = (fun x => w.value x * w.value x) := by
    have h : u 0 = (fun x => w.value x * w.value x) := by
      rw [hu0eval, hu0]
    exact h
  have hW := DifferentialGeometry.PDE.RicciFlow.Entropy.gallim_w_lt
    (I := I) (M := M) hS hr hlim hpot href htheta hposPath (t - s) hqIco
  have hWflow : DifferentialGeometry.PDE.RicciFlow.Entropy.flowW (I := I) (M := M) S s
        (theta + (t - s)) (u (t - s)) ≤
      DifferentialGeometry.PDE.RicciFlow.Entropy.flowW (I := I) (M := M) S t theta
        (fun x => w.value x * w.value x) := by
    dsimp only [DifferentialGeometry.PDE.RicciFlow.Entropy.flowW, u]
    have hts : t - (t - s) = s := by ring
    simpa only [G, hGq, hG0, hts, hu0fun,
      DifferentialGeometry.Integral.Measure.volumeMeasureFamily,
      DifferentialGeometry.Integral.Measure.metricFamilyForMeasure,
      DifferentialGeometry.Integral.Measure.riemannianMeasureFamily,
      add_zero, sub_zero] using hW
  have htau : theta + t - s = theta + (t - s) := by ring
  have hleft_eq : (entropyValue (S.base.metric s) (theta + t - s) ws : EReal) =
      (DifferentialGeometry.PDE.RicciFlow.Entropy.flowW (I := I) (M := M) S s
        (theta + (t - s)) (u (t - s)) : EReal) := by
    rw [htau]
    rw [entropyValue_eq_wFunctional (I := I) (M := M) (S.base.metric s)
      (by linarith : (0 : ℝ) < theta + (t - s)) ws hsqrtDiff
      (fun x => Real.sqrt_pos.mpr (hposq x))]
    dsimp only [DifferentialGeometry.PDE.RicciFlow.Entropy.flowW]
    simp only [hdensityq, hscalarS,
      DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun,
      SolutionOn.family_metric]
  have hright_eq : (DifferentialGeometry.PDE.RicciFlow.Entropy.flowW (I := I) (M := M) S t
        theta (fun x => w.value x * w.value x) : EReal) =
      (entropyValue (S.base.metric t) theta w : EReal) := by
    rw [entropyValue_eq_wFunctional (I := I) (M := M) (S.base.metric t) htheta w hw hwpos]
    dsimp only [DifferentialGeometry.PDE.RicciFlow.Entropy.flowW]
    simp only [hscalarT, DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun,
      SolutionOn.family_metric]
  have hmule : muSmooth (S.base.metric s) (theta + t - s) ≤
      (entropyValue (S.base.metric s) (theta + t - s) ws : EReal) := by
    unfold muSmooth
    refine (iInf_le (f := fun w : EntropyTest (S.base.metric s) =>
      ⨅ (_ : ContMDiff I 𝓘(ℝ, ℝ) ∞ w.value),
        ⨅ (_ : ∀ x, 0 < w.value x),
          (entropyValue (S.base.metric s) (theta + t - s) w : EReal)) ws).trans ?_
    refine (iInf_le (f := fun _ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ws.value =>
      ⨅ (_ : ∀ x, 0 < ws.value x),
        (entropyValue (S.base.metric s) (theta + t - s) ws : EReal)) hsqrtDiff).trans ?_
    exact iInf_le (f := fun _ : ∀ x, 0 < ws.value x =>
      (entropyValue (S.base.metric s) (theta + t - s) ws : EReal))
      (fun x => Real.sqrt_pos.mpr (hposq x))
  exact hmule.trans (hleft_eq.trans_le
    ((EReal.coe_le_coe hWflow).trans_eq hright_eq))

theorem exists_muSmooth_step_chain [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a₀ a b : ℝ} (ha₀a : a₀ < a)
    (hab : Set.Icc a₀ b ⊆ D.regular) {t1 t2 tau : ℝ}
    (h1 : t1 ∈ Set.Icc a b) (h2 : t2 ∈ Set.Icc a b) (hle : t1 ≤ t2) (htau : 0 < tau) :
    muSmooth (S.base.metric t1) (tau + t2 - t1) ≤ muSmooth (S.base.metric t2) tau := by
  classical
  obtain ⟨rho, hrho, hstepL⟩ := exists_muSmooth_step (I := I) (M := M) S hS ha₀a hab
  let delta : ℝ := rho / 2
  have hdelta : 0 < delta := half_pos hrho
  have hdelta_rho : delta ≤ rho := by
    dsimp only [delta]
    linarith
  let Good : ℝ → Prop := fun t => ∀ theta : ℝ, 0 < theta →
    muSmooth (S.base.metric t1) (theta + t - t1) ≤ muSmooth (S.base.metric t) theta
  have hbase : Good t1 := by
    intro theta htheta
    have h : theta + t1 - t1 = theta := by ring
    rw [h]
  have hgrid : ∀ n : Nat, ∀ t ∈ Set.Icc t1 b, t ≤ t1 + (n : ℝ) * delta → Good t := by
    intro n
    induction n with
    | zero =>
        intro t ht hta
        have hta' : t = t1 := by
          norm_num at hta
          exact le_antisymm hta ht.1
        subst hta'
        exact hbase
    | succ n ih =>
        intro t ht htn
        let s : ℝ := max t1 (t - delta)
        have hs1 : t1 ≤ s := le_max_left _ _
        have hst : s ≤ t := by
          apply max_le ht.1
          linarith [hdelta.le]
        have hsb : s ≤ b := hst.trans ht.2
        have hsn : s ≤ t1 + (n : ℝ) * delta := by
          apply max_le
          · have hn0 : 0 ≤ (n : ℝ) * delta := mul_nonneg (Nat.cast_nonneg n) hdelta.le
            linarith
          · norm_num [Nat.cast_succ] at htn ⊢
            linarith
        have hgap : t - s ≤ delta := by
          have hsLower : t - delta ≤ s := le_max_right _ _
          linarith
        have hgood := ih s ⟨hs1, hsb⟩ hsn
        intro theta htheta
        have htheta' : 0 < theta + t - s := by linarith
        have hgood' := hgood (theta + t - s) htheta'
        have hstep' := hstepL (s := s) (t := t) (theta := theta)
          ⟨h1.1.trans hs1, hsb⟩ ⟨h1.1.trans ht.1, ht.2⟩ hst
          (hgap.trans hdelta_rho) htheta
        have hchain : (theta + t - s) + s - t1 = theta + t - t1 := by ring
        rw [hchain] at hgood'
        exact hgood'.trans hstep'
  obtain ⟨N, hN⟩ := exists_nat_gt ((t2 - t1) / delta)
  have hcover : t2 ≤ t1 + (N : ℝ) * delta := by
    have hmul : t2 - t1 < (N : ℝ) * delta := (div_lt_iff₀ hdelta).mp hN
    linarith
  have hgood2 := hgrid N t2 ⟨hle, h2.2⟩ hcover
  exact hgood2 tau htau

theorem mu_monotone_of_regular [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t1 t2 tau : ℝ} (hle : t1 ≤ t2)
    (hreg : Set.Icc t1 t2 ⊆ D.regular) (htau : 0 < tau) :
    muSmooth (S.base.metric t1) (tau + t2 - t1) ≤ muSmooth (S.base.metric t2) tau := by
  classical
  obtain ⟨l1, u1, ht1in, hsl1⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp
      (D.regular_isOpen.mem_nhds (hreg ⟨le_rfl, hle⟩))
  obtain ⟨l2, u2, ht2in, hsl2⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp
      (D.regular_isOpen.mem_nhds (hreg ⟨hle, le_rfl⟩))
  have ha₀a : (l1 + t1) / 2 < t1 := by linarith [ht1in.1]
  have hsub : Set.Icc ((l1 + t1) / 2) t2 ⊆ D.regular := by
    intro x hx
    rcases le_total x t1 with hx1 | hx1
    · exact hsl1 ⟨by linarith [hx.1, ht1in.1], by linarith [hx1, ht1in.2]⟩
    · rcases le_total x t2 with hx2 | hx2
      · exact hreg ⟨hx1, hx2⟩
      · exact hsl2 ⟨by linarith [hx2, ht2in.1], by linarith [hx.2, ht2in.2]⟩
  exact exists_muSmooth_step_chain (I := I) (M := M) S hS ha₀a hsub
    ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle htau

end MuMonotoneBridge

theorem mu_monotone [I.Boundaryless] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) {t1 t2 tau : ℝ}
    (hle : t1 ≤ t2) (hreg : Set.Icc t1 t2 ⊆ D.regular) (htau : 0 < tau) :
    muSmooth (S.base.metric t1) (tau + t2 - t1) ≤ muSmooth (S.base.metric t2) tau := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  exact mu_monotone_of_regular (I := I) (M := M) S hS hle hreg htau


theorem mu_compact_scale_lower [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, ∀ tau ∈ Set.Icc a b, (L : EReal) ≤ muSmooth g tau := by
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let R : M → ℝ := fun x => metricScalarAt (I := I) (M := M) g x
  have hRcont : Continuous R := by
    simpa only [R] using (metricScalar_smooth (I := I) (M := M) g).continuous
  obtain ⟨B, hB⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Entropy.w_fixed_lower (I := I) (M := M) g hdim b
  refine ⟨B, ?_⟩
  intro tau htau
  obtain ⟨htau0, htb⟩ := (Set.Icc_subset_Ioc_iff hab).mpr ⟨ha, le_rfl⟩ htau
  unfold muSmooth
  refine le_iInf fun w => le_iInf fun hw => le_iInf fun hwpos => ?_
  refine EReal.coe_le_coe ?_
  let v : M → ℝ := w.value
  have hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := hw
  have hvpos : ∀ x : M, 0 < v x := hwpos
  have hmass : (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 := by
    simpa only [v] using w.normalized
  have hWlb : B ≤ DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional
      (riemannianVolumeMeasure I M g) 3 tau R
      (fun x => g.inner x
        (DifferentialGeometry.Geometry.Operator.gradientFun g
          (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential 3 tau
            (fun y => v y * v y)) x)
        (DifferentialGeometry.Geometry.Operator.gradientFun g
          (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential 3 tau
            (fun y => v y * v y)) x))
      (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential 3 tau
        (fun y => v y * v y)) :=
    hB ⟨htau0, htb⟩ hv hvpos hmass
  have hSq := DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form
    (riemannianVolumeMeasure I M g) g 3 htau0 R hv hvpos
  simp only [DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] at hSq
  have hae : (fun x : M => (w.gradient x : TangentSpace I x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun x => DifferentialGeometry.Geometry.Operator.gradFun g v x) :=
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.ae_eq
      (g := g) (u := v)
      (G := fun x : M => (w.gradient x : TangentSpace I x))
      (G' := fun x => DifferentialGeometry.Geometry.Operator.gradFun g v x)
      w.weak_gradient
      (hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hv)
      (by
        have h2 : MemLp (fun x => Real.sqrt
            (g.inner x (w.gradient x) (w.gradient x))) 2
            (riemannianVolumeMeasure I M g) := w.gradient_memLp
        exact h2.mono_exponent (by norm_num))
      (by
        have h2 : MemLp (fun x => Real.sqrt
            (g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v x)
              (DifferentialGeometry.Geometry.Operator.gradFun g v x))) 2
            (riemannianVolumeMeasure I M g) :=
          DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
            (I := I) (M := M) g 2 hv
        exact h2.mono_exponent (by norm_num))
  let I₁ : M → ℝ := fun x => 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
      tau * metricScalarAt (I := I) (M := M) g x * w.value x ^ 2 -
      w.value x ^ 2 * Real.log (w.value x ^ 2)
  let I₂ : M → ℝ := fun x =>
      4 * tau * g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
      tau * R x * (v x * v x) - (v x * v x) * Real.log (v x * v x)
  let c : ℝ := Real.log
    (DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor 3 tau) - (3 : ℕ)
  have henergy : Continuous (fun x => g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun g v x)
      (DifferentialGeometry.Geometry.Operator.gradFun g v x)) := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨v, hv⟩)
      (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨v, hv⟩)
    exact hinner.congr (fun _ => rfl)
  have hsq : Continuous (fun x : M => v x * v x) := hv.continuous.mul hv.continuous
  have hI₂cont : Continuous I₂ := by
    have h3 : Continuous (fun x => (v x * v x) * Real.log (v x * v x)) :=
      hsq.mul (hsq.log fun x => (mul_pos (hvpos x) (hvpos x)).ne')
    have h1 : Continuous (fun x => 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)) := henergy.const_mul (4 * tau)
    have h2 : Continuous (fun x => tau * R x * (v x * v x)) :=
      (hRcont.const_mul tau).mul hsq
    exact ((h1.add h2).sub h3).congr
      (fun x => by simp only [I₂, Pi.add_apply, Pi.sub_apply])
  have hI₂int : Integrable I₂ (riemannianVolumeMeasure I M g) :=
    hI₂cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvvint : Integrable (fun x => v x * v x) (riemannianVolumeMeasure I M g) :=
    hsq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI₁I₂ : (∫ x, I₁ x ∂(riemannianVolumeMeasure I M g)) =
      ∫ x, I₂ x ∂(riemannianVolumeMeasure I M g) := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp only [I₁, I₂, R, v, hx, pow_two]
  have hvvmass : (∫ x, v x * v x ∂(riemannianVolumeMeasure I M g)) = 1 := by
    rw [← hmass]
    apply integral_congr_ae
    filter_upwards with x
    rw [pow_two]
  have hI₂add : (∫ x, I₂ x + c * (v x * v x) ∂(riemannianVolumeMeasure I M g)) =
      (∫ x, I₂ x ∂(riemannianVolumeMeasure I M g)) + c := by
    rw [integral_add hI₂int (hvvint.const_mul c), integral_const_mul, hvvmass, mul_one]
  have hc : c = -((3 : ℝ) / 2 * Real.log (4 * Real.pi * tau)) - 3 := by
    have hpref := DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor 3 htau0
    dsimp only [c]
    rw [hpref]
    norm_num
  have hent : entropyValue g tau w =
      (∫ x, I₁ x ∂(riemannianVolumeMeasure I M g)) -
        ((3 : ℝ) / 2 * Real.log (4 * Real.pi * tau)) - 3 := by
    simp only [entropyValue, I₁, hdim]
    norm_num
  have hkey : entropyValue g tau w =
      (∫ x, I₂ x ∂(riemannianVolumeMeasure I M g)) + c := by
    rw [hent, hI₁I₂, hc]
    ring
  rw [hkey]
  exact hWlb.trans (le_of_eq (hSq.trans hI₂add))



def cutoffEntropyConstant (n : ℕ) (D b : ℝ) : ℝ :=
  36 * D + b + D / Real.exp 1 - (n : ℝ) / 2 * Real.log (4 * Real.pi) - n

theorem cutoff_entropy_doubling [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    (x : M) {r D b : ℝ} (hr : 0 < r) (hD : 1 ≤ D) (hb : 0 ≤ b)
    (hdoubling : (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal ≤
      D * (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x (r / 2))).toReal)
    (hscalar : ∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) :
    muSobolev g (r ^ 2) ≤
      ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
        r ^ Module.finrank ℝ E) + cutoffEntropyConstant (Module.finrank ℝ E) D b : ℝ) : EReal) := by
  let _ := hdim
  let _ := hb
  let μ := riemannianVolumeMeasure I M g
  let U : Set M := riemannianBallOf (I := I) g x r
  have hVpos : 0 < (μ U).toReal := by
    simpa only [μ, U, riemannianBallOf] using
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.edist_vol_pos
        (I := I) (M := M) g x hr
  obtain ⟨w, G, _hwcont, hw2, hwweak, hwgrad2, hwpos, hwmass, hwbound⟩ :=
    exists_normalized_cutoff_wform (I := I) (M := M) g x hr hD hdoubling
      (R := fun y => metricScalarAt (I := I) (M := M) g y)
      (metricScalar_smooth (I := I) (M := M) g).continuous
      (fun y hy => hscalar y hy)
  let W : EntropyTest g :=
    { value := w
      gradient := G
      value_memLp := hw2
      weak_gradient := hwweak
      gradient_memLp := hwgrad2
      nonnegative := Filter.Eventually.of_forall hwpos
      normalized := hwmass }
  refine (iInf_le (fun w : EntropyTest g => (entropyValue g (r ^ 2) w : EReal)) W).trans ?_
  have hbound : (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) +
        r ^ 2 * metricScalarAt g y * w y ^ 2 -
        w y ^ 2 * Real.log (w y ^ 2) ∂μ) ≤
      36 * D + b + Real.log (μ U).toReal := by
    simpa only [μ, U] using hwbound
  have hlog4 : Real.log (4 * Real.pi * r ^ 2) =
      Real.log (4 * Real.pi) + 2 * Real.log r := by
    rw [Real.log_mul (by positivity) (pow_ne_zero 2 hr.ne'), Real.log_pow]
    norm_num
  have hkey : entropyValue g (r ^ 2) W ≤
      Real.log ((μ U).toReal / r ^ Module.finrank ℝ E) +
        cutoffEntropyConstant (Module.finrank ℝ E) D b := by
    have hE : entropyValue g (r ^ 2) W =
        (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) +
          r ^ 2 * metricScalarAt g y * w y ^ 2 -
          w y ^ 2 * Real.log (w y ^ 2) ∂μ) -
          (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * r ^ 2) -
          Module.finrank ℝ E := rfl
    have hlogV : Real.log ((μ U).toReal / r ^ Module.finrank ℝ E) =
        Real.log (μ U).toReal - (Module.finrank ℝ E : ℝ) * Real.log r := by
      rw [Real.log_div hVpos.ne' (pow_ne_zero _ hr.ne'), Real.log_pow]
    have hconst : cutoffEntropyConstant (Module.finrank ℝ E) D b =
        36 * D + b + D / Real.exp 1 -
          (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi) -
          Module.finrank ℝ E := rfl
    have hDe : 0 ≤ D / Real.exp 1 :=
      div_nonneg (le_trans zero_le_one hD) (Real.exp_pos 1).le
    rw [hE, hlogV, hlog4, hconst]
    linarith only [hbound, hDe]
  exact EReal.coe_le_coe hkey


section LocalEntropyVolume

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

open Bundle DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_entropy_volume [I.Boundaryless]
    (hdim : 2 ≤ Module.finrank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
        -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) →
      (∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) →
      muSobolev g (r ^ 2) ≤
        ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
          r ^ Module.finrank ℝ E) + C : ℝ) : EReal) := by
  refine ⟨cutoffEntropyConstant (Module.finrank ℝ E)
    (max 1 (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant
      (Module.finrank ℝ E) a)) b, ?_⟩
  intro M _ _ _ _ _ _ g x r hr hRic hscalar
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace M := (RiemannianMetricComplete.of_compact (I := I) g).complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun y v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  refine cutoff_entropy_doubling (I := I) (M := M) g hdim x hr (le_max_left _ _) hb ?_ hscalar
  have hballR : riemannianBallOf (I := I) g x r =
      {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal r} := by
    unfold riemannianBallOf
    rfl
  have hballS : riemannianBallOf (I := I) g x (r / 2) =
      {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal (r / 2)} := by
    unfold riemannianBallOf
    rfl
  have hRicOn : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn
      (I := I) g {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal r} (-a / r ^ 2) := by
    intro y hy v
    have hyb : y ∈ riemannianBallOf (I := I) g x r := by
      rw [hballR]
      exact hy
    have h := hRic y hyb v
    have hmetric : metricRicciAt (I := I) g y (fun _ : Fin 2 => v) =
        ricciTensor (I := I) g y v v := by
      have hv : (fun _ : Fin 2 => v) = vec2 v v := by
        funext i
        fin_cases i <;> simp [vec2]
      rw [hv]
      exact metricRicciAt_apply_eq_ricciTensor (I := I) g y v v
    have hc : -a * r⁻¹ ^ 2 = -a / r ^ 2 := by rw [inv_pow, div_eq_mul_inv]
    rw [hmetric, hc] at h
    exact h
  rw [hballR, hballS]
  have hmain := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.localDoubling
    (I := I) (M := M) g hEnorm x hdim ha hr hRicOn
  have hmono : (riemannianVolumeMeasure I M g
        {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal (r / 2)}) ≤
      riemannianVolumeMeasure I M g
        {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal r} :=
    measure_mono fun y hy => lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by linarith))
  have hdcpos : 0 ≤ DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant
      (Module.finrank ℝ E) a :=
    (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant_pos
      (Module.finrank ℝ E) a hdim ha).le
  calc (riemannianVolumeMeasure I M g
        {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal r}).toReal
      ≤ (ENNReal.ofReal
            (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant
              (Module.finrank ℝ E) a) *
          riemannianVolumeMeasure I M g
            {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal :=
        ENNReal.toReal_mono' hmain fun hb => by
          rcases ENNReal.mul_eq_top.1 hb with ⟨h1, h2⟩ | ⟨h1, _⟩
          · exact top_unique (h2 ▸ hmono)
          · exact absurd h1 ENNReal.ofReal_ne_top
      _ = DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant
            (Module.finrank ℝ E) a *
          (riemannianVolumeMeasure I M g
            {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal :=
        ENNReal.toReal_ofReal_mul _ _ hdcpos
      _ ≤ max 1 (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.doublingConstant
            (Module.finrank ℝ E) a) *
          (riemannianVolumeMeasure I M g
            {y : M | Manifold.riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg

end LocalEntropyVolume

theorem strong_scalar_no_local_collapsing [I.Boundaryless] [ConnectedSpace M]
    [T2Space (TangentBundle I M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {rho : ℝ} (hrho : 0 < rho) : StrongScalarNoLocalCollapsing S rho := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.strongScalarNoLocalCollapsing_three
    hT S hS hdim hrho

theorem spatial_no_local_collapsing [I.Boundaryless] [ConnectedSpace M]
    [T2Space (TangentBundle I M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {rho : ℝ} (hrho : 0 < rho) : SpatialNoLocalCollapsing S rho := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.spatialNoLocalCollapsing_three
    hT S hS hdim hrho

theorem local_metric_injectivity [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
        [T2Space (TangentBundle I M)] (g : SmoothRiemannianMetric I M),
        RiemannianMetricComplete g → ∀ x : M, ∀ r : ℝ, 0 < r →
          (∀ y ∈ riemannianBallOf (I := I) g x r,
            r ^ 4 * Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y) ≤ 1) →
          ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) ≤
            riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r) →
          Set.InjOn (fun v : TangentSpace I x =>
            DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) g x v)
            {v | Real.sqrt (g.inner x v v) < iota * r} := by
  sorry

omit [CompleteSpace E] in
theorem parabolic_noncollapse_of_spatial {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {rho : ℝ}
    (h : SpatialNoLocalCollapsing S rho) : ParabolicNoLocalCollapsing S rho :=
  parabolicNoLocalCollapsing_of_spatial h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
