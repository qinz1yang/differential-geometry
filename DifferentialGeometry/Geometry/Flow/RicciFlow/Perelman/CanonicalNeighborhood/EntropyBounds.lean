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

theorem mu_monotone [I.Boundaryless] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) {t1 t2 tau : ℝ}
    (h1 : t1 ∈ D.carrier) (h2 : t2 ∈ D.carrier) (hle : t1 ≤ t2) (htau : 0 < tau) :
    muSmooth (S.base.metric t1) (tau + t2 - t1) ≤ muSmooth (S.base.metric t2) tau := by
  sorry


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
