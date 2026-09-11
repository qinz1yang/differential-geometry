import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.CalculusBackground
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Basis.VectorSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength

noncomputable section

open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology


abbrev Disk := Metric.closedBall (0 : ℂ) 1


def diskCenter : Disk := ⟨0, by simp⟩


def diskBoundary (θ : Surgery.Topology.Circle) : Disk :=
  ⟨(AddCircle.toCircle θ : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (AddCircle.toCircle θ).norm_coe.le⟩

theorem diskBoundary_coe (t : ℝ) :
    (diskBoundary (t : Surgery.Topology.Circle) : ℂ) =
      (_root_.Circle.exp (2 * Real.pi * t) : ℂ) := by
  simp [diskBoundary, AddCircle.toCircle_apply_mk]

private theorem norm_toCircle_sub_one_le (x : Surgery.Topology.Circle) :
    ‖(AddCircle.toCircle x : ℂ) - 1‖ ≤ (2 * Real.pi) * ‖x‖ := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [mul_comm (2 * Real.pi), ← div_le_iff₀ hp]
  apply QuotientAddGroup.le_norm_iff.mpr
  intro t ht
  rw [← ht, AddCircle.toCircle_apply_mk]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  apply (div_le_iff₀ hp).mpr
  have he : Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := mul_comm _ _
  rw [he] at hb
  have hn : ‖2 * Real.pi * t‖ = ‖t‖ * (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp, Real.norm_eq_abs]
    ring
  simpa only [div_one, Circle.coe_exp] using hb.trans_eq hn

private theorem diskBoundary_lipschitz :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩ diskBoundary := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have halg : (AddCircle.toCircle x : ℂ) - (AddCircle.toCircle y : ℂ) =
      ((AddCircle.toCircle (x - y) : ℂ) - 1) * (AddCircle.toCircle y : ℂ) := by
    have hadd : AddCircle.toCircle (x - y) * AddCircle.toCircle y = AddCircle.toCircle x := by
      rw [← AddCircle.toCircle_add, sub_add_cancel]
    have hc := congrArg (fun z : _root_.Circle => (z : ℂ)) hadd
    change (AddCircle.toCircle (x - y) : ℂ) * (AddCircle.toCircle y : ℂ) = _ at hc
    rw [sub_mul, hc, one_mul]
  rw [Subtype.dist_eq, dist_eq_norm]
  change ‖(AddCircle.toCircle x : ℂ) - (AddCircle.toCircle y : ℂ)‖ ≤
    (2 * Real.pi) * dist x y
  rw [halg, norm_mul, (AddCircle.toCircle y).norm_coe, mul_one, dist_eq_norm]
  exact norm_toCircle_sub_one_le (x - y)


abbrev Annulus := Icc (0 : ℝ) 1 × Surgery.Topology.Circle


def annulusRectangle : Set ℂ :=
  {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1}

private def annulusParameter (z : annulusRectangle) : Annulus :=
  (⟨z.1.re, z.2.1⟩, (z.1.im : Surgery.Topology.Circle))

private theorem annulusParameter_lipschitz : LipschitzWith 1 annulusParameter := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, Prod.dist_eq]
  apply max_le
  · change dist z.1.re w.1.re ≤ dist z.1 w.1
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, Complex.sub_re] using
      Complex.abs_re_le_norm (z.1 - w.1)
  · change dist (z.1.im : Surgery.Topology.Circle) (w.1.im : Surgery.Topology.Circle) ≤ dist z.1 w.1
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    calc
      _ ≤ ‖z.1.im - w.1.im‖ := QuotientAddGroup.norm_mk_le_norm
      _ ≤ dist z.1 w.1 := by
        simpa only [Real.norm_eq_abs, dist_eq_norm, Complex.sub_im] using
          Complex.abs_im_le_norm (z.1 - w.1)

private theorem annulusRectangle_convex : Convex ℝ annulusRectangle :=
  ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.reLm).inter
    ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.imLm)

private theorem annulusRectangle_compact : IsCompact annulusRectangle := by
  change IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    (isCompact_Icc.isBounded.reProdIm isCompact_Icc.isBounded)

section DerivativeBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompactSpace Q] [T2Space Q]

private theorem exists_pos_derivative_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I Q) (f : Q → F)
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ q (v : TangentSpace I q),
      ‖mfderiv I 𝓘(ℝ, F) f q v‖ ≤ C * Real.sqrt (g.inner q v v) := by
  let U := MetricUnitTangent (I := I) (M := Q) g
  let : CompactSpace U := isCompact_univ_iff.mp (metricUnit_compact g)
  have ht : Continuous (fun p : TangentBundle I Q =>
      mfderiv I 𝓘(ℝ, F) f p.proj p.2) :=
    continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).continuous.comp
      (hf.continuous_tangentMap le_rfl))
  have hn : Continuous (fun p : U => ‖mfderiv I 𝓘(ℝ, F) f p.1.proj p.1.2‖) :=
    (ht.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hn).bddAbove
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun q v => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp
  · let r := Real.sqrt (g.inner q v v)
    have hr : 0 < r := Real.sqrt_pos.mpr (g.pos q v hv)
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hr2 : r ^ 2 = g.inner q v v := Real.sq_sqrt (g.pos q v hv).le
    let w : TangentSpace I q := r⁻¹ • v
    have hw : g.inner q w w = 1 := by
      simp only [w, map_smul, smul_apply, smul_eq_mul]
      rw [← hr2]
      field_simp
    let p : U := ⟨(⟨q, w⟩ : TangentBundle I Q), hw⟩
    have hb : ‖mfderiv I 𝓘(ℝ, F) f q w‖ ≤ max 1 B :=
      (hB ⟨p, rfl⟩).trans (le_max_right _ _)
    have hvw : v = r • w := by
      simp only [w, smul_smul, mul_inv_cancel₀ hr0, one_smul]
    have heq : ‖mfderiv I 𝓘(ℝ, F) f q v‖ =
        r * ‖mfderiv I 𝓘(ℝ, F) f q w‖ := by
      conv_lhs => rw [hvw, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact heq.trans_le ((mul_le_mul_of_nonneg_left hb hr.le).trans_eq (mul_comm _ _))

end DerivativeBound

section DistanceBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edist_le_of_derivative_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : SmoothRiemannianMetric I Q) (f : Q → F)
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ q (v : TangentSpace I q),
      ‖mfderiv I 𝓘(ℝ, F) f q v‖ ≤ C * Real.sqrt (g.inner q v v)) (x y : Q) :
    edist (f x) (f y) ≤ ENNReal.ofReal C * riemannianEDistOf g x y := by
  have hC0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  rw [edistOf_iInf, ENNReal.mul_iInf_of_ne hC0 ENNReal.ofReal_ne_top]
  refine le_iInf fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hγ => ?_
  have hmap : ContMDiff (𝓡∂ 1) 𝓘(ℝ, F) 1 (γ.map hf.continuous) :=
    hf.comp hγ
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F))]
  have hpath : Manifold.riemannianEDist 𝓘(ℝ, F) (f x) (f y) ≤
      ∫⁻ t, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, F) (γ.map hf.continuous) t 1‖ₑ := by
    rw [Manifold.riemannianEDist]
    exact biInf_le _ hmap
  refine hpath.trans ?_
  rw [← lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  have hderiv : mfderiv (𝓡∂ 1) 𝓘(ℝ, F) (γ.map hf.continuous) t 1 =
      mfderiv I 𝓘(ℝ, F) f (γ t) (mfderiv (𝓡∂ 1) I γ t 1) := by
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, F) (f ∘ γ) t 1 = _
    exact mfderiv_comp_apply t (hf.mdifferentiable one_ne_zero (γ t))
      (hγ.mdifferentiable one_ne_zero t) 1
  dsimp only
  rw [← ofReal_norm, norm_tangentSpace_vectorSpace, hderiv]
  have hb := hbound (γ t) (mfderiv (𝓡∂ 1) I γ t 1)
  rw [norm_tangentSpace_vectorSpace] at hb
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq
    (ENNReal.ofReal_mul hC.le)

end DistanceBound

section ChartReflection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [IsManifold I ∞ Q] in
private theorem mdifferentiableWithinAt_of_injective_derivative_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : Q → F) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : V → Q) (s : Set V) {z : V} (hz : z ∈ s)
    (hu : ContinuousWithinAt u s z)
    (hi : Function.Injective (mfderiv I 𝓘(ℝ, F) e (u z)))
    (hh : DifferentiableWithinAt ℝ (e ∘ u) s z) :
    MDifferentiableWithinAt 𝓘(ℝ, V) I u s z := by
  let D : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) e (u z)
  obtain ⟨p, hp⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  let pC : F →L[ℝ] E := p.toContinuousLinearMap
  have hleft : Function.LeftInverse pC D := by
    intro v
    exact congrArg (fun A : E →ₗ[ℝ] E => A v) hp
  have hout : HasFDerivAt (e ∘ (extChartAt I (u z)).symm) D
      (extChartAt I (u z) (u z)) := by
    have h := (he.mdifferentiable one_ne_zero (u z)).hasMFDerivAt.2
    have h' : HasFDerivWithinAt (e ∘ (extChartAt I (u z)).symm) D Set.univ
        (extChartAt I (u z) (u z)) := by
      simp only [I.range_eq_univ, writtenInExtChartAt,
        extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h
      convert! h using 1
    exact h'.hasFDerivAt Filter.univ_mem
  have hcont : ContinuousWithinAt (extChartAt I (u z) ∘ u) s z :=
    (continuousAt_extChartAt (I := I) (u z)).comp_continuousWithinAt hu
  have heq : (e ∘ (extChartAt I (u z)).symm) ∘ (extChartAt I (u z) ∘ u)
      =ᶠ[𝓝[s] z] e ∘ u := by
    filter_upwards [hu.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I) (u z))]
      with w hw
    exact congrArg e ((extChartAt I (u z)).left_inv hw)
  have hcoord : HasFDerivWithinAt (extChartAt I (u z) ∘ u)
      (pC.comp (fderivWithin ℝ (e ∘ u) s z)) s z :=
    HasFDerivWithinAt.of_comp_of_leftInverse (t := Set.univ)
      (hcont.tendsto_nhdsWithin (fun _ _ => Set.mem_univ _))
      hout.hasFDerivWithinAt hh.hasFDerivWithinAt heq hleft hz
  apply mdifferentiableWithinAt_iff_target.mpr
  exact ⟨hu, hcoord.differentiableWithinAt.mdifferentiableWithinAt⟩

end ChartReflection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def diskExtension (u : Disk → Q) (z : ℂ) : Q := by
  classical
  exact if hz : z ∈ Metric.closedBall (0 : ℂ) 1 then u ⟨z, hz⟩ else u diskCenter

omit [TopologicalSpace Q] in
@[simp] theorem diskExtension_coe (u : Disk → Q) (z : Disk) :
    diskExtension u (z : ℂ) = u z := by
  simp [diskExtension, z.property]

omit [TopologicalSpace Q] in
theorem diskExtension_agrees (u : Disk → Q) :
    ∀ z : Disk, diskExtension u z = u z := diskExtension_coe u


structure LipschitzDisk (g : SmoothRiemannianMetric I Q) where
  map : C(Disk, Q)
  isLipschitz : ∃ L : ℝ≥0, ∀ z w : Disk,
    riemannianEDistOf g (map z) (map w) ≤ (L : ℝ≥0∞) * edist z w


def LipschitzDisk.changeMetric (g h : SmoothRiemannianMetric I Q)
    {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ q (v : TangentSpace I q), h.inner q v v ≤ c * g.inner q v v)
    (u : LipschitzDisk g) : LipschitzDisk h where
  map := u.map
  isLipschitz := by
    obtain ⟨L, hL⟩ := u.isLipschitz
    refine ⟨Real.toNNReal (Real.sqrt c) * L, fun z w => ?_⟩
    calc
      riemannianEDistOf h (u.map z) (u.map w) ≤
          ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf g (u.map z) (u.map w) :=
        edistOf_le_of_quad g h hc hmetric _ _
      _ ≤ ENNReal.ofReal (Real.sqrt c) * ((L : ℝ≥0∞) * edist z w) :=
        mul_le_mul' le_rfl (hL z w)
      _ = ((Real.toNNReal (Real.sqrt c) * L : ℝ≥0) : ℝ≥0∞) * edist z w := by
        simp only [ENNReal.coe_mul, ENNReal.ofReal, mul_assoc]


abbrev DiskCompetitor (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) :=
  {u : LipschitzDisk g // ∀ θ : Surgery.Topology.Circle, u.map (diskBoundary θ) = γ θ}


def diskBasis (i : Fin 2) : ℂ := if i = 0 then 1 else Complex.I


def parametricJacobian (g : SmoothRiemannianMetric I Q) (u : ℂ → Q)
    (s : Set ℂ) (z : ℂ) : ℝ := by
  classical
  exact if MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z then
    Real.sqrt (Matrix.det (fun i j : Fin 2 =>
      g.inner (u z) (mfderivWithin 𝓘(ℝ, ℂ) I u s z (diskBasis i))
        (mfderivWithin 𝓘(ℝ, ℂ) I u s z (diskBasis j))))
  else 0


def diskJacobian (g : SmoothRiemannianMetric I Q) (u : Disk → Q) (z : ℂ) : ℝ :=
  parametricJacobian g (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z


def diskArea (g : SmoothRiemannianMetric I Q) (u : Disk → Q) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) 1, diskJacobian g u z


def annulusExtension (u : Annulus → Q) (z : ℂ) : Q := by
  classical
  exact if hz : z.re ∈ Icc (0 : ℝ) 1 then u (⟨z.re, hz⟩, (z.im : Surgery.Topology.Circle))
  else u (⟨0, by simp⟩, (z.im : Surgery.Topology.Circle))

omit [TopologicalSpace Q] in
theorem annulusExtension_agrees (u : Annulus → Q) {z : ℂ}
    (hz : z ∈ annulusRectangle) :
    annulusExtension u z = u (⟨z.re, hz.1⟩, (z.im : Surgery.Topology.Circle)) := by
  simp only [annulusExtension, dif_pos hz.1]


def annulusArea (g : SmoothRiemannianMetric I Q) (u : Annulus → Q) : ℝ :=
  ∫ z in annulusRectangle, parametricJacobian g (annulusExtension u) annulusRectangle z

structure LipschitzAnnulus (g : SmoothRiemannianMetric I Q) where
  map : C(Annulus, Q)
  isLipschitz : ∃ L : ℝ≥0, ∀ z w : Annulus,
    riemannianEDistOf g (map z) (map w) ≤ (L : ℝ≥0∞) * edist z w

theorem parametricJacobian_nonneg (g : SmoothRiemannianMetric I Q)
    (u : ℂ → Q) (s : Set ℂ) (z : ℂ) : 0 ≤ parametricJacobian g u s z := by
  unfold parametricJacobian
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_refl _

theorem diskArea_nonneg (g : SmoothRiemannianMetric I Q) (u : Disk → Q) :
    0 ≤ diskArea g u := by
  exact integral_nonneg fun z => parametricJacobian_nonneg _ _ _ _

theorem annulusArea_nonneg (g : SmoothRiemannianMetric I Q) (u : Annulus → Q) :
    0 ≤ annulusArea g u := by
  exact integral_nonneg fun z => parametricJacobian_nonneg _ _ _ _


def constantLipschitzDisk (g : SmoothRiemannianMetric I Q) (q : Q) : LipschitzDisk g :=
  ⟨ContinuousMap.const Disk q, 0, fun _ _ => by
    change riemannianEDistOf g q q ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le⟩

def constantDiskCompetitor (g : SmoothRiemannianMetric I Q) (q : Q) :
    DiskCompetitor g (constantLoops q) :=
  ⟨constantLipschitzDisk g q, fun _ => rfl⟩

theorem parametricJacobian_congr_on (g : SmoothRiemannianMetric I Q)
    {u v : ℂ → Q} {s : Set ℂ} (h : EqOn u v s) {z : ℂ} (hz : z ∈ s) :
    parametricJacobian g u s z = parametricJacobian g v s z := by
  have hdiff : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z ↔
      MDifferentiableWithinAt 𝓘(ℝ, ℂ) I v s z :=
    ⟨fun hu => hu.congr_of_mem h.symm hz, fun hv => hv.congr_of_mem h hz⟩
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := I) h hz
  unfold parametricJacobian
  split_ifs with hu hv hv
  · dsimp only [TangentSpace] at hd ⊢
    rw [hd, h hz]
  · exact (hv (hdiff.mp hu)).elim
  · exact (hu (hdiff.mpr hv)).elim
  · rfl


theorem disk_uniqueDiffWithinAt (z : Disk) :
    UniqueDiffWithinAt ℝ (Metric.closedBall (0 : ℂ) 1) (z : ℂ) := by
  apply uniqueDiffOn_convex (convex_closedBall (0 : ℂ) 1) _ z z.property
  exact (Metric.nonempty_ball.mpr (show (0 : ℝ) < 1 by norm_num) :
    (Metric.ball (0 : ℂ) 1).Nonempty).mono Metric.ball_subset_interior_closedBall

theorem diskArea_const (g : SmoothRiemannianMetric I Q) (q : Q) :
    diskArea g (fun _ : Disk => q) = 0 := by
  have hext : diskExtension (fun _ : Disk => q) = fun _ : ℂ => q := by
    funext z
    simp [diskExtension]
  unfold diskArea diskJacobian
  rw [hext]
  have hzero (A : ℂ →L[ℝ] TangentSpace I q) (hA : A = 0) :
      Real.sqrt (Matrix.det (fun i j : Fin 2 => g.inner q (A (diskBasis i)) (A (diskBasis j)))) = 0 := by
    subst A
    simp only [zero_apply, map_zero]
    change Real.sqrt (Matrix.det (0 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
    rw [Matrix.det_zero, Real.sqrt_zero]
  have hJ (z : ℂ) :
      parametricJacobian g (fun _ : ℂ => q) (Metric.closedBall (0 : ℂ) 1) z = 0 := by
    unfold parametricJacobian
    split_ifs
    · exact hzero _ mfderivWithin_const
    · rfl
  simp only [hJ, integral_zero]

private theorem bilinear_gram_shear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (v w : V) (r : ℝ) :
    B v v * B (w - r • v) (w - r • v) -
        B v (w - r • v) * B (w - r • v) v =
      B v v * B w w - B v w * B w v := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [hB w v]
  ring

private theorem bilinear_gram_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G B : V →L[ℝ] V →L[ℝ] ℝ)
    (hGsym : ∀ v w, G v w = G w v) (hBsym : ∀ v w, B v w = B w v)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) (hBnonneg : ∀ v, 0 ≤ B v v)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ v, B v v ≤ c * G v v) (v w : V) :
    B v v * B w w - B v w * B w v ≤
      c ^ 2 * (G v v * G w w - G v w * G w v) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos := hGpos v hv
  let r : ℝ := G v w / G v v
  let z := w - r • v
  have hvz : G v z = 0 := by
    simp only [z, map_sub, map_smul, smul_eq_mul]
    dsimp only [r]
    rw [div_mul_cancel₀ _ (ne_of_gt hvpos), sub_self]
  have hgramG : G v v * G w w - G v w * G w v = G v v * G z z := by
    rw [← bilinear_gram_shear G hGsym v w r]
    change G v v * G z z - G v z * G z v = _
    rw [hvz, zero_mul, sub_zero]
  have hgramB : B v v * B w w - B v w * B w v =
      B v v * B z z - (B v z) ^ 2 := by
    rw [← bilinear_gram_shear B hBsym v w r]
    change B v v * B z z - B v z * B z v = _
    rw [hBsym z v, pow_two]
  rw [hgramB, hgramG]
  calc
    B v v * B z z - (B v z) ^ 2 ≤ B v v * B z z :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ (c * G v v) * (c * G z z) :=
      mul_le_mul (hbound v) (hbound z) (hBnonneg z) (mul_nonneg hc hvpos.le)
    _ = c ^ 2 * (G v v * G z z) := by ring

private theorem sqrt_bilinear_gram_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G B : V →L[ℝ] V →L[ℝ] ℝ)
    (hGsym : ∀ v w, G v w = G w v) (hBsym : ∀ v w, B v w = B w v)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) (hBnonneg : ∀ v, 0 ≤ B v v)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ v, B v v ≤ c * G v v) (v w : V) :
    Real.sqrt (B v v * B w w - B v w * B w v) ≤
      c * Real.sqrt (G v v * G w w - G v w * G w v) := by
  have h := Real.sqrt_le_sqrt (bilinear_gram_le G B hGsym hBsym hGpos hBnonneg hc hbound v w)
  simpa only [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] using h

private theorem sqrt_bilinear_gram_matrix_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (G B : V →L[ℝ] V →L[ℝ] ℝ)
    (hGsym : ∀ v w, G v w = G w v) (hBsym : ∀ v w, B v w = B w v)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) (hBnonneg : ∀ v, 0 ≤ B v v)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ v, B v v ≤ c * G v v) (v : Fin 2 → V) :
    Real.sqrt (Matrix.det (fun i j : Fin 2 => B (v i) (v j))) ≤
      c * Real.sqrt (Matrix.det (fun i j : Fin 2 => G (v i) (v j))) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => B (v i) (v j))
  let C : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => G (v i) (v j))
  calc
    Real.sqrt (Matrix.det (fun i j : Fin 2 => B (v i) (v j))) =
        Real.sqrt (B (v 0) (v 0) * B (v 1) (v 1) - B (v 0) (v 1) * B (v 1) (v 0)) :=
      congrArg Real.sqrt (Matrix.det_fin_two A)
    _ ≤ c * Real.sqrt
        (G (v 0) (v 0) * G (v 1) (v 1) - G (v 0) (v 1) * G (v 1) (v 0)) :=
      sqrt_bilinear_gram_le G B hGsym hBsym hGpos hBnonneg hc hbound (v 0) (v 1)
    _ = c * Real.sqrt (Matrix.det (fun i j : Fin 2 => G (v i) (v j))) :=
      congrArg (fun x : ℝ => c * Real.sqrt x) (Matrix.det_fin_two C).symm

private theorem parametricJacobian_metric_upper (g h : SmoothRiemannianMetric I Q)
    {c : ℝ} (hc : 0 ≤ c)
    (hmetric : ∀ q (v : TangentSpace I q), h.inner q v v ≤ c * g.inner q v v)
    (u : ℂ → Q) (s : Set ℂ) (z : ℂ) :
    parametricJacobian h u s z ≤ c * parametricJacobian g u s z := by
  classical
  unfold parametricJacobian
  split_ifs
  · let D : ℂ →L[ℝ] TangentSpace I (u z) := mfderivWithin 𝓘(ℝ, ℂ) I u s z
    have hnonneg (v : TangentSpace I (u z)) : 0 ≤ h.inner (u z) v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact (h.pos (u z) v hv).le
    change Real.sqrt (Matrix.det (fun i j : Fin 2 => h.inner (u z) (D (diskBasis i))
      (D (diskBasis j)))) ≤ c * Real.sqrt (Matrix.det (fun i j : Fin 2 =>
      g.inner (u z) (D (diskBasis i)) (D (diskBasis j))))
    exact sqrt_bilinear_gram_matrix_le (g.inner (u z)) (h.inner (u z))
      (g.symm (u z)) (h.symm (u z)) (g.pos (u z)) hnonneg hc (hmetric (u z))
      (fun i => D (diskBasis i))
  · simp

private theorem complex_lipschitzOn_image_volume_zero
    {s : Set ℂ} {f : ℂ → ℂ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  let μ : Measure ℂ := Measure.hausdorffMeasure (Module.finrank ℝ ℂ)
  have hμs : μ s = 0 := Measure.absolutelyContinuous_isAddHaarMeasure μ volume hs
  have hμimage : μ (f '' s) = 0 := by
    apply le_antisymm _ (by positivity)
    calc
      μ (f '' s) ≤ (L : ENNReal) ^ (Module.finrank ℝ ℂ : ℝ) * μ s :=
        hf.hausdorffMeasure_image_le (by positivity)
      _ = 0 := by rw [hμs, mul_zero]
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume μ hμimage

private theorem complex_lipschitzOn_measurable_differentiability_subset
    {s : Set ℂ} (hs : MeasurableSet s) {f : ℂ → ℂ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) :
    ∃ t : Set ℂ, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[volume] s ∧
      f '' t =ᵐ[volume] f '' s ∧
      ∀ x ∈ t, HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := by
  have hae := (ae_restrict_iff' hs).mp (hf.ae_differentiableWithinAt (μ := volume) hs)
  obtain ⟨n, hbn, hn, hn0⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let t := s \ n
  have hts : t ⊆ s := sdiff_subset
  have htd : ∀ x ∈ t, DifferentiableWithinAt ℝ f s x := by
    intro x hx
    by_contra h
    exact hx.2 (hbn (Classical.not_imp.mpr ⟨hx.1, h⟩))
  have himg0 : volume (f '' (s ∩ n)) = 0 :=
    complex_lipschitzOn_image_volume_zero (hf.mono inter_subset_left)
      (measure_mono_null inter_subset_right hn0)
  have himg : f '' t =ᵐ[volume] f '' s := by
    apply ae_eq_set.mpr
    constructor
    · rw [sdiff_eq_empty.mpr (image_mono hts), measure_empty]
    · apply measure_mono_null _ himg0
      rintro y ⟨⟨x, hx, rfl⟩, hyt⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      by_contra hxn
      exact hyt ⟨x, ⟨hx, hxn⟩, rfl⟩
  exact ⟨t, hts, hs.diff hn, sdiff_null_ae_eq_self hn0, himg,
    fun x hx => (htd x hx).hasFDerivWithinAt.mono hts⟩

private theorem complex_lipschitz_integral_image
    {s : Set ℂ} (hs : MeasurableSet s) {f : ℂ → ℂ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hinj : InjOn f s) (h : ℂ → ℝ) :
    ∫ x in f '' s, h x =
      ∫ x in s, |(fderivWithin ℝ f s x).det| * h (f x) := by
  obtain ⟨t, hts, ht, hteq, himg, hd⟩ :=
    complex_lipschitzOn_measurable_differentiability_subset hs hf
  calc
    (∫ x in f '' s, h x) = ∫ x in f '' t, h x := setIntegral_congr_set himg.symm
    _ = ∫ x in t, |(fderivWithin ℝ f s x).det| * h (f x) := by
      simpa only [smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume ht hd (hinj.mono hts) h
    _ = ∫ x in s, |(fderivWithin ℝ f s x).det| * h (f x) :=
      setIntegral_congr_set hteq

private def diskReparamExtension (φ : Disk ≃ₜ Disk) : ℂ → ℂ :=
  diskExtension (fun x => (φ x : ℂ))

private theorem diskReparamExtension_coe (φ : Disk ≃ₜ Disk) (z : Disk) :
    diskReparamExtension φ z = (φ z : ℂ) := diskExtension_coe _ _

private theorem diskReparamExtension_mapsTo (φ : Disk ≃ₜ Disk) :
    MapsTo (diskReparamExtension φ) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro z hz
  have he := diskReparamExtension_coe φ (⟨z, hz⟩ : Disk)
  rw [he]
  exact (φ ⟨z, hz⟩).property

private theorem diskReparamExtension_image (φ : Disk ≃ₜ Disk) :
    diskReparamExtension φ '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  apply subset_antisymm (diskReparamExtension_mapsTo φ).image_subset
  intro z hz
  refine ⟨(φ.symm ⟨z, hz⟩ : ℂ), (φ.symm ⟨z, hz⟩).property, ?_⟩
  simp only [diskReparamExtension_coe, φ.apply_symm_apply]

private theorem diskReparamExtension_leftInverse (φ : Disk ≃ₜ Disk)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    diskReparamExtension φ.symm (diskReparamExtension φ z) = z := by
  have he := diskReparamExtension_coe φ (⟨z, hz⟩ : Disk)
  rw [he, diskReparamExtension_coe]
  simp only [Homeomorph.symm_apply_apply]

private theorem diskReparamExtension_injOn (φ : Disk ≃ₜ Disk) :
    InjOn (diskReparamExtension φ) (Metric.closedBall 0 1) := by
  intro z hz w hw hzw
  have h := congrArg (diskReparamExtension φ.symm) hzw
  simpa only [diskReparamExtension_leftInverse φ hz,
    diskReparamExtension_leftInverse φ hw] using h

private theorem diskReparamExtension_lipschitz (φ : Disk ≃ₜ Disk)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    LipschitzOnWith L (diskReparamExtension φ) (Metric.closedBall 0 1) := by
  intro z hz w hw
  have h := hφ (⟨z, hz⟩ : Disk) (⟨w, hw⟩ : Disk)
  simpa only [Subtype.edist_eq, ← diskReparamExtension_coe] using h

private theorem diskReparamExtension_ae (φ : Disk ≃ₜ Disk)
    (hφinv : ∃ L : ℝ≥0, LipschitzWith L φ.symm) {p : ℂ → Prop}
    (hp : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1), p z) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
      p (diskReparamExtension φ z) := by
  obtain ⟨L, hL⟩ := hφinv
  have hp0 : volume {z : ℂ | z ∈ Metric.closedBall 0 1 ∧ ¬p z} = 0 := by
    simpa only [Classical.not_imp] using ae_iff.mp ((ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).mp hp)
  have himg0 := complex_lipschitzOn_image_volume_zero
    ((diskReparamExtension_lipschitz φ.symm hL).mono
      (show {z : ℂ | z ∈ Metric.closedBall 0 1 ∧ ¬p z} ⊆ Metric.closedBall 0 1 from
        fun z hz => hz.1)) hp0
  apply (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).mpr
  apply ae_iff.mpr
  apply measure_mono_null _ himg0
  intro z hz
  have hz' : z ∈ Metric.closedBall 0 1 ∧ ¬p (diskReparamExtension φ z) :=
    Classical.not_imp.mp hz
  exact ⟨diskReparamExtension φ z,
    ⟨diskReparamExtension_mapsTo φ hz'.1, hz'.2⟩,
    diskReparamExtension_leftInverse φ hz'.1⟩

private theorem diskBasis_eq_basisOneI : diskBasis = Complex.basisOneI := by
  funext i
  fin_cases i <;> simp [diskBasis, Complex.coe_basisOneI]

private theorem sqrt_bilin_gram_comp (B : LinearMap.BilinForm ℝ ℂ) (A : ℂ →ₗ[ℝ] ℂ) :
    Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin 2 =>
      B (A (diskBasis i)) (A (diskBasis j))))) =
      |A.det| * Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin 2 =>
        B (diskBasis i) (diskBasis j)))) := by
  have hm : Matrix.of (fun i j : Fin 2 => B (A (diskBasis i)) (A (diskBasis j))) =
      LinearMap.BilinForm.toMatrix Complex.basisOneI (B.comp A A) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, diskBasis_eq_basisOneI]
    rfl
  have hb : Matrix.of (fun i j : Fin 2 => B (diskBasis i) (diskBasis j)) =
      LinearMap.BilinForm.toMatrix Complex.basisOneI B := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, diskBasis_eq_basisOneI]
    rfl
  rw [hm, hb, LinearMap.BilinForm.toMatrix_comp Complex.basisOneI Complex.basisOneI]
  simp only [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
  rw [show A.det * (LinearMap.BilinForm.toMatrix Complex.basisOneI B).det * A.det =
      A.det ^ 2 * (LinearMap.BilinForm.toMatrix Complex.basisOneI B).det by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem parametricJacobian_comp_within (g : SmoothRiemannianMetric I Q)
    (u : ℂ → Q) (f : ℂ → ℂ) {s : Set ℂ} {z : ℂ}
    (hu : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s (f z))
    (hf : DifferentiableWithinAt ℝ f s z) (hfs : MapsTo f s s)
    (hz : UniqueDiffWithinAt ℝ s z) :
    parametricJacobian g (u ∘ f) s z =
      |(fderivWithin ℝ f s z).det| * parametricJacobian g u s (f z) := by
  have hmf := hf.mdifferentiableWithinAt
  have hc := hu.comp z hmf hfs
  simp only [parametricJacobian, if_pos hc, if_pos hu]
  let D : ℂ →L[ℝ] TangentSpace I (u (f z)) := mfderivWithin 𝓘(ℝ, ℂ) I u s (f z)
  let A : ℂ →L[ℝ] ℂ := fderivWithin ℝ f s z
  let B : LinearMap.BilinForm ℝ ℂ :=
    (g.inner (u (f z))).toBilinForm.comp D.toLinearMap D.toLinearMap
  have hchain := mfderivWithin_comp z hu hmf hfs hz.uniqueMDiffWithinAt
  simp only [mfderivWithin_eq_fderivWithin] at hchain
  rw [hchain]
  change Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin 2 =>
    B (A (diskBasis i)) (A (diskBasis j))))) =
      |A.toLinearMap.det| * Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin 2 =>
        B (diskBasis i) (diskBasis j))))
  exact sqrt_bilin_gram_comp B A.toLinearMap

omit [TopologicalSpace Q] in
private theorem diskExtension_reparam (u : Disk → Q) (φ : Disk ≃ₜ Disk) :
    diskExtension (u ∘ φ) = diskExtension u ∘ diskReparamExtension φ := by
  funext z
  change diskExtension (u ∘ φ) z = diskExtension u (diskReparamExtension φ z)
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
  · have he := diskReparamExtension_coe φ (⟨z, hz⟩ : Disk)
    rw [he, diskExtension_coe]
    exact diskExtension_coe (u ∘ φ) (⟨z, hz⟩ : Disk)
  · have he : diskReparamExtension φ z = (φ diskCenter : ℂ) := by
      simp only [diskReparamExtension, diskExtension, hz, ↓reduceDIte]
    rw [he, diskExtension_coe]
    simp only [diskExtension, hz, ↓reduceDIte, Function.comp_apply]

variable [finiteDimensionalE : FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q] [connectedQ : ConnectedSpace Q]

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit connectedQ in
theorem ae_mdifferentiable_loopLift (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (loopLift γ) t := by
  have hquot : LipschitzWith 1 (fun t : ℝ => (t : Surgery.Topology.Circle)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    rw [← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨C, hC, hbound⟩ := exists_pos_derivative_bound g e.map (e.smooth.of_le (by simp))
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : ENNReal.ofReal C = (Cn : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  obtain ⟨L, hL⟩ := hlip
  have hlip : LipschitzWith (Cn * L) (e.map ∘ loopLift γ) := by
    intro x y
    have hq : edist (x : Surgery.Topology.Circle) (y : Surgery.Topology.Circle) ≤
        edist x y := by
      simpa only [ENNReal.coe_one, one_mul] using hquot x y
    change edist (e.map (γ (x : Surgery.Topology.Circle)))
      (e.map (γ (y : Surgery.Topology.Circle))) ≤ _
    calc
      _ ≤ ENNReal.ofReal C * riemannianEDistOf g (γ (x : Surgery.Topology.Circle))
          (γ (y : Surgery.Topology.Circle)) :=
        edist_le_of_derivative_bound g e.map (e.smooth.of_le (by simp)) hC (fun q v => by
          rw [norm_tangentSpace_vectorSpace]
          exact hbound q v) _ _
      _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) *
          edist (x : Surgery.Topology.Circle) (y : Surgery.Topology.Circle)) :=
        mul_le_mul' le_rfl (hL _ _)
      _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) * edist x y) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hq)
      _ = _ := by rw [hCn, ENNReal.coe_mul, mul_assoc]
  have hc : Continuous (loopLift γ) := γ.continuous.comp hquot.continuous
  have ha := hlip.ae_differentiableAt (μ := volume)
  filter_upwards [ae_restrict_of_ae ha] with t ht
  have hwithin := mdifferentiableWithinAt_of_injective_derivative_comp e.map
    (e.smooth.of_le (by simp)) (loopLift γ) univ (Set.mem_univ t)
    (hc.continuousWithinAt) (e.injective_mfderiv _) ht.differentiableWithinAt
  simpa only [mdifferentiableWithinAt_univ] using hwithin

section JacobianIntegrability

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ

variable [FiniteDimensional ℝ E] [I.Boundaryless]
omit [FiniteDimensional ℝ E] in
private theorem continuous_inverseChart_metricQuad
    (g : SmoothRiemannianMetric I Q) (q : Q) :
    Continuous (fun p : (extChartAt I q).target × E =>
      g.inner ((extChartAt I q).symm p.1)
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q).target p.1 p.2)
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q).target p.1 p.2)) := by
  let T := (extChartAt I q).target
  let A : T × E → TangentBundle 𝓘(ℝ, E) E := fun p => ⟨p.1, p.2⟩
  have hA : Continuous A :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hr := (contMDiffOn_extChartAt_symm (I := I) (n := 1) q).continuousOn_tangentMapWithin
    le_rfl (isOpen_extChartAt_target (I := I) q).uniqueMDiffOn
  have hA' : Continuous (fun p : T × E =>
      (⟨A p, p.1.2⟩ : {z : TangentBundle 𝓘(ℝ, E) E | z.proj ∈ T})) :=
    hA.subtype_mk _
  exact (metricQuad_cont g).comp (hr.domRestrict.comp hA')

private theorem aemeasurable_inverseChart_metricQuad
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [OpensMeasurableSpace V] {μ : Measure V}
    (g : SmoothRiemannianMetric I Q) (q : Q)
    {U : Set V} (hU : MeasurableSet U) (F : V → E) (hF : ContinuousOn F U)
    (hFT : MapsTo F U (extChartAt I q).target) (v : V) :
    AEMeasurable (fun z =>
      g.inner ((extChartAt I q).symm (F z))
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q).target
          (F z) (fderiv ℝ F z v))
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q).target
          (F z) (fderiv ℝ F z v))) (μ.restrict U) := by
  borelize E
  let c := extChartAt I q
  let G : c.target × E → ℝ := fun p =>
    g.inner (c.symm p.1)
      (mfderivWithin 𝓘(ℝ, E) I c.symm c.target p.1 p.2)
      (mfderivWithin 𝓘(ℝ, E) I c.symm c.target p.1 p.2)
  have hG : Continuous G := continuous_inverseChart_metricQuad g q
  apply aemeasurable_restrict_of_measurable_subtype hU
  have hcoord : Continuous (fun z : U => (⟨F z, hFT z.2⟩ : c.target)) :=
    hF.domRestrict.subtype_mk _
  have hdv : Measurable (fun z : V => fderiv ℝ F z v) :=
    measurable_fderiv_apply_const ℝ F v
  have hdvU : Measurable (fun z : U => fderiv ℝ F z v) :=
    hdv.comp measurable_subtype_coe
  have hjet : Measurable (fun z : U =>
      ((⟨F z, hFT z.2⟩ : c.target), fderiv ℝ F z v)) :=
    hcoord.measurable.prodMk hdvU
  exact hG.measurable.comp hjet

private theorem aemeasurable_metricQuad_mfderiv_on_chart
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [OpensMeasurableSpace V] {μ : Measure V}
    (g : SmoothRiemannianMetric I Q) {Ω : Set V} (hΩ : IsOpen Ω)
    (u : V → Q) (hu : ContinuousOn u Ω)
    (hd : ∀ᵐ z ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, V) I u z)
    (q : Q) (v : V) :
    AEMeasurable (fun z => g.inner (u z)
      (mfderiv 𝓘(ℝ, V) I u z v) (mfderiv 𝓘(ℝ, V) I u z v))
      (μ.restrict (Ω ∩ u ⁻¹' (extChartAt I q).source)) := by
  borelize E
  let c := extChartAt I q
  let U : Set V := Ω ∩ u ⁻¹' c.source
  let F : V → E := c ∘ u
  have hU : IsOpen U := hu.isOpen_inter_preimage hΩ (isOpen_extChartAt_source q)
  have hF : ContinuousOn F U := (continuousOn_extChartAt (I := I) q).comp (hu.mono inter_subset_left)
    (fun z hz => hz.2)
  let J : V → ℝ := fun z =>
    g.inner (c.symm (F z))
      (mfderivWithin 𝓘(ℝ, E) I c.symm c.target (F z) (fderiv ℝ F z v))
      (mfderivWithin 𝓘(ℝ, E) I c.symm c.target (F z) (fderiv ℝ F z v))
  have hJ : AEMeasurable J (μ.restrict U) :=
    aemeasurable_inverseChart_metricQuad g q hU.measurableSet F hF
      (fun z hz => c.map_source hz.2) v
  apply hJ.congr
  filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),
    ae_restrict_mem hU.measurableSet] with z hdz hz
  have hzchart : u z ∈ (extChartAt I q).source := hz.2
  have hc : MDifferentiableAt I 𝓘(ℝ, E) c (u z) :=
    (contMDiffAt_extChartAt' (I := I) (n := 1)
      (by simpa only [extChartAt_source] using hzchart)).mdifferentiableAt (by simp)
  have hdF : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) F z := hc.comp z hdz
  have hsame : ∀ y ∈ U, u y = (c.symm ∘ F) y := by
    intro y hy
    exact (c.left_inv hy.2).symm
  let p : TangentBundle 𝓘(ℝ, V) V := ⟨z, v⟩
  have hcongr := tangentMapWithin_congr (I := 𝓘(ℝ, V)) (I' := I) hsame p hz
  have hchain := tangentMapWithin_comp_at (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := F) (g := c.symm) (s := U) (u := c.target) p
    ((contMDiffOn_extChartAt_symm (I := I) (n := 1) q _ (c.map_source hz.2)).mdifferentiableWithinAt (by simp))
    hdF.mdifferentiableWithinAt (fun y hy => c.map_source hy.2)
    (hU.uniqueMDiffWithinAt hz)
  have hmap := hcongr.trans hchain
  rw [tangentMapWithin_eq_tangentMap (hU.uniqueMDiffWithinAt hz) hdz,
    tangentMapWithin_eq_tangentMap (hU.uniqueMDiffWithinAt hz) hdF] at hmap
  have hvalue := congrArg (fun p : TangentBundle I Q => g.inner p.proj p.2 p.2) hmap
  simp only [p, tangentMap, tangentMapWithin, mfderiv_eq_fderiv] at hvalue
  convert! hvalue.symm using 1

private theorem aemeasurable_metricQuad_mfderiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [OpensMeasurableSpace V] {μ : Measure V}
    [CompactSpace Q] (g : SmoothRiemannianMetric I Q)
    {Ω : Set V} (hΩ : IsOpen Ω) (u : V → Q) (hu : ContinuousOn u Ω)
    (hd : ∀ᵐ z ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, V) I u z) (v : V) :
    AEMeasurable (fun z => g.inner (u z)
      (mfderiv 𝓘(ℝ, V) I u z v) (mfderiv 𝓘(ℝ, V) I u z v)) (μ.restrict Ω) := by
  classical
  obtain ⟨a, ha⟩ := (isCompact_univ : IsCompact (univ : Set Q)).elim_finite_subcover
    (fun q : Q => (extChartAt I q).source) (fun q => isOpen_extChartAt_source q)
    (fun q _ => mem_iUnion.mpr ⟨q, mem_extChartAt_source q⟩)
  have hcover : Ω = ⋃ q : a, Ω ∩ u ⁻¹' (extChartAt I (q : Q)).source := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨q, hq⟩ := mem_iUnion.mp (ha (mem_univ (u z)))
      obtain ⟨hqa, hqz⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨⟨q, hqa⟩, hz, hqz⟩
    · exact iUnion_subset fun _ => inter_subset_left
  rw [hcover]
  exact AEMeasurable.iUnion fun q : a =>
    aemeasurable_metricQuad_mfderiv_on_chart g hΩ u hu hd q v

private theorem gram_two_eq_quadratic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (v : Fin 2 → V) :
    Matrix.det (fun i j : Fin 2 => B (v i) (v j)) =
      B (v 0) (v 0) * B (v 1) (v 1) -
        ((B (v 0 + v 1) (v 0 + v 1) - B (v 0) (v 0) - B (v 1) (v 1)) / 2) ^ 2 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => B (v i) (v j))
  calc
    Matrix.det (fun i j : Fin 2 => B (v i) (v j)) =
        B (v 0) (v 0) * B (v 1) (v 1) - B (v 0) (v 1) * B (v 1) (v 0) :=
      Matrix.det_fin_two A
    _ = _ := by
      simp only [map_add, add_apply, hB (v 1) (v 0)]
      ring

private theorem aemeasurable_parametricJacobian_univ
    [CompactSpace Q] (g : SmoothRiemannianMetric I Q)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (u : ℂ → Q) (hu : ContinuousOn u Ω)
    (hd : ∀ᵐ z ∂volume.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℂ) I u z) :
    AEMeasurable (parametricJacobian g u univ) (volume.restrict Ω) := by
  have h0 := aemeasurable_metricQuad_mfderiv g hΩ u hu hd (diskBasis 0)
  have h1 := aemeasurable_metricQuad_mfderiv g hΩ u hu hd (diskBasis 1)
  have hsum := aemeasurable_metricQuad_mfderiv g hΩ u hu hd (diskBasis 0 + diskBasis 1)
  have hm := ((h0.mul h1).sub ((((hsum.sub h0).sub h1).div_const 2).pow_const 2)).sqrt
  apply hm.congr
  filter_upwards [hd] with z hz
  simp only [parametricJacobian, if_pos hz.mdifferentiableWithinAt, mfderivWithin_univ]
  dsimp only [Pi.mul_apply, Pi.sub_apply]
  let D : ℂ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℂ) I u z
  change Real.sqrt (g.inner (u z) (D (diskBasis 0)) (D (diskBasis 0)) *
      g.inner (u z) (D (diskBasis 1)) (D (diskBasis 1)) -
      ((g.inner (u z) (D (diskBasis 0 + diskBasis 1)) (D (diskBasis 0 + diskBasis 1)) -
        g.inner (u z) (D (diskBasis 0)) (D (diskBasis 0)) -
        g.inner (u z) (D (diskBasis 1)) (D (diskBasis 1))) / 2) ^ 2) =
    Real.sqrt (Matrix.det (fun i j : Fin 2 => g.inner (u z) (D (diskBasis i)) (D (diskBasis j))))
  have hgram := gram_two_eq_quadratic (g.inner (u z)) (g.symm (u z))
    (fun i => D (diskBasis i))
  rw [hgram, D.map_add]

variable [CompactSpace Q] [T2Space Q]

omit [I.Boundaryless] in
private theorem smoothLoopEmbedding_inverse_derivative_bound
    {N : ℕ} (g : SmoothRiemannianMetric I Q)
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) :
    ∃ C : ℝ, 0 < C ∧ ∀ q (v : TangentSpace I q),
      Real.sqrt (g.inner q v v) ≤
        C * ‖mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map q v‖ := by
  let F := EuclideanSpace ℝ (Fin N)
  let U := MetricUnitTangent (I := I) (M := Q) g
  let : CompactSpace U := isCompact_univ_iff.mp (metricUnit_compact g)
  have he1 : ContMDiff I 𝓘(ℝ, F) 1 e.map := e.smooth.of_le (by simp)
  have ht : Continuous (fun p : TangentBundle I Q =>
      mfderiv I 𝓘(ℝ, F) e.map p.proj p.2) :=
    continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).continuous.comp
      (he1.continuous_tangentMap le_rfl))
  have hn : Continuous (fun p : U => ‖mfderiv I 𝓘(ℝ, F) e.map p.1.proj p.1.2‖) :=
    (ht.comp continuous_subtype_val).norm
  have hne (p : U) : mfderiv I 𝓘(ℝ, F) e.map p.1.proj p.1.2 ≠ 0 := by
    intro h
    have hv : p.1.2 = 0 := e.injective_mfderiv p.1.proj (by simpa using h)
    have hunit := p.2
    rw [hv] at hunit
    simp at hunit
  have hinv : Continuous (fun p : U => ‖mfderiv I 𝓘(ℝ, F) e.map p.1.proj p.1.2‖⁻¹) :=
    hn.inv₀ fun p => norm_ne_zero_iff.mpr (hne p)
  obtain ⟨B, hB⟩ := (isCompact_range hinv).bddAbove
  let C : ℝ := max 1 B
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, fun q v => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp
  · let r := Real.sqrt (g.inner q v v)
    have hr : 0 < r := Real.sqrt_pos.mpr (g.pos q v hv)
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hr2 : r ^ 2 = g.inner q v v := Real.sq_sqrt (g.pos q v hv).le
    let w : TangentSpace I q := r⁻¹ • v
    have hw : g.inner q w w = 1 := by
      simp only [w, map_smul, smul_apply, smul_eq_mul]
      rw [← hr2]
      field_simp
    let p : U := ⟨(⟨q, w⟩ : TangentBundle I Q), hw⟩
    have hb : ‖mfderiv I 𝓘(ℝ, F) e.map q w‖⁻¹ ≤ C :=
      (hB ⟨p, rfl⟩).trans (le_max_right _ _)
    have hnpos : 0 < ‖mfderiv I 𝓘(ℝ, F) e.map q w‖ := norm_pos_iff.mpr (hne p)
    have hunit : 1 ≤ C * ‖mfderiv I 𝓘(ℝ, F) e.map q w‖ :=
      (inv_le_iff_one_le_mul₀ hnpos).mp hb
    have hvw : v = r • w := by
      simp only [w, smul_smul, mul_inv_cancel₀ hr0, one_smul]
    have heq : ‖mfderiv I 𝓘(ℝ, F) e.map q v‖ =
        r * ‖mfderiv I 𝓘(ℝ, F) e.map q w‖ := by
      conv_lhs => rw [hvw, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      r = r * 1 := (mul_one r).symm
      _ ≤ r * (C * ‖mfderiv I 𝓘(ℝ, F) e.map q w‖) :=
        mul_le_mul_of_nonneg_left hunit hr.le
      _ = C * (r * ‖mfderiv I 𝓘(ℝ, F) e.map q w‖) := by ring
      _ = C * ‖mfderiv I 𝓘(ℝ, F) e.map q v‖ := by rw [← heq]

private theorem sqrt_gram_le_product
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (v : Fin 2 → V) :
    Real.sqrt (Matrix.det (fun i j : Fin 2 => B (v i) (v j))) ≤
      Real.sqrt (B (v 0) (v 0)) * Real.sqrt (B (v 1) (v 1)) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => B (v i) (v j))
  calc
    Real.sqrt (Matrix.det (fun i j : Fin 2 => B (v i) (v j))) =
        Real.sqrt (B (v 0) (v 0) * B (v 1) (v 1) - B (v 0) (v 1) * B (v 1) (v 0)) :=
      congrArg Real.sqrt (Matrix.det_fin_two A)
    _ ≤ Real.sqrt (B (v 0) (v 0) * B (v 1) (v 1)) := by
      apply Real.sqrt_le_sqrt
      rw [hB (v 1) (v 0)]
      exact sub_le_self _ (mul_self_nonneg _)
    _ = _ := Real.sqrt_mul (hpos _) _

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace Q] [T2Space Q] in
private theorem metric_sqrt_gram_le_product (g : SmoothRiemannianMetric I Q)
    (q : Q) (v : Fin 2 → TangentSpace I q) :
    Real.sqrt (Matrix.det (fun i j : Fin 2 => g.inner q (v i) (v j))) ≤
      Real.sqrt (g.inner q (v 0) (v 0)) * Real.sqrt (g.inner q (v 1) (v 1)) := by
  apply sqrt_gram_le_product _ (g.symm q)
  intro w
  by_cases hw : w = 0
  · subst w; simp
  · exact (g.pos q w hw).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
private theorem embedded_lipschitzOn {N : ℕ}
    (g : SmoothRiemannianMetric I Q) (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (u : ℂ → Q) (s : Set ℂ)
    (hu : ∃ L : ℝ≥0, ∀ z ∈ s, ∀ w ∈ s,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ L : ℝ≥0, LipschitzOnWith L (e.map ∘ u) s := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_derivative_bound g e.map (e.smooth.of_le (by simp))
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : ENNReal.ofReal C = (Cn : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  obtain ⟨L, hL⟩ := hu
  refine ⟨Cn * L, fun z hz w hw => ?_⟩
  calc
    edist (e.map (u z)) (e.map (u w)) ≤
        ENNReal.ofReal C * riemannianEDistOf g (u z) (u w) :=
      edist_le_of_derivative_bound g e.map (e.smooth.of_le (by simp)) hC (fun q v => by
        rw [norm_tangentSpace_vectorSpace]
        exact hbound q v) _ _
    _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) * edist z w) :=
      mul_le_mul' le_rfl (hL z hz w hw)
    _ = _ := by rw [hCn, ENNReal.coe_mul, mul_assoc]

private theorem convex_restrict_interior {s : Set ℂ} (hs : Convex ℝ s) :
    volume.restrict s = volume.restrict (interior s) := by
  apply Measure.restrict_congr_set
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _ (hs.addHaar_frontier volume)
    exact fun z hz => ⟨subset_closure hz.1, hz.2⟩
  · rw [sdiff_eq_empty.mpr interior_subset, measure_empty]

omit [T2Space Q] in
private theorem aemeasurable_parametricJacobian_convex
    (g : SmoothRiemannianMetric I Q) (u : ℂ → Q) {s : Set ℂ}
    (hsc : Convex ℝ s) (hu : ContinuousOn u s)
    (hd : ∀ᵐ z ∂volume.restrict s, MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z) :
    AEMeasurable (parametricJacobian g u s) (volume.restrict s) := by
  rw [convex_restrict_interior hsc] at hd ⊢
  have hmd : ∀ᵐ z ∂volume.restrict (interior s), MDifferentiableAt 𝓘(ℝ, ℂ) I u z := by
    filter_upwards [hd, ae_restrict_mem isOpen_interior.measurableSet] with z hz hzs
    exact hz.mdifferentiableAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hzs) interior_subset)
  have hm := aemeasurable_parametricJacobian_univ g isOpen_interior u
    (hu.mono interior_subset) hmd
  apply hm.congr
  filter_upwards [hmd, ae_restrict_mem isOpen_interior.measurableSet] with z hz hzs
  have hnhds : s ∈ 𝓝 z := Filter.mem_of_superset (isOpen_interior.mem_nhds hzs) interior_subset
  have hdu : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u univ z := hz.mdifferentiableWithinAt
  have hds : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z := hz.mdifferentiableWithinAt
  simp only [parametricJacobian, if_pos hdu, if_pos hds,
    mfderivWithin_univ, mfderivWithin_of_mem_nhds hnhds]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem integrable_parametricJacobian_compact_convex
    (g : SmoothRiemannianMetric I Q) (u : ℂ → Q) {s : Set ℂ}
    (hs : IsCompact s) (hsc : Convex ℝ s) (hu : ContinuousOn u s)
    (hlip : ∃ L : ℝ≥0, ∀ z ∈ s, ∀ w ∈ s,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    IntegrableOn (parametricJacobian g u s) s := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨C, hC, hbound⟩ := smoothLoopEmbedding_inverse_derivative_bound g e
  obtain ⟨L, hL⟩ := embedded_lipschitzOn g e u s hlip
  have hd : ∀ᵐ z ∂volume.restrict s, MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z := by
    filter_upwards [hL.ae_differentiableWithinAt hs.isClosed.measurableSet,
      ae_restrict_mem hs.isClosed.measurableSet] with z hz hzs
    exact mdifferentiableWithinAt_of_injective_derivative_comp e.map
      (e.smooth.of_le (by simp)) u s hzs (hu z hzs) (e.injective_mfderiv _) hz
  let M : ℝ := C * (L : ℝ)
  have hM : 0 ≤ M := mul_nonneg hC.le L.coe_nonneg
  have hi : IntegrableOn (fun _ : ℂ => M ^ 2) s :=
    integrableOn_const (hs := hs.measure_lt_top.ne)
  apply hi.mono_nonneg (aemeasurable_parametricJacobian_convex g u hsc hu hd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => parametricJacobian_nonneg g _ _ z)
  rw [convex_restrict_interior hsc] at hd ⊢
  filter_upwards [hd, ae_restrict_mem isOpen_interior.measurableSet] with z hdz hzs
  have hnhds : s ∈ 𝓝 z := Filter.mem_of_superset (isOpen_interior.mem_nhds hzs) interior_subset
  have hdA := hdz.mdifferentiableAt hnhds
  let V : ℂ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℂ) I u z
  have hchain : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (u z)).comp V =
      fderiv ℝ (e.map ∘ u) z := by
    rw [← mfderiv_eq_fderiv]
    exact (mfderiv_comp z ((e.smooth.mdifferentiable (by simp)) _) hdA).symm
  have hnorm : ‖fderiv ℝ (e.map ∘ u) z‖ ≤ L := norm_fderiv_le_of_lipschitzOn ℝ hnhds hL
  have hb (i : Fin 2) : Real.sqrt (g.inner (u z) (V (diskBasis i)) (V (diskBasis i))) ≤ M := by
    have h := hbound (u z) (V (diskBasis i))
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have heval := congrArg (fun A : ℂ →L[ℝ] EuclideanSpace ℝ (Fin N) => A (diskBasis i)) hchain
    rw [show mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (u z) (V (diskBasis i)) =
      fderiv ℝ (e.map ∘ u) z (diskBasis i) from heval]
    have hbi : ‖diskBasis i‖ = 1 := by fin_cases i <;> simp [diskBasis]
    calc
      _ ≤ ‖fderiv ℝ (e.map ∘ u) z‖ * ‖diskBasis i‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) := by simpa only [hbi, mul_one] using hnorm
  unfold parametricJacobian
  rw [if_pos hdz, mfderivWithin_of_mem_nhds hnhds]
  change Real.sqrt (Matrix.det (fun i j : Fin 2 => g.inner (u z)
    (V (diskBasis i)) (V (diskBasis j)))) ≤ M ^ 2
  calc
    _ ≤ Real.sqrt (g.inner (u z) (V (diskBasis 0)) (V (diskBasis 0))) *
        Real.sqrt (g.inner (u z) (V (diskBasis 1)) (V (diskBasis 1))) :=
      metric_sqrt_gram_le_product g _ (fun i => V (diskBasis i))
    _ ≤ M * M := mul_le_mul (hb 0) (hb 1) (Real.sqrt_nonneg _) hM
    _ = M ^ 2 := (pow_two M).symm

omit [CompactSpace Q] [T2Space Q] in
private theorem annulusExtension_continuousOn (u : C(Annulus, Q)) :
    ContinuousOn (annulusExtension u) annulusRectangle := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (u.continuous.comp annulusParameter_lipschitz.continuous).congr
    (fun z => (annulusExtension_agrees u z.2).symm)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace Q] [T2Space Q] in
private theorem annulusExtension_metric_lipschitz (g : SmoothRiemannianMetric I Q)
    (u : LipschitzAnnulus g) :
    ∃ L : ℝ≥0, ∀ z ∈ annulusRectangle, ∀ w ∈ annulusRectangle,
      riemannianEDistOf g (annulusExtension u.map z) (annulusExtension u.map w) ≤
        (L : ℝ≥0∞) * edist z w := by
  obtain ⟨L, hL⟩ := u.isLipschitz
  refine ⟨L, fun z hz w hw => ?_⟩
  rw [annulusExtension_agrees u.map hz, annulusExtension_agrees u.map hw]
  have h := hL (annulusParameter ⟨z, hz⟩) (annulusParameter ⟨w, hw⟩)
  apply h.trans
  apply mul_le_mul' le_rfl
  have hq := annulusParameter_lipschitz (⟨z, hz⟩ : annulusRectangle) ⟨w, hw⟩
  simp only [ENNReal.coe_one, one_mul] at hq
  convert! hq using 1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
private theorem embedded_loop_lipschitz {N : ℕ}
    (g : SmoothRiemannianMetric I Q) (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    ∃ L : ℝ≥0, LipschitzWith L (e.map ∘ loopLift γ) := by
  have hquot : LipschitzWith 1 (fun t : ℝ => (t : Surgery.Topology.Circle)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    rw [← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  obtain ⟨C, hC, hbound⟩ := exists_pos_derivative_bound g e.map (e.smooth.of_le (by simp))
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : ENNReal.ofReal C = (Cn : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  obtain ⟨L, hL⟩ := hlip
  have hlip : LipschitzWith (Cn * L) (e.map ∘ loopLift γ) := by
    intro x y
    have hq : edist (x : Surgery.Topology.Circle) (y : Surgery.Topology.Circle) ≤
        edist x y := by
      simpa only [ENNReal.coe_one, one_mul] using hquot x y
    change edist (e.map (γ (x : Surgery.Topology.Circle)))
      (e.map (γ (y : Surgery.Topology.Circle))) ≤ _
    calc
      _ ≤ ENNReal.ofReal C * riemannianEDistOf g (γ (x : Surgery.Topology.Circle))
          (γ (y : Surgery.Topology.Circle)) :=
        edist_le_of_derivative_bound g e.map (e.smooth.of_le (by simp)) hC (fun q v => by
          rw [norm_tangentSpace_vectorSpace]
          exact hbound q v) _ _
      _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) *
          edist (x : Surgery.Topology.Circle) (y : Surgery.Topology.Circle)) :=
        mul_le_mul' le_rfl (hL _ _)
      _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) * edist x y) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hq)
      _ = _ := by rw [hCn, ENNReal.coe_mul, mul_assoc]
  exact ⟨Cn * L, hlip⟩

private theorem aemeasurable_loopSpeed_actual (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    AEMeasurable (fun t : ℝ => Real.sqrt (g.inner (loopLift γ t)
      (loopVelocity (I := I) γ t) (loopVelocity (I := I) γ t)))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hc : Continuous (loopLift γ) := γ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hd := ae_mdifferentiable_loopLift g γ hlip
  have hμ : (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) =
      volume.restrict (Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[volume] Icc 0 1).symm
  rw [hμ] at hd ⊢
  have hm := aemeasurable_metricQuad_mfderiv g isOpen_Ioo (loopLift γ) hc.continuousOn hd (1 : ℝ)
  simpa only [loopVelocity] using hm.sqrt

end JacobianIntegrability

omit connectedQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_loopSpeed (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    IntegrableOn (fun t : ℝ => Real.sqrt (g.inner (loopLift γ t)
      (loopVelocity (I := I) γ t) (loopVelocity (I := I) γ t))) (Icc (0 : ℝ) 1) := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨C, hC, hbound⟩ := smoothLoopEmbedding_inverse_derivative_bound g e
  obtain ⟨L, hL⟩ := embedded_loop_lipschitz g e γ hlip
  have hi : IntegrableOn (fun _ : ℝ => C * (L : ℝ)) (Icc (0 : ℝ) 1) :=
    integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
  apply hi.mono_nonneg (aemeasurable_loopSpeed_actual g γ hlip).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
  filter_upwards [ae_mdifferentiable_loopLift g γ hlip] with t ht
  let V : ℝ →L[ℝ] TangentSpace I (loopLift γ t) := mfderiv 𝓘(ℝ, ℝ) I (loopLift γ) t
  have hchain : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (loopLift γ t)).comp V =
      fderiv ℝ (e.map ∘ loopLift γ) t := by
    rw [← mfderiv_eq_fderiv]
    exact (mfderiv_comp t ((e.smooth.mdifferentiable (by simp)) _) ht).symm
  have hnorm : ‖fderiv ℝ (e.map ∘ loopLift γ) t‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hL
  change Real.sqrt (g.inner (loopLift γ t) (V 1) (V 1)) ≤ C * (L : ℝ)
  have h := hbound (loopLift γ t) (V 1)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have heval := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin N) => A 1) hchain
  rw [show mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (loopLift γ t) (V 1) =
    fderiv ℝ (e.map ∘ loopLift γ) t 1 from heval]
  calc
    _ ≤ ‖fderiv ℝ (e.map ∘ loopLift γ) t‖ * ‖(1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L : ℝ) := by simpa only [norm_one, mul_one] using hnorm

omit connectedQ in
theorem loopLength_eq_riemannianCurveLength (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    ENNReal.ofReal (loopLength g γ) =
      Surgery.Topology.riemannianCurveLength g (loopLift γ) 0 1 := by
  sorry

omit connectedQ in
theorem riemannianCurveLength_loop_ne_top (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hlip : IsLipschitzLoop g γ) :
    Surgery.Topology.riemannianCurveLength g (loopLift γ) 0 1 ≠ (∞ : ℝ≥0∞) := by
  rw [← loopLength_eq_riemannianCurveLength g γ hlip]
  exact ENNReal.ofReal_ne_top

omit connectedQ in
theorem RegularLoop.length_eq_riemannianCurveLength (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) :
    ENNReal.ofReal (loopLength g γ.toContinuousLoop) =
      Surgery.Topology.riemannianCurveLength g (loopLift γ.toContinuousLoop) 0 1 :=
  loopLength_eq_riemannianCurveLength g γ.toContinuousLoop (γ.isLipschitz g)

omit boundarylessI connectedQ in
theorem isLipschitzLoop_metric_iff (g h : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) : IsLipschitzLoop g γ ↔ IsLipschitzLoop h γ := by
  have htransfer (g h : SmoothRiemannianMetric I Q)
      (hlip : IsLipschitzLoop g γ) : IsLipschitzLoop h γ := by
    obtain ⟨c, hc, hbound⟩ := metric_lower_bound_of_compact g h
    obtain ⟨L, hL⟩ := hlip
    have hquad : ∀ q (v : TangentSpace I q),
        h.inner q v v ≤ c⁻¹ * g.inner q v v :=
      fun q v => (le_inv_mul_iff₀ hc).mpr (hbound q v)
    refine ⟨Real.toNNReal (Real.sqrt c⁻¹) * L, fun x y => ?_⟩
    calc
      riemannianEDistOf h (γ x) (γ y) ≤
          ENNReal.ofReal (Real.sqrt c⁻¹) * riemannianEDistOf g (γ x) (γ y) :=
        edistOf_le_of_quad g h (inv_pos.mpr hc) hquad _ _
      _ ≤ ENNReal.ofReal (Real.sqrt c⁻¹) * ((L : ℝ≥0∞) * edist x y) :=
        mul_le_mul' le_rfl (hL x y)
      _ = ((Real.toNNReal (Real.sqrt c⁻¹) * L : ℝ≥0) : ℝ≥0∞) * edist x y := by
        simp only [ENNReal.coe_mul, ENNReal.ofReal, mul_assoc]
  exact ⟨htransfer g h, htransfer h g⟩

omit boundarylessI connectedQ in
theorem diskCompetitor_maps_metric_iff (g h : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (u : C(Disk, Q)) :
    (∃ v : DiskCompetitor g γ, v.1.map = u) ↔
      ∃ v : DiskCompetitor h γ, v.1.map = u := by
  have htransfer (g h : SmoothRiemannianMetric I Q)
      (v : DiskCompetitor g γ) : ∃ w : DiskCompetitor h γ, w.1.map = v.1.map := by
    obtain ⟨c, hc, hbound⟩ := metric_lower_bound_of_compact g h
    exact ⟨⟨v.1.changeMetric g h (inv_pos.mpr hc)
      (fun q w => (le_inv_mul_iff₀ hc).mpr (hbound q w)), v.2⟩, rfl⟩
  constructor
  · rintro ⟨v, rfl⟩
    exact htransfer g h v
  · rintro ⟨v, rfl⟩
    exact htransfer h g v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit connectedQ in
theorem LipschitzDisk.ae_mdifferentiable (g : SmoothRiemannianMetric I Q)
    (u : LipschitzDisk g) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
      MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨C, hC, hbound⟩ := exists_pos_derivative_bound g e.map (e.smooth.of_le (by simp))
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : ENNReal.ofReal C = (Cn : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  obtain ⟨L, hL⟩ := u.isLipschitz
  let φ : ℂ → EuclideanSpace ℝ (Fin N) := e.map ∘ diskExtension u.map
  have hlip : LipschitzOnWith (Cn * L) φ (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz w hw
    have hez : diskExtension u.map z = u.map ⟨z, hz⟩ := diskExtension_coe _ ⟨z, hz⟩
    have hew : diskExtension u.map w = u.map ⟨w, hw⟩ := diskExtension_coe _ ⟨w, hw⟩
    change edist (e.map (diskExtension u.map z)) (e.map (diskExtension u.map w)) ≤ _
    rw [hez, hew]
    calc
      _ ≤ ENNReal.ofReal C * riemannianEDistOf g (u.map ⟨z, hz⟩) (u.map ⟨w, hw⟩) :=
        edist_le_of_derivative_bound g e.map (e.smooth.of_le (by simp)) hC (fun q v => by
          rw [norm_tangentSpace_vectorSpace]
          exact hbound q v) _ _
      _ ≤ ENNReal.ofReal C * ((L : ℝ≥0∞) * edist (⟨z, hz⟩ : Disk) ⟨w, hw⟩) :=
        mul_le_mul' le_rfl (hL _ _)
      _ = _ := by rw [hCn, ENNReal.coe_mul, mul_assoc]; rfl
  have hcont : ContinuousOn (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact u.map.continuous.congr (fun z => (diskExtension_coe u.map z).symm)
  filter_upwards [hlip.ae_differentiableWithinAt measurableSet_closedBall,
    ae_restrict_mem measurableSet_closedBall] with z hz hzs
  exact mdifferentiableWithinAt_of_injective_derivative_comp e.map
    (e.smooth.of_le (by simp)) (diskExtension u.map) _ hzs (hcont z hzs)
    (e.injective_mfderiv _) hz

omit connectedQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem LipschitzDisk.integrable_jacobian (g : SmoothRiemannianMetric I Q)
    (u : LipschitzDisk g) :
    IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) := by
  change IntegrableOn (parametricJacobian g (diskExtension u.map)
    (Metric.closedBall (0 : ℂ) 1)) (Metric.closedBall (0 : ℂ) 1)
  refine integrable_parametricJacobian_compact_convex g (diskExtension u.map)
    (isCompact_closedBall (0 : ℂ) 1) (convex_closedBall (0 : ℂ) 1) ?_ ?_
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact u.map.continuous.congr (fun z => (diskExtension_coe u.map z).symm)
  · obtain ⟨L, hL⟩ := u.isLipschitz
    refine ⟨L, fun z hz w hw => ?_⟩
    have hez : diskExtension u.map z = u.map ⟨z, hz⟩ := diskExtension_coe _ ⟨z, hz⟩
    have hew : diskExtension u.map w = u.map ⟨w, hw⟩ := diskExtension_coe _ ⟨w, hw⟩
    rw [hez, hew]
    convert! hL (⟨z, hz⟩ : Disk) ⟨w, hw⟩ using 1

omit connectedQ in
theorem LipschitzAnnulus.integrable_jacobian (g : SmoothRiemannianMetric I Q)
    (u : LipschitzAnnulus g) :
    IntegrableOn (parametricJacobian g (annulusExtension u.map) annulusRectangle)
      annulusRectangle := by
  exact integrable_parametricJacobian_compact_convex g (annulusExtension u.map)
    annulusRectangle_compact annulusRectangle_convex (annulusExtension_continuousOn u.map)
    (annulusExtension_metric_lipschitz g u)

omit connectedQ in
theorem diskArea_finite_decomposition (g : SmoothRiemannianMetric I Q)
    (u : LipschitzDisk g) {ι : Type*} [Fintype ι] (s : ι → Set ℂ)
    (hs : ∀ i, MeasurableSet (s i))
    (hcover : Metric.closedBall (0 : ℂ) 1 = ⋃ i, s i)
    (hdisj : ∀ i j, i ≠ j → volume (s i ∩ s j) = 0) :
    diskArea g u.map = ∑ i, ∫ z in s i, diskJacobian g u.map z := by
  have hi : IntegrableOn (diskJacobian g u.map) (⋃ i, s i) := by
    rw [← hcover]
    exact u.integrable_jacobian g
  unfold diskArea
  rw [hcover, integral_iUnion_ae (fun i => (hs i).nullMeasurableSet)
    (fun i j hij => hdisj i j hij) hi]
  exact tsum_fintype _

omit connectedQ in
theorem annulusArea_finite_decomposition (g : SmoothRiemannianMetric I Q)
    (u : LipschitzAnnulus g) {ι : Type*} [Fintype ι] (s : ι → Set ℂ)
    (hs : ∀ i, MeasurableSet (s i))
    (hcover : annulusRectangle = ⋃ i, s i)
    (hdisj : ∀ i j, i ≠ j → volume (s i ∩ s j) = 0) :
    annulusArea g u.map = ∑ i, ∫ z in s i,
      parametricJacobian g (annulusExtension u.map) annulusRectangle z := by
  have hi : IntegrableOn
      (parametricJacobian g (annulusExtension u.map) annulusRectangle) (⋃ i, s i) := by
    rw [← hcover]
    exact u.integrable_jacobian g
  have h := integral_iUnion_ae (fun i => (hs i).nullMeasurableSet)
    (fun i j hij => hdisj i j hij) hi
  rw [← hcover] at h
  exact h.trans (tsum_fintype _)


def loopUniformDistance (g : SmoothRiemannianMetric I Q)
    (γ₀ γ₁ : ContinuousFreeLoop Q) : ℝ :=
  sSup (Set.range (fun θ => (riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toReal))

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem loopUniformDistance_comm (g : SmoothRiemannianMetric I Q)
    (γ₀ γ₁ : ContinuousFreeLoop Q) :
    loopUniformDistance g γ₀ γ₁ = loopUniformDistance g γ₁ γ₀ := by
  have hd (x y : Q) : riemannianEDistOf g x y = riemannianEDistOf g y x := by
    let : Bundle.RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist I x y = Manifold.riemannianEDist I y x
    exact Manifold.riemannianEDist_comm (I := I) (x := x) (y := y)
  exact congrArg sSup (congrArg Set.range (funext fun θ => congrArg ENNReal.toReal (hd _ _)))

omit connectedQ in
theorem disk_annulus_gluing (g : SmoothRiemannianMetric I Q)
    (γ₀ γ₁ : ContinuousFreeLoop Q) (u : DiskCompetitor g γ₀) (A : LipschitzAnnulus g)
    (htrace₀ : ∀ θ, A.map (⟨0, by simp⟩, θ) = γ₀ θ)
    (htrace₁ : ∀ θ, A.map (⟨1, by simp⟩, θ) = γ₁ θ) :
    ∃ v : DiskCompetitor g γ₁,
      diskArea g v.1.map = diskArea g u.1.map + annulusArea g A.map := by
  sorry

theorem rfs_nearby_loop_annulus (g : SmoothRiemannianMetric I Q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : ContinuousFreeLoop Q),
        IsLipschitzLoop g γ₀ → IsLipschitzLoop g γ₁ →
        loopUniformDistance g γ₀ γ₁ < ρ →
        ∃ A : LipschitzAnnulus g,
          (∀ θ, A.map (⟨0, by simp⟩, θ) = γ₀ θ) ∧
          (∀ θ, A.map (⟨1, by simp⟩, θ) = γ₁ θ) ∧
          (∀ θ (s t : Icc (0 : ℝ) 1),
            riemannianEDistOf g (A.map (s, θ)) (A.map (t, θ)) =
              ENNReal.ofReal |(s : ℝ) - t| * riemannianEDistOf g (γ₀ θ) (γ₁ θ)) ∧
          annulusArea g A.map ≤ C * loopUniformDistance g γ₀ γ₁ *
            (loopLength g γ₀ + loopLength g γ₁) ∧
          ∀ u : DiskCompetitor g γ₀, ∃ v : DiskCompetitor g γ₁,
            diskArea g v.1.map = diskArea g u.1.map + annulusArea g A.map := by
  sorry

omit connectedQ in
theorem rfs_disk_competitor_exists (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    Nonempty (DiskCompetitor g γ) := by
  sorry

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem LipschitzDisk.isLipschitz_trace
    (g : SmoothRiemannianMetric I Q)
    (u : LipschitzDisk g) (γ : ContinuousFreeLoop Q)
    (htrace : ∀ θ, u.map (diskBoundary θ) = γ θ) : IsLipschitzLoop g γ := by
  obtain ⟨L, hL⟩ := u.isLipschitz
  let K : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩
  refine ⟨L * K, fun x y => ?_⟩
  rw [← htrace x, ← htrace y]
  calc
    riemannianEDistOf g (u.map (diskBoundary x)) (u.map (diskBoundary y)) ≤
        (L : ℝ≥0∞) * edist (diskBoundary x) (diskBoundary y) := hL _ _
    _ ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * edist x y) :=
      mul_le_mul' le_rfl (diskBoundary_lipschitz x y)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

omit connectedQ in
private theorem diskArea_metric_upper (g h : SmoothRiemannianMetric I Q)
    {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ q (v : TangentSpace I q), h.inner q v v ≤ c * g.inner q v v)
    (u : LipschitzDisk g) : diskArea h u.map ≤ c * diskArea g u.map := by
  let uh := u.changeMetric g h hc hmetric
  have hih : IntegrableOn (diskJacobian h u.map) (Metric.closedBall (0 : ℂ) 1) :=
    uh.integrable_jacobian h
  calc
    diskArea h u.map ≤ ∫ z in Metric.closedBall (0 : ℂ) 1, c * diskJacobian g u.map z := by
      exact integral_mono hih ((u.integrable_jacobian g).const_mul c)
        (fun z => parametricJacobian_metric_upper g h hc.le hmetric _ _ z)
    _ = c * diskArea g u.map := integral_const_mul _ _

omit connectedQ in
theorem diskArea_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (u : LipschitzDisk g) :
    a ^ 2 * diskArea g u.map ≤ diskArea h u.map ∧
      diskArea h u.map ≤ b ^ 2 * diskArea g u.map := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos (ha.trans_le hab)
  have hupper := diskArea_metric_upper g h hb2 (fun q v => (hmetric q v).2) u
  let uh := u.changeMetric g h hb2 (fun q v => (hmetric q v).2)
  have hreverse : ∀ q (v : TangentSpace I q),
      g.inner q v v ≤ (a ^ 2)⁻¹ * h.inner q v v := by
    intro q v
    have hr : g.inner q v v ≤ h.inner q v v / a ^ 2 :=
      (le_div_iff₀ ha2).mpr (by simpa only [mul_comm] using (hmetric q v).1)
    simpa only [div_eq_mul_inv, mul_comm] using hr
  have hlow := diskArea_metric_upper h g (inv_pos.mpr ha2) hreverse uh
  refine ⟨?_, hupper⟩
  have hmul := mul_le_mul_of_nonneg_left hlow ha2.le
  change a ^ 2 * diskArea g u.map ≤ a ^ 2 * ((a ^ 2)⁻¹ * diskArea h u.map) at hmul
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha2), one_mul] using hmul

omit finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem diskArea_scale (g : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (u : LipschitzDisk g) :
    diskArea (scaleMetric c hc g) u.map = c * diskArea g u.map := by
  have hscale (A : Matrix (Fin 2) (Fin 2) ℝ) :
      Real.sqrt (Matrix.det (fun i j => c * A i j)) = c * Real.sqrt (Matrix.det A) := by
    change Real.sqrt (Matrix.det (c • A)) = c * Real.sqrt (Matrix.det A)
    rw [Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hJ : ∀ z, diskJacobian (scaleMetric c hc g) u.map z =
      c * diskJacobian g u.map z := by
    intro z
    unfold diskJacobian parametricJacobian
    split_ifs
    · simpa only [scaleMetric_inner] using hscale
        (fun i j : Fin 2 => g.inner (diskExtension u.map z)
          (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
            (Metric.closedBall (0 : ℂ) 1) z (diskBasis i))
          (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
            (Metric.closedBall (0 : ℂ) 1) z (diskBasis j)))
    · simp
  unfold diskArea
  simp_rw [hJ]
  exact integral_const_mul _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem diskArea_reparametrize (g : SmoothRiemannianMetric I Q) (u : LipschitzDisk g)
    (φ : Disk ≃ₜ Disk) (hφ : ∃ L : ℝ≥0, LipschitzWith L φ)
    (hφinv : ∃ L : ℝ≥0, LipschitzWith L φ.symm) :
    diskArea g (u.map ∘ φ) = diskArea g u.map := by
  let _ := connectedQ
  obtain ⟨L, hL⟩ := hφ
  let f := diskReparamExtension φ
  let s := Metric.closedBall (0 : ℂ) 1
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hf : LipschitzOnWith L f s := diskReparamExtension_lipschitz φ hL
  have hdu := diskReparamExtension_ae φ hφinv (u.ae_mdifferentiable g)
  have hdf := hf.ae_differentiableWithinAt (μ := volume) hs
  have hj : ∀ᵐ z ∂volume.restrict s,
      diskJacobian g (u.map ∘ φ) z =
        |(fderivWithin ℝ f s z).det| * diskJacobian g u.map (f z) := by
    filter_upwards [hdu, hdf, ae_restrict_mem hs] with z hzU hzF hz
    change parametricJacobian g (diskExtension (u.map ∘ φ)) s z = _
    rw [diskExtension_reparam]
    exact parametricJacobian_comp_within g (diskExtension u.map) f hzU hzF
      (diskReparamExtension_mapsTo φ) (disk_uniqueDiffWithinAt (⟨z, hz⟩ : Disk))
  have hcov := complex_lipschitz_integral_image hs hf
    (diskReparamExtension_injOn φ) (diskJacobian g u.map)
  rw [diskReparamExtension_image φ] at hcov
  exact (integral_congr_ae hj).trans hcov.symm

section Composition

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]
  [T2Space P] [CompactSpace P]

theorem diskArea_lipschitz_comp (g : SmoothRiemannianMetric I Q)
    (h : SmoothRiemannianMetric J P) (f : C(Q, P)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y) (u : LipschitzDisk g) :
    diskArea h (f ∘ u.map) ≤ (L : ℝ) ^ 2 * diskArea g u.map := by
  sorry

end Composition

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
