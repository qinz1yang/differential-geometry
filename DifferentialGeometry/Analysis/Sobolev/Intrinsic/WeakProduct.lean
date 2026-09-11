import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp.Basic
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.GradientProduct
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [T2Space M]


theorem HasWeakRiemannianGradLp.congr_fun_ae
    {g : SmoothRiemannianMetric I M} {u v : M → ℝ} {G : M → E}
    (hG : HasWeakRiemannianGradLp g u G)
    (huv : u =ᵐ[riemannianVolumeMeasure I M g] v) :
    HasWeakRiemannianGradLp g v G := by
  refine ⟨hG.1, fun X hX => ?_⟩
  rw [hG.pairing_eq X hX]
  congr 1
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

omit [T2Space M] in
private lemma integrable_mul_continuous {μ : Measure M} {u f : M → ℝ}
    (hu : Integrable u μ) (hf : Continuous f) :
    Integrable (fun x => u x * f x) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact hu.mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun x => hC x (mem_univ x))


theorem HasWeakRiemannianGradLp.pairing_integrable
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : M → E}
    (hG : HasWeakRiemannianGradLp g u G)
    (hGn : Integrable (fun x => Real.sqrt (g.inner x (G x) (G x)))
      (riemannianVolumeMeasure I M g))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Integrable (fun x => g.inner x (G x) (X x))
      (riemannianVolumeMeasure I M g) := by
  have hX : Continuous (fun x => Real.sqrt (g.inner x (X x) (X x))) :=
    Real.continuous_sqrt.comp
      (TangentBundle.continuous_g_inner_of_smooth_sections g X X)
  refine (integrable_mul_continuous hGn hX).mono' (hG.pairing_aestronglyMeasurable X) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt g x (G x) (X x)


theorem HasWeakRiemannianGradLp.pairing_memLp
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : M → E} {p : ℝ≥0∞}
    (hG : HasWeakRiemannianGradLp g u G)
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    MemLp (fun x => g.inner x (G x) (X x)) p (riemannianVolumeMeasure I M g) := by
  have hX : Continuous (fun x => Real.sqrt (g.inner x (X x) (X x))) :=
    Real.continuous_sqrt.comp
      (TangentBundle.continuous_g_inner_of_smooth_sections g X X)
  have hdom : MemLp (fun x => Real.sqrt (g.inner x (X x) (X x)) *
      Real.sqrt (g.inner x (G x) (G x))) p (riemannianVolumeMeasure I M g) :=
    hGn.mul' (hX.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact
      (riemannianVolumeMeasure I M g))
  refine hdom.mono (hG.pairing_aestronglyMeasurable X) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  simpa only [mul_comm] using
    EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt g x (G x) (X x)


theorem HasWeakRiemannianGradLp.smooth_mul [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : Integrable u (riemannianVolumeMeasure I M g))
    (hGn : Integrable (fun x => Real.sqrt (g.inner x (G x) (G x)))
      (riemannianVolumeMeasure I M g))
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    HasWeakRiemannianGradLp g (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradFun (I := I) g φ x) := by
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG g ⟨φ, hφ⟩
  have hpair (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
      g.inner x (φ x • G x + u x • gradFun (I := I) g φ x) (X x) =
        φ x * g.inner x (G x) (X x) + u x * g.inner x (Z x) (X x) := by
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    rfl
  have hZ (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      Continuous (fun x => g.inner x (Z x) (X x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections g Z X
  refine ⟨?_, ?_⟩
  · intro X
    have hm := (hφ.continuous.aestronglyMeasurable.mul
        (hG.pairing_aestronglyMeasurable X)).add
      (hu.aestronglyMeasurable.mul (hZ X).aestronglyMeasurable)
    exact hm.congr (Eventually.of_forall fun x => (hpair X x).symm)
  · intro X _hX
    let Y := smoothSmul φ hφ X
    have hY : HasCompactSupport (fun x : M => (Y x : E)) :=
      (isClosed_tsupport _).isCompact
    have hweak := hG.pairing_eq Y hY
    have hleft : Integrable (fun x => φ x * g.inner x (G x) (X x))
        (riemannianVolumeMeasure I M g) := by
      simpa only [mul_comm] using
        integrable_mul_continuous (hG.pairing_integrable hGn X) hφ.continuous
    have hright : Integrable (fun x => u x * g.inner x (Z x) (X x))
        (riemannianVolumeMeasure I M g) :=
      integrable_mul_continuous hu (hZ X)
    have hdiv : Integrable (fun x => φ x * u x * divergenceG g X x)
        (riemannianVolumeMeasure I M g) := by
      simpa only [Pi.mul_apply, mul_left_comm, mul_assoc] using
        integrable_mul_continuous hu
          (hφ.continuous.mul (divergence_g_contMDiff g X).continuous)
    have hact (x : M) : tangentSectionAction X φ x = g.inner x (Z x) (X x) := by
      rw [g.symm x (Z x) (X x)]
      exact tangentSectionAction_eq_inner_grad_g g ⟨φ, hφ⟩ X x
    have hleft_eq : (fun x => g.inner x (G x) (Y x)) =
        (fun x => φ x * g.inner x (G x) (X x)) := by
      funext x
      change g.inner x (G x) (φ x • X x) = _
      rw [map_smul, smul_eq_mul]
    have hright_eq : (fun x => u x * divergenceG g Y x) =
        (fun x => φ x * u x * divergenceG g X x +
          u x * g.inner x (Z x) (X x)) := by
      funext x
      rw [show divergenceG g Y x =
          φ x * divergenceG g X x + tangentSectionAction X φ x from
        divergence_g_smoothSmul g φ hφ X x, hact x]
      ring
    rw [hleft_eq, hright_eq, integral_add hdiv hright] at hweak
    rw [integral_congr_ae (Eventually.of_forall (hpair X)), integral_add hleft hright]
    linarith


theorem HasWeakRiemannianGradLp.smooth_mul_witness [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u φ : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g))
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    MemLp (fun x => φ x * u x) p (riemannianVolumeMeasure I M g) ∧
      HasWeakRiemannianGradLp g (fun x => φ x * u x)
        (fun x => φ x • G x + u x • gradFun (I := I) g φ x) ∧
      MemLp (fun x => Real.sqrt
        (g.inner x (φ x • G x + u x • gradFun (I := I) g φ x)
          (φ x • G x + u x • gradFun (I := I) g φ x))) p
        (riemannianVolumeMeasure I M g) := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG g ⟨φ, hφ⟩
  have hφtop : MemLp φ ⊤ μ :=
    hφ.continuous.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact μ
  refine ⟨hu.mul' hφtop, ?_, ?_⟩
  · exact hG.smooth_mul (memLp_one_iff_integrable.mp (hu.mono_exponent hp))
      (memLp_one_iff_integrable.mp (hGn.mono_exponent hp)) hφ
  · change MemLp (fun x => Real.sqrt
      (g.inner x (φ x • G x + u x • Z x) (φ x • G x + u x • Z x))) p μ
    have hZ : Continuous (fun x => Real.sqrt (g.inner x (Z x) (Z x))) :=
      Real.continuous_sqrt.comp
        (TangentBundle.continuous_g_inner_of_smooth_sections g Z Z)
    have hZtop : MemLp (fun x => Real.sqrt (g.inner x (Z x) (Z x))) ⊤ μ :=
      hZ.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact μ
    have hGself : AEStronglyMeasurable (fun x => g.inner x (G x) (G x)) μ := by
      have hmeas := hGn.aestronglyMeasurable.pow 2
      refine hmeas.congr (Eventually.of_forall fun x => ?_)
      apply Real.sq_sqrt
      by_cases hx : G x = 0
      · simpa only [hx, map_zero] using (le_rfl : (0 : ℝ) ≤ 0)
      · exact (g.pos x (G x) hx).le
    have hZself : AEStronglyMeasurable (fun x => g.inner x (Z x) (Z x)) μ :=
      (TangentBundle.continuous_g_inner_of_smooth_sections g Z Z).aestronglyMeasurable
    have hcross : AEStronglyMeasurable (fun x => g.inner x (G x) (Z x)) μ :=
      hG.pairing_aestronglyMeasurable Z
    have hφmeas : AEStronglyMeasurable φ μ := hφ.continuous.aestronglyMeasurable
    have humeas : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
    have hself : AEStronglyMeasurable (fun x =>
        g.inner x (φ x • (G x : TangentSpace I x) + u x • Z x) (φ x • (G x : TangentSpace I x) + u x • Z x)) μ := by
      have hm := (((hφmeas.pow 2).mul hGself).add
          (((hφmeas.const_mul 2).mul humeas).mul hcross)).add
        ((humeas.pow 2).mul hZself)
      refine hm.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
      rw [g.symm x (Z x) (G x)]
      ring
    have hnorm : AEStronglyMeasurable (fun x =>
        Real.sqrt (g.inner x (φ x • (G x : TangentSpace I x) + u x • Z x)
          (φ x • (G x : TangentSpace I x) + u x • Z x))) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hself
    have hdom : MemLp (fun x =>
        ‖φ x‖ * Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (Z x) (Z x)) * ‖u x‖) p μ :=
      (hGn.mul' hφtop.norm).add (hu.norm.mul' hZtop)
    refine hdom.mono hnorm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg
      (add_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))]
    have hb := Geometry.Riemannian.sqrt_inner_add_le g x (φ x • (G x : TangentSpace I x)) (u x • Z x)
    rw [Geometry.Riemannian.sqrt_inner_smul, Geometry.Riemannian.sqrt_inner_smul] at hb
    simpa only [Real.norm_eq_abs, mul_comm] using hb


theorem MemW1pIntrinsicLp.smooth_mul [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u φ : M → ℝ} (hu : MemW1pIntrinsicLp g p u)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    MemW1pIntrinsicLp g p (fun x => φ x * u x) := by
  obtain ⟨hu, G₀, hG₀, hGn₀⟩ := hu
  let G : ∀ x : M, TangentSpace I x := fun x => G₀ x
  have hG : HasWeakRiemannianGradLp g u G := hG₀
  obtain ⟨hprod, hweak, hnorm⟩ := hG.smooth_mul_witness hp hu hGn₀ hφ
  exact ⟨hprod, _, hweak, hnorm⟩

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
