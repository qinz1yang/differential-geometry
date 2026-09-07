import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_riemannianEDistOf_le_mul_abs_sub
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} {τ : ℝ}
    (hK : K ∈ 𝓝 τ) (hG : Continuous (metricTimeBundleQuad (I := I) g K))
    {x : ℝ → M} (hx : ContMDiffAt 𝓘(ℝ, ℝ) I 1 x τ) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 τ,
      riemannianEDistOf (I := I) (g s) (x τ) (x s) ≤
        ENNReal.ofReal ((Real.sqrt ((g τ).inner (x τ)
          (mfderiv 𝓘(ℝ, ℝ) I x τ 1) (mfderiv 𝓘(ℝ, ℝ) I x τ 1)) + ε) *
          |s - τ|) := by
  classical
  intro ε hε
  obtain ⟨U, hU, hxU⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := (1 : WithTop ℕ∞)) (by simp)).mp hx
  obtain ⟨a, b, hτab, habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  have hxab : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Ioo a b) := hxU.mono habU
  let v : (u : ℝ) → TangentSpace I (x u) :=
    fun u ↦ mfderivWithin 𝓘(ℝ, ℝ) I x (Ioo a b) u 1
  let P : Set (ℝ × ℝ) := K ×ˢ Ioo a b
  let p₀ : P := ⟨(τ, τ), mem_of_mem_nhds hK, hτab⟩
  have hunit : Continuous (fun u : ℝ ↦
      (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hunitMaps : MapsTo
      (fun u : ℝ ↦ (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Ioo a b) (TotalSpace.proj ⁻¹' Ioo a b) := fun _ hu ↦ hu
  have hvelOn : ContinuousOn
      (fun u : ℝ ↦ tangentMapWithin 𝓘(ℝ, ℝ) I x (Ioo a b)
        (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) (Ioo a b) :=
    (hxab.continuousOn_tangentMapWithin (le_refl 1)
      isOpen_Ioo.uniqueMDiffOn).comp hunit.continuousOn hunitMaps
  have hparam : Continuous (fun p : P ↦
      (⟨(p.1 : ℝ × ℝ).2, p.2.2⟩ : Ioo a b)) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hvel : Continuous (fun p : P ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (x (p.1 : ℝ × ℝ).2) (v (p.1 : ℝ × ℝ).2)) := by
    convert (continuousOn_iff_continuous_domRestrict.mp hvelOn).comp hparam using 1
    rfl
  let q : P → ℝ := fun p ↦ (g (p.1 : ℝ × ℝ).1).inner
    (x (p.1 : ℝ × ℝ).2) (v (p.1 : ℝ × ℝ).2) (v (p.1 : ℝ × ℝ).2)
  have hq : Continuous q := by
    have htime : Continuous (fun p : P ↦
        (⟨(p.1 : ℝ × ℝ).1, p.2.1⟩ : K)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    exact hG.comp (htime.prodMk hvel)
  have hv_eq {u : ℝ} (hu : u ∈ Ioo a b) :
      v u = mfderiv 𝓘(ℝ, ℝ) I x u 1 :=
    congrArg (fun A ↦ A (1 : ℝ))
      (mfderivWithin_of_isOpen (I := 𝓘(ℝ, ℝ)) (I' := I) (f := x) isOpen_Ioo hu)
  let q₀ : ℝ := (g τ).inner (x τ)
    (mfderiv 𝓘(ℝ, ℝ) I x τ 1) (mfderiv 𝓘(ℝ, ℝ) I x τ 1)
  have hq₀ : 0 ≤ q₀ := by
    by_cases hv : mfderiv 𝓘(ℝ, ℝ) I x τ 1 = 0
    · simp only [q₀, hv, map_zero]
      exact le_rfl
    · exact ((g τ).pos (x τ) _ hv).le
  let C : ℝ := Real.sqrt q₀ + ε
  have hC : 0 < C := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hε
  have hq₀C : q p₀ < C ^ 2 := by
    dsimp only [q, p₀]
    rw [hv_eq hτab]
    change q₀ < C ^ 2
    dsimp only [C]
    nlinarith [Real.sq_sqrt hq₀, Real.sqrt_nonneg q₀]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt hq continuous_const).mem_nhds hq₀C)
  obtain ⟨rK, hrK, hballK⟩ := Metric.mem_nhds_iff.mp hK
  let δ : ℝ := min (τ - a) (min (b - τ) (min rK r))
  have hδ : 0 < δ :=
    lt_min (sub_pos.mpr hτab.1) (lt_min (sub_pos.mpr hτab.2) (lt_min hrK hr))
  have hδa : δ ≤ τ - a := min_le_left _ _
  have hδb : δ ≤ b - τ := (min_le_right _ _).trans (min_le_left _ _)
  have hδK : δ ≤ rK := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ ≤ r := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
  have hsδ : |s - τ| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
  have hsK : s ∈ K := hballK (by
    simpa only [Metric.mem_ball, Real.dist_eq] using hsδ.trans_le hδK)
  have huδ {u : ℝ} (hu : u ∈ uIcc τ s) : |u - τ| < δ :=
    (abs_sub_left_of_mem_uIcc hu).trans_lt hsδ
  have huab {u : ℝ} (hu : u ∈ uIcc τ s) : u ∈ Ioo a b := by
    have hu' := abs_lt.mp (huδ hu)
    constructor <;> linarith
  have hpoint : ∀ u ∈ uIcc τ s,
      Real.sqrt ((g s).inner (x u)
        (mfderiv 𝓘(ℝ, ℝ) I x u 1) (mfderiv 𝓘(ℝ, ℝ) I x u 1)) ≤ C := by
    intro u hu
    let p : P := ⟨(s, u), hsK, huab hu⟩
    have hpr : dist p p₀ < r := by
      rw [Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨hsδ.trans_le hδr, (huδ hu).trans_le hδr⟩
    have hpq : q p < C ^ 2 := hball (Metric.mem_ball.mpr hpr)
    apply le_of_lt
    rw [Real.sqrt_lt' hC]
    simpa only [q, p, hv_eq (huab hu)] using hpq
  have hbound {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ uIcc τ s) :
      riemannianEDistOf (I := I) (g s) (x c) (x d) ≤
        ENNReal.ofReal (C * (d - c)) := by
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc c d) :=
      hxab.mono (fun u hu ↦ huab (hsub hu))
    have hspeedInt : IntervalIntegrable (fun u ↦ Real.sqrt ((g s).inner (x u)
        (mfderiv 𝓘(ℝ, ℝ) I x u 1) (mfderiv 𝓘(ℝ, ℝ) I x u 1))) volume c d := by
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le hcd]
      exact Geodesic.speedSqrt_integrableOn_Icc_of_C1 (g s) hcd hcurve
    have hlen : Variation.arcLength (I := I) (g s) x c d ≤ C * (d - c) := by
      have hmono := intervalIntegral.integral_mono_on hcd hspeedInt
        intervalIntegrable_const (fun u hu ↦ hpoint u (hsub hu))
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      convert hmono using 1
      · rfl
      · exact mul_comm C (d - c)
    exact (riemannianEDistOf_le_arcLength (g s) hcd hcurve).trans
      (ENNReal.ofReal_le_ofReal hlen)
  change riemannianEDistOf (I := I) (g s) (x τ) (x s) ≤
    ENNReal.ofReal (C * |s - τ|)
  rcases le_total τ s with hτs | hsτ
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hτs)] using
      hbound hτs (by rw [uIcc_of_le hτs])
  · have hcomm : riemannianEDistOf (I := I) (g s) (x τ) (x s) =
        riemannianEDistOf (I := I) (g s) (x s) (x τ) := by
      let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g s).toRiemannianMetric⟩
      change riemannianEDist I (x τ) (x s) = riemannianEDist I (x s) (x τ)
      exact riemannianEDist_comm
    rw [hcomm, abs_of_nonpos (sub_nonpos.mpr hsτ), neg_sub]
    exact hbound hsτ (by rw [uIcc_of_ge hsτ])

end DifferentialGeometry
