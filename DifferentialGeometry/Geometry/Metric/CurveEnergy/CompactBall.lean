import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Geometry.Curve.Reparametrization
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

noncomputable section
open Set Manifold Bundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_minimizer_in_riemannianClosedBall
    (g : SmoothRiemannianMetric I M) (p q : M) {R : ℝ}
    (hR : riemannianEDistOf g p q < ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g p R)) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ γ 0 = p ∧ γ 1 = q ∧
      MapsTo γ (Icc 0 1) (riemannianClosedBallOf g p R) ∧
      ∀ t ∈ Icc 0 1, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = (riemannianEDistOf g p q).toReal ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have hdist : riemannianEDist I p q < ENNReal.ofReal R := hR
    obtain ⟨δ, hzero, hone, hδ, _⟩ := exists_lt_of_riemannianEDist_lt hdist
    have hpq : p = q := by
      rw [← hzero, ← hone]
      exact isPreconnected_Icc.constant hδ.continuousOn (by simp) (by simp)
    cases hpq
    refine ⟨fun _ => p, contMDiff_const, rfl, rfl, ?_, ?_⟩
    · intro t _
      change riemannianEDistOf g p p ≤ ENNReal.ofReal R
      rw [riemannianEDistOf_self]
      exact bot_le
    · intro t _
      rw [riemannianEDistOf_self]
      simp only [mfderiv_const, zero_apply, map_zero, ENNReal.toReal_zero, zero_pow two_ne_zero]
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : T2Space (TangentBundle I M) := inferInstance
  have hfinite : riemannianEDistOf g p q ≠ ⊤ := ne_top_of_lt hR
  have hRpos : 0 < R := ENNReal.ofReal_pos.mp (bot_le.trans_lt hR)
  have hdR : (riemannianEDistOf g p q).toReal < R :=
    (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hR |>.trans_eq (ENNReal.toReal_ofReal hRpos.le)
  let δ := (R - (riemannianEDistOf g p q).toReal) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hdR)
  have htrap : ∀ γ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) → γ 0 = p → γ 1 = q →
      metricPathELength g γ 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal δ →
      ∀ t ∈ Icc 0 1, γ t ∈ riemannianClosedBallOf g p R := by
    intro γ hγ hzero _ hnear t ht
    have hpref := edistOf_le_metricPathELength g ht.1 (hγ.mono (Icc_subset_Icc le_rfl ht.2))
    rw [hzero] at hpref
    have hh := hpref.trans ((metricPathELength_mono g γ le_rfl ht.2).trans hnear)
    have heq := ENNReal.ofReal_toReal hfinite
    rw [← heq, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ.le] at hh
    exact hh.trans (ENNReal.ofReal_le_ofReal (by dsimp only [δ]; linarith))
  obtain ⟨γ, hzero, hend, hγ, hstay, _, _, _, hspeed⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_geodesic_minimizer_of_compact_trapping
      g hcompact hδ hfinite htrap
  exact ⟨γ, hγ, hzero, hend, hstay, hspeed⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_curve_energy_eq_of_isCompact_riemannianClosedBall
    (g : SmoothRiemannianMetric I M) (p q : M) {R a b : ℝ} (hab : a < b)
    (hR : riemannianEDistOf g p q < ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g p R)) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α a = p ∧ α b = q ∧
      MapsTo α (Icc a b) (riemannianClosedBallOf g p R) ∧
      curveEnergy g α a b = (riemannianEDistOf g p q).toReal ^ 2 / (b - a) := by
  obtain ⟨γ, hγ, hzero, hone, hstay, hspeed⟩ :=
    exists_contMDiff_minimizer_in_riemannianClosedBall g p q hR hcompact
  let τ : ℝ → ℝ := fun t => (t - a) / (b - a)
  let α : ℝ → M := γ ∘ τ
  have hτ : ContDiff ℝ ∞ τ := (contDiff_id.sub contDiff_const).div_const _
  have hα : ContMDiff 𝓘(ℝ, ℝ) I ∞ α := hγ.comp hτ.contMDiff
  have hτmap : MapsTo τ (Icc a b) (Icc 0 1) := by
    intro t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 a)⟩
  refine ⟨α, hα, ?_, ?_, (fun t ht => hstay (hτmap ht)), ?_⟩
  · simpa only [α, τ, Function.comp_apply, sub_self, zero_div] using hzero
  · simpa only [α, τ, Function.comp_apply, div_self (sub_ne_zero.mpr hab.ne')] using hone
  have hvel (t : ℝ) : mfderiv 𝓘(ℝ, ℝ) I α t 1 =
      (b - a)⁻¹ • mfderiv 𝓘(ℝ, ℝ) I γ (τ t) 1 := by
    have haff : τ = fun s : ℝ => (b - a)⁻¹ * s + (-(b - a)⁻¹ * a) := by
      funext s
      dsimp only [τ]
      ring
    have hh := DifferentialGeometry.Geometry.mfderiv_comp_affine_apply_one t (b - a)⁻¹
      (-(b - a)⁻¹ * a) (hγ.mdifferentiable (by simp) _)
    have heq : α = fun s : ℝ => γ ((b - a)⁻¹ * s + (-(b - a)⁻¹ * a)) := by
      rw [show α = γ ∘ τ from rfl, haff]
      rfl
    rw [heq, haff]
    exact hh
  have hconstant (t : ℝ) (ht : t ∈ Icc a b) :
      g.inner (α t) (mfderiv 𝓘(ℝ, ℝ) I α t 1) (mfderiv 𝓘(ℝ, ℝ) I α t 1) =
        (riemannianEDistOf g p q).toReal ^ 2 / (b - a) ^ 2 := by
    rw [hvel, Exponential.gInner_smul_self]
    change (b - a)⁻¹ ^ 2 * g.inner (γ (τ t))
      (mfderiv 𝓘(ℝ, ℝ) I γ (τ t) 1) (mfderiv 𝓘(ℝ, ℝ) I γ (τ t) 1) = _
    rw [hspeed (τ t) (hτmap ht)]
    simp only [div_eq_mul_inv, inv_pow, mul_comm]
  have hi : curveEnergy g α a b = ∫ _t in a..b, (riemannianEDistOf g p q).toReal ^ 2 / (b - a) ^ 2 := by
    unfold curveEnergy
    apply intervalIntegral.integral_congr
    intro t ht
    exact hconstant t (by simpa only [uIcc_of_le hab.le] using ht)
  rw [hi, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp

end DifferentialGeometry.Geometry.Riemannian
