import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionDecay
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionRate
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Tower
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA2
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

/-!
# The normalized scalar curvature rate of a surface Ricci flow (assembly of a5.2)

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (viii),
review 18 §6).

* `tracelessHessField g f`: the traceless Hessian `∇²f - ½ (Δf) g` as a smooth `(0, 2)`-field.
* `kInf_bounds_of_rate`: a limit `k∞` of metrics `k(t)` (rate `(T* - t)^β` in `C^q`, `q ≤ 2`, with
  respect to `g(0)`) inherits half the common lower bound and the `C²` bounds.
* `surfaceFlow_normalized_scalar_rate` (D18 (viii)): the conditional core. Besides `T = T*` and
  a5.1 (`hshi`) it takes the frozen statements of (i) (`hpot`, lane U1V), (iii) (`hiii`, lane
  U1E2) and (v)+(vi) (`hgauge`, lane U1V) as hypotheses, and composes them with (ii′)
  (`surfaceFlow_tracelessHess_decay`), (iv) (`surfaceFlow_exists_potential_gauge`) and (vii)
  (`normalizedFlowMetric_scalar_rate_of_gauge`); a4 gives the exponent `c`. All rates are written
  in `t`: the exponent `β` of (v) is already the `t`-exponent `β_t` (a rate `e^{-β_s s}` in
  normalized time is `(T* - t)^{β_s / 2}`, `flowExtinctionTime_sub_eq_exp`). The terminal rate on
  `[t₀, T)` extends to `[0, T)` by compactness.
* `a5_decay`: D17's form for a maximal flow: `hTeq` from `surfaceFlow_maximal_time_eq` (a2) and
  `hshi` from `surfaceFlow_shi_iterCov_bound` (a5.1); (i), (iii), (v)+(vi) remain hypotheses.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open Bundle Filter Topology Set MeasureTheory
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance a5EvolutionMeasurable : MeasurableSpace M := borel M
private local instance a5EvolutionBorel : BorelSpace M := ⟨rfl⟩

def tracelessHessField [NeZero (Module.finrank ℝ E)] (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  covStep g 1 (duSec f f.contMDiff) -
    tensor0SFieldSmulByFun ∞ (fun y => ΔG g f y / 2) ((Δ_g_contMDiff g f).div_const 2)
      (metricTensorField g)

theorem tracelessHessField_apply [NeZero (Module.finrank ℝ E)] (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) : tracelessHessField g f x = tracelessHessAt g f x := by
  refine tensor0SSpace_ext 2 x fun v => ?_
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hv2 : v = vec2 (v 0) (v 1) := by funext i; fin_cases i <;> rfl
  rw [tracelessHessField, ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
    tensor0SField_smulByFun_apply, Tensor0SSpace.smul_apply, metricTensorField_apply, hv,
    covStep_duSec_apply_vec, ← hv, hv2, tracelessHessAt_vec2, smul_eq_mul]
  rfl

omit [I.Boundaryless] in
theorem kInf_bounds_of_rate [CompactSpace M] (g0 kInf : SmoothRiemannianMetric I M)
    (k : ℝ → SmoothRiemannianMetric I M) {t₀ Tst lam B β : ℝ} (ht₀ : t₀ < Tst) (hlam : 0 < lam)
    (hβ : 0 < β)
    (hlow : ∀ t ∈ Ico t₀ Tst, ∀ x (v : TangentSpace I x), lam * g0.inner x v v ≤ (k t).inner x v v)
    (hbdd : ∀ t ∈ Ico t₀ Tst, ∀ x, ∀ q ≤ 2, metricCovDerivNorm q (k t) g0 x ≤ B)
    (hrate : ∀ t ∈ Ico t₀ Tst, ∀ q ≤ 2, ∀ x,
      metricDerivNorm q (k t) kInf g0 x ≤ B * (Tst - t) ^ β) :
    (∀ x (v : TangentSpace I x), lam / 2 * g0.inner x v v ≤ kInf.inner x v v) ∧
      ∀ x, ∀ q ≤ 2, metricCovDerivNorm q kInf g0 x ≤ B + B * (Tst - t₀) ^ β := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  constructor
  · intro x v
    set B' := max B 1 with hB'
    have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set ε := min ((Tst - t₀) / 2) ((lam / (2 * B')) ^ (1 / β)) with hε
    have hεpos : 0 < ε := lt_min (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
    have hεle : ε ≤ (Tst - t₀) / 2 := min_le_left _ _
    have ht : Tst - ε ∈ Ico t₀ Tst := ⟨by linarith, by linarith⟩
    have hpow : ε ^ β ≤ lam / (2 * B') := by
      calc ε ^ β ≤ ((lam / (2 * B')) ^ (1 / β)) ^ β :=
            Real.rpow_le_rpow hεpos.le (min_le_right _ _) hβ.le
        _ = lam / (2 * B') := by
            rw [one_div, Real.rpow_inv_rpow (by positivity) hβ.ne']
    have hd : metricDerivNorm 0 (k (Tst - ε)) kInf g0 x ≤ lam / 2 := by
      have h := hrate _ ht 0 (by norm_num) x
      rw [show Tst - (Tst - ε) = ε by ring] at h
      calc metricDerivNorm 0 (k (Tst - ε)) kInf g0 x ≤ B * ε ^ β := h
        _ ≤ B' * ε ^ β := mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hεpos.le _)
        _ ≤ B' * (lam / (2 * B')) := mul_le_mul_of_nonneg_left hpow hB'pos.le
        _ = lam / 2 := by field_simp
    have habs := metricDifference_abs_le (k (Tst - ε)) kInf g0 x v v
    have hg0 : 0 ≤ g0.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g0.pos x v hv).le
    rw [mul_assoc, Real.mul_self_sqrt hg0] at habs
    have hk := hlow _ ht x v
    have h2 : metricDerivNorm 0 (k (Tst - ε)) kInf g0 x * g0.inner x v v ≤
        lam / 2 * g0.inner x v v := mul_le_mul_of_nonneg_right hd hg0
    have := (abs_le.mp habs).2
    nlinarith
  · intro x q hq
    have ht : t₀ ∈ Ico t₀ Tst := ⟨le_rfl, ht₀⟩
    have hsplit : metricCovDeriv kInf g0 q x =
        metricCovDeriv (k t₀) g0 q x - metricDiffCovDerivAt q (k t₀) kInf g0 x := by
      rw [metricDiffCovDerivAt, sub_sub_cancel]
    have h := sqrt_normSq0S_sub_le g0 x (q + 2) (metricCovDeriv (k t₀) g0 q x)
      (metricDiffCovDerivAt q (k t₀) kInf g0 x)
    rw [← hsplit] at h
    have h1 := hbdd t₀ ht x q hq
    have h2 := hrate t₀ ht q hq x
    unfold metricCovDerivNorm
    unfold metricCovDerivNorm at h1
    unfold metricDerivNorm at h2
    linarith

omit [I.Boundaryless] in
theorem surfaceFlow_rate_extend_to_zero {T : ℝ} {hT : 0 < T}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    [CompactSpace M] {t₀ C δ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (hδ : 0 < δ)
    (h : ∀ t ∈ Ico t₀ T, ∀ x, |S.scalar t x * (2 * (T - t)) - 2| ≤ C * (T - t) ^ δ) :
    ∃ C' : ℝ, ∀ t ∈ Ico 0 T, ∀ x, |S.scalar t x * (2 * (T - t)) - 2| ≤ C' * (T - t) ^ δ := by
  have hcont : ContinuousOn (fun q : ℝ × M => S.scalar q.1 q.2 * (2 * (T - q.1)) - 2)
      (Icc 0 t₀ ×ˢ univ) := by
    have hsub : Icc 0 t₀ ×ˢ (univ : Set M) ⊆ (RealTimeInterval.closedOpen 0 T hT).carrier ×ˢ univ :=
      prod_mono (fun s hs => (⟨hs.1, hs.2.trans_lt ht₀.2⟩ : s ∈ Ico 0 T)) le_rfl
    exact ((hS.scalarCont.mono hsub).mul (continuousOn_const.mul
      (continuousOn_const.sub continuous_fst.continuousOn))).sub continuousOn_const
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hcont
  have hgap : 0 < T - t₀ := by linarith [ht₀.2]
  refine ⟨max C (|K| / (T - t₀) ^ δ), fun t ht x => ?_⟩
  have hτ : 0 < T - t := by linarith [ht.2]
  rcases lt_or_ge t t₀ with hlt | hge
  · have hb := hK (t, x) ⟨⟨ht.1, hlt.le⟩, mem_univ x⟩
    simp only [Real.norm_eq_abs] at hb
    have hpos : 0 < (T - t) ^ δ := Real.rpow_pos_of_pos hτ _
    have hle : (T - t₀) ^ δ ≤ (T - t) ^ δ := Real.rpow_le_rpow hgap.le (by linarith) hδ.le
    have hpos₀ : 0 < (T - t₀) ^ δ := Real.rpow_pos_of_pos hgap _
    calc |S.scalar t x * (2 * (T - t)) - 2| ≤ |K| := hb.trans (le_abs_self K)
      _ = |K| / (T - t₀) ^ δ * (T - t₀) ^ δ := by field_simp
      _ ≤ |K| / (T - t₀) ^ δ * (T - t) ^ δ :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ max C (|K| / (T - t₀) ^ δ) * (T - t) ^ δ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
  · calc |S.scalar t x * (2 * (T - t)) - 2| ≤ C * (T - t) ^ δ := h t ⟨hge, ht.2⟩ x
      _ ≤ max C (|K| / (T - t₀) ^ δ) * (T - t) ^ δ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hτ.le _)

theorem surfaceFlow_normalized_scalar_rate [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [ConnectedSpace M] {T : ℝ} {hT : 0 < T} (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (hTeq : T = flowExtinctionTime S)
    (hshi : ∀ t₀ ∈ Ioo 0 T, ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
      normSq0S (S.family.metric t) x (4 + q)
          (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
        B * (flowExtinctionTime S - t) ^ (-(2 + q : ℝ)))
    (hpot : ∃ f : ℝ → C^∞⟮I, M; ℝ⟯,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 T ×ˢ univ) ∧
      (∀ t ∈ Ico 0 T, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
        ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t)) ∧
      ∃ a : ℝ → ℝ, ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
    (hiii : ∀ (f : ℝ → C^∞⟮I, M; ℝ⟯)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 T ×ˢ univ))
      (_ : ∀ t ∈ Ioo 0 T, ∀ x,
        ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
      (a : ℝ → ℝ) (_ : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
      (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
      (_ : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
      (t₀ C₀ c : ℝ) (_ : t₀ ∈ Ioo 0 T) (_ : 0 < c)
      (_ : ∀ t ∈ Ico t₀ T, ∀ x,
        (flowExtinctionTime S - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤
          C₀ * (flowExtinctionTime S - t) ^ c)
      (_ : ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
        normSq0S (S.family.metric t) x (4 + q)
            (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
          B * (flowExtinctionTime S - t) ^ (-(2 + q : ℝ))),
      ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
        (flowExtinctionTime S - t) ^ (2 + q) *
            normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
          C * (flowExtinctionTime S - t) ^ γ)
    (hgauge : ∀ (f : ℝ → C^∞⟮I, M; ℝ⟯)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 T ×ˢ univ))
      (_ : ∀ t ∈ Ico 0 T, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
        ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
      (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
      (_ : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
      (t₀ : ℝ) (_ : t₀ ∈ Ioo 0 T)
      (_ : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
        (flowExtinctionTime S - t) ^ (2 + q) *
            normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
          C * (flowExtinctionTime S - t) ^ γ)
      (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) (_ : ∀ x, ψ t₀ x = x)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
      (_ : ∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀)
      (_ : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
      (c : ℝ) (_ : 0 < c)
      (_ : ∀ t ∈ Ico 0 T, ∀ x, c ≤ S.scalar t x * (2 * (flowExtinctionTime S - t))),
      ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
        (∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v) ∧
        (∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤
            B) ∧
        (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ T, ∀ q ≤ N, ∀ x,
          metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
            (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β) ∧
        ∀ x, metricScalarAt kInf x = 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 T, ∀ x,
      |S.scalar t x * (2 * (T - t)) - 2| ≤ C * (T - t) ^ δ := by
  obtain ⟨c, hc, hlowA⟩ := surfaceFlow_normalized_scalar_lower hdim S hS hscal
  obtain ⟨f, hf, hfeq0, a, hft⟩ := hpot
  have hfeqI : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t) :=
    fun t ht => (hfeq0 t (Ioo_subset_Ico_self ht)).2
  set Mf := fun t => tracelessHessField (S.family.metric t) (f t) with hMfdef
  have hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x :=
    fun t _ x => tracelessHessField_apply _ _ x
  set t₀ := T / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo 0 T := ⟨by positivity, by linarith⟩
  obtain ⟨C₀, hC₀⟩ := surfaceFlow_tracelessHess_decay hdim S hS hscal f hf hfeqI hft Mf hM hc
    hlowA ht₀
  have hdecayAll := hiii f hf hfeqI a hft Mf hM t₀ C₀ c ht₀ hc hC₀ (hshi t₀ ht₀)
  obtain ⟨ψ, hψ0, hψsm, hψc, -, hψd⟩ :=
    surfaceFlow_exists_potential_gauge hdim S hS hscal f hf hfeqI ht₀
  obtain ⟨lam, hlam, kInf, hlowk, hbddk, hratek, hround⟩ :=
    hgauge f hf hfeq0 Mf hM t₀ ht₀ hdecayAll ψ hψ0 hψsm hψc hψd c hc hlowA
  obtain ⟨B0, hB0⟩ := hbddk 0
  obtain ⟨B1, hB1⟩ := hbddk 1
  obtain ⟨B2, hB2⟩ := hbddk 2
  obtain ⟨Br, β, hβ, hBr⟩ := hratek 2
  set Bm := max (max (max B0 B1) B2) (max Br 0) with hBm
  have hBm0 : 0 ≤ Bm := le_trans (le_max_right _ _) (le_max_right _ _)
  have hTT : t₀ < flowExtinctionTime S := hTeq ▸ ht₀.2
  set k := fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t) with hkdef
  have hbddm : ∀ t ∈ Ico t₀ (flowExtinctionTime S), ∀ x, ∀ q ≤ 2,
      metricCovDerivNorm q (k t) (S.family.metric 0) x ≤ Bm := by
    intro t ht x q hq
    rw [← hTeq] at ht
    interval_cases q
    · exact (hB0 t ht x).trans (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact (hB1 t ht x).trans (le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact (hB2 t ht x).trans (le_trans (le_max_right _ _) (le_max_left _ _))
  have hratem : ∀ t ∈ Ico t₀ (flowExtinctionTime S), ∀ q ≤ 2, ∀ x,
      metricDerivNorm q (k t) kInf (S.family.metric 0) x ≤
        Bm * (flowExtinctionTime S - t) ^ β := by
    intro t ht q hq x
    have ht' : t ∈ Ico t₀ T := hTeq ▸ ht
    have hτ : 0 ≤ (flowExtinctionTime S - t) ^ β :=
      Real.rpow_nonneg (by linarith [ht.2]) _
    exact (hBr t ht' q hq x).trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) hτ)
  have hlowm : ∀ t ∈ Ico t₀ (flowExtinctionTime S), ∀ x (v : TangentSpace I x),
      lam * (S.family.metric 0).inner x v v ≤ (k t).inner x v v := fun t ht =>
    hlowk t (hTeq ▸ ht)
  obtain ⟨hlowInf, hbddInf⟩ := kInf_bounds_of_rate (S.family.metric 0) kInf k hTT hlam hβ
    hlowm hbddm hratem
  set Bf := Bm + Bm * (flowExtinctionTime S - t₀) ^ β with hBf
  have hτ₀ : 0 ≤ Bm * (flowExtinctionTime S - t₀) ^ β :=
    mul_nonneg hBm0 (Real.rpow_nonneg (by linarith) _)
  obtain ⟨C, hC⟩ := normalizedFlowMetric_scalar_rate_of_gauge hdim S hS hscal (t₀ := t₀) ψ
    (lam := lam / 2) (B := Bf) (by positivity) hβ kInf
    (fun t ht x v => le_trans (by
        have := (S.family.metric 0).pos x v
        by_cases hv : v = 0
        · simp [hv]
        · nlinarith [this hv]) (hlowk t ht x v))
    hlowInf
    (fun t ht x q hq => (hbddm t (hTeq ▸ ht) x q hq).trans (by linarith))
    hbddInf
    (fun t ht q hq x => (hratem t (hTeq ▸ ht) q hq x).trans (mul_le_mul_of_nonneg_right
      (by linarith) (Real.rpow_nonneg (by rw [← hTeq]; linarith [ht.2]) _)))
    hround
  have hfinal : ∀ t ∈ Ico t₀ T, ∀ x,
      |S.scalar t x * (2 * (T - t)) - 2| ≤ C * (T - t) ^ β := by
    intro t ht x
    have h := hC t ht x
    have e : flowExtinctionTime S - t = T - t := by rw [← hTeq]
    rwa [e] at h
  obtain ⟨C', hC'⟩ := surfaceFlow_rate_extend_to_zero S hS ht₀ hβ hfinal
  exact ⟨C', β, hβ, hC'⟩

theorem a5_decay [NeZero (Module.finrank ℝ E)] [CompactSpace M] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hscal : ∀ x, 0 < S.scalar 0 x)
    (hmax : IsMaximalAtEndpoint (I := I) hTm S)
    (hpot : ∃ f : ℝ → C^∞⟮I, M; ℝ⟯,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 Tm ×ˢ univ) ∧
      (∀ t ∈ Ico 0 Tm, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
        ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t)) ∧
      ∃ a : ℝ → ℝ, ∀ t ∈ Ioo 0 Tm, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
    (hiii : ∀ (f : ℝ → C^∞⟮I, M; ℝ⟯)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 Tm ×ˢ univ))
      (_ : ∀ t ∈ Ioo 0 Tm, ∀ x,
        ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
      (a : ℝ → ℝ) (_ : ∀ t ∈ Ioo 0 Tm, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
      (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
      (_ : ∀ t ∈ Ioo 0 Tm, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
      (t₀ C₀ c : ℝ) (_ : t₀ ∈ Ioo 0 Tm) (_ : 0 < c)
      (_ : ∀ t ∈ Ico t₀ Tm, ∀ x,
        (flowExtinctionTime S - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤
          C₀ * (flowExtinctionTime S - t) ^ c)
      (_ : ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ Tm, ∀ x,
        normSq0S (S.family.metric t) x (4 + q)
            (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
          B * (flowExtinctionTime S - t) ^ (-(2 + q : ℝ))),
      ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
        (flowExtinctionTime S - t) ^ (2 + q) *
            normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
          C * (flowExtinctionTime S - t) ^ γ)
    (hgauge : ∀ (f : ℝ → C^∞⟮I, M; ℝ⟯)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 Tm ×ˢ univ))
      (_ : ∀ t ∈ Ico 0 Tm, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
        ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
      (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
      (_ : ∀ t ∈ Ioo 0 Tm, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
      (t₀ : ℝ) (_ : t₀ ∈ Ioo 0 Tm)
      (_ : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
        (flowExtinctionTime S - t) ^ (2 + q) *
            normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
          C * (flowExtinctionTime S - t) ^ γ)
      (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) (_ : ∀ x, ψ t₀ x = x)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ Tm ×ˢ univ))
      (_ : ∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀)
      (_ : ∀ t ∈ Ioo t₀ Tm, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
      (c : ℝ) (_ : 0 < c)
      (_ : ∀ t ∈ Ico 0 Tm, ∀ x, c ≤ S.scalar t x * (2 * (flowExtinctionTime S - t))),
      ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
        (∀ t ∈ Ico t₀ Tm, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v) ∧
        (∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ Tm, ∀ x, metricCovDerivNorm q
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤
            B) ∧
        (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ Tm, ∀ q ≤ N, ∀ x,
          metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
            (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β) ∧
        ∀ x, metricScalarAt kInf x = 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ :=
  surfaceFlow_normalized_scalar_rate hdim S hS hscal
    (surfaceFlow_maximal_time_eq hdim hTm S hS hscal hmax)
    (surfaceFlow_shi_iterCov_bound hdim S hS hscal) hpot hiii hgauge

end GC.Geometry
