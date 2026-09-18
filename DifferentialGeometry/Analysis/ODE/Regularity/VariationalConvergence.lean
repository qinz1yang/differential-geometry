import DifferentialGeometry.Analysis.ODE.Flow.VariationalBounds
import DifferentialGeometry.Analysis.ODE.Stability.Tube
import DifferentialGeometry.Analysis.Calculus.Periodic.Convergence

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set

theorem paramTangentVF_tendstoUniformlyOn
    {ι P Q X : Type*} {l : Filter ι}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v : ι → ℝ → X → X} {vInf : ℝ → X → X}
    {J : Set ℝ} {K : Set P}
    (z : P → ℝ → X × (Q →L[ℝ] X)) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p ∈ K, ∀ t ∈ J, ‖(z p t).2‖ ≤ B)
    (hv : TendstoUniformlyOn
      (fun i (q : P × ℝ) => v i q.2 (z q.1 q.2).1)
      (fun q : P × ℝ => vInf q.2 (z q.1 q.2).1) l (K ×ˢ J))
    (hDv : TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (v i q.2) (z q.1 q.2).1)
      (fun q : P × ℝ => fderiv ℝ (vInf q.2) (z q.1 q.2).1) l (K ×ˢ J)) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => paramTangentVF Q (v i) q.2 (z q.1 q.2))
      (fun q : P × ℝ => paramTangentVF Q vInf q.2 (z q.1 q.2))
      l (K ×ˢ J) := by
  rw [Metric.tendstoUniformlyOn_iff] at hv hDv ⊢
  intro ε hε
  let δ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ ≤ ε := div_le_self hε.le (by linarith)
  filter_upwards [hv δ hδ, hDv δ hδ] with i hi hDi
  intro q hq
  have hderivative : ‖fderiv ℝ (vInf q.2) (z q.1 q.2).1 -
      fderiv ℝ (v i q.2) (z q.1 q.2).1‖ < δ := by
    simpa only [dist_eq_norm] using hDi q hq
  have hsecond : dist
      ((fderiv ℝ (vInf q.2) (z q.1 q.2).1).comp (z q.1 q.2).2)
      ((fderiv ℝ (v i q.2) (z q.1 q.2).1).comp (z q.1 q.2).2) < ε := by
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    calc
      ‖(fderiv ℝ (vInf q.2) (z q.1 q.2).1 -
          fderiv ℝ (v i q.2) (z q.1 q.2).1).comp (z q.1 q.2).2‖ ≤
          ‖fderiv ℝ (vInf q.2) (z q.1 q.2).1 -
            fderiv ℝ (v i q.2) (z q.1 q.2).1‖ * ‖(z q.1 q.2).2‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ δ * B := mul_le_mul hderivative.le (hz q.1 hq.1 q.2 hq.2)
        (norm_nonneg _) hδ.le
      _ < δ * (B + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
      _ = ε := div_mul_cancel₀ ε (by linarith)
  exact max_lt ((hi q hq).trans_le hδε) hsecond

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set

theorem paramTangentVF_tendstoUniformlyOn_fderiv
    {ι P Q X : Type*} {l : Filter ι}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v : ι → ℝ → X → X} {vInf : ℝ → X → X}
    {J : Set ℝ} {K : Set P}
    (z : P → ℝ → X × (Q →L[ℝ] X)) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p ∈ K, ∀ t ∈ J, ‖(z p t).2‖ ≤ B)
    (hv : ∀ᶠ i in l, ∀ p ∈ K, ∀ t ∈ J,
      DifferentiableAt ℝ (v i t) (z p t).1 ∧
        DifferentiableAt ℝ (fderiv ℝ (v i t)) (z p t).1)
    (hvInf : ∀ p ∈ K, ∀ t ∈ J,
      DifferentiableAt ℝ (vInf t) (z p t).1 ∧
        DifferentiableAt ℝ (fderiv ℝ (vInf t)) (z p t).1)
    (hDv : TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (v i q.2) (z q.1 q.2).1)
      (fun q : P × ℝ => fderiv ℝ (vInf q.2) (z q.1 q.2).1) l (K ×ˢ J))
    (hD₂v : TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (fderiv ℝ (v i q.2)) (z q.1 q.2).1)
      (fun q : P × ℝ => fderiv ℝ (fderiv ℝ (vInf q.2)) (z q.1 q.2).1) l (K ×ˢ J)) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (paramTangentVF Q (v i) q.2) (z q.1 q.2))
      (fun q : P × ℝ => fderiv ℝ (paramTangentVF Q vInf q.2) (z q.1 q.2))
      l (K ×ˢ J) := by
  rw [Metric.tendstoUniformlyOn_iff] at hDv hD₂v ⊢
  intro ε hε
  let δ := ε / (B + 2)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [hv, hDv δ hδ, hD₂v δ hδ] with i hi hDi hD₂i
  intro q hq
  have hfirst : ‖fderiv ℝ (vInf q.2) (z q.1 q.2).1 -
      fderiv ℝ (v i q.2) (z q.1 q.2).1‖ < δ := by
    simpa only [dist_eq_norm] using hDi q hq
  have hsecond : ‖fderiv ℝ (fderiv ℝ (vInf q.2)) (z q.1 q.2).1 -
      fderiv ℝ (fderiv ℝ (v i q.2)) (z q.1 q.2).1‖ < δ := by
    simpa only [dist_eq_norm] using hD₂i q hq
  rw [dist_eq_norm]
  calc
    _ ≤ ‖fderiv ℝ (vInf q.2) (z q.1 q.2).1 -
          fderiv ℝ (v i q.2) (z q.1 q.2).1‖ +
        ‖fderiv ℝ (fderiv ℝ (vInf q.2)) (z q.1 q.2).1 -
          fderiv ℝ (fderiv ℝ (v i q.2)) (z q.1 q.2).1‖ * ‖(z q.1 q.2).2‖ :=
      norm_fderiv_paramTangentVF_sub_le vInf (v i) q.2 (z q.1 q.2).1
        (z q.1 q.2).2 (hvInf q.1 hq.1 q.2 hq.2).1 (hvInf q.1 hq.1 q.2 hq.2).2
        (hi q.1 hq.1 q.2 hq.2).1 (hi q.1 hq.1 q.2 hq.2).2
    _ ≤ δ + δ * B := add_le_add hfirst.le
      (mul_le_mul hsecond.le (hz q.1 hq.1 q.2 hq.2) (norm_nonneg _) hδ.le)
    _ < δ * (B + 2) := by nlinarith
    _ = ε := div_mul_cancel₀ ε (by linarith)

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set
open scoped ContDiff NNReal

theorem paramTangentCurve_tendstoUniformlyOn_fderiv_of_limit_tube
    {ι P X : Type*} {l : Filter ι}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A K : Set P} (hA : IsOpen A) (hKA : K ⊆ A)
    {V : Set X} (hV : IsOpen V)
    {t₀ t₁ r : ℝ} (ht₀₁ : t₀ ≤ t₁) (hr : 0 < r)
    {v : ι → ℝ → X → X} {vInf : ℝ → X → X}
    (hv : ∀ i t, t ∈ Icc t₀ t₁ → DifferentiableOn ℝ (v i t) V)
    (hvInf : ∀ t ∈ Icc t₀ t₁, DifferentiableOn ℝ (vInf t) V)
    {a : ι → P → X} {aInf : P → X}
    {γ : ι → P → ℝ → X} {γInf : P → ℝ → X}
    (hγjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (A ×ˢ Icc t₀ t₁))
    (hγInfJoint : ContDiffOn ℝ ∞ (Function.uncurry γInf) (A ×ˢ Icc t₀ t₁))
    (hγ : ∀ i p, p ∈ A →
      γ i p t₀ = a i p ∧ IsIntegralCurveOn (γ i p) (v i) (Icc t₀ t₁))
    (hγInf : ∀ p, p ∈ A →
      γInf p t₀ = aInf p ∧ IsIntegralCurveOn (γInf p) vInf (Icc t₀ t₁))
    (hstay : ∀ i p, p ∈ A → ∀ t ∈ Icc t₀ t₁, γ i p t ∈ V)
    (hstayInf : ∀ p, p ∈ A → ∀ t ∈ Icc t₀ t₁, γInf p t ∈ V)
    (hinit : TendstoUniformlyOn (fun i => paramTangentInitial (a i))
      (paramTangentInitial aInf) l K)
    (hfield : TendstoUniformlyOn
      (fun i (q : P × ℝ) => paramTangentVF P (v i) q.2 (paramTangentCurve γInf q.1 q.2))
      (fun q : P × ℝ => paramTangentVF P vInf q.2 (paramTangentCurve γInf q.1 q.2))
      l (K ×ˢ Icc t₀ t₁))
    (hLip : ∃ L : ℝ≥0, ∀ᶠ i in l, ∀ p ∈ K, ∀ t ∈ Ico t₀ t₁,
      LipschitzOnWith L (paramTangentVF P (v i) t)
        (closedBall (paramTangentCurve γInf p t) r)) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (fun p => γ i p q.2) q.1)
      (fun q : P × ℝ => fderiv ℝ (fun p => γInf p q.2) q.1)
      l (K ×ˢ Icc t₀ t₁) := by
  have htan (i : ι) := paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn
    hA hV ht₀₁ (hv i) (hγjoint i) (hγ i) (hstay i)
  have htanInf := paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn
    hA hV ht₀₁ hvInf hγInfJoint hγInf hstayInf
  have hinit' : TendstoUniformlyOn
      (fun i p => paramTangentCurve (γ i) p t₀)
      (fun p => paramTangentCurve γInf p t₀) l K := by
    rw [Metric.tendstoUniformlyOn_iff] at hinit ⊢
    intro ε hε
    filter_upwards [hinit ε hε] with i hi
    intro p hp
    simpa only [(htan i p (hKA hp)).1, (htanInf p (hKA hp)).1] using hi p hp
  have hpair := integralCurve_tendstoUniformlyOn_of_limit_tube ht₀₁ hr
    (fun i p hp => (htan i p (hKA hp)).2)
    (fun p hp => (htanInf p (hKA hp)).2) hinit' hfield hLip
  rw [Metric.tendstoUniformlyOn_iff] at hpair ⊢
  intro ε hε
  filter_upwards [hpair ε hε] with i hi
  intro q hq
  have hh := hi q hq
  change max (dist (γInf q.1 q.2) (γ i q.1 q.2))
    (dist (fderiv ℝ (fun p => γInf p q.2) q.1)
      (fderiv ℝ (fun p => γ i p q.2) q.1)) < ε at hh
  exact (max_lt_iff.mp hh).2

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set

theorem paramTangentVF_tendstoUniformlyOn_of_periodic
    {ι P Q : Type*} {l : Filter ι}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {v : ι → ℝ → ℝ → ℝ} {vInf : ℝ → ℝ → ℝ}
    {J : Set ℝ} {K : Set P} {c : ℝ} (hc : 0 < c)
    (hper : ∀ i t, t ∈ J → Function.Periodic (v i t) c)
    (hperInf : ∀ t ∈ J, Function.Periodic (vInf t) c)
    (hv : TendstoUniformlyOn (fun i (q : ℝ × ℝ) => v i q.2 q.1)
      (fun q : ℝ × ℝ => vInf q.2 q.1) l (Icc (0 : ℝ) c ×ˢ J))
    (hDv : TendstoUniformlyOn (fun i (q : ℝ × ℝ) => fderiv ℝ (v i q.2) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (vInf q.2) q.1) l (Icc (0 : ℝ) c ×ˢ J))
    (z : P → ℝ → ℝ × (Q →L[ℝ] ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p ∈ K, ∀ t ∈ J, ‖(z p t).2‖ ≤ B) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => paramTangentVF Q (v i) q.2 (z q.1 q.2))
      (fun q : P × ℝ => paramTangentVF Q vInf q.2 (z q.1 q.2))
      l (K ×ˢ J) := by
  apply paramTangentVF_tendstoUniformlyOn z hB hz
  · exact Function.Periodic.tendstoUniformlyOn_comp_of_Icc hc
      (Eventually.of_forall hper) hperInf hv (fun p t => (z p t).1)
  · have hpD : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (fderiv ℝ (v i t)) c :=
      Eventually.of_forall fun i t ht => (hper i t ht).fderiv (𝕜 := ℝ)
    have hpDInf : ∀ t ∈ J, Function.Periodic (fderiv ℝ (vInf t)) c :=
      fun t ht => (hperInf t ht).fderiv (𝕜 := ℝ)
    exact Function.Periodic.tendstoUniformlyOn_comp_of_Icc hc hpD hpDInf hDv
      (fun p t => (z p t).1)

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Set
open scoped ContDiff

theorem paramTangentVF_tendstoUniformlyOn_fderiv_of_periodic
    {ι P Q : Type*} {l : Filter ι}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {v : ι → ℝ → ℝ → ℝ} {vInf : ℝ → ℝ → ℝ}
    {J : Set ℝ} {K : Set P} {c : ℝ} (hc : 0 < c)
    (hper : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (v i t) c)
    (hperInf : ∀ t ∈ J, Function.Periodic (vInf t) c)
    (hv : ∀ᶠ i in l, ∀ t ∈ J, ContDiff ℝ 2 (v i t))
    (hvInf : ∀ t ∈ J, ContDiff ℝ 2 (vInf t))
    (hDv : TendstoUniformlyOn (fun i (q : ℝ × ℝ) => fderiv ℝ (v i q.2) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (vInf q.2) q.1) l (Icc (0 : ℝ) c ×ˢ J))
    (hD₂v : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ (fderiv ℝ (v i q.2)) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fderiv ℝ (vInf q.2)) q.1)
      l (Icc (0 : ℝ) c ×ˢ J))
    (z : P → ℝ → ℝ × (Q →L[ℝ] ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p ∈ K, ∀ t ∈ J, ‖(z p t).2‖ ≤ B) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => fderiv ℝ (paramTangentVF Q (v i) q.2) (z q.1 q.2))
      (fun q : P × ℝ => fderiv ℝ (paramTangentVF Q vInf q.2) (z q.1 q.2))
      l (K ×ˢ J) := by
  have hpD : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (fderiv ℝ (v i t)) c := by
    filter_upwards [hper] with i hi
    exact fun t ht => (hi t ht).fderiv (𝕜 := ℝ)
  have hpDInf : ∀ t ∈ J, Function.Periodic (fderiv ℝ (vInf t)) c :=
    fun t ht => (hperInf t ht).fderiv (𝕜 := ℝ)
  have hpD₂ : ∀ᶠ i in l, ∀ t ∈ J,
      Function.Periodic (fderiv ℝ (fderiv ℝ (v i t))) c := by
    filter_upwards [hpD] with i hi
    exact fun t ht => (hi t ht).fderiv (𝕜 := ℝ)
  have hpD₂Inf : ∀ t ∈ J, Function.Periodic (fderiv ℝ (fderiv ℝ (vInf t))) c :=
    fun t ht => (hpDInf t ht).fderiv (𝕜 := ℝ)
  apply paramTangentVF_tendstoUniformlyOn_fderiv z hB hz
  · filter_upwards [hv] with i hi
    intro p _ t ht
    exact ⟨((hi t ht).differentiable (by norm_num)).differentiableAt,
      (((hi t ht).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)).differentiableAt⟩
  · intro p _ t ht
    exact ⟨((hvInf t ht).differentiable (by norm_num)).differentiableAt,
      (((hvInf t ht).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)).differentiableAt⟩
  · exact Function.Periodic.tendstoUniformlyOn_comp_of_Icc hc hpD hpDInf hDv
      (fun p t => (z p t).1)
  · exact Function.Periodic.tendstoUniformlyOn_comp_of_Icc hc hpD₂ hpD₂Inf hD₂v
      (fun p t => (z p t).1)

end DifferentialGeometry.Analysis.ODE.Flow
