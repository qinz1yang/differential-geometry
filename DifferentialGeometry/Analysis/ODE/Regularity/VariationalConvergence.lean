import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Analysis.Calculus.Periodic.Derivative
import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointJets
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

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set
open scoped ContDiff NNReal

theorem paramTangentCurve_tendstoUniformlyOn_of_periodic
    {ι : Type*} {l : Filter ι} {a b : ℝ} (hab : a ≤ b)
    {K : Set ℝ} (hK : IsCompact K)
    {v : ι → ℝ → ℝ → ℝ} {vInf : ℝ → ℝ → ℝ}
    (hvjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (v i)) (Icc a b ×ˢ univ))
    (hvInfJoint : ContDiffOn ℝ ∞ (Function.uncurry vInf) (Icc a b ×ˢ univ))
    (hper : ∀ i t, t ∈ Icc a b → Function.Periodic (v i t) 1)
    (hperInf : ∀ t ∈ Icc a b, Function.Periodic (vInf t) 1)
    {γ : ι → ℝ → ℝ → ℝ} {γInf : ℝ → ℝ → ℝ}
    (hγjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b))
    (hγInfJoint : ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b))
    (hγ : ∀ i x, γ i x a = x ∧ IsIntegralCurveOn (γ i x) (v i) (Icc a b))
    (hγInf : ∀ x, γInf x a = x ∧ IsIntegralCurveOn (γInf x) vInf (Icc a b))
    (hv : TendstoUniformlyOn (fun i (q : ℝ × ℝ) => v i q.2 q.1)
      (fun q : ℝ × ℝ => vInf q.2 q.1) l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hDv : TendstoUniformlyOn (fun i (q : ℝ × ℝ) => fderiv ℝ (v i q.2) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (vInf q.2) q.1) l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hD₂v : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ (fderiv ℝ (v i q.2)) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fderiv ℝ (vInf q.2)) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => paramTangentCurve (γ i) q.1 q.2)
      (fun q : ℝ × ℝ => paramTangentCurve γInf q.1 q.2) l (K ×ˢ Icc a b) := by
  have hslice (i : ι) (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (v i t) := by
    apply contDiffOn_univ.mp
    exact (hvjoint i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)
  have hsliceInf (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (vInf t) := by
    apply contDiffOn_univ.mp
    exact hvInfJoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)
  have htan (i : ι) := paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn
    isOpen_univ isOpen_univ hab
    (fun t ht => (hslice i t ht).differentiable (by simp) |>.differentiableOn)
    (hγjoint i) (fun x _ => hγ i x) (fun _ _ _ _ => mem_univ _)
  have htanInf := paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn
    isOpen_univ isOpen_univ hab
    (fun t ht => (hsliceInf t ht).differentiable (by simp) |>.differentiableOn)
    hγInfJoint (fun x _ => hγInf x) (fun _ _ _ _ => mem_univ _)
  rcases hab.eq_or_lt with rfl | hab
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with i
    intro q hq
    have ht : q.2 = a := by simpa only [Icc_self, mem_singleton_iff] using hq.2
    rw [ht, (htan i q.1 (mem_univ _)).1, (htanInf q.1 (mem_univ _)).1, dist_self]
    exact hε
  · have hJ : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
    obtain ⟨B, hB, hbound⟩ := exists_pos_bound_paramTangentCurve isOpen_univ hK
      (subset_univ K) hJ isCompact_Icc hγInfJoint
    have hZ : ∀ x ∈ K, ∀ t ∈ Icc a b,
        ‖(paramTangentCurve γInf x t).2‖ ≤ B := by
      intro x hx t ht
      exact (norm_snd_le _).trans (hbound x hx t ht)
    have hDInf := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      hJ isOpen_univ hvInfJoint
    have hD₂Inf := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      hJ isOpen_univ hDInf
    have hDcont : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ (vInf q.2) q.1)
        (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
      hDInf.continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun q hq => ⟨hq.2, mem_univ _⟩)
    have hD₂cont : ContinuousOn
        (fun q : ℝ × ℝ => fderiv ℝ (fderiv ℝ (vInf q.2)) q.1)
        (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
      hD₂Inf.continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun q hq => ⟨hq.2, mem_univ _⟩)
    obtain ⟨C₀, hC₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hDcont
    obtain ⟨C₁, hC₁⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hD₂cont
    let L₀ : ℝ≥0 := ⟨max C₀ 0 + 1, by positivity⟩
    let L₁ : ℝ≥0 := ⟨max C₁ 0 + 1, by positivity⟩
    have hcoeff : ∀ᶠ i in l, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (v i t) x‖ ≤ (L₀ : ℝ) ∧
          ‖fderiv ℝ (fderiv ℝ (v i t)) x‖ ≤ (L₁ : ℝ) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hDv 1 zero_lt_one,
        Metric.tendstoUniformlyOn_iff.mp hD₂v 1 zero_lt_one] with i hi hi₂
      intro t ht x hx
      constructor
      · have hd : dist (fderiv ℝ (v i t) x) (fderiv ℝ (vInf t) x) ≤ 1 :=
          (dist_comm _ _).trans_le (hi (x, t) ⟨hx, ht⟩).le
        exact (norm_le_norm_add_const_of_dist_le hd).trans
          (add_le_add ((hC₀ (x, t) ⟨hx, ht⟩).trans (le_max_left C₀ 0)) le_rfl)
      · have hd : dist (fderiv ℝ (fderiv ℝ (v i t)) x)
            (fderiv ℝ (fderiv ℝ (vInf t)) x) ≤ 1 :=
          (dist_comm _ _).trans_le (hi₂ (x, t) ⟨hx, ht⟩).le
        exact (norm_le_norm_add_const_of_dist_le hd).trans
          (add_le_add ((hC₁ (x, t) ⟨hx, ht⟩).trans (le_max_left C₁ 0)) le_rfl)
    have hLip := paramTangentVF_eventually_lipschitzOnWith_closedBall_of_periodic
      (paramTangentCurve γInf) 1 (⟨B, hB.le⟩ : ℝ≥0) L₀ L₁ zero_lt_one
      (Eventually.of_forall hper)
      (Eventually.of_forall fun i t ht =>
        (show ContDiff ℝ 2 (v i t) from (hslice i t ht).of_le
          (WithTop.coe_le_coe.mpr le_top))) hcoeff hZ
    have hfield := paramTangentVF_tendstoUniformlyOn_of_periodic zero_lt_one
      hper hperInf hv hDv (paramTangentCurve γInf) hB.le hZ
    have hinit : TendstoUniformlyOn
        (fun i x => paramTangentCurve (γ i) x a)
        (fun x => paramTangentCurve γInf x a) l K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [] with i
      intro x _
      rw [(htan i x (mem_univ _)).1, (htanInf x (mem_univ _)).1, dist_self]
      exact hε
    apply integralCurve_tendstoUniformlyOn_of_limit_tube hab.le zero_lt_one
      (fun i x _ => (htan i x (mem_univ _)).2)
      (fun x _ => (htanInf x (mem_univ _)).2) hinit hfield
    refine ⟨max L₀ (L₁ * (⟨B, hB.le⟩ + 1) + L₀), ?_⟩
    filter_upwards [hLip] with i hi
    intro x hx t ht
    exact hi x hx t ⟨ht.1, ht.2.le⟩

end DifferentialGeometry.Analysis.ODE.Flow

noncomputable section

open Filter Metric Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {Q X : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem spatialJetPrefix_paramTangentVF_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} (n : ℕ) {J : Set ℝ} (hJ : IsCompact J)
    {C : Set (X × (Q →L[ℝ] X))} (hC : IsCompact C)
    {v : ι → ℝ → X → X} {vInf : ℝ → X → X}
    (hv : ∀ i t, t ∈ J → ContDiff ℝ (n + 1) (v i t))
    (hvInf : ∀ t ∈ J, ContDiff ℝ (n + 1) (vInf t))
    (hcInf : ∀ k ≤ n + 1, ContinuousOn
      (fun q : X × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1)
      ((Prod.fst '' C) ×ˢ J))
    (hconv : ∀ k ≤ n + 1, TendstoUniformlyOn
      (fun i (q : X × ℝ) => iteratedFDeriv ℝ k (v i q.2) q.1)
      (fun q : X × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1)
      l ((Prod.fst '' C) ×ˢ J)) :
    TendstoUniformlyOn
      (fun i (q : (X × (Q →L[ℝ] X)) × ℝ) =>
        spatialJetPrefix n (paramTangentVF Q (v i) q.2) q.1)
      (fun q : (X × (Q →L[ℝ] X)) × ℝ =>
        spatialJetPrefix n (paramTangentVF Q vInf q.2) q.1) l (C ×ˢ J) := by
  let Y := X × (Q →L[ℝ] X)
  let A := (i : Fin (n + 2)) → X [×i.val]→L[ℝ] X
  let F (i : ι) (q : Y × ℝ) : A × Y :=
    (spatialJetPrefix (n + 1) (v i q.2) q.1.1, q.1)
  let FInf (q : Y × ℝ) : A × Y :=
    (spatialJetPrefix (n + 1) (vInf q.2) q.1.1, q.1)
  have hF : TendstoUniformlyOn F FInf l (C ×ˢ J) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hall : ∀ᶠ i in l, ∀ k : Fin (n + 2), ∀ q ∈ ((Prod.fst '' C) ×ˢ J),
        dist (iteratedFDeriv ℝ k.val (vInf q.2) q.1)
          (iteratedFDeriv ℝ k.val (v i q.2) q.1) < ε :=
      Filter.eventually_all.mpr fun k => Metric.tendstoUniformlyOn_iff.mp
        (hconv k.val (by omega)) ε hε
    filter_upwards [hall] with i hi
    intro q hq
    dsimp only [FInf, F]
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    apply (dist_pi_lt_iff hε).mpr
    intro k
    exact hi k (q.1.1, q.2) ⟨⟨q.1, hq.1, rfl⟩, hq.2⟩
  have hFInf : ContinuousOn FInf (C ×ˢ J) := by
    apply ContinuousOn.prodMk ?_ continuousOn_fst
    apply continuousOn_spatialJetPrefix
    intro k hk
    exact (hcInf k hk).comp
      ((continuous_fst.fst.prodMk continuous_snd).continuousOn)
      (fun q hq => ⟨⟨q.1, hq.1, rfl⟩, hq.2⟩)
  let D : Set (A × Y) := FInf '' (C ×ˢ J)
  have hD : IsCompact D := (hC.prod hJ).image_of_continuousOn hFInf
  obtain ⟨T, hT, hTeq⟩ := exists_continuous_spatialJetPrefix_paramTangentVF (Q := Q) (X := X) n
  have hcomp : TendstoUniformlyOn (fun i q => T (F i q)) (fun q => T (FInf q))
      l (C ×ˢ J) := by
    intro V hV
    have hnear := hD.uniformContinuousAt_of_continuousAt T
      (fun _ _ => hT.continuousAt) hV
    filter_upwards [hF _ hnear] with i hi
    intro q hq
    exact hi q hq ⟨q, hq, rfl⟩
  apply (hcomp.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
    (fun q hq => ?_)
  · exact hTeq (v i) q.2 (hv i q.2 hq.2) q.1
  · exact hTeq vInf q.2 (hvInf q.2 hq.2) q.1

end DifferentialGeometry.Analysis.ODE.Flow

end

noncomputable section

open Filter Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

private theorem continuousOn_spatialJetPrefix_paramTangentVF
    {Q X : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) {J : Set ℝ} {C : Set (X × (Q →L[ℝ] X))}
    {v : ℝ → X → X} (hv : ∀ t ∈ J, ContDiff ℝ (n + 1) (v t))
    (hc : ∀ k ≤ n + 1, ContinuousOn
      (fun q : X × ℝ => iteratedFDeriv ℝ k (v q.2) q.1) ((Prod.fst '' C) ×ˢ J)) :
    ContinuousOn (fun q : (X × (Q →L[ℝ] X)) × ℝ =>
      spatialJetPrefix n (paramTangentVF Q v q.2) q.1) (C ×ˢ J) := by
  obtain ⟨T, hT, hTeq⟩ := exists_continuous_spatialJetPrefix_paramTangentVF (Q := Q) (X := X) n
  have hF : ContinuousOn
      (fun q : (X × (Q →L[ℝ] X)) × ℝ =>
        (spatialJetPrefix (n + 1) (v q.2) q.1.1, q.1)) (C ×ˢ J) := by
    apply ContinuousOn.prodMk ?_ continuousOn_fst
    apply continuousOn_spatialJetPrefix
    intro k hk
    exact (hc k hk).comp ((continuous_fst.fst.prodMk continuous_snd).continuousOn)
      (fun q hq => ⟨⟨q.1, hq.1, rfl⟩, hq.2⟩)
  exact (hT.comp_continuousOn hF).congr fun q hq =>
    (hTeq v q.2 (hv q.2 hq.2) q.1).symm

private theorem iteratedFDeriv_paramTangentInitial_tendstoUniformlyOn
    {ι P X : Type*} {l : Filter ι}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ι → P → X} {fInf : P → X} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfInf : ContDiff ℝ ∞ fInf) {K : Set P} (n : ℕ)
    (h₀ : TendstoUniformlyOn (fun i p => iteratedFDeriv ℝ n (f i) p)
      (fun p => iteratedFDeriv ℝ n fInf p) l K)
    (h₁ : TendstoUniformlyOn (fun i p => iteratedFDeriv ℝ (n + 1) (f i) p)
      (fun p => iteratedFDeriv ℝ (n + 1) fInf p) l K) :
    TendstoUniformlyOn
      (fun i p => iteratedFDeriv ℝ n (paramTangentInitial (f i)) p)
      (fun p => iteratedFDeriv ℝ n (paramTangentInitial fInf) p) l K := by
  have hDf (i : ι) : ContDiff ℝ ∞ (fderiv ℝ (f i)) :=
    (hf i).fderiv_right (by rw [ENat.coe_top_add_one])
  have hDfInf : ContDiff ℝ ∞ (fderiv ℝ fInf) :=
    hfInf.fderiv_right (by rw [ENat.coe_top_add_one])
  rw [Metric.tendstoUniformlyOn_iff] at h₀ h₁ ⊢
  intro ε hε
  filter_upwards [h₀ ε hε, h₁ ε hε] with i hi hi₁
  intro p hp
  have hs : iteratedFDeriv ℝ n (paramTangentInitial (f i)) p =
      (iteratedFDeriv ℝ n (f i) p).prod (iteratedFDeriv ℝ n (fderiv ℝ (f i)) p) := by
    exact iteratedFDeriv_prodMk (hf i).contDiffAt (hDf i).contDiffAt
      (by exact_mod_cast le_top)
  have hl : iteratedFDeriv ℝ n (paramTangentInitial fInf) p =
      (iteratedFDeriv ℝ n fInf p).prod (iteratedFDeriv ℝ n (fderiv ℝ fInf) p) := by
    exact iteratedFDeriv_prodMk hfInf.contDiffAt hDfInf.contDiffAt
      (by exact_mod_cast le_top)
  have hd := hi₁ p hp
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.dist_map] at hd
  rw [hl, hs]
  change dist ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => P) X (P →L[ℝ] X))
      (iteratedFDeriv ℝ n fInf p, iteratedFDeriv ℝ n (fderiv ℝ fInf) p))
    ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => P) X (P →L[ℝ] X))
      (iteratedFDeriv ℝ n (f i) p, iteratedFDeriv ℝ n (fderiv ℝ (f i)) p)) < ε
  rw [LinearIsometryEquiv.dist_map, Prod.dist_eq]
  exact max_lt (hi p hp) hd

universe uP uX

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

theorem iteratedFDeriv_integralCurve_tendstoUniformlyOn
    (n : ℕ) {X : Type (max uP uX)}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι : Type*} {l : Filter ι} {a b : ℝ} (hab : a ≤ b)
    {v : ι → ℝ → X → X} {vInf : ℝ → X → X}
    (hv : ∀ i t, t ∈ Icc a b → ContDiff ℝ ∞ (v i t))
    (hvInf : ∀ t ∈ Icc a b, ContDiff ℝ ∞ (vInf t))
    (hcInf : ∀ k : ℕ, ContinuousOn
      (fun q : X × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1) (univ ×ˢ Icc a b))
    (hconv : ∀ C : Set X, IsCompact C → ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : X × ℝ) => iteratedFDeriv ℝ k (v i q.2) q.1)
      (fun q : X × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1) l (C ×ˢ Icc a b))
    {γ : ι → P → ℝ → X} {γInf : P → ℝ → X}
    (hγjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b))
    (hγInfJoint : ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b))
    (hγ : ∀ i p, IsIntegralCurveOn (γ i p) (v i) (Icc a b))
    (hγInf : ∀ p, IsIntegralCurveOn (γInf p) vInf (Icc a b))
    {K : Set P} (hK : IsCompact K)
    (hinit : ∀ k : ℕ, TendstoUniformlyOn
      (fun i p => iteratedFDeriv ℝ k (fun x => γ i x a) p)
      (fun p => iteratedFDeriv ℝ k (fun x => γInf x a) p) l K) :
    TendstoUniformlyOn
      (fun i (q : P × ℝ) => iteratedFDeriv ℝ n (fun p => γ i p q.2) q.1)
      (fun q : P × ℝ => iteratedFDeriv ℝ n (fun p => γInf p q.2) q.1)
      l (K ×ˢ Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hinit n) ε hε] with i hi
    intro q hq
    have ht : q.2 = a := by simpa only [Icc_self, mem_singleton_iff] using hq.2
    simpa only [ht] using hi q.1 hq.1
  induction n generalizing X with
  | zero =>
      have hzero (f : X → X) (x : X) :
          continuousMultilinearCurryFin0 ℝ X X (iteratedFDeriv ℝ 0 f x) = f x := rfl
      have hone (f : X → X) (x : X) :
          continuousMultilinearCurryFin1 ℝ X X (iteratedFDeriv ℝ 1 f x) =
            fderiv ℝ f x := by
        ext z
        simp
      have hv₀ (C : Set X) (hC : IsCompact C) : TendstoUniformlyOn
          (fun i (q : X × ℝ) => v i q.2 q.1)
          (fun q : X × ℝ => vInf q.2 q.1) l (C ×ˢ Icc a b) := by
        have hh := (continuousMultilinearCurryFin0 ℝ X X).isometry.uniformContinuous.comp_tendstoUniformlyOn
          (hconv C hC 0)
        simpa only [Function.comp_def, hzero] using hh
      have hv₁ (C : Set X) (hC : IsCompact C) : TendstoUniformlyOn
          (fun i (q : X × ℝ) => fderiv ℝ (v i q.2) q.1)
          (fun q : X × ℝ => fderiv ℝ (vInf q.2) q.1) l (C ×ˢ Icc a b) := by
        have hh := (continuousMultilinearCurryFin1 ℝ X X).isometry.uniformContinuous.comp_tendstoUniformlyOn
          (hconv C hC 1)
        simpa only [Function.comp_def, hone] using hh
      have hdInf : ContinuousOn (fun q : X × ℝ => fderiv ℝ (vInf q.2) q.1)
          (univ ×ˢ Icc a b) := by
        have hh := (continuousMultilinearCurryFin1 ℝ X X).continuous.comp_continuousOn
          (hcInf 1)
        simpa only [Function.comp_def, hone] using hh
      have hi₀ : TendstoUniformlyOn (fun i p => γ i p a) (fun p => γInf p a) l K := by
        have hh := (continuousMultilinearCurryFin0 ℝ P X).isometry.uniformContinuous.comp_tendstoUniformlyOn
          (hinit 0)
        exact hh
      have hraw := integralCurve_tendstoUniformlyOn_of_fderiv_compact hab.le hK
        (fun i p _ => hγ i p) (fun p _ => hγInf p)
        (hγInfJoint.continuousOn.mono (prod_mono (subset_univ K) Subset.rfl))
        (Eventually.of_forall fun i t ht => (hv i t ht).differentiable (by simp))
        hdInf hi₀ hv₀ hv₁
      have hh := (continuousMultilinearCurryFin0 ℝ P X).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hraw
      exact hh
  | succ n ih =>
      have hJ : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
      have hs (i : ι) (t : ℝ) (ht : t ∈ Icc a b) :
          ContDiff ℝ ∞ (fun p => γ i p t) := by
        apply contDiffOn_univ.mp
        exact (hγjoint i).comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p _ => ⟨mem_univ p, ht⟩)
      have hsInf (t : ℝ) (ht : t ∈ Icc a b) :
          ContDiff ℝ ∞ (fun p => γInf p t) := by
        apply contDiffOn_univ.mp
        exact hγInfJoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p _ => ⟨mem_univ p, ht⟩)
      have hvTan (i : ι) (t : ℝ) (ht : t ∈ Icc a b) :
          ContDiff ℝ ∞ (paramTangentVF P (v i) t) := by
        have hd : ContDiff ℝ ∞ (fderiv ℝ (v i t)) :=
          (hv i t ht).fderiv_right (by rw [ENat.coe_top_add_one])
        exact ((hv i t ht).comp contDiff_fst).prodMk
          ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff.comp
            ((hd.comp contDiff_fst).prodMk contDiff_snd))
      have hvInfTan (t : ℝ) (ht : t ∈ Icc a b) :
          ContDiff ℝ ∞ (paramTangentVF P vInf t) := by
        have hd : ContDiff ℝ ∞ (fderiv ℝ (vInf t)) :=
          (hvInf t ht).fderiv_right (by rw [ENat.coe_top_add_one])
        exact ((hvInf t ht).comp contDiff_fst).prodMk
          ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff.comp
            ((hd.comp contDiff_fst).prodMk contDiff_snd))
      have hcInfTan (k : ℕ) : ContinuousOn
          (fun q : (X × (P →L[ℝ] X)) × ℝ =>
            iteratedFDeriv ℝ k (paramTangentVF P vInf q.2) q.1) (univ ×ˢ Icc a b) := by
        have hh := continuousOn_spatialJetPrefix_paramTangentVF (Q := P)
          (C := univ) k (fun t ht => (hvInf t ht).of_le (by exact_mod_cast le_top))
          (fun j _ => (hcInf j).mono (prod_mono (subset_univ _) Subset.rfl))
        exact (continuous_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp_continuousOn hh
      have hconvTan (C : Set (X × (P →L[ℝ] X))) (hC : IsCompact C) (k : ℕ) :
          TendstoUniformlyOn
            (fun i (q : (X × (P →L[ℝ] X)) × ℝ) =>
              iteratedFDeriv ℝ k (paramTangentVF P (v i) q.2) q.1)
            (fun q : (X × (P →L[ℝ] X)) × ℝ =>
              iteratedFDeriv ℝ k (paramTangentVF P vInf q.2) q.1) l (C ×ˢ Icc a b) := by
        have hh := spatialJetPrefix_paramTangentVF_tendstoUniformlyOn (Q := P) k isCompact_Icc hC
          (fun i t ht => (hv i t ht).of_le (by exact_mod_cast le_top))
          (fun t ht => (hvInf t ht).of_le (by exact_mod_cast le_top))
          (fun j _ => (hcInf j).mono (prod_mono (subset_univ _) Subset.rfl))
          (fun j _ => hconv (Prod.fst '' C) (hC.image continuous_fst) j)
        exact (ContinuousLinearMap.proj (R := ℝ)
          (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).uniformContinuous.comp_tendstoUniformlyOn hh
      have hγTan (i : ι) (p : P) : IsIntegralCurveOn (paramTangentCurve (γ i) p)
          (paramTangentVF P (v i)) (Icc a b) :=
        (paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn isOpen_univ isOpen_univ hab.le
          (fun t ht => (hv i t ht).differentiable (by simp) |>.differentiableOn)
          (hγjoint i) (fun p _ => ⟨rfl, hγ i p⟩)
          (fun _ _ _ _ => mem_univ _) p (mem_univ p)).2
      have hγInfTan (p : P) : IsIntegralCurveOn (paramTangentCurve γInf p)
          (paramTangentVF P vInf) (Icc a b) :=
        (paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn isOpen_univ isOpen_univ hab.le
          (fun t ht => (hvInf t ht).differentiable (by simp) |>.differentiableOn)
          hγInfJoint (fun p _ => ⟨rfl, hγInf p⟩)
          (fun _ _ _ _ => mem_univ _) p (mem_univ p)).2
      have hinitTan (k : ℕ) : TendstoUniformlyOn
          (fun i p => iteratedFDeriv ℝ k (fun x => paramTangentCurve (γ i) x a) p)
          (fun p => iteratedFDeriv ℝ k (fun x => paramTangentCurve γInf x a) p) l K :=
        iteratedFDeriv_paramTangentInitial_tendstoUniformlyOn
          (fun i => hs i a (left_mem_Icc.mpr hab.le))
          (hsInf a (left_mem_Icc.mpr hab.le)) k (hinit k) (hinit (k + 1))
      have hTan := ih hvTan hvInfTan hcInfTan hconvTan
        (fun i => paramTangentCurve_contDiffOn isOpen_univ hJ (hγjoint i))
        (paramTangentCurve_contDiffOn isOpen_univ hJ hγInfJoint)
        hγTan hγInfTan hinitTan
      rw [Metric.tendstoUniformlyOn_iff] at hTan ⊢
      intro ε hε
      filter_upwards [hTan ε hε] with i hi
      intro q hq
      have hd := hi q hq
      have hds := (hs i q.2 hq.2).fderiv_right
        (m := ∞) (by rw [ENat.coe_top_add_one])
      have hdl := (hsInf q.2 hq.2).fderiv_right
        (m := ∞) (by rw [ENat.coe_top_add_one])
      have heqs : iteratedFDeriv ℝ n (fun p => paramTangentCurve (γ i) p q.2) q.1 =
          (iteratedFDeriv ℝ n (fun p => γ i p q.2) q.1).prod
            (iteratedFDeriv ℝ n (fderiv ℝ (fun p => γ i p q.2)) q.1) :=
        iteratedFDeriv_prodMk (hs i q.2 hq.2).contDiffAt hds.contDiffAt
          (by exact_mod_cast le_top)
      have heql : iteratedFDeriv ℝ n (fun p => paramTangentCurve γInf p q.2) q.1 =
          (iteratedFDeriv ℝ n (fun p => γInf p q.2) q.1).prod
            (iteratedFDeriv ℝ n (fderiv ℝ (fun p => γInf p q.2)) q.1) :=
        iteratedFDeriv_prodMk (hsInf q.2 hq.2).contDiffAt hdl.contDiffAt
          (by exact_mod_cast le_top)
      rw [heql, heqs] at hd
      change dist ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => P) X (P →L[ℝ] X))
          (iteratedFDeriv ℝ n (fun p => γInf p q.2) q.1,
            iteratedFDeriv ℝ n (fderiv ℝ (fun p => γInf p q.2)) q.1))
        ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => P) X (P →L[ℝ] X))
          (iteratedFDeriv ℝ n (fun p => γ i p q.2) q.1,
            iteratedFDeriv ℝ n (fderiv ℝ (fun p => γ i p q.2)) q.1)) < ε at hd
      rw [LinearIsometryEquiv.dist_map, Prod.dist_eq] at hd
      simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.dist_map] using (lt_of_le_of_lt (le_max_right _ _) hd)

end DifferentialGeometry.Analysis.ODE.Flow

end

noncomputable section

open Filter Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

theorem iteratedFDeriv_integralCurve_tendstoUniformlyOn_of_periodic
    {ι : Type*} {l : Filter ι} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    {v : ι → ℝ → ℝ → ℝ} {vInf : ℝ → ℝ → ℝ}
    (hvjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (v i)) (Icc a b ×ˢ univ))
    (hvInfJoint : ContDiffOn ℝ ∞ (Function.uncurry vInf) (Icc a b ×ˢ univ))
    (hper : ∀ i t, t ∈ Icc a b → Function.Periodic (v i t) c)
    (hperInf : ∀ t ∈ Icc a b, Function.Periodic (vInf t) c)
    {γ : ι → ℝ → ℝ → ℝ} {γInf : ℝ → ℝ → ℝ}
    (hγjoint : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b))
    (hγInfJoint : ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b))
    (hγ : ∀ i x, γ i x a = x ∧ IsIntegralCurveOn (γ i x) (v i) (Icc a b))
    (hγInf : ∀ x, γInf x a = x ∧ IsIntegralCurveOn (γInf x) vInf (Icc a b))
    (hconv : ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (v i q.2) q.1)
      (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1)
      l (Icc (0 : ℝ) c ×ˢ Icc a b))
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ n (fun x => γ i x q.2) q.1)
      (fun q : ℝ × ℝ => iteratedFDeriv ℝ n (fun x => γInf x q.2) q.1)
      l (K ×ˢ Icc a b) := by
  have hi (i : ι) : (fun x => γ i x a) = id := funext fun x => (hγ i x).1
  have hiInf : (fun x => γInf x a) = id := funext fun x => (hγInf x).1
  rcases hab.eq_or_lt with rfl | hab
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with i
    intro q hq
    have ht : q.2 = a := by simpa only [Icc_self, mem_singleton_iff] using hq.2
    rw [ht, hi i, hiInf, dist_self]
    exact hε
  · have hslice (i : ι) (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (v i t) := by
      apply contDiffOn_univ.mp
      exact (hvjoint i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hsliceInf (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (vInf t) := by
      apply contDiffOn_univ.mp
      exact hvInfJoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hcInf (k : ℕ) : ContinuousOn
        (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1) (univ ×ˢ Icc a b) :=
      (DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn
        isOpen_univ hvInfJoint k).continuousOn.comp
          (continuous_snd.prodMk continuous_fst).continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
    have hconvAll (C : Set ℝ) (k : ℕ) : TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (v i q.2) q.1)
        (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (vInf q.2) q.1)
        l (C ×ˢ Icc a b) := by
      exact Function.Periodic.tendstoUniformlyOn_comp_of_Icc hc
        (Eventually.of_forall fun i t ht => (hper i t ht).iteratedFDeriv (𝕜 := ℝ) k)
        (fun t ht => (hperInf t ht).iteratedFDeriv (𝕜 := ℝ) k) (hconv k) (fun x _ => x)
    have hinit (k : ℕ) : TendstoUniformlyOn
        (fun i x => iteratedFDeriv ℝ k (fun y => γ i y a) x)
        (fun x => iteratedFDeriv ℝ k (fun y => γInf y a) x) l K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [] with i
      intro x _
      rw [hi i, hiInf, dist_self]
      exact hε
    exact iteratedFDeriv_integralCurve_tendstoUniformlyOn n hab.le hslice hsliceInf hcInf
      (fun C _ k => hconvAll C k) hγjoint hγInfJoint (fun i x => (hγ i x).2) (fun x => (hγInf x).2) hK hinit

end DifferentialGeometry.Analysis.ODE.Flow

end
