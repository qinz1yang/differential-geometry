import DifferentialGeometry.Analysis.Elliptic.WeightedTensorMinimum
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialGrowth
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialIntegralCurve
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Reciprocal
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ScalarRigidity
import DifferentialGeometry.Geometry.Metric.RicciSoliton.WeightedRicci
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v) (x : M) :
    0 < f x := by
  have hf_nonneg := normalizedGradientRicciSoliton_potential_nonneg (I := I) h x
  by_contra hnot
  have hf_zero : f x = 0 := le_antisymm (le_of_not_gt hnot) hf_nonneg
  have hscalar_nonneg := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h x
  have hgrad_nonneg :
      0 ≤ g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
    simpa only [normGradSqFun_def] using
      normGradSqFun_nonneg (I := I) g (f : M → Real) x
  have hpotential := normalizedGradientRicciSoliton_potential_equation (I := I) h x
  have hscalar_zero : metricScalarAt (I := I) g x = 0 := by
    linarith
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  let L := tangentSpaceModelContinuousLinearEquiv (I := I) x
  let v : TangentSpace I x := L.symm e
  have hv : v ≠ 0 := by
    intro hvzero
    have hLe := congrArg L hvzero
    have hleft : L v = e := by
      change L (L.symm e) = e
      exact L.apply_symm_apply e
    have hright : L (0 : TangentSpace I x) = 0 := map_zero L
    exact he (hleft.symm.trans (hLe.trans hright))
  have hzero := normalizedGradientRicciSoliton_ricciTensor_eq_zero_of_scalar_eq_zero
    (I := I) h hscalar_zero x v v
  have hpositive := hRic x v hv
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

theorem normalizedGradientRicciSoliton_exists_ricci_reciprocalPotentialBarrier_lower_on_sublevel
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v)
    (p : M) (F : Real) (hp : f p ≤ F) :
    ∃ c : Real, 0 < c ∧ ∀ (x : M), f x ≤ F → ∀ v : TangentSpace I x,
      c * reciprocalPotentialBarrier (I := I) f
          (normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
            (I := I) h hRic) x * g.inner x v v ≤
        ricciTensor (I := I) g x v v := by
  classical
  let hpos : ∀ x : M, 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
      (I := I) h hRic
  let B : C^∞⟮I, M; Real⟯ := reciprocalPotentialBarrier (I := I) f hpos
  let K : Set M := {x | f x ≤ F}
  have hK_eq : K = (f : M → Real) ⁻¹' Set.Icc 0 F := by
    ext x
    simp only [K, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    exact (and_iff_right (hpos x).le).symm
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    exact (normalizedGradientRicciSoliton_potential_isProperMap (I := I) h).isCompact_preimage
      isCompact_Icc
  have hpK : p ∈ K := hp
  have hBpos (x : M) : 0 < B x := by
    change 0 < f x ^ (-1 : Real) + (Module.finrank Real E : Real) * f x ^ (-2 : Real)
    have h1 : 0 < f x ^ (-1 : Real) := Real.rpow_pos_of_pos (hpos x) _
    have h2 : 0 < f x ^ (-2 : Real) := Real.rpow_pos_of_pos (hpos x) _
    have hn : 0 ≤ (Module.finrank Real E : Real) := by positivity
    positivity
  obtain ⟨z, hzK, hzmax⟩ :=
    hKcompact.exists_isMaxOn ⟨p, hpK⟩ B.contMDiff.continuous.continuousOn
  have hRicQuad : ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x), v ≠ 0 →
      0 < quad02 (I := I) (M := M)
        (metricRicci (I := I) (M := M) g x) v := by
    intro x _hx v hv
    have hslots : (fun _ : Fin 2 => v) = vec2 (I := I) v v := by
      funext i
      fin_cases i <;> rfl
    change 0 < metricRicciAt (I := I) (M := M) g x (fun _ : Fin 2 => v)
    rw [hslots, metricRicciAt_apply_eq_ricciTensor]
    exact hRic x v hv
  obtain ⟨a, ha, haLower⟩ :=
    tensor02_lower_on_of_positive_definite
      (I := I) (M := M) hKcompact g
      (metricRicci (I := I) (M := M) g) hRicQuad
  let c : Real := a / B z
  have hc : 0 < c := div_pos ha (hBpos z)
  refine ⟨c, hc, ?_⟩
  intro x hx v
  have hxK : x ∈ K := hx
  have hB_le : B x ≤ B z := hzmax hxK
  have hcoef : c * B x ≤ a := by
    have hmul : c * B x ≤ c * B z :=
      mul_le_mul_of_nonneg_left hB_le hc.le
    have hcancel : c * B z = a := by
      dsimp only [c]
      exact div_mul_cancel₀ a (hBpos z).ne'
    exact hmul.trans_eq hcancel
  have hg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (g.pos x v hv).le
  have hscaled : c * B x * g.inner x v v ≤ a * g.inner x v v :=
    mul_le_mul_of_nonneg_right hcoef hg
  have hquad := hscaled.trans (haLower x hxK v)
  have hslots : (fun _ : Fin 2 => v) = vec2 (I := I) v v := by
    funext i
    fin_cases i <;> rfl
  change c * B x * g.inner x v v ≤
    metricRicciAt (I := I) (M := M) g x (fun _ : Fin 2 => v) at hquad
  rw [hslots, metricRicciAt_apply_eq_ricciTensor] at hquad
  simpa [B, hpos] using hquad

theorem normalizedGradientRicciSoliton_exists_ricci_reciprocalPotentialBarrier_lower
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hsec : ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v) :
    ∃ c : Real, 0 < c ∧ ∀ (x : M) (v : TangentSpace I x),
      c * reciprocalPotentialBarrier (I := I) f
          (normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
            (I := I) h hRic) x * g.inner x v v ≤
        ricciTensor (I := I) g x v v := by
  classical
  let hpos : ∀ x : M, 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
      (I := I) h hRic
  let B : C^∞⟮I, M; Real⟯ := reciprocalPotentialBarrier (I := I) f hpos
  let n : Real := Module.finrank Real E
  let p : M := Classical.choice (inferInstance : Nonempty M)
  let F : Real := max (f p) (2 * n + 1)
  have hpF : f p ≤ F := le_max_left _ _
  obtain ⟨c, hc, hcK⟩ :=
    normalizedGradientRicciSoliton_exists_ricci_reciprocalPotentialBarrier_lower_on_sublevel
      (I := I) h hRic p F hpF
  refine ⟨c, hc, ?_⟩
  by_contra hbound
  simp only [not_forall, not_le] at hbound
  obtain ⟨y, w, hyw⟩ := hbound
  let cB : C^∞⟮I, M; Real⟯ := c • B
  let metric := metricTensorField (I := I) g
  let U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    tensor0SFieldSmulByFun (I := I) (n := (∞ : WithTop ℕ∞)) (s := 2)
      (cB : M → Real) cB.contMDiff metric
  let T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    metricRicci (I := I) (M := M) g - U
  have hTquad (x : M) (v : TangentSpace I x) :
      quad02 (I := I) (M := M) (T x) v =
        ricciTensor (I := I) g x v v - c * B x * g.inner x v v := by
    have hslots : (fun _ : Fin 2 => v) = vec2 (I := I) v v := by
      funext i
      fin_cases i <;> rfl
    change metricRicciAt (I := I) (M := M) g x (fun _ : Fin 2 => v) -
        cB x * metric x (fun _ : Fin 2 => v) = _
    rw [hslots, metricRicciAt_apply_eq_ricciTensor, metricTensorField_apply]
    rfl
  have hw : w ≠ 0 := by
    intro hwzero
    subst hwzero
    simp at hyw
  have hrpos : 0 < g.inner y w w := g.pos y w hw
  let r : Real := Real.sqrt (g.inner y w w)
  have hrpos' : 0 < r := Real.sqrt_pos.mpr hrpos
  have hrne : r ≠ 0 := hrpos'.ne'
  have hrr : r * r = g.inner y w w := by
    simpa [r, sq] using Real.sq_sqrt hrpos.le
  let u : TangentSpace I y := r⁻¹ • w
  have huunit : g.inner y u u = 1 := by
    rw [show u = r⁻¹ • w by rfl, metric_smul2]
    field_simp [hrne]
    linarith [hrr]
  have hru : r • u = w := by
    simp [u, hrne]
  have hyTneg : quad02 (I := I) (M := M) (T y) u < 0 := by
    have hywT : quad02 (I := I) (M := M) (T y) w < 0 := by
      rw [hTquad]
      exact sub_neg.mpr (by simpa [B, hpos] using hyw)
    have hscale : quad02 (I := I) (M := M) (T y) w =
        r * r * quad02 (I := I) (M := M) (T y) u := by
      rw [← hru, tensor02_smul2]
    rw [hscale] at hywT
    nlinarith [mul_pos hrpos' hrpos']
  let p₀ : MetricUnitTangent (I := I) (M := M) g :=
    ⟨(⟨y, u⟩ : TangentBundle I M), huunit⟩
  let q : MetricUnitTangent (I := I) (M := M) g → Real := fun z =>
    quad02 (I := I) (M := M)
      (T (MetricUnitTangent.base (I := I) (M := M) z))
      (MetricUnitTangent.vec (I := I) (M := M) z)
  have hp₀neg : q p₀ < 0 := by
    simpa [q, p₀] using hyTneg
  have hlim1 : Tendsto (fun t : Real => t ^ (-1 : Real)) atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop (show (0 : Real) < 1 by norm_num)
  have hlim2 : Tendsto (fun t : Real => t ^ (-2 : Real)) atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop (show (0 : Real) < 2 by norm_num)
  have hlim : Tendsto
      (fun t : Real => c * (t ^ (-1 : Real) + n * t ^ (-2 : Real)))
      atTop (nhds 0) := by
    have hnlim : Tendsto (fun t : Real => n * t ^ (-2 : Real))
        atTop (nhds 0) := by
      simpa using Tendsto.const_mul n hlim2
    have hsum : Tendsto
        (fun t : Real => t ^ (-1 : Real) + n * t ^ (-2 : Real))
        atTop (nhds 0) := by
      simpa using hlim1.add hnlim
    simpa using Tendsto.const_mul c hsum
  have hsmall : ∀ᶠ t : Real in atTop,
      c * (t ^ (-1 : Real) + n * t ^ (-2 : Real)) < -q p₀ / 2 :=
    (tendsto_order.mp hlim).2 (-q p₀ / 2) (by linarith)
  have hlarge : ∀ᶠ t : Real in atTop, max F (f y) < t :=
    eventually_gt_atTop (max F (f y))
  obtain ⟨R, hRsmall, hRlarge⟩ := (hsmall.and hlarge).exists
  have hFR : F < R := (le_max_left _ _).trans_lt hRlarge
  have hfyR : f y < R := (le_max_right _ _).trans_lt hRlarge
  have hn : 0 ≤ n := by positivity
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (NeZero.ne (Module.finrank Real E))
  have hRpos : 0 < R := by
    have hFlarge : 1 ≤ F := by
      calc
        1 ≤ 2 * n + 1 := by linarith
        _ ≤ F := le_max_right _ _
    linarith
  let L : Set M := {x | f x ≤ R}
  have hL_eq : L = (f : M → Real) ⁻¹' Set.Icc 0 R := by
    ext x
    simp only [L, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    exact (and_iff_right (hpos x).le).symm
  have hLcompact : IsCompact L := by
    rw [hL_eq]
    exact (normalizedGradientRicciSoliton_potential_isProperMap (I := I) h).isCompact_preimage
      isCompact_Icc
  have hp₀L : MetricUnitTangent.base (I := I) (M := M) p₀ ∈ L := by
    change f y ≤ R
    exact hfyR.le
  have hqcont : Continuous q :=
    metricUnit_quadCont (I := I) (M := M) g T
  have hunitCompact : IsCompact
      {z : MetricUnitTangent (I := I) (M := M) g |
        MetricUnitTangent.base (I := I) (M := M) z ∈ L} :=
    metricUnitOn_compact (I := I) (M := M) g hLcompact
  obtain ⟨z₀, hz₀L, hz₀min⟩ :=
    hunitCompact.exists_isMinOn ⟨p₀, hp₀L⟩ hqcont.continuousOn
  have hout (z : MetricUnitTangent (I := I) (M := M) g)
      (hz : R < f (MetricUnitTangent.base (I := I) (M := M) z)) :
      q p₀ < q z := by
    let x := MetricUnitTangent.base (I := I) (M := M) z
    let v := MetricUnitTangent.vec (I := I) (M := M) z
    have hp1 : f x ^ (-1 : Real) ≤ R ^ (-1 : Real) :=
      Real.rpow_le_rpow_of_nonpos hRpos hz.le (by norm_num)
    have hp2 : f x ^ (-2 : Real) ≤ R ^ (-2 : Real) :=
      Real.rpow_le_rpow_of_nonpos hRpos hz.le (by norm_num)
    have hBx : B x ≤ R ^ (-1 : Real) + n * R ^ (-2 : Real) := by
      change f x ^ (-1 : Real) + n * f x ^ (-2 : Real) ≤ _
      nlinarith
    have hRicnonneg : 0 ≤ ricciTensor (I := I) g x v v :=
      ricciTensor_nonneg_of_sectionalNonnegative (I := I) g x (hsec x) v
    have hunit : g.inner x v v = 1 :=
      MetricUnitTangent.unit (I := I) (M := M) z
    have hcB : c * B x ≤ c *
        (R ^ (-1 : Real) + n * R ^ (-2 : Real)) :=
      mul_le_mul_of_nonneg_left hBx hc.le
    change q p₀ < quad02 (I := I) (M := M) (T x) v
    rw [hTquad, hunit, mul_one]
    nlinarith
  have hz₀global : ∀ z : MetricUnitTangent (I := I) (M := M) g,
      q z₀ ≤ q z := by
    intro z
    by_cases hzL : MetricUnitTangent.base (I := I) (M := M) z ∈ L
    · exact hz₀min hzL
    · have hzR : R < f (MetricUnitTangent.base (I := I) (M := M) z) := by
        change ¬ f (MetricUnitTangent.base (I := I) (M := M) z) ≤ R at hzL
        exact lt_of_not_ge hzL
      exact (hz₀min hp₀L).trans (hout z hzR).le
  let x₀ := MetricUnitTangent.base (I := I) (M := M) z₀
  let v₀ := MetricUnitTangent.vec (I := I) (M := M) z₀
  have hv₀unit : g.inner x₀ v₀ v₀ = 1 :=
    MetricUnitTangent.unit (I := I) (M := M) z₀
  have hz₀neg : q z₀ < 0 := (hz₀min hp₀L).trans_lt hp₀neg
  have hTsym : ∀ (x : M) (v w : TangentSpace I x),
      T x (vec2 (I := I) v w) = T x (vec2 (I := I) w v) := by
    intro x v w
    change metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) -
        U x (vec2 (I := I) v w) =
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) w v) -
        U x (vec2 (I := I) w v)
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    change ricciTensor (I := I) g x v w - cB x * g.inner x v w =
      ricciTensor (I := I) g x w v - cB x * g.inner x w v
    rw [ricciTensor_symm (I := I) g x v w, g.symm x v w]
  have hminimum : ∀ (x : M) (v : TangentSpace I x),
      g.inner x v v = 1 →
        quad02 (I := I) (M := M) (T x₀) v₀ ≤
          quad02 (I := I) (M := M) (T x) v := by
    intro x v hv
    let z : MetricUnitTangent (I := I) (M := M) g :=
      ⟨(⟨x, v⟩ : TangentBundle I M), hv⟩
    exact hz₀global z
  have hweightedT : 0 ≤ quad02 (I := I) (M := M)
      (weightedRoughLaplacian0S (I := I) g f T x₀) v₀ :=
    weightedRoughLaplacian0S_quad_nonnegative_at_unit_global_min
      (I := I) g f T x₀ v₀ hv₀unit hTsym hminimum
  have hx₀notK : ¬ f x₀ ≤ F := by
    intro hxK
    have hlower := hcK x₀ hxK v₀
    have hTnonneg : 0 ≤ quad02 (I := I) (M := M) (T x₀) v₀ := by
      rw [hTquad]
      simpa [B, hpos] using sub_nonneg.mpr hlower
    change quad02 (I := I) (M := M) (T x₀) v₀ < 0 at hz₀neg
    linarith
  have hx₀large : 2 * (Module.finrank Real E : Real) ≤ f x₀ := by
    have hFx₀ : F < f x₀ := lt_of_not_ge hx₀notK
    change 2 * n ≤ f x₀
    have hFlarge : 2 * n + 1 ≤ F := le_max_right _ _
    linarith
  have hweightedB :=
    normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_ge
      (I := I) h hpos x₀ hx₀large
  have hweightedRic :=
    gradientRicciSoliton_weightedRoughLaplacian_ricci
      (I := I) h.2.1 x₀
  have hweightedU := weightedRoughLaplacian0S_smul_metric
    (I := I) g f cB x₀
  have hweightedcB := weightedLaplacian_const_smul
    (I := I) g f B c x₀
  have hcurvnonneg : 0 ≤ curvatureRicciContractionAt
      (I := I) (M := M) g x₀ (vec2 (I := I) v₀ v₀) :=
    curvatureRicciContractionAt_nonneg_of_sectionalNonnegative
      (I := I) g x₀ (hsec x₀) v₀
  rw [show T = metricRicci (I := I) (M := M) g - U by rfl,
    weightedRoughLaplacian0S_sub] at hweightedT
  rw [hweightedRic, hweightedU] at hweightedT
  simp only [one_smul] at hweightedT
  change 0 ≤
    (metricRicciAt (I := I) (M := M) g x₀ -
      2 • curvatureRicciContractionAt (I := I) (M := M) g x₀ -
      weightedLaplacian (I := I) g f cB x₀ • metric x₀)
        (fun _ : Fin 2 => v₀) at hweightedT
  have hv₀slots : (fun _ : Fin 2 => v₀) = vec2 (I := I) v₀ v₀ := by
    funext i
    fin_cases i <;> rfl
  rw [hv₀slots] at hweightedT
  rw [Tensor0SSpace.sub_apply, Tensor0SSpace.sub_apply,
    Tensor0SSpace.smul_apply,
    metricRicciAt_apply_eq_ricciTensor, metricTensorField_apply] at hweightedT
  simp only [smul_eq_mul] at hweightedT
  change weightedLaplacian (I := I) g f B x₀ ≥ B x₀ at hweightedB
  change weightedLaplacian (I := I) g f cB x₀ =
      c * weightedLaplacian (I := I) g f B x₀ at hweightedcB
  rw [hweightedcB] at hweightedT
  change 0 ≤
    ricciTensor (I := I) g x₀ v₀ v₀ -
      (2 • curvatureRicciContractionAt (I := I) (M := M) g x₀)
        (vec2 (I := I) v₀ v₀) -
      c * weightedLaplacian (I := I) g f B x₀ *
        g.inner x₀ v₀ v₀ at hweightedT
  rw [hv₀unit, mul_one] at hweightedT
  have hTneg : ricciTensor (I := I) g x₀ v₀ v₀ - c * B x₀ < 0 := by
    change quad02 (I := I) (M := M) (T x₀) v₀ < 0 at hz₀neg
    rw [hTquad, hv₀unit, mul_one] at hz₀neg
    exact hz₀neg
  have htwo :
      (2 • curvatureRicciContractionAt (I := I) (M := M) g x₀)
          (vec2 (I := I) v₀ v₀) =
        2 * curvatureRicciContractionAt (I := I) (M := M) g x₀
          (vec2 (I := I) v₀ v₀) := by
    rw [two_smul, Tensor0SSpace.add_apply]
    ring
  rw [htwo] at hweightedT
  have hcB_le : c * B x₀ ≤
      c * weightedLaplacian (I := I) g f B x₀ :=
    mul_le_mul_of_nonneg_left hweightedB hc.le
  linarith

theorem normalizedGradientRicciSoliton_scalar_lower_bound_by_min_rank_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hsec : ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v) :
    ∃ a : Real, 0 < a ∧ ∀ x : M,
      min (Module.finrank Real E : Real) (a * f x) ≤
        metricScalarAt (I := I) g x := by
  classical
  let hpos : ∀ x : M, 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_ricci_pos
      (I := I) h hRic
  let B : C^∞⟮I, M; Real⟯ := reciprocalPotentialBarrier (I := I) f hpos
  obtain ⟨c, hc, hbarrier⟩ :=
    normalizedGradientRicciSoliton_exists_ricci_reciprocalPotentialBarrier_lower
      (I := I) h hsec hRic
  let n : Real := Module.finrank Real E
  let L : Real := n / c
  let a : Real := (1 / 2 : Real) * Real.exp (-L)
  have ha : 0 < a := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨a, ha, ?_⟩
  intro x
  have hRicInv (y : M) (v : TangentSpace I y) :
      c / f y * g.inner y v v ≤ ricciTensor (I := I) g y v v := by
    have hBge : (f y)⁻¹ ≤ B y := by
      change (f y)⁻¹ ≤ f y ^ (-1 : Real) + n * f y ^ (-2 : Real)
      rw [Real.rpow_neg_one]
      have hn : 0 ≤ n := by positivity
      have hp2 : 0 ≤ f y ^ (-2 : Real) :=
        (Real.rpow_pos_of_pos (hpos y) _).le
      exact le_add_of_nonneg_right (mul_nonneg hn hp2)
    have hcoef : c / f y ≤ c * B y := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hBge hc.le
    have hmetric : 0 ≤ g.inner y v v := by
      by_cases hv : v = 0
      · subst hv
        simp
      · exact (g.pos y v hv).le
    calc
      c / f y * g.inner y v v ≤ c * B y * g.inner y v v :=
        mul_le_mul_of_nonneg_right hcoef hmetric
      _ ≤ ricciTensor (I := I) g y v v := by
        simpa [B, hpos] using hbarrier y v
  obtain ⟨γ, hγ0, hγ⟩ :=
    gradientRicciSoliton_exists_globalIntegralCurve_potential
      (I := I) g f 1 h.1 h.2.1 x
  let R : Real → Real := (fun y : M => metricScalarAt (I := I) g y) ∘ γ
  let F : Real → Real := (f : M → Real) ∘ γ
  have hRderiv (s : Real) : HasDerivAt R
      (2 * ricciTensor (I := I) g (γ s)
        (gradFun (I := I) g f (γ s)) (gradFun (I := I) g f (γ s))) s := by
    simpa [R] using
      gradientRicciSoliton_hasDerivAt_scalar_comp_integralCurve
        (I := I) h.2.1 hγ s
  have hRicNonneg : ∀ (y : M) (v : TangentSpace I y),
      0 ≤ ricciTensor (I := I) g y v v := by
    intro y v
    exact ricciTensor_nonneg_of_sectionalNonnegative (I := I) g y (hsec y) v
  have hRmono : Monotone R := by
    simpa [R] using
      gradientRicciSoliton_scalar_comp_integralCurve_monotone_of_ricci_nonneg
        (I := I) h.2.1 hRicNonneg hγ
  have hFanti : Antitone (fun s : Real => Real.exp (-s) * F s) := by
    simpa [F] using
      normalizedGradientRicciSoliton_exp_neg_mul_potential_comp_integralCurve_antitone
        (I := I) h hγ
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  have hL : 0 < L := div_pos hn hc
  by_cases hsmall : ∀ s : Real, s ∈ Set.Icc (-L) 0 → R s / F s ≤ 1 / 2
  · let S : Real → Real := R - fun s => c * s
    have hSderiv (s : Real) : HasDerivAt S
        (2 * ricciTensor (I := I) g (γ s)
          (gradFun (I := I) g f (γ s)) (gradFun (I := I) g f (γ s)) - c) s := by
      simpa [S] using (hRderiv s).sub ((hasDerivAt_id s).const_mul c)
    have hderivNonneg (s : Real) (hs : s ∈ Set.Icc (-L) 0) :
        0 ≤ 2 * ricciTensor (I := I) g (γ s)
            (gradFun (I := I) g f (γ s)) (gradFun (I := I) g f (γ s)) - c := by
      let V := gradFun (I := I) g f (γ s)
      let G := g.inner (γ s) V V
      have hpot := normalizedGradientRicciSoliton_potential_equation (I := I) h (γ s)
      change R s + G = F s at hpot
      have hFpos : 0 < F s := hpos (γ s)
      have hratio : 1 / 2 ≤ G / F s := by
        have hsum : R s / F s + G / F s = 1 := by
          field_simp [hFpos.ne']
          linarith
        linarith [hsmall s hs]
      have hcG : c / 2 ≤ c / F s * G := by
        calc
          c / 2 = c * (1 / 2) := by ring
          _ ≤ c * (G / F s) := mul_le_mul_of_nonneg_left hratio hc.le
          _ = c / F s * G := by ring
      have hric := hRicInv (γ s) V
      change c / F s * G ≤ ricciTensor (I := I) g (γ s) V V at hric
      linarith
    have hSdiff : DifferentiableOn Real S (Set.Icc (-L) 0) := by
      intro s hs
      exact (hSderiv s).differentiableAt.differentiableWithinAt
    have hSmono : MonotoneOn S (Set.Icc (-L) 0) :=
      monotoneOn_of_deriv_nonneg (convex_Icc (-L) 0) hSdiff.continuousOn
        (hSdiff.mono interior_subset) (by
          intro s hs
          rw [(hSderiv s).deriv]
          exact hderivNonneg s (interior_subset hs))
    have hnegL : -L ≤ 0 := by linarith
    have hcompare := hSmono (a := -L) (b := 0)
      ⟨le_rfl, hnegL⟩ ⟨hnegL, le_rfl⟩ hnegL
    have hscalarNonneg := normalizedGradientRicciSoliton_scalar_nonneg
      (I := I) h (γ (-L))
    have hcL : c * L = n := by
      dsimp only [L]
      field_simp [hc.ne']
    have hnR : n ≤ R 0 := by
      change R (-L) - c * (-L) ≤ R 0 - c * 0 at hcompare
      rw [mul_zero, sub_zero] at hcompare
      change 0 ≤ R (-L) at hscalarNonneg
      nlinarith [hcL]
    have hR0 : R 0 = metricScalarAt (I := I) g x := by
      simp [R, hγ0]
    rw [hR0] at hnR
    exact (min_le_left n (a * f x)).trans hnR
  · simp only [not_forall, not_le] at hsmall
    obtain ⟨s, hs, hratio⟩ := hsmall
    have hRforward : R s ≤ R 0 := hRmono hs.2
    have hweightedPotential := hFanti hs.2
    have hFs : Real.exp s * F 0 ≤ F s := by
      have hmul := mul_le_mul_of_nonneg_left hweightedPotential (Real.exp_pos s).le
      calc
        Real.exp s * F 0 = Real.exp s * (Real.exp (-0) * F 0) := by simp
        _ ≤ Real.exp s * (Real.exp (-s) * F s) := hmul
        _ = F s := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
    have hexp : Real.exp (-L) ≤ Real.exp s :=
      Real.exp_le_exp.mpr hs.1
    have hF0pos : 0 < F 0 := hpos (γ 0)
    have hFlow : Real.exp (-L) * F 0 ≤ F s :=
      (mul_le_mul_of_nonneg_right hexp hF0pos.le).trans hFs
    have hhalf : (1 / 2 : Real) * F s < R s := by
      exact (lt_div_iff₀ (hpos (γ s))).mp hratio
    have haf : a * f x < R s := by
      have hγf : F 0 = f x := by simp [F, hγ0]
      calc
        a * f x = (1 / 2 : Real) * (Real.exp (-L) * F 0) := by
          rw [hγf]
          simp [a]
          ring
        _ ≤ (1 / 2 : Real) * F s :=
          mul_le_mul_of_nonneg_left hFlow (by norm_num)
        _ < R s := hhalf
    have hR0 : R 0 = metricScalarAt (I := I) g x := by
      simp [R, hγ0]
    rw [hR0] at hRforward
    exact (min_le_right n (a * f x)).trans (haf.le.trans hRforward)

end DifferentialGeometry.Geometry
