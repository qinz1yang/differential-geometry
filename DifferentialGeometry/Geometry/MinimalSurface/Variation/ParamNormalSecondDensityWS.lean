import DifferentialGeometry.Geometry.Submanifold.Variation.SecondMetricDerivative
import DifferentialGeometry.Geometry.Submanifold.Variation.NormalMetricDerivative
import DifferentialGeometry.Geometry.Measure.Area.ChangeOfFrame
import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace
import DifferentialGeometry.Geometry.Connection.SourceSectionRestriction
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import DifferentialGeometry.Geometry.Metric.SourceTangent
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# S-W-STAB G2：parametrized 变分的面积密度二阶导（逐点公式）

`NormalSecondVariation.lean` 的 parametrized 版：`F : ℝ × ℂ → M` 是 `V` 上光滑的族，`F(0,·) = U`（`N` 上），
`∂_t F(0,·) = φ ν`（`ν` 单位法向），且 `t = 0` 处加速度为 0（geodesic 变分）。则 `z ∈ N` 处
`d²/dt² dens(F_t)(z) = dens(U)(z) · (Σ_i |D_{b_i}(φν)|² − φ² Σ_i⟨R(ν,P_i)P_i,ν⟩
− φ²((h₀₀−h₁₁)²+4h₀₁²))`。
没有 ambient flow、没有加速度项（`⟨∇A, P⟩` 整项消失）、没有 embedding。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.Variation Riemannian.CovariantDerivativeAlong

private theorem hasDerivAt_deriv_sqrt_gram_WS
    {a b c : ℝ → ℝ} {t : ℝ}
    (ha : ContDiffAt ℝ 2 a t) (hb : ContDiffAt ℝ 2 b t)
    (hc : ContDiffAt ℝ 2 c t) (hpos : 0 < a t)
    (heq : a t = b t) (horth : c t = 0) :
    HasDerivAt (deriv (fun r => Real.sqrt (a r * b r - c r ^ 2)))
      ((deriv (deriv a) t + deriv (deriv b) t) / 2 -
        ((deriv a t - deriv b t) ^ 2 + 4 * deriv c t ^ 2) / (4 * a t)) t := by
  have ha₀ := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hb₀ := (hb.differentiableAt (by norm_num)).hasDerivAt
  have hc₀ := (hc.differentiableAt (by norm_num)).hasDerivAt
  have ha₁ := ((ha.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hb₁ := ((hb.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hc₁ := ((hc.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hdet : a t * b t - c t ^ 2 ≠ 0 := by
    rw [horth, ← heq]
    nlinarith
  have hsqrt : Real.sqrt (a t * b t - c t ^ 2) = a t := by
    rw [horth, ← heq]
    simpa using Real.sqrt_mul_self hpos.le
  have hnear : ∀ᶠ r in 𝓝 t, a r * b r - c r ^ 2 ≠ 0 :=
    ((ha.continuousAt.mul hb.continuousAt).sub (hc.continuousAt.pow 2)).eventually_ne hdet
  have hfirst : deriv (fun r => Real.sqrt (a r * b r - c r ^ 2)) =ᶠ[𝓝 t]
      fun r => (deriv a r * b r + a r * deriv b r - 2 * c r * deriv c r) /
        (2 * Real.sqrt (a r * b r - c r ^ 2)) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num),
      hc.eventually (by norm_num), hnear] with r har hbr hcr hdr
    have hd := (((har.differentiableAt (by norm_num)).hasDerivAt.mul
      (hbr.differentiableAt (by norm_num)).hasDerivAt).sub
      ((hcr.differentiableAt (by norm_num)).hasDerivAt.pow 2)).sqrt hdr
    simpa only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, pow_one,
      Nat.cast_ofNat] using hd.deriv
  have hnum := ((ha₁.mul hb₀).add (ha₀.mul hb₁)).sub ((hc₀.const_mul 2).mul hc₁)
  have hden := (((ha₀.mul hb₀).sub (hc₀.pow 2)).sqrt hdet).const_mul 2
  have hden_ne : 2 * Real.sqrt (a t * b t - c t ^ 2) ≠ 0 := by
    rw [hsqrt]
    positivity
  have hquot := hnum.div hden hden_ne
  have hquot' := hquot.congr_of_eventuallyEq hfirst
  apply hquot'.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Nat.reduceSub,
    pow_one, Nat.cast_ofNat, hsqrt]
  simp only [horth, ← heq]
  field_simp [ne_of_gt hpos]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **parametrized 版逐点二阶公式.**  见模块说明。 -/
theorem hasDerivAt_deriv_areaDensity_param_normal_WS
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (φ : N → ℝ) (Wsec : ∀ q : ℂ, TangentSpace 𝓘(ℝ, E) (U q))
    (hW_eq : ∀ q : N, (Wsec q : E) = φ q • (ν q : E))
    {F : ℝ × ℂ → M} {V : Set (ℝ × ℂ)} (hV : IsOpen V) (hVN : ∀ p ∈ V, p.2 ∈ N)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V)
    (h0V : ∀ z ∈ N, ((0 : ℝ), z) ∈ V) (hF0 : ∀ z ∈ N, F (0, z) = U z)
    (hvel : ∀ (z : ℂ) (hz : z ∈ N),
      (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, z) (1, 0) : E) = φ ⟨z, hz⟩ • (ν ⟨z, hz⟩ : E))
    (hacc : ∀ z ∈ N, covDerivAlong g (fun s : ℝ => F (s, z))
      (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => F (r, z)) s (1 : ℝ)) 0 = 0)
    (z : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    let P : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)
    let DX : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      sourceSectionCovariantDerivative g U Wsec z (b i)
    let h : Fin 2 → Fin 2 → ℝ := fun i j => g.inner (U z) (ν z)
      (secondFundamentalFormAmbientAt gN g (fun q : N => U q) z (b i) (b j))
    HasDerivAt (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z))
      (riemannianAreaDensity g U z *
        ((∑ i : Fin 2, g.inner (U z) (DX i) (DX i)) -
          φ z ^ 2 * (∑ i : Fin 2, g.inner (U z)
            ((riemannOp (LeviCivita g) (U z)) (ν z) (P i) (P i)) (ν z)) -
          φ z ^ 2 * ((h 0 0 - h 1 1) ^ 2 + 4 * (h 0 1) ^ 2))) 0 := by
  classical
  intro gN P DX h
  have hzN : (z : ℂ) ∈ N := z.property
  have hzV : ((0 : ℝ), (z : ℂ)) ∈ V := h0V z hzN
  have hFprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V := by
    have h' := hF
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h'
    exact h'
  have hFd (p : ℝ × ℂ) (hp : p ∈ V) :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F p :=
    ((hFprod p hp).contMDiffAt (hV.mem_nhds hp)).mdifferentiableAt (by simp)
  let Pm (a : ℝ × ℂ) (p : ℝ × ℂ) : E := mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p a
  have hspace (t : ℝ) (q : ℂ) (hq : (t, q) ∈ V) (a : ℂ) :
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y => F (t, y)) q a : E) = Pm (0, a) (t, q) := by
    have h' := mfderiv_parameter_slice (hFd (t, q) hq) a
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h'
  have hUz : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    DifferentialGeometry.mdifferentiableAt_subtype_iff.mp (hU.mdifferentiableAt (x := z) (by simp))
  have hcentral (q : ℂ) (hq : q ∈ N) : (fun y => F (0, y)) =ᶠ[𝓝 q] U :=
    Filter.eventually_of_mem (N.isOpen.mem_nhds hq) (fun y hy => hF0 y hy)
  have hP₀ (q : ℂ) (hq : q ∈ N) (a : ℂ) :
      Pm (0, a) (0, q) = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q a : E) := by
    rw [← hspace 0 q (h0V q hq) a]
    exact congrArg (fun L : ℂ →L[ℝ] E => L a) (hcentral q hq).mfderiv_eq
  have hvel' (q : ℂ) (hq : q ∈ N) :
      Pm (1, 0) (0, q) = φ ⟨q, hq⟩ • (ν ⟨q, hq⟩ : E) := hvel q hq
  have hnormalU (q : N) (v : ℂ) :
      g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q v) = 0 := by
    have hd := DifferentialGeometry.mfderiv_restrict_open
      (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N q
    exact (congrArg
      (fun L : ℂ →L[ℝ] E => g.inner (U q) (ν q) (L v)) hd).symm.trans (hnormal q v)
  have hnormalF : ∀ q, ((0 : ℝ), q) ∈ V → ∀ a : ℂ,
      g.inner (F (0, q))
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, q) (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, q) (0, a)) = 0 := by
    intro q hq a
    have hqN : q ∈ N := hVN _ hq
    change g.inner (F (0, q)) (Pm (1, 0) (0, q)) (Pm (0, a) (0, q)) = 0
    rw [hvel' q hqN, hP₀ q hqN a, hF0 q hqN]
    rw [map_smul, _root_.smul_apply, smul_eq_mul, hnormalU ⟨q, hqN⟩ a, mul_zero]
  have hscp (v w : ℂ) :
      (sourceCovariantPartial g (fun q => F (0, q)) z v w : E) =
        (diskMapCovariantPartial g U z v w : E) := by
    have hline : Continuous (fun r : ℝ => (z : ℂ) + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), (z : ℂ) + r • v ∈ N := by
      apply hline.continuousAt.preimage_mem_nhds
      apply N.isOpen.mem_nhds
      change (z : ℂ) + (0 : ℝ) • v ∈ N
      rw [zero_smul, add_zero]
      exact hzN
    have hγ : (fun r : ℝ => F (0, (z : ℂ) + r • v)) =ᶠ[𝓝 (0 : ℝ)] fun r => U ((z : ℂ) + r • v) := by
      filter_upwards [hmem] with r hr
      exact hF0 _ hr
    have hVV : ∀ᶠ r in 𝓝 (0 : ℝ),
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => F (0, q)) ((z : ℂ) + r • v) w : E)) =
          (diskMapPartial U ((z : ℂ) + r • v) w : E) := by
      filter_upwards [hmem] with r hr
      exact congrArg (fun L : ℂ →L[ℝ] E => L w) (hcentral _ hr).mfderiv_eq
    exact covDerivAlong_congr_curve g
      (γ := fun r : ℝ => F (0, (z : ℂ) + r • v)) (γ' := fun r : ℝ => U ((z : ℂ) + r • v))
      (fun r => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => F (0, q)) ((z : ℂ) + r • v) w)
      (fun r => diskMapPartial U ((z : ℂ) + r • v) w) hγ hVV
  let gr : ℝ → ℂ → ℂ → ℝ := fun t v w =>
    g.inner (F (t, z)) (Pm (0, v) (t, z)) (Pm (0, w) (t, z))
  have hinner0 (X Y : E) : g.inner (F (0, z)) X Y = g.inner (U z) X Y := by
    rw [hF0 z hzN]
  have hcoef (v w : ℂ) : HasDerivAt (fun t => gr t v w)
      (-2 * φ z * g.inner (U z) (ν z) (diskMapCovariantPartial g U z v w)) 0 := by
    have hd := hasDerivAt_gramCoefficient_of_normal_velocity g hV hF hzV hnormalF v w
    refine hd.congr_deriv ?_
    have h1 : (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (1, 0) : E) = φ z • (ν z : E) :=
      hvel z hzN
    have h2 : g.inner (F (0, z))
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (1, 0))
        (sourceCovariantPartial g (fun q => F (0, q)) z v w) =
        g.inner (U z) (φ z • (ν z : E)) (diskMapCovariantPartial g U z v w) := by
      refine (hinner0 _ _).trans ?_
      rw [h1, hscp v w]
    rw [h2, map_smul, _root_.smul_apply, smul_eq_mul]
    ring
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let ℓ : E →L[ℝ] ℝ := g.inner (U z) (ν z)
  let H : ℂ → ℂ → ℝ := fun v w => ℓ (Q v w)
  have hdiag (v : ℂ) :
      g.inner (U z) (ν z) (diskMapCovariantPartial g U z v v) = H v v :=
    (inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
      N gN g U hU z (ν z) (hnormalU z) v).symm
  have hcoefdiag (v : ℂ) : HasDerivAt (fun t => gr t v v) (-2 * φ z * H v v) 0 := by
    simpa only [hdiag] using hcoef v v
  have hHsum (v w : ℂ) : H (v + w) (v + w) = H v v + 2 * H v w + H w w := by
    have hsymm : Q w v = Q v w :=
      secondFundamentalFormAmbientAt_symmetric gN g
        ((hU.contMDiffAt (x := z)).of_le (by simp)) w v
    change ℓ (Q (v + w) (v + w)) = ℓ (Q v v) + 2 * ℓ (Q v w) + ℓ (Q w w)
    simp only [map_add, _root_.add_apply, hsymm]
    ring
  have hgrsymm (t : ℝ) (v w : ℂ) : gr t v w = gr t w v := by
    exact g.symm (F (t, z)) _ _
  have hcoefmixed (v w : ℂ) : HasDerivAt (fun t => gr t v w) (-2 * φ z * H v w) 0 := by
    have hd := (((hcoefdiag (v + w)).sub (hcoefdiag v)).sub (hcoefdiag w)).div_const 2
    have heq : (fun t => gr t v w) =ᶠ[𝓝 (0 : ℝ)]
        fun t => (gr t (v + w) (v + w) - gr t v v - gr t w w) / 2 := by
      apply Eventually.of_forall
      intro t
      have hadd : Pm (0, v + w) (t, z) = Pm (0, v) (t, z) + Pm (0, w) (t, z) := by
        change (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (t, (z : ℂ)) : ℝ × ℂ →L[ℝ] E) (0, v + w) =
          (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (t, (z : ℂ)) : ℝ × ℂ →L[ℝ] E) (0, v) +
          (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (t, (z : ℂ)) : ℝ × ℂ →L[ℝ] E) (0, w)
        have h0 : ((0 : ℝ), v + w) = ((0 : ℝ), v) + ((0 : ℝ), w) := by ext <;> simp
        rw [h0]
        exact ContinuousLinearMap.map_add _ _ _
      let Bt : E →L[ℝ] E →L[ℝ] ℝ := g.inner (F (t, z))
      have hgr (a c : ℂ) : gr t a c = Bt (Pm (0, a) (t, z)) (Pm (0, c) (t, z)) := rfl
      have hs (x y : E) : Bt y x = Bt x y := g.symm (F (t, z)) y x
      change gr t v w = (gr t (v + w) (v + w) - gr t v v - gr t w w) / 2
      rw [hgr, hgr, hgr, hgr, hadd]
      simp only [map_add, add_apply]
      rw [hs (Pm (0, w) (t, z)) (Pm (0, v) (t, z))]
      ring
    apply (hd.congr_of_eventuallyEq heq).congr_deriv
    change ((-2 * φ z * H (v + w) (v + w) - (-2 * φ z * H v v)) -
      (-2 * φ z * H w w)) / 2 = -2 * φ z * H v w
    rw [hHsum]
    ring
  have hmemv (v : ℂ) : ∀ᶠ r in 𝓝 (0 : ℝ), (z : ℂ) + r • v ∈ N := by
    have hline : Continuous (fun r : ℝ => (z : ℂ) + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply hline.continuousAt.preimage_mem_nhds
    apply N.isOpen.mem_nhds
    change (z : ℂ) + (0 : ℝ) • v ∈ N
    rw [zero_smul, add_zero]
    exact hzN
  have htime (q : ℂ) (hq : ((0 : ℝ), q) ∈ V) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => F (s, q)) 0 (1 : ℝ) : E) = Pm (1, 0) (0, q) := by
    have h' := mfderiv_parameter_time (hFd (0, q) hq) 1
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h'
  let T : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let D : ℂ → E := fun v => sourceSectionCovariantDerivative g U Wsec z v
  let R : M → E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fun x => riemannOp (LeviCivita g) x
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun x => g.inner x
  let K : ℂ → ℝ := fun v => B (U z) (R (U z) (ν z) (T v) (T v)) (ν z)
  let e : ℂ → ℝ := fun v => B (U z) (D v) (D v) - φ z ^ 2 * K v
  have hsecond (v : ℂ) : HasDerivAt (deriv (fun t => gr t v v)) (2 * e v) 0 := by
    let γ : ℝ → M := fun r => U ((z : ℂ) + r • v)
    let f : ℝ → ℝ → M := fun t r => F (t, (z : ℂ) + r • v)
    have hfzero : f 0 =ᶠ[𝓝 (0 : ℝ)] γ := by
      filter_upwards [hmemv v] with r hr
      exact hF0 _ hr
    have hfield : ∀ᶠ r in 𝓝 (0 : ℝ),
        (centralVariationField (I := 𝓘(ℝ, E)) f r : E) = (Wsec ((z : ℂ) + r • v) : E) := by
      filter_upwards [hmemv v] with r hr
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => F (s, (z : ℂ) + r • v)) 0 (1 : ℝ) : E) = _
      rw [htime _ (h0V _ hr), hvel' _ hr]
      exact (hW_eq ⟨_, hr⟩).symm
    have hfieldzero : (centralVariationField (I := 𝓘(ℝ, E)) f 0 : E) = φ z • (ν z : E) := by
      have harg : (z : ℂ) + (0 : ℝ) • v = z := by rw [zero_smul, add_zero]
      rw [hfield.self_of_nhds]
      exact (congrArg (fun q : ℂ => (Wsec q : E)) harg).trans (hW_eq z)
    have hbase : f 0 0 = U z := by
      change F (0, (z : ℂ) + (0 : ℝ) • v) = U z
      rw [zero_smul, add_zero]
      exact hF0 z hzN
    have hvelv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ) : E) = T v := by
      have hc := congrArg (fun L : ℝ →L[ℝ] E => (L (1 : ℝ) : E))
        (Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) hfzero)
      exact hc.trans (source_mfderiv_line hUz v)
    have hD : (covDerivAlong g (f 0) (centralVariationField (I := 𝓘(ℝ, E)) f) 0 : E) =
        D v := by
      change (covDerivAlong g (f 0) (centralVariationField (I := 𝓘(ℝ, E)) f) 0 : E) =
        (covDerivAlong g γ (fun r => Wsec ((z : ℂ) + r • v)) 0 : E)
      exact covDerivAlong_congr_curve g _ _ hfzero hfield
    have hacc' : (covDerivAlong g (f 0)
        (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0 : E) = 0 := by
      have hzero : ∀ᶠ r in 𝓝 (0 : ℝ), centralVariationAcceleration (I := 𝓘(ℝ, E)) g f r =
          (0 : TangentSpace 𝓘(ℝ, E) (f 0 r)) := by
        filter_upwards [hmemv v] with r hr
        exact hacc _ hr
      rw [covDerivAlong_congr_of_eventuallyEq g (f 0) hzero]
      exact covDerivAlong_zero g (f 0) 0
    have hindex : indexFormIntegrand (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationField (I := 𝓘(ℝ, E)) f)
        (centralVariationField (I := 𝓘(ℝ, E)) f) 0 =
        B (U z) (D v) (D v) - φ z ^ 2 * K v := by
      change g.inner (f 0 0)
          (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
            (centralVariationField (I := 𝓘(ℝ, E)) f) 0)
          (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
            (centralVariationField (I := 𝓘(ℝ, E)) f) 0) -
        g.inner (f 0 0) (R (f 0 0) (centralVariationField (I := 𝓘(ℝ, E)) f 0)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ)))
          (centralVariationField (I := 𝓘(ℝ, E)) f 0) = _
      rw [hD, hfieldzero, hvelv, hbase]
      let n : E := ν z
      change B (U z) (D v) (D v) -
        B (U z) (R (U z) (φ z • n) (T v) (T v)) (φ z • n) =
          B (U z) (D v) (D v) - φ z ^ 2 * B (U z) (R (U z) n (T v) (T v)) n
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring
    have hpair : g.inner (F (0, z))
        (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
          (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0)
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (0, v)) = 0 := by
      refine (hinner0 _ _).trans ((congrArg (fun a : E => B (U z) a
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (0, v))) hacc').trans ?_)
      change B (U z) (0 : E) (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (0, v)) = 0
      exact (congrArg (fun L : E →L[ℝ] ℝ => L (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (0, v)))
        (map_zero (B (U z)))).trans rfl
    have hd := hasDerivAt_deriv_gramDiagonal_local g hV hF hzV v
    refine hd.congr_deriv ?_
    change 2 * (indexFormIntegrand (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationField (I := 𝓘(ℝ, E)) f)
        (centralVariationField (I := 𝓘(ℝ, E)) f) 0 +
      g.inner (F (0, z))
        (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
          (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0)
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, (z : ℂ)) (0, v))) = 2 * e v
    rw [hindex, hpair]
    change 2 * (B (U z) (D v) (D v) - φ z ^ 2 * K v + 0) =
      2 * (B (U z) (D v) (D v) - φ z ^ 2 * K v)
    rw [add_zero]
  have hPregular (a : ℝ × ℂ) : ContMDiffOn 𝓘(ℝ, ℝ × ℂ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p) (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p a)) V :=
    contMDiffOn_source_partial hV hF (m := ∞) (by simp) a
  have hcoefregular (v w : ℂ) : ContDiffAt ℝ 2 (fun t => gr t v w) 0 := by
    have hp : ContDiffAt ℝ ∞
        (fun p => g.inner (F p) (Pm (0, v) p) (Pm (0, w) p)) (0, (z : ℂ)) :=
      ((contDiffOn_sourceSectionPairing g hF (hPregular (0, v)) (hPregular (0, w)))
        (0, z) hzV).contDiffAt (hV.mem_nhds hzV)
    have ht : ContDiffAt ℝ ∞ (fun t : ℝ => (t, (z : ℂ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hc := hp.comp 0 ht
    exact hc.of_le (by simp)
  have hLD : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z = T :=
    DifferentialGeometry.mfderiv_restrict_open U N z
  have hgr0 (v w : ℂ) : gr 0 v w = g.inner (U z) (T v) (T w) := by
    change g.inner (F (0, z)) (Pm (0, v) (0, z)) (Pm (0, w) (0, z)) = _
    refine (hinner0 _ _).trans ?_
    rw [hP₀ z hzN v, hP₀ z hzN w]
    rfl
  have hgN (v w : ℂ) : gN.inner z v w = g.inner (U z) (T v) (T w) := by
    change g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z w) = _
    rw [hLD]
    rfl
  let β : Fin 2 → ℂ := fun i => b i
  have hβ (i j : Fin 2) : gN.inner z (β i) (β j) = if i = j then 1 else 0 := hb i j
  have h00 : gr 0 (β 0) (β 0) = 1 := by
    rw [hgr0 (β 0) (β 0), ← hgN (β 0) (β 0)]; simpa using hβ 0 0
  have h01 : gr 0 (β 0) (β 1) = 0 := by
    rw [hgr0 (β 0) (β 1), ← hgN (β 0) (β 1)]; simpa using hβ 0 1
  have h11 : gr 0 (β 1) (β 1) = 1 := by
    rw [hgr0 (β 1) (β 1), ← hgN (β 1) (β 1)]; simpa using hβ 1 1
  let Jt : ℝ → ℝ := fun r =>
    Real.sqrt (gr r (β 0) (β 0) * gr r (β 1) (β 1) - gr r (β 0) (β 1) ^ 2)
  have hJ : HasDerivAt (deriv Jt)
      (e (β 0) + e (β 1) -
        φ z ^ 2 * ((H (β 0) (β 0) - H (β 1) (β 1)) ^ 2 + 4 * (H (β 0) (β 1)) ^ 2)) 0 := by
    have hd := hasDerivAt_deriv_sqrt_gram_WS (hcoefregular (β 0) (β 0))
      (hcoefregular (β 1) (β 1)) (hcoefregular (β 0) (β 1)) (by rw [h00]; norm_num)
      (h00.trans h11.symm) h01
    refine hd.congr_deriv ?_
    rw [(hsecond (β 0)).deriv, (hsecond (β 1)).deriv, (hcoefdiag (β 0)).deriv,
      (hcoefdiag (β 1)).deriv, (hcoefmixed (β 0) (β 1)).deriv, h00]
    ring
  let r : ℂ → Fin 2 → ℝ := fun a i => b.repr (show TangentSpace 𝓘(ℝ, ℂ) z from a) i
  have hexpand (a : ℂ) : a = r a 0 • β 0 + r a 1 • β 1 := by
    have h' := (b.sum_repr (show TangentSpace 𝓘(ℝ, ℂ) z from a)).symm
    simp only [Fin.sum_univ_two] at h'
    exact h'
  let d : ℝ := |r 1 0 * r Complex.I 1 - r 1 1 * r Complex.I 0|
  have hdensF (t : ℝ) (ht : (t, (z : ℂ)) ∈ V) :
      riemannianAreaDensity g (fun y => F (t, y)) z = d * Jt t := by
    let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y => F (t, y)) z
    have hL (a : ℂ) : (L a : E) = r a 0 • L (β 0) + r a 1 • L (β 1) := by
      conv_lhs => rw [hexpand a]
      rw [map_add, map_smul, map_smul]
    have e0 : (L (β 0) : E) = Pm (0, β 0) (t, z) := hspace t z ht (β 0)
    have e1 : (L (β 1) : E) = Pm (0, β 1) (t, z) := hspace t z ht (β 1)
    have hJL : tangentTwoJacobian g (x := F (t, (z : ℂ))) (L (β 0)) (L (β 1)) = Jt t := by
      unfold tangentTwoJacobian
      rw [e0, e1]
    have hexp : riemannianAreaDensity g (fun y => F (t, y)) z =
        tangentTwoJacobian g (x := F (t, (z : ℂ)))
          (r 1 0 • L (β 0) + r 1 1 • L (β 1))
          (r Complex.I 0 • L (β 0) + r Complex.I 1 • L (β 1)) :=
      congrArg₂ (tangentTwoJacobian g) (hL 1) (hL Complex.I)
    rw [hexp]
    have hcof := tangentTwoJacobian_changeOfFrame g (x := F (t, (z : ℂ)))
      (L (β 0)) (L (β 1)) (r 1 0) (r 1 1) (r Complex.I 0) (r Complex.I 1)
    refine hcof.trans ?_
    rw [hJL]
  have hJ0 : Jt 0 = 1 := by
    change Real.sqrt (gr 0 (β 0) (β 0) * gr 0 (β 1) (β 1) - gr 0 (β 0) (β 1) ^ 2) = 1
    rw [h00, h01, h11]
    simp
  have hdU : d = riemannianAreaDensity g U z := by
    have h1 := hdensF 0 hzV
    rw [hJ0, mul_one] at h1
    rw [← h1]
    exact riemannianAreaDensity_congr g (hcentral z hzN)
  have hVz : ∀ᶠ t in 𝓝 (0 : ℝ), ((t, (z : ℂ)) ∈ V) :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  have hderivscale : deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) =ᶠ[𝓝 (0 : ℝ)]
      fun t => riemannianAreaDensity g U z * deriv Jt t := by
    filter_upwards [hVz.eventually_nhds] with t ht
    have heq : (fun s => riemannianAreaDensity g (fun y => F (s, y)) z) =ᶠ[𝓝 t]
        fun s => d * Jt s := ht.mono (fun s hs => hdensF s hs)
    rw [heq.deriv_eq, deriv_const_mul_field', hdU]
  have hfinal := (hJ.const_mul (riemannianAreaDensity g U z)).congr_of_eventuallyEq hderivscale
  refine hfinal.congr_deriv ?_
  change riemannianAreaDensity g U z * (e (β 0) + e (β 1) -
      φ z ^ 2 * ((H (β 0) (β 0) - H (β 1) (β 1)) ^ 2 + 4 * (H (β 0) (β 1)) ^ 2)) =
    riemannianAreaDensity g U z * ((∑ i : Fin 2, B (U z) (D (β i)) (D (β i))) -
      φ z ^ 2 * (∑ i : Fin 2, K (β i)) -
      φ z ^ 2 * ((H (β 0) (β 0) - H (β 1) (β 1)) ^ 2 + 4 * (H (β 0) (β 1)) ^ 2))
  simp only [Fin.sum_univ_two, e]
  ring

end DifferentialGeometry.Geometry
