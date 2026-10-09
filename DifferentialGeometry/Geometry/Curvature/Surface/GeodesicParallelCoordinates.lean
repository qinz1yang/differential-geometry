import DifferentialGeometry.Geometry.Curvature.Surface.DivergenceForm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Curvature of a coefficient field of the form `G dt² + dh²` (local, dimension two)

Let `b` be a `C²` positive symmetric coefficient field on an open set `U` of a two-dimensional inner
product space, and `(v₁, v₂)` a basis with `b(v₁, v₂) ≡ 0` and `b(v₂, v₂) ≡ 1` on `U` (geodesic
parallel coordinates: the `v₂`-lines are unit-speed and orthogonal to the `v₁`-direction). Then along
the `v₂`-line through `y ∈ U` the function `φ(s) = √(b(y + s v₂)(v₁, v₁))` satisfies the scalar Jacobi
equation `φ'' = -K φ` at `s = 0`, with `K = coefficientSectional b y v₁ v₂`
(`hasDerivAt_deriv_sqrt_of_geodesicParallel`).

Proof: cut `b` off with a smooth bump to a globally `C²` positive field `b'` equal to `b` near `y`,
apply SF-B's divergence identity `K √D = ∂₂ P − ∂₁ Q` (`coefficientSectional_mul_sqrt_eq_fderiv_sub`),
and read the potentials near `y`: `Q = 0` and `P = −∂₂ √G`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance parallelBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance parallelBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Coefficient sectional curvature only depends on the germ of the field. -/
theorem coefficientSectional_congr_of_eventuallyEq'
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : b =ᶠ[𝓝 x] c) (v w : E) :
    coefficientSectional b x v w = coefficientSectional c x v w := by
  have hG : coefficientGram b =ᶠ[𝓝 x] coefficientGram c :=
    h.mono fun y hy => congrArg (coefficientGramCLM E) hy
  unfold coefficientSectional coefficientRm04
  rw [jet2_congr_of_eventuallyEq hG, h.eq_of_nhds]

/-- **Bump cut-off.** A coefficient field which is `C²`, symmetric and positive on an open set `U`
agrees near any `y ∈ U` with a globally `C²`, symmetric, positive field. -/
theorem exists_global_coefficient_eventuallyEq {b : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hU : IsOpen U) (hb : ContDiffOn ℝ 2 b U) (hsymm : ∀ y ∈ U, ∀ u v, b y u v = b y v u)
    (hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < b y v v) {y : E} (hy : y ∈ U) :
    ∃ b' : E → E →L[ℝ] E →L[ℝ] ℝ, ContDiff ℝ 2 b' ∧ (∀ z u v, b' z u v = b' z v u) ∧
      (∀ z v, v ≠ 0 → 0 < b' z v v) ∧ ∃ ε > 0, ball y ε ⊆ U ∧ ∀ z ∈ ball y ε, b' z = b z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy
  let χ : ContDiffBump y := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set b' : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => χ z • b z + (1 - χ z) • b y with hb'
  have hsuppU : ∀ z, χ z ≠ 0 → z ∈ U := by
    intro z hz
    have hz' : z ∈ Function.support χ := hz
    rw [χ.support_eq] at hz'
    exact hball (ball_subset_ball (by change ε / 2 ≤ ε; linarith) hz')
  have hval : ∀ z u v, b' z u v = χ z * b z u v + (1 - χ z) * b y u v := by
    intro z u v
    simp [hb']
  refine ⟨b', ?_, ?_, ?_, ε / 4, by positivity, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact ((χ.contDiff.contDiffAt).smul (hb.contDiffAt (hU.mem_nhds hz))).add
        ((contDiffAt_const.sub χ.contDiff.contDiffAt).smul contDiffAt_const)
    · have hzt : z ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        intro hz'
        exact hz (hball (lt_of_le_of_lt (mem_closedBall.mp hz') (by
          change ε / 2 < ε; linarith)))
      have hev : (χ : E → ℝ) =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
      have heq : b' =ᶠ[𝓝 z] fun _ => b y := by
        filter_upwards [hev] with w hw
        simp only [hb']
        rw [hw]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro z u v
    rw [hval, hval, hsymm y hy u v]
    by_cases hz : χ z = 0
    · rw [hz]; ring
    · rw [hsymm z (hsuppU z hz) u v]
  · intro z v hv
    rw [hval]
    have hin : 0 < b y v v := hpos y hy v hv
    have h0 := χ.nonneg (x := z)
    have h1 := χ.le_one (x := z)
    by_cases hz : χ z = 0
    · rw [hz]
      simpa using hin
    · have hbz := hpos z (hsuppU z hz) v hv
      have hχ : 0 < χ z := lt_of_le_of_ne h0 (Ne.symm hz)
      have : 0 ≤ (1 - χ z) * b y v v := mul_nonneg (by linarith) hin.le
      nlinarith
  · exact (ball_subset_ball (by linarith)).trans hball
  · intro z hz
    have h1 : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp only [hb', h1, one_smul, sub_self, zero_smul, add_zero]

/-- **The scalar Jacobi equation in geodesic parallel coordinates.** For a `C²` positive symmetric
coefficient field `b` on an open set `U` of a two-dimensional space, and a basis `(v₁, v₂)` with
`b(v₁, v₂) ≡ 0`, `b(v₂, v₂) ≡ 1` on `U`, the function `φ(s) = √(b(y + s v₂)(v₁, v₁))` is differentiable
near `0` and `φ''(0) = -K φ(0)` with `K = coefficientSectional b y v₁ v₂`. -/
theorem hasDerivAt_deriv_sqrt_of_geodesicParallel (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U) (hb : ContDiffOn ℝ 2 b U)
    (hsymm : ∀ y ∈ U, ∀ u v, b y u v = b y v u) (hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < b y v v)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (h12 : ∀ y ∈ U, b y v₁ v₂ = 0)
    (h22 : ∀ y ∈ U, b y v₂ v₂ = 1) {y : E} (hy : y ∈ U) :
    (∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => Real.sqrt (b (y + s • v₂) v₁ v₁))
        (deriv (fun s : ℝ => Real.sqrt (b (y + s • v₂) v₁ v₁)) s) s) ∧
      HasDerivAt (deriv (fun s : ℝ => Real.sqrt (b (y + s • v₂) v₁ v₁)))
        (-(coefficientSectional b y v₁ v₂ * Real.sqrt (b y v₁ v₁))) 0 := by
  obtain ⟨b', hb'c, hb's, hb'p, ε, hε, hballU, hb'eq⟩ :=
    exists_global_coefficient_eventuallyEq hU hb hsymm hpos hy
  set W := ball y ε with hW
  have hWo : IsOpen W := isOpen_ball
  have hyW : y ∈ W := mem_ball_self hε
  have hb'd : Differentiable ℝ b' := hb'c.differentiable (by norm_num)
  set e : E → ℝ := fun z => b' z v₁ v₁ with he
  have hed : Differentiable ℝ e := fun z =>
    ((hb'd z).clm_apply (differentiableAt_const v₁)).clm_apply (differentiableAt_const v₁)
  -- the field on `W`
  have h12' : ∀ z ∈ W, b' z v₁ v₂ = 0 := fun z hz => by
    rw [hb'eq z hz]; exact h12 z (hballU hz)
  have h22' : ∀ z ∈ W, b' z v₂ v₂ = 1 := fun z hz => by
    rw [hb'eq z hz]; exact h22 z (hballU hz)
  have hepos : ∀ z, 0 < e z := fun z => hb'p z v₁ (by simpa using hli.ne_zero 0)
  have hd12 : ∀ z ∈ W, fderiv ℝ (fun w => b' w v₁ v₂) z = 0 := by
    intro z hz
    have hev : (fun w => b' w v₁ v₂) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      eventually_of_mem (hWo.mem_nhds hz) fun w hw => h12' w hw
    rw [hev.fderiv_eq]
    simp
  have hd22 : ∀ z ∈ W, fderiv ℝ (fun w => b' w v₂ v₂) z = 0 := by
    intro z hz
    have hev : (fun w => b' w v₂ v₂) =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      eventually_of_mem (hWo.mem_nhds hz) fun w hw => h22' w hw
    rw [hev.fderiv_eq]
    simp
  have hD : ∀ z ∈ W, surfaceGramDet b' v₁ v₂ z = e z := by
    intro z hz
    rw [surfaceGramDet_def, h12' z hz, h22' z hz]
    simp [he]
  -- the potentials on `W`
  have hP : ∀ z ∈ W, surfaceConnectionP b' v₁ v₂ z =
      -(fderiv ℝ e z v₂ / (2 * Real.sqrt (e z))) := by
    intro z hz
    rw [surfaceConnectionP_def, hd12 z hz, h12' z hz, hD z hz]
    have hez := hepos z
    have hs := Real.sqrt_pos.mpr hez
    change (2 * e z * (0 : E →L[ℝ] ℝ) v₁ - e z * fderiv ℝ e z v₂ - 0 * fderiv ℝ e z v₁) /
      (2 * e z * Real.sqrt (e z)) = _
    rw [zero_apply]
    field_simp
    ring
  have hQ : ∀ z ∈ W, surfaceConnectionQ b' v₁ v₂ z = 0 := by
    intro z hz
    rw [surfaceConnectionQ_def, hd22 z hz, h12' z hz]
    simp
  -- the divergence identity at `y`
  have hdiv := coefficientSectional_mul_sqrt_eq_fderiv_sub hE hb'c hb's hb'p hli y
  have hQy : fderiv ℝ (surfaceConnectionQ b' v₁ v₂) y = 0 := by
    have hev : surfaceConnectionQ b' v₁ v₂ =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      eventually_of_mem (hWo.mem_nhds hyW) hQ
    rw [hev.fderiv_eq]
    simp
  have hK : coefficientSectional b' y v₁ v₂ = coefficientSectional b y v₁ v₂ :=
    coefficientSectional_congr_of_eventuallyEq'
      (eventually_of_mem (hWo.mem_nhds hyW) hb'eq) v₁ v₂
  rw [hQy, zero_apply, sub_zero, hD y hyW, hK] at hdiv
  have hPd : DifferentiableAt ℝ (surfaceConnectionP b' v₁ v₂) y :=
    (contDiff_surfaceConnectionP hb'c hb's hb'p hli).differentiable (by norm_num) y
  -- the line through `y`
  set ℓ : ℝ → E := fun s => y + s • v₂ with hℓ
  have hℓd : ∀ s, HasDerivAt ℓ v₂ s := fun s => by
    have h := ((hasDerivAt_id s).smul_const v₂).const_add y
    rw [one_smul] at h
    exact h
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hline : ∀ᶠ s in 𝓝 (0 : ℝ), ℓ s ∈ W := by
    apply hℓc.continuousAt.preimage_mem_nhds
    simpa [hℓ] using hWo.mem_nhds hyW
  set φ : ℝ → ℝ := fun s => Real.sqrt (b (y + s • v₂) v₁ v₁) with hφ
  have hφe : ∀ s, ℓ s ∈ W → φ s = Real.sqrt (e (ℓ s)) := by
    intro s hs
    simp only [hφ, he]
    rw [hb'eq _ hs]
  have hφder : ∀ s, ℓ s ∈ W → HasDerivAt φ (-surfaceConnectionP b' v₁ v₂ (ℓ s)) s := by
    intro s hs
    have he1 : HasDerivAt (fun s => e (ℓ s)) (fderiv ℝ e (ℓ s) v₂) s :=
      (hed (ℓ s)).hasFDerivAt.comp_hasDerivAt s (hℓd s)
    have he2 := he1.sqrt (hepos (ℓ s)).ne'
    rw [hP _ hs, neg_neg]
    have hev : φ =ᶠ[𝓝 s] fun s => Real.sqrt (e (ℓ s)) := by
      have hpre : ∀ᶠ t in 𝓝 s, ℓ t ∈ W := hℓc.continuousAt.preimage_mem_nhds (hWo.mem_nhds hs)
      filter_upwards [hpre] with t ht using hφe t ht
    exact he2.congr_of_eventuallyEq hev
  have hderiv_eq : deriv φ =ᶠ[𝓝 (0 : ℝ)] fun s => -surfaceConnectionP b' v₁ v₂ (ℓ s) := by
    have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 s, ℓ t ∈ W := hline.eventually_nhds
    filter_upwards [hline] with s hs using (hφder s hs).deriv
  refine ⟨?_, ?_⟩
  · filter_upwards [hline] with s hs
    have h := hφder s hs
    rw [h.deriv]
    exact h
  · have hPl : HasDerivAt (fun s => -surfaceConnectionP b' v₁ v₂ (ℓ s))
        (-(fderiv ℝ (surfaceConnectionP b' v₁ v₂) y v₂)) 0 := by
      have hℓ0 : ℓ 0 = y := by simp [hℓ]
      have hPd' : HasFDerivAt (surfaceConnectionP b' v₁ v₂)
          (fderiv ℝ (surfaceConnectionP b' v₁ v₂) y) (ℓ 0) := by
        rw [hℓ0]; exact hPd.hasFDerivAt
      exact (hPd'.comp_hasDerivAt 0 (hℓd 0)).neg
    have hy' : Real.sqrt (b y v₁ v₁) = Real.sqrt (e y) := by
      simp only [he]
      rw [hb'eq y hyW]
    rw [hy', hdiv]
    exact hPl.congr_of_eventuallyEq hderiv_eq

end DifferentialGeometry.Analysis
