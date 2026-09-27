import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampUniqueness
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.AlongCurveKato

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]

namespace ProductCurve

variable (c : ProductCurve M)

def Dt (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t =>
    (covDerivAlong (I := I) (g t) (fun z => c.projection.lift x z)
        (fun z => (V x z).1) t,
      derivWithin (fun z => (V x z).2) J t)

omit [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem Dt_fst (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (V : c.Field (I := I)) (x t : ℝ) :
    (c.Dt g J V x t).1 =
      covDerivAlong (I := I) (g t) (fun z => c.projection.lift x z)
        (fun z => (V x z).1) t := rfl

omit [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem Dt_snd (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (V : c.Field (I := I)) (x t : ℝ) :
    (c.Dt g J V x t).2 = derivWithin (fun z => (V x z).2) J t := rfl

omit [CompleteSpace E] in
theorem ds_normSq (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) (x t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 (fun z : ℝ => c.projection.lift z t) x)
    (hV : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun z : ℝ => c.projection.lift z t)
        (fun z => (V z t).1) x) x)
    (hV₂ : DifferentiableAt ℝ (fun z : ℝ => (V z t).2) x) :
    c.ds g lambda (fun y r => c.normSq g lambda V y r) x t =
      2 * c.inner g lambda x t (c.Ds g lambda V x t) (V x t) := by
  have hinner := inner_self_hasDerivAt_along (I := I) (n := 1) le_rfl (g t)
    (fun z : ℝ => c.projection.lift z t) (fun z => (V z t).1) x hγ hV
  have hsnd := (hV₂.hasDerivAt.mul hV₂.hasDerivAt).const_mul (lambda ^ 2)
  have hderiv : HasDerivAt (fun z : ℝ => (g t).inner (c.projection.lift z t)
        (V z t).1 (V z t).1 + lambda ^ 2 * (V z t).2 * (V z t).2)
      (2 * (g t).inner (c.projection.lift x t)
          (covDerivAlong (I := I) (g t) (fun z => c.projection.lift z t)
            (fun z => (V z t).1) x) (V x t).1 +
        lambda ^ 2 * (deriv (fun z : ℝ => (V z t).2) x * (V x t).2 +
          (V x t).2 * deriv (fun z : ℝ => (V z t).2) x)) x := by
    have hfun : (fun z : ℝ => (g t).inner (c.projection.lift z t)
          (V z t).1 (V z t).1 + lambda ^ 2 * (V z t).2 * (V z t).2) =
        (fun z : ℝ => (g t).inner (c.projection.lift z t) (V z t).1 (V z t).1 +
          lambda ^ 2 * ((V z t).2 * (V z t).2)) := by
      funext z; ring
    rw [hfun]
    exact hinner.add hsnd
  have hd : deriv (fun z : ℝ => c.normSq g lambda V z t) x =
      2 * c.inner g lambda x t (c.Dx g V x t) (V x t) := by
    have hne : (fun z : ℝ => c.normSq g lambda V z t) =
        (fun z : ℝ => (g t).inner (c.projection.lift z t) (V z t).1 (V z t).1 +
          lambda ^ 2 * (V z t).2 * (V z t).2) := by
      funext z; rfl
    rw [hne, hderiv.deriv]
    simp only [ProductCurve.Dx, ProductCurve.inner]
    ring
  have hsmul : c.inner g lambda x t (c.Ds g lambda V x t) (V x t) =
      (c.speed g lambda x t)⁻¹ * c.inner g lambda x t (c.Dx g V x t) (V x t) := by
    simp only [ProductCurve.Ds, ProductCurve.inner, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, smul_apply, map_smul]
    ring
  simp only [ProductCurve.ds, hd, hsmul]
  ring

end ProductCurve

namespace CurveMap

variable (c : CurveMap M)

omit [CompleteSpace E] in
theorem ds_normSq (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) (x t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 (fun z : ℝ => c.lift z t) x)
    (hV : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun z : ℝ => c.lift z t) (fun z => V z t) x) x) :
    c.ds g (fun y r => c.normSq g V y r) x t =
      2 * (g t).inner (c.lift x t) (c.Ds g V x t) (V x t) := by
  have hinner := inner_self_hasDerivAt_along (I := I) (n := 1) le_rfl (g t)
    (fun z : ℝ => c.lift z t) (fun z => V z t) x hγ hV
  have hd : deriv (fun z : ℝ => c.normSq g V z t) x =
      2 * (g t).inner (c.lift x t) (c.Dx g V x t) (V x t) := by
    have hne : (fun z : ℝ => c.normSq g V z t) =
        (fun z : ℝ => (g t).inner (c.lift z t) (V z t) (V z t)) := by
      funext z; rfl
    rw [hne, hinner.deriv]
    rfl
  have hsmul : (g t).inner (c.lift x t) (c.Ds g V x t) (V x t) =
      (c.speed g x t)⁻¹ * (g t).inner (c.lift x t) (c.Dx g V x t) (V x t) := by
    simp only [CurveMap.Ds, map_smul, smul_apply, smul_eq_mul]
  simp only [CurveMap.ds, hd, hsmul]
  ring

end CurveMap

namespace ProductCurve

variable (c : ProductCurve M)

section ScalarMaximumPrinciple

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem velocity_contMDiff (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ)) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I γ ∘ fun x : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ))
  exact (hγ.contMDiff_tangentMap (le_refl _)).comp hunit

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem inner_contDiff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ x, TangentSpace I (γ x))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (V x)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (W x))) :
    ContDiff ℝ ∞ (fun x => g.inner (γ x) (V x) (W x)) := by
  have htotal : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (γ x) (g.inner (γ x) (V x) (W x))) := by
    apply ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.comp hγ
    · exact hV
    · exact hW
  apply contMDiff_iff_contDiff.mp
  intro x
  have hx := htotal x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem speed_contDiff (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (hlambda : 0 < lambda) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => c.speed g lambda x t) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => c.projection.lift x t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c.projection J hc.1 t ht)
  have hX : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.projection.lift x t)
        (c.projection.X (I := I) x t)) := by
    have h := velocity_contMDiff (I := I) (fun x : ℝ => c.projection.lift x t) hγ
    simpa only [CurveMap.X] using h
  have hinner := inner_contDiff (I := I) (g t) (fun x : ℝ => c.projection.lift x t)
    (fun x => c.projection.X x t) (fun x => c.projection.X x t) hγ hX hX
  have hslice : ContDiff ℝ ∞ (fun x : ℝ => c.y x t) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun x : ℝ => (x, t)) (univ : Set ℝ) :=
      hc.2.comp (by fun_prop) (fun x _ => ⟨trivial, ht⟩)
    simpa [Function.comp_def] using contDiffOn_univ.mp hcomp
  have hderiv : ContDiff ℝ ∞ (fun x : ℝ => deriv (fun z => c.y z t) x) := by
    have h := (contDiff_infty_iff_deriv.mp hslice).2
    simpa using h
  have hsub : ContDiff ℝ ∞ (fun x : ℝ =>
      (g t).inner (c.projection.lift x t) (c.projection.X x t) (c.projection.X x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x * deriv (fun z => c.y z t) x)) :=
    hinner.add (contDiff_const.mul (hderiv.mul hderiv))
  have hspeed : (fun x => c.speed g lambda x t) = fun x => Real.sqrt
      ((g t).inner (c.projection.lift x t) (c.projection.X x t) (c.projection.X x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x * deriv (fun z => c.y z t) x)) := by
    funext x
    have harg : c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
        (g t).inner (c.projection.lift x t) (c.projection.X x t) (c.projection.X x t) +
          lambda ^ 2 * (deriv (fun z => c.y z t) x * deriv (fun z => c.y z t) x) := by
      simp only [ProductCurve.inner, ProductCurve.X]
      ring
    simp only [ProductCurve.speed, harg]
  rw [hspeed]
  refine hsub.sqrt fun x => ne_of_gt ?_
  have hXne : c.projection.X (I := I) x t ≠ 0 ∨ deriv (fun z => c.y z t) x ≠ 0 := by
    by_contra hcon
    rw [not_or, not_ne_iff, not_ne_iff] at hcon
    exact hi x t ht (by simp [ProductCurve.X, hcon.1, hcon.2, Prod.mk_eq_zero])
  rcases hXne with h1 | h2
  · exact lt_of_lt_of_le ((g t).pos _ _ h1)
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (mul_self_nonneg _)))
  · exact add_pos_of_nonneg_of_pos (metric_inner_self_nonneg (g t) _ _)
      (mul_pos (pow_pos hlambda 2) (mul_self_pos.mpr h2))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem deriv_deriv_nonpos_of_isLocalMax {G : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax G x₀) (hG : ContDiffAt ℝ 2 G x₀) :
    deriv (deriv G) x₀ ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hd0 : deriv G x₀ = 0 := hmax.deriv_eq_zero
  have h2 : HasDerivAt (deriv G) (deriv (deriv G) x₀) x₀ :=
    ((hG.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hEv : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → deriv (deriv G) x₀ / 2 < slope (deriv G) x₀ y :=
    eventually_nhdsWithin_iff.mp
      (h2.tendsto_slope.eventually (eventually_gt_nhds (by linarith)))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hEv
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hmax
  obtain ⟨v, hvopen, hvmem, hvCD⟩ :=
    (hG.contDiffWithinAt (s := univ)).contDiffOn' (m := 2) le_rfl (by simp)
  have hvmem' : v ∈ 𝓝 x₀ := hvopen.mem_nhds hvmem
  have hvCD' : ContDiffOn ℝ 2 G v := by simpa using hvCD
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hvmem'
  have hm : 0 < min δ (min ε ρ) := lt_min hδpos (lt_min hεpos hρpos)
  have hhδ : min δ (min ε ρ) / 2 < δ := by
    have := min_le_left δ (min ε ρ); linarith
  have hhε : min δ (min ε ρ) / 2 < ε := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_left ε ρ; linarith
  have hhρ : min δ (min ε ρ) / 2 < ρ := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_right ε ρ; linarith
  have hderivpos : ∀ y ∈ Ioo x₀ (x₀ + min δ (min ε ρ) / 2), 0 < deriv G y := by
    intro y hy
    have hdist : dist y x₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]
      linarith [hy.2, hhδ]
    have hne : y ≠ x₀ := by linarith [hy.1]
    have hb := hδ hdist hne
    have hsl : slope (deriv G) x₀ y = deriv G y / (y - x₀) := by
      rw [slope_def_field, hd0, sub_zero]
    rw [hsl] at hb
    have hyx : 0 < y - x₀ := by linarith [hy.1]
    have : 0 < deriv G y / (y - x₀) := by linarith
    exact (div_pos_iff_of_pos_right hyx).mp this
  have hcont : ContinuousOn G (Icc x₀ (x₀ + min δ (min ε ρ) / 2)) := by
    refine hvCD'.continuousOn.mono ?_
    intro y hy
    refine hρ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1, hm], by linarith [hy.2, hhρ]⟩
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    (fun y hy => by
      rw [interior_Icc] at hy
      exact hderivpos y hy)
  have hlt : G x₀ < G (x₀ + min δ (min ε ρ) / 2) :=
    hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
      (by linarith)
  have hle : G (x₀ + min δ (min ε ρ) / 2) ≤ G x₀ :=
    hε (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hm], by linarith [hhε]⟩)
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem deriv_inv_mul_nonpos {σ φ : ℝ → ℝ} {x₀ L : ℝ}
    (hσ : ContinuousAt σ x₀) (hσpos : 0 < σ x₀)
    (hφ0 : φ x₀ = 0) (hφ : HasDerivAt φ L x₀) (hL : L ≤ 0) :
    deriv (fun y => (σ y)⁻¹ * φ y) x₀ ≤ 0 := by
  have hderiv : HasDerivAt (fun y => (σ y)⁻¹ * φ y) ((σ x₀)⁻¹ * L) x₀ := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 : Tendsto (fun y => (σ y)⁻¹) (𝓝[≠] x₀) (𝓝 ((σ x₀)⁻¹)) :=
      (hσ.inv₀ (ne_of_gt hσpos)).tendsto.mono_left inf_le_left
    have h2 : Tendsto (fun y => (φ y - φ x₀) / (y - x₀)) (𝓝[≠] x₀) (𝓝 L) := by
      simpa only [slope_fun_def_field] using hφ.tendsto_slope
    refine Tendsto.congr' ?_ (h1.mul h2)
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field]
    rw [hφ0]
    ring
  rw [hderiv.deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hL

end ScalarMaximumPrinciple

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
theorem scalar_maximum_principle (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    {s u : ℝ} (hsu : s < u)
    (hc : c.SmoothOn (I := I) (Icc s u)) (hi : c.ImmersedOn (I := I) (Icc s u))
    (hlambda : 0 < lambda)
    (f : ℝ → ℝ → ℝ) (hper : ∀ x t, f (x + 1) t = f x t)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      derivWithin (f x) (Icc s u) t ≤
        c.ds g lambda (c.ds g lambda f) x t + A * f x t + F t)
    (hinit : ∀ x, f x s ≤ y s) :
    ∀ x t, t ∈ Icc s u → f x t ≤ y t := by
  classical
  let _ := hF
  have hyc : ContinuousOn y (Icc s u) := fun t ht => (hy t ht).continuousWithinAt
  suffices hkey : ∀ η : ℝ, 0 < η → ∀ x ∈ Icc 0 1, ∀ t ∈ Icc s u,
      Real.exp (-A * (t - s)) * (f x t - y t) ≤ η * (1 + (t - s)) by
    intro x t ht
    have hx : f x t = f (Int.fract x) t := by
      have hp : Function.Periodic (fun z => f z t) 1 := fun z => hper z t
      have h1 := hp.int_mul ⌊x⌋ (Int.fract x)
      simp only [mul_one] at h1
      rw [Int.fract_add_floor x] at h1
      exact h1
    have hxI : Int.fract x ∈ Icc 0 1 :=
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have hmain : Real.exp (-A * (t - s)) * (f x t - y t) ≤ 0 := by
      rw [hx]
      have hpos1 : 0 < 1 + (t - s) := by linarith [ht.1]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hη : 0 < ε / (1 + (t - s)) := div_pos hε hpos1
      have h1 := hkey (ε / (1 + (t - s))) hη (Int.fract x) hxI t ht
      have h2 : ε / (1 + (t - s)) * (1 + (t - s)) = ε := by field_simp
      linarith
    nlinarith [hmain, Real.exp_pos (-A * (t - s))]
  intro η hη x₁ hx₁ t₁ ht₁
  by_contra hcon
  rw [not_le] at hcon
  set W : ℝ → ℝ → ℝ := fun x t =>
    Real.exp (-A * (t - s)) * (f x t - y t) - η * (1 + (t - s)) with hW
  have hWper : ∀ x t, W (x + 1) t = W x t := by
    intro x t
    simp only [hW, hper x t]
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) (Icc 0 1 ×ˢ Icc s u) := by
    have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-A * (p.2 - s))) univ :=
      Real.continuous_exp.comp_continuousOn (by fun_prop)
    have hy2 : ContinuousOn (fun p : ℝ × ℝ => y p.2) (univ ×ˢ Icc s u) :=
      hyc.comp (f := fun p : ℝ × ℝ => p.2) continuous_snd.continuousOn
        (fun p hp => hp.2)
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        Real.exp (-A * (p.2 - s)) * (f p.1 p.2 - y p.2)) (univ ×ˢ Icc s u) :=
      (hexp.mono (Set.subset_univ _)).mul (hf.continuousOn.sub hy2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => η * (1 + (p.2 - s))) univ :=
      (continuous_const.mul (continuous_const.add
        (continuous_snd.sub continuous_const))).continuousOn
    refine (h1.sub (h2.mono (Set.subset_univ _))).mono ?_
    exact Set.prod_mono (Set.subset_univ _) Subset.rfl
  obtain ⟨p₀, hp₀K, hp₀max⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(0, s), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hsu.le⟩⟩⟩ hcontW
  have hp₀max' : ∀ p ∈ (Icc 0 1 ×ˢ Icc s u), W p.1 p.2 ≤ W p₀.1 p₀.2 :=
    fun _ hp => hp₀max hp
  have ht₀ : p₀.2 ∈ Icc s u := hp₀K.2
  have hx₀ : p₀.1 ∈ Icc 0 1 := hp₀K.1
  have hmaxT : IsMaxOn (fun t => W p₀.1 t) (Icc s u) p₀.2 :=
    fun t ht => hp₀max' (p₀.1, t) ⟨hx₀, ht⟩
  have hMpos : 0 < W p₀.1 p₀.2 := by
    have hle : W x₁ t₁ ≤ W p₀.1 p₀.2 := hp₀max' (x₁, t₁) ⟨hx₁, ht₁⟩
    have h1 : 0 < W x₁ t₁ := by
      simp only [hW]
      linarith
    exact lt_of_lt_of_le h1 hle
  have hWs : W p₀.1 s < 0 := by
    have h1 : W p₀.1 s = (f p₀.1 s - y s) - η := by
      simp only [hW, sub_self, mul_zero, Real.exp_zero, one_mul, add_zero, mul_one]
    rw [h1]
    linarith [hinit p₀.1, hη]
  have ht₀pos : s < p₀.2 := by
    rcases lt_or_eq_of_le ht₀.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hMpos
      linarith
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) p₀.2 := (uniqueDiffOn_Icc hsu) p₀.2 ht₀
  have hfdiff : HasDerivWithinAt (fun t => f p₀.1 t)
      (derivWithin (f p₀.1) (Icc s u) p₀.2) (Icc s u) p₀.2 := by
    have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => f p₀.1 t) (Icc s u) p₀.2 :=
      (hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩).comp p₀.2
        (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
        (fun t ht => ⟨trivial, ht⟩)
    exact (hcomp.differentiableWithinAt (by norm_num)).hasDerivWithinAt
  have hderivW : HasDerivWithinAt (fun t => W p₀.1 t)
      (Real.exp (-A * (p₀.2 - s)) * (-A * (f p₀.1 p₀.2 - y p₀.2) +
        (derivWithin (f p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))) - η)
      (Icc s u) p₀.2 := by
    have h1 : HasDerivWithinAt (fun t : ℝ => Real.exp (-A * (t - s)))
        (Real.exp (-A * (p₀.2 - s)) * (-A)) (Icc s u) p₀.2 := by
      have h2 : HasDerivAt (fun t : ℝ => -A * (t - s)) (-A) p₀.2 := by
        simpa using ((hasDerivAt_id p₀.2).sub_const s).const_mul (-A)
      exact h2.exp.hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t => f p₀.1 t - y t)
        (derivWithin (f p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))
        (Icc s u) p₀.2 :=
      hfdiff.sub (hy p₀.2 ht₀)
    have h4 : HasDerivWithinAt (fun t : ℝ => η * (1 + (t - s))) η (Icc s u) p₀.2 := by
      have h5 : HasDerivAt (fun t : ℝ => η * (1 + (t - s))) η p₀.2 := by
        simpa using (((hasDerivAt_id p₀.2).sub_const s).const_add 1).const_mul η
      exact h5.hasDerivWithinAt
    have h6 := (h1.mul h3).sub h4
    refine h6.congr_deriv ?_
    ring
  have hnonneg : 0 ≤ derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 := by
    have htend := hasDerivWithinAt_iff_tendsto_slope.mp hderivW
    have hsub : (Icc s u \ {p₀.2}) ∩ Iio p₀.2 ⊆ Icc s u \ {p₀.2} :=
      Set.inter_subset_left
    have htend2 := htend.mono_left (nhdsWithin_mono p₀.2 hsub)
    have hcl : p₀.2 ∈ closure ((Icc s u \ {p₀.2}) ∩ Iio p₀.2) := by
      have hsub' : Ioo s p₀.2 ⊆ (Icc s u \ {p₀.2}) ∩ Iio p₀.2 := by
        intro t ht
        exact ⟨⟨⟨ht.1.le, ht.2.le.trans ht₀.2⟩, ne_of_lt ht.2⟩, ht.2⟩
      have h2 : p₀.2 ∈ closure (Ioo s p₀.2) := by
        rw [closure_Ioo (ne_of_lt ht₀pos)]
        exact right_mem_Icc.mpr ht₀pos.le
      exact closure_mono hsub' h2
    rw [hderivW.derivWithin huniq]
    refine ge_of_tendsto (hx := mem_closure_iff_nhdsWithin_neBot.mp hcl) htend2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨⟨htJ, htne⟩, htlt⟩ := ht
    have hlt : t < p₀.2 := htlt
    have hle : W p₀.1 t ≤ W p₀.1 p₀.2 := hmaxT htJ
    rw [slope_def_field]
    exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  have hlocalW : ∀ᶠ x in 𝓝 p₀.1, W x p₀.2 ≤ W p₀.1 p₀.2 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨1 / 2, by norm_num, fun y hy => ?_⟩
    rw [Real.dist_eq, abs_lt] at hy
    by_cases hy01 : y ∈ Icc 0 1
    · exact hp₀max' (y, p₀.2) ⟨hy01, ht₀⟩
    · rw [mem_Icc] at hy01
      have hy01' : 0 ≤ y → 1 < y := by
        intro h
        by_contra h1
        exact hy01 ⟨h, not_lt.mp h1⟩
      rcases lt_or_ge y 0 with hlt | hge
      · have hy1 : y + 1 ∈ Icc 0 1 :=
          ⟨by linarith [hy.1, hx₀.1], by linarith [hlt]⟩
        rw [← hWper y p₀.2]
        exact hp₀max' (y + 1, p₀.2) ⟨hy1, ht₀⟩
      · have hgt : 1 < y := hy01' hge
        have hy1 : y - 1 ∈ Icc 0 1 :=
          ⟨by linarith [hgt], by linarith [hy.2, hx₀.2]⟩
        have hshift : y - 1 + 1 = y := by ring
        rw [← hshift, hWper (y - 1) p₀.2]
        exact hp₀max' (y - 1, p₀.2) ⟨hy1, ht₀⟩
  have hlocmaxW : IsLocalMax (fun x => W x p₀.2) p₀.1 := hlocalW
  have hlocmaxf : IsLocalMax (fun x => f x p₀.2) p₀.1 := by
    filter_upwards [hlocalW] with z hz
    simp only [hW] at hz
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have h2 : Real.exp (-A * (p₀.2 - s)) * (f z p₀.2 - y p₀.2) ≤
        Real.exp (-A * (p₀.2 - s)) * (f p₀.1 p₀.2 - y p₀.2) := by linarith
    have h3 := le_of_mul_le_mul_left h2 hexp
    linarith
  have hslice2 : ContDiffAt ℝ 2 (fun x => f x p₀.2) p₀.1 := by
    have hjoint : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)
        (univ ×ˢ Icc s u) (p₀.1, p₀.2) := hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩
    have hsnd : ContDiffWithinAt ℝ ∞ (fun x : ℝ => (x, p₀.2)) univ p₀.1 := by
      fun_prop
    have hmaps : MapsTo (fun x : ℝ => (x, p₀.2)) univ (univ ×ˢ Icc s u) :=
      fun _ _ => ⟨trivial, ht₀⟩
    have hcomp := hjoint.comp p₀.1 hsnd hmaps
    exact ((contDiffWithinAt_univ.mp hcomp).of_le (m := 2)
      (WithTop.coe_le_coe.mpr le_top))
  have hderiv0 : deriv (fun x => f x p₀.2) p₀.1 = 0 := hlocmaxf.deriv_eq_zero
  have hsecond : deriv (deriv (fun x => f x p₀.2)) p₀.1 ≤ 0 :=
    deriv_deriv_nonpos_of_isLocalMax hlocmaxf hslice2
  have hds0 : c.ds g lambda f p₀.1 p₀.2 = 0 := by
    simp only [ProductCurve.ds, hderiv0, mul_zero]
  have hdsds : c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2 ≤ 0 := by
    have hσcont : ContinuousAt (fun y => c.speed g lambda y p₀.2) p₀.1 :=
      (speed_contDiff c g lambda hc hi hlambda p₀.2 ht₀).continuous.continuousAt
    have hσpos : 0 < c.speed g lambda p₀.1 p₀.2 := by
      have hinnerpos : 0 < c.inner g lambda p₀.1 p₀.2
          (c.X (I := I) p₀.1 p₀.2) (c.X (I := I) p₀.1 p₀.2) := by
        rcases eq_or_ne (c.projection.X (I := I) p₀.1 p₀.2) 0 with h1 | h1
        · have h2 : deriv (fun z => c.y z p₀.2) p₀.1 ≠ 0 := by
            intro h2
            exact hi p₀.1 p₀.2 ht₀
              (by simp [ProductCurve.X, h1, h2, Prod.mk_eq_zero])
          have hsq : 0 < (lambda * deriv (fun z => c.y z p₀.2) p₀.1) *
              (lambda * deriv (fun z => c.y z p₀.2) p₀.1) :=
            mul_self_pos.mpr (mul_ne_zero (ne_of_gt hlambda) h2)
          have hinner : c.inner g lambda p₀.1 p₀.2
              (c.X (I := I) p₀.1 p₀.2) (c.X (I := I) p₀.1 p₀.2) =
              (lambda * deriv (fun z => c.y z p₀.2) p₀.1) *
                (lambda * deriv (fun z => c.y z p₀.2) p₀.1) := by
            simp only [ProductCurve.inner, ProductCurve.X, h1, map_zero]
            ring
          rw [hinner]; exact hsq
        · have hg : 0 < (g p₀.2).inner (c.projection.lift p₀.1 p₀.2)
              (c.projection.X (I := I) p₀.1 p₀.2)
              (c.projection.X (I := I) p₀.1 p₀.2) :=
            (g p₀.2).pos _ _ h1
          have hsq : 0 ≤ (lambda * deriv (fun z => c.y z p₀.2) p₀.1) *
              (lambda * deriv (fun z => c.y z p₀.2) p₀.1) := mul_self_nonneg _
          have hinner : c.inner g lambda p₀.1 p₀.2
              (c.X (I := I) p₀.1 p₀.2) (c.X (I := I) p₀.1 p₀.2) =
              (g p₀.2).inner (c.projection.lift p₀.1 p₀.2)
                (c.projection.X (I := I) p₀.1 p₀.2)
                (c.projection.X (I := I) p₀.1 p₀.2) +
              (lambda * deriv (fun z => c.y z p₀.2) p₀.1) *
                (lambda * deriv (fun z => c.y z p₀.2) p₀.1) := by
            simp only [ProductCurve.inner, ProductCurve.X]
            ring
          rw [hinner]
          exact add_pos_of_pos_of_nonneg hg hsq
      exact Real.sqrt_pos.2 hinnerpos
    have hφderiv : HasDerivAt (fun y => deriv (fun z => f z p₀.2) y)
        (deriv (deriv (fun z => f z p₀.2)) p₀.1) p₀.1 :=
      ((hslice2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hkey := deriv_inv_mul_nonpos hσcont hσpos hderiv0 hφderiv hsecond
    have hfund : c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2 =
        (c.speed g lambda p₀.1 p₀.2)⁻¹ *
          deriv (fun y => (c.speed g lambda y p₀.2)⁻¹ * deriv (fun z => f z p₀.2) y) p₀.1 :=
      rfl
    rw [hfund]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hkey
  have hbound : derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 < 0 := by
    rw [hderivW.derivWithin huniq]
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have hpde' := hpde p₀.1 p₀.2 ht₀
    have hA : -A * (f p₀.1 p₀.2 - y p₀.2) +
          (derivWithin (f p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2)) ≤
        -A * (f p₀.1 p₀.2 - y p₀.2) +
          (c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2 +
            A * f p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) := by linarith
    have hB : -A * (f p₀.1 p₀.2 - y p₀.2) +
          (c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2 +
            A * f p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) =
        c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2 := by ring
    have hC : Real.exp (-A * (p₀.2 - s)) *
        (c.ds g lambda (c.ds g lambda f) p₀.1 p₀.2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hexp.le hdsds
    have hD := mul_le_mul_of_nonneg_left (hA.trans_eq hB) hexp.le
    linarith
  linarith [hnonneg, hbound]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem inner_add_left (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (x t : ℝ) (u v w : TangentSpace I (c.projection.lift x t) × ℝ) :
    c.inner g lambda x t (u + v) w =
      c.inner g lambda x t u w + c.inner g lambda x t v w := by
  simp only [ProductCurve.inner, Prod.fst_add, Prod.snd_add, map_add,
    add_apply]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem normSq_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) (x t : ℝ) :
    0 ≤ c.normSq g lambda V x t := by
  have hsq : 0 ≤ (lambda * (V x t).2) * (lambda * (V x t).2) := mul_self_nonneg _
  simp only [ProductCurve.normSq, ProductCurve.inner]
  nlinarith [hsq, metric_inner_self_nonneg (g t) (c.projection.lift x t) (V x t).1]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem normSq_eq_zero_of_apply_eq_zero (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) (x t : ℝ) (hV : V x t = 0) :
    c.normSq g lambda V x t = 0 := by
  simp [ProductCurve.normSq, ProductCurve.inner, hV]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem ds_zero (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) :
    c.ds g lambda (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  funext x t
  simp only [ProductCurve.ds, deriv_const, mul_zero]

structure DifferenceEquation
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (s T : ℝ)
    (c₁ c₂ : ProductCurve M) where
  field : c₁.Field (I := I)
  initial : ∀ x, field x s = 0
  lower : c₁.Field (I := I)
  drift : ℝ
  equation : ∀ x t, t ∈ Icc s T →
    c₁.Dt g (Icc s T) field x t =
      c₁.Ds g lambda (c₁.Ds g lambda field) x t + lower x t
  lower_bound : ∀ x t, t ∈ Icc s T →
    2 * |c₁.inner g lambda x t (lower x t) (field x t)| ≤
      c₁.normSq g lambda (c₁.Ds g lambda field) x t +
        drift * c₁.normSq g lambda field x t
  detects : ∀ x t, t ∈ Icc s T → c₁.normSq g lambda field x t = 0 →
    c₁.map (x : Surgery.Topology.Circle) t = c₂.map (x : Surgery.Topology.Circle) t

structure DifferenceSubsolution
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (s T : ℝ)
    (c₁ c₂ : ProductCurve M) where
  discrepancy : ℝ → ℝ → ℝ
  drift : ℝ
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => discrepancy p.1 p.2) (univ ×ˢ Icc s T)
  periodic : ∀ x t, discrepancy (x + 1) t = discrepancy x t
  initial : ∀ x, discrepancy x s = 0
  nonneg : ∀ x t, t ∈ Icc s T → 0 ≤ discrepancy x t
  inequality : ∀ x t, t ∈ Icc s T →
    derivWithin (discrepancy x) (Icc s T) t ≤
      c₁.ds g lambda (c₁.ds g lambda discrepancy) x t + drift * discrepancy x t
  detects : ∀ x t, t ∈ Icc s T → discrepancy x t = 0 →
    c₁.map (x : Surgery.Topology.Circle) t = c₂.map (x : Surgery.Topology.Circle) t

def differenceSubsolution_of_differenceEquation
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (s T : ℝ)
    (c₁ c₂ : ProductCurve M) (h : c₁.DifferenceEquation (I := I) g lambda s T c₂)
    (hsmooth : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => c₁.normSq g lambda h.field p.1 p.2) (univ ×ˢ Icc s T))
    (hperiodic : ∀ x t,
      c₁.normSq g lambda h.field (x + 1) t = c₁.normSq g lambda h.field x t)
    (curvature : ℝ)
    (hkatoTime : ∀ x t, t ∈ Icc s T →
      derivWithin (fun r => c₁.normSq g lambda h.field x r) (Icc s T) t ≤
        2 * c₁.inner g lambda x t (c₁.Dt g (Icc s T) h.field x t) (h.field x t) +
          curvature * c₁.normSq g lambda h.field x t)
    (hkatoSpace : ∀ x t, t ∈ Icc s T →
      c₁.ds g lambda (c₁.ds g lambda
          (fun y r => c₁.normSq g lambda h.field y r)) x t =
        2 * c₁.inner g lambda x t
            (c₁.Ds g lambda (c₁.Ds g lambda h.field) x t) (h.field x t) +
          2 * c₁.normSq g lambda (c₁.Ds g lambda h.field) x t) :
    c₁.DifferenceSubsolution (I := I) g lambda s T c₂ where
  discrepancy := fun x t => c₁.normSq g lambda h.field x t
  drift := h.drift + curvature
  smooth := hsmooth
  periodic := hperiodic
  initial := fun x =>
    normSq_eq_zero_of_apply_eq_zero (I := I) c₁ g lambda h.field x s (h.initial x)
  nonneg := fun x t _ => normSq_nonneg (I := I) c₁ g lambda h.field x t
  inequality := by
    intro x t ht
    have hsigma : 0 ≤ c₁.normSq g lambda (c₁.Ds g lambda h.field) x t :=
      normSq_nonneg (I := I) c₁ g lambda _ x t
    have hsplit : 2 * c₁.inner g lambda x t
        (c₁.Dt g (Icc s T) h.field x t) (h.field x t) =
        c₁.ds g lambda (c₁.ds g lambda
          (fun y r => c₁.normSq g lambda h.field y r)) x t -
          2 * c₁.normSq g lambda (c₁.Ds g lambda h.field) x t +
        2 * c₁.inner g lambda x t (h.lower x t) (h.field x t) := by
      rw [h.equation x t ht, ProductCurve.inner_add_left, hkatoSpace x t ht]
      ring
    have habs : 2 * c₁.inner g lambda x t (h.lower x t) (h.field x t) ≤
        2 * |c₁.inner g lambda x t (h.lower x t) (h.field x t)| := by
      linarith [le_abs_self (c₁.inner g lambda x t (h.lower x t) (h.field x t))]
    have hbound := h.lower_bound x t ht
    have htime := hkatoTime x t ht
    linarith
  detects := h.detects

def differenceSubsolution_self (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (s T : ℝ) (c : ProductCurve M) :
    c.DifferenceSubsolution (I := I) g lambda s T c where
  discrepancy := fun _ _ => 0
  drift := 0
  smooth := contDiffOn_const
  periodic := fun _ _ => rfl
  initial := fun _ => rfl
  nonneg := fun _ _ _ => le_rfl
  inequality := by
    intro x t _
    rw [ProductCurve.ds_zero, ProductCurve.ds_zero]
    simp
  detects := fun _ _ _ _ => rfl

end ProductCurve

section Wiring

variable [SigmaCompactSpace M] [T2Space M]
variable {D : RealTimeInterval} {a b : ℝ}

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem rampLocalUniqueness_of_differenceSubsolution
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (h : ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b → ∀ c₁ c₂ : ProductCurve M,
      c₁.IsSolutionOn B.family.metric lambda (Icc s T) →
      c₂.IsSolutionOn B.family.metric lambda (Icc s T) →
      (∀ z, c₁.map z s = c₂.map z s) →
      c₁.DifferenceSubsolution (I := I) B.family.metric lambda s T c₂) :
    RampLocalUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda := by
  intro s t₁ t₂ has hs₁ hs₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ h₀ z t ht
  set T : ℝ := min t₁ t₂ with hT
  have hsT : s < T := lt_min hs₁ hs₂
  have hTt₁ : T ≤ t₁ := min_le_left t₁ t₂
  have hTt₂ : T ≤ t₂ := min_le_right t₁ t₂
  have hTb : T ≤ b := hTt₁.trans hb₁
  have hc₁' : c₁.IsSolutionOn B.family.metric lambda (Icc s T) :=
    hc₁.mono_Icc le_rfl hTt₁ hsT
  have hc₂' : c₂.IsSolutionOn B.family.metric lambda (Icc s T) :=
    hc₂.mono_Icc le_rfl hTt₂ hsT
  obtain ⟨ρ, drift, hsmooth, hper, hinit, hnonneg, hineq, hdet⟩ :=
    h s T has hsT hTb c₁ c₂ hc₁' hc₂' h₀
  have hcomp : ∀ x r, r ∈ Icc s T → ρ x r ≤ 0 :=
    c₁.scalar_maximum_principle B.family.metric lambda hsT hc₁'.smooth hc₁'.immersed
      hlambda ρ hper hsmooth drift (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      continuousOn_const
      (fun r _ => by simpa using (hasDerivWithinAt_const (x := r) (s := Icc s T) (c := (0 : ℝ))))
      (fun x r hr => by simpa using hineq x r hr)
      (fun x => by rw [hinit x])
  obtain ⟨x, -, hx⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  rw [← hx]
  have htT : t ∈ Icc s T := by rw [hT]; exact ht
  exact hdet x t htT (le_antisymm (hcomp x t htT) (hnonneg x t htT))

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem rampShortTimeUniqueness_of_differenceSubsolution
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (h : ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b → ∀ c₁ c₂ : ProductCurve M,
      c₁.IsSolutionOn B.family.metric lambda (Icc s T) →
      c₂.IsSolutionOn B.family.metric lambda (Icc s T) →
      (∀ z, c₁.map z s = c₂.map z s) →
      c₁.DifferenceSubsolution (I := I) B.family.metric lambda s T c₂) :
    RampShortTimeUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda :=
  RampShortTimeUniqueness.of_localUniqueness (I := I) (M := M) (D := D) (a := a) (b := b)
    B lambda (rampLocalUniqueness_of_differenceSubsolution (I := I) (M := M) B lambda hlambda h)

end Wiring

theorem exists_subsolution_of_zero_initial_not_vanishing :
    ∃ ρ : ℝ → ℝ → ℝ, ρ 0 0 = 0 ∧
      (∀ x t, deriv (fun s : ℝ => ρ x s) t ≤ deriv (deriv (fun y : ℝ => ρ y t)) x) ∧
      ∃ x t, ρ x t ≠ 0 :=
  ⟨fun _ t => -t, by norm_num, fun x t => by simp, 1, 1, by norm_num⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
