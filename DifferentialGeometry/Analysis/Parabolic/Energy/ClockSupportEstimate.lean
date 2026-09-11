import DifferentialGeometry.Analysis.Parabolic.Energy.ClockCutoffEnergy
import DifferentialGeometry.Analysis.Elliptic.Barrier.SupportComparison

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_product_local (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh)
    (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    (gradientFun_mul g hfy hhy)

private theorem gradient_const_mul_local (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) (a : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hg : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g f)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => a * f y))) x := by
  apply (hg.smul_const_section (a := a)).congr_of_eventuallyEq
  filter_upwards [hf] with y hy
  exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    (gradientFun_const_smul g a hy)

private theorem clock_pair_regular
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T ε A t : ℝ) (χ : ℝ → M → ℝ) (x : M)
    (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (u v : ℝ → M → ℝ)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (u t))) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (v t))) x) :
    DifferentiableWithinAt ℝ
        (fun s => s * (F.phi s x ^ 2 * u s x) + A * (F.phi s x * v s x))
        (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z => t * (F.phi t z ^ 2 * u t z) + A * (F.phi t z * v t z)) y) ∧
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t)
          (fun z => t * (F.phi t z ^ 2 * u t z) + A * (F.phi t z * v t z)))) x := by
  let φ := F.phi
  let q := fun s y => φ s y * φ s y
  let U := fun s y => q s y * u s y
  let V := fun s y => φ s y * v s y
  have hqtime := F.time_diff.mul F.time_diff
  have hqspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hqgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hUtime := hqtime.mul hu_time
  have hVtime := F.time_diff.mul hv_time
  have hUspace := hqspace.and hu_space |>.mono fun y hy => hy.1.mul hy.2
  have hVspace := F.space_diff_nhds.and hv_space |>.mono fun y hy => hy.1.mul hy.2
  have hUgrad := gradient_product_local (G.metric t) (q t) (u t) x
    hqspace hu_space hqgrad hu_grad
  have hVgrad := gradient_product_local (G.metric t) (φ t) (v t) x
    F.space_diff_nhds hv_space F.grad_diff hv_grad
  have hclocktime : DifferentiableWithinAt ℝ
      (fun s => s * U s x) (Icc 0 T) t :=
    differentiableWithinAt_id.mul hUtime
  have hclockspace := hUspace.mono fun y hy =>
    (mdifferentiableAt_const (c := t)).mul hy
  have hclockgrad := gradient_const_mul_local (G.metric t) (U t) x t hUspace hUgrad
  have hAtime := hVtime.const_mul A
  have hAspace := hVspace.mono fun y hy =>
    (mdifferentiableAt_const (c := A)).mul hy
  have hAgrad := gradient_const_mul_local (G.metric t) (V t) x A hVspace hVgrad
  have hsumspace := hclockspace.and hAspace |>.mono fun y hy => hy.1.add hy.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_two, U, V, q, φ, Pi.mul_def, Pi.add_def] using hclocktime.add hAtime
  · simpa only [pow_two, U, V, q, φ, Pi.mul_def, Pi.add_def] using hsumspace
  · have hr := mdifferentiableAt_add_section hclockgrad hAgrad
    apply hr.congr_of_eventuallyEq
    filter_upwards [hclockspace, hAspace] with y hcy hay
    apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    simpa only [pow_two, U, V, q, φ, Pi.mul_def, Pi.add_def] using gradientFun_add (G.metric t) hcy hay

variable [I.Boundaryless]

section FiniteSupport

variable
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T K ε a b A : ℝ) (hT : 0 < T) (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 1 + 18 * ε * T ≤ A)
    (χ u v w : ℝ → M → ℝ) (Cpt : Set M) (hCpt : IsCompact Cpt)
    (hχcont : ContinuousOn (fun p : ℝ × M => χ p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hχrange : ∀ t ∈ Icc 0 T, ∀ x : M, χ t x ∈ Icc 0 1)
    (hχout : ∀ t ∈ Icc 0 T, ∀ x ∉ Cpt, χ t x = 0)
    (hucont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ Cpt))
    (hvcont : ContinuousOn (fun p : ℝ × M => v p.1 p.2) (Icc 0 T ×ˢ Cpt))
    (hnonneg : ∀ t ∈ Icc 0 T, ∀ x : M, 0 < χ t x → 0 ≤ u t x ∧ 0 ≤ v t x)
    (hvK : ∀ t ∈ Icc 0 T, ∀ x : M, 0 < χ t x → v t x ≤ K ^ 2)
    (hw : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x → 0 ≤ w t x)
    (hcut : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      Nonempty (ShiCutoffLowerSupportAt G T ε χ t x))
    (hu_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (u t))) x)
    (hv_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (v t))) x)
    (hgu : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (u t) x)
        (gradientFun (I := I) (G.metric t) (u t) x) ≤ 4 * u t x * w t x)
    (hgv : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (v t) x)
        (gradientFun (I := I) (G.metric t) (v t) x) ≤ 4 * v t x * u t x)
    (hPu : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      parabolicOperatorWithDrift G T (fun _ _ => 0) u t x ≤ -2 * w t x + a * u t x)
    (hPv : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < χ t x →
      parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤ -2 * u t x + b)

include hT hε ha hb hA hCpt hχcont hχrange hχout hucont hvcont hnonneg hvK hw hcut
  hu_time hv_time hu_space hv_space hu_grad hv_grad hgu hgv hPu hPv

theorem clock_cutoff_pair_bound :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      t * (χ t x ^ 2 * u t x) + A * (χ t x * v t x) ≤
        Real.exp (a * t) * (A * K ^ 2 + (A * b + 5 * A * ε * K ^ 2) * t) := by
  let Q := fun t x => t * (χ t x ^ 2 * u t x) + A * (χ t x * v t x)
  let B := A * b + 5 * A * ε * K ^ 2
  have hA0 : 0 ≤ A := by
    have heT : 0 ≤ 18 * ε * T := by positivity
    linarith only [hA, heT]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hAK : 0 ≤ A * K ^ 2 := mul_nonneg hA0 (sq_nonneg K)
  have hχCpt : ContinuousOn (fun p : ℝ × M => χ p.1 p.2) (Icc 0 T ×ˢ Cpt) :=
    hχcont.mono (prod_mono subset_rfl (subset_univ _))
  have hQc : ContinuousOn (fun p : ℝ × M => Q p.1 p.2) (Icc 0 T ×ˢ Cpt) :=
    (continuous_fst.continuousOn.mul ((hχCpt.pow 2).mul hucont)).add
      (continuousOn_const.mul (hχCpt.mul hvcont))
  have hQout : ∀ t ∈ Icc 0 T, ∀ x ∉ Cpt, Q t x ≤ 0 := by
    intro t ht x hx
    simp only [Q, hχout t ht x hx, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul, mul_zero, add_zero, le_refl]
  have hQinit : ∀ x : M, Q 0 x ≤ A * K ^ 2 := by
    intro x
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    by_cases hpos : 0 < χ 0 x
    · have hv0 := (hnonneg 0 hz x hpos).2
      have hprod : χ 0 x * v 0 x ≤ K ^ 2 := by
        calc
          _ ≤ 1 * v 0 x := mul_le_mul_of_nonneg_right (hχrange 0 hz x).2 hv0
          _ ≤ K ^ 2 := by simpa only [one_mul] using hvK 0 hz x hpos
      simpa only [Q, zero_mul, zero_add] using mul_le_mul_of_nonneg_left hprod hA0
    · have hzero : χ 0 x = 0 :=
        le_antisymm (le_of_not_gt hpos) (hχrange 0 hz x).1
      simpa only [Q, hzero, zero_mul, mul_zero, add_zero] using hAK
  have hQbound := scalar_linear_reaction_bound_support G T hT (fun _ _ => 0)
    Q Cpt hCpt a B (A * K ^ 2) ha hB hAK hQc hQout hQinit
    (fun t ht htpos x hQpos => by
      have hχpos : 0 < χ t x := by
        by_contra hnpos
        have hzero : χ t x = 0 :=
          le_antisymm (le_of_not_gt hnpos) (hχrange t ht x).1
        simp only [Q, hzero, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
          mul_zero, add_zero, lt_self_iff_false] at hQpos
      obtain ⟨F⟩ := hcut t ht htpos x hχpos
      let V := fun s y => s * (F.phi s y ^ 2 * u s y) + A * (F.phi s y * v s y)
      have hr := clock_pair_regular G T ε A t χ x F u v
        (hu_time t ht htpos x hχpos) (hv_time t ht htpos x hχpos)
        (hu_space t ht htpos x hχpos) (hv_space t ht htpos x hχpos)
        (hu_grad t ht htpos x hχpos) (hv_grad t ht htpos x hχpos)
      refine ⟨V, ?_, ?_, hr.1, hr.2.1, hr.2.2, ?_⟩
      · simp only [V, Q, F.eq_at]
      · have hχnear : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
            0 < χ p.1 p.2 :=
          Tendsto.eventually_const_lt hχpos (hχcont (t, x) ⟨ht, mem_univ x⟩)
        filter_upwards [F.lower_nhds, hχnear, self_mem_nhdsWithin] with p hp hpχ hpSlab
        have hpt : p.1 ∈ Icc 0 T := hpSlab.1
        obtain ⟨hup, hvp⟩ := hnonneg p.1 hpt p.2 hpχ
        have hupper := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.1 hp.2 2) hup) hpt.1
        have hlower := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp.2 hvp) hA0
        exact add_le_add hupper hlower
      · exact parabolic_clock_cutoff_pair_le G T ε T t χ x F
          ((uniqueDiffOn_Icc hT) t ht) hε ht (hχrange t ht x)
          u v (w t x) a b (K ^ 2) A
          (hnonneg t ht x hχpos).1 (hnonneg t ht x hχpos).2
          (hw t ht htpos x hχpos) (hvK t ht x hχpos) ha hb hA
          (hu_time t ht htpos x hχpos) (hv_time t ht htpos x hχpos)
          (hu_space t ht htpos x hχpos) (hv_space t ht htpos x hχpos)
          (hu_grad t ht htpos x hχpos) (hv_grad t ht htpos x hχpos)
          (hgu t ht htpos x hχpos) (hgv t ht htpos x hχpos)
          (hPu t ht htpos x hχpos) (hPv t ht htpos x hχpos))
  exact hQbound

theorem upper_energy_bound_of_clock_cutoff :
    ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, χ t x = 1 →
      u t x ≤ Real.exp (a * t) *
        (A * K ^ 2 + (A * b + 5 * A * ε * K ^ 2) * t) / t := by
  have hQ := clock_cutoff_pair_bound
    (G := G) (T := T) (K := K) (ε := ε) (a := a) (b := b) (A := A)
    (hT := hT) (hε := hε) (ha := ha) (hb := hb) (hA := hA)
    (χ := χ) (u := u) (v := v) (w := w) (Cpt := Cpt) (hCpt := hCpt)
    (hχcont := hχcont) (hχrange := hχrange) (hχout := hχout)
    (hucont := hucont) (hvcont := hvcont) (hnonneg := hnonneg) (hvK := hvK)
    (hw := hw) (hcut := hcut) (hu_time := hu_time) (hv_time := hv_time)
    (hu_space := hu_space) (hv_space := hv_space) (hu_grad := hu_grad) (hv_grad := hv_grad)
    (hgu := hgu) (hgv := hgv) (hPu := hPu) (hPv := hPv)
  have hA0 : 0 ≤ A := by
    have heT : 0 ≤ 18 * ε * T := by positivity
    linarith only [hA, heT]
  intro t ht htpos x hχone
  have hv0 := (hnonneg t ht x (by rw [hχone]; norm_num)).2
  have hAv : 0 ≤ A * v t x := mul_nonneg hA0 hv0
  have hh := hQ t ht x
  simp only [hχone, one_pow, one_mul] at hh
  apply (le_div_iff₀ htpos).2
  nlinarith only [hh, hAv]

end FiniteSupport

end DifferentialGeometry.Analysis

end
