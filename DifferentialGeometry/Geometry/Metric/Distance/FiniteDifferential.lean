import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts

/-!
# Infinitesimal distances for a finite-regularity Riemannian metric

The actual finite normal chart identifies first-order distance with the metric norm. Exact
local distance equality between differentiable maps therefore preserves their metric pairings.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteMetricDistance

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞}

theorem tendsto_dist_ray
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)))
    {u : V → M} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x) (w : V) :
    Tendsto (fun t : ℝ => |t| * dist (u x) (u (x + t⁻¹ • w)))
      atTop (𝓝 (Real.sqrt (g.inner (u x)
        (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x w)))) := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (u x)
  let L : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I u x
  change Tendsto (fun t : ℝ => |t| * dist (u x) (u (x + t⁻¹ • w)))
    atTop (𝓝 (Real.sqrt (B (L w) (L w))))
  obtain ⟨ρ, hρ, hcharts⟩ := g.exists_uniform_normal_charts hr hnorm
    (isCompact_singleton (x := u x))
  obtain ⟨e, hsrc, htgt, hexp, he, hi, hdist⟩ := hcharts (u x) (mem_singleton _)
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr1).ne'
  have hzero : (0 : E) ∈ e.source := by
    rw [hsrc]
    change (g.inner (u x) : E →L[ℝ] E →L[ℝ] ℝ) 0 0 < ρ ^ 2
    simpa only [map_zero] using pow_pos hρ 2
  have he0 : e 0 = u x := (hexp 0 hzero).2.trans (g.expMap_zero hr1 (u x))
  have hbase : u x ∈ e.target := he0 ▸ e.map_source hzero
  have hed : MDifferentiableAt 𝓘(ℝ, E) I e 0 :=
    (he.contMDiffAt (e.open_source.mem_nhds hzero)).mdifferentiableAt hr0
  have hid : MDifferentiableAt I 𝓘(ℝ, E) e.symm (u x) :=
    (hi.contMDiffAt (e.open_target.mem_nhds hbase)).mdifferentiableAt hr0
  have heexp : (e : E → M) =ᶠ[𝓝 0]
      (fun w : E => g.expMap (⟨u x, w⟩ : TangentBundle I M)) := by
    filter_upwards [e.open_source.mem_nhds hzero] with w hw
    exact (hexp w hw).2
  have heD : mfderiv 𝓘(ℝ, E) I e 0 = ContinuousLinearMap.id ℝ E :=
    heexp.mfderiv_eq.trans (g.hasMFDerivAt_expMap_zero hr1 (u x)).mfderiv
  have hinv : mfderiv I 𝓘(ℝ, E) e.symm (u x) = ContinuousLinearMap.id ℝ E := by
    have heq : e.symm ∘ e =ᶠ[𝓝 0] (id : E → E) := by
      filter_upwards [e.open_source.mem_nhds hzero] with w hw
      exact e.left_inv hw
    have hid0 : MDifferentiableAt I 𝓘(ℝ, E) e.symm (e 0) := by rwa [he0]
    have hcomp := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    rw [mfderiv_comp 0 hid0 hed, heD, mfderiv_id] at hcomp
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun C => C v) hcomp
    change (mfderiv I 𝓘(ℝ, E) e.symm (e 0) : E →L[ℝ] E) v = v at hv
    erw [he0] at hv
    exact hv
  have hD : HasFDerivAt (e.symm ∘ u) L x := by
    have h := (hid.hasMFDerivAt.comp x hu.hasMFDerivAt).hasFDerivAt
    change HasFDerivAt (e.symm ∘ u)
      ((mfderiv I 𝓘(ℝ, E) e.symm (u x) : E →L[ℝ] E).comp
        (mfderiv 𝓘(ℝ, V) I u x : V →L[ℝ] E)) x at h
    erw [hinv, ContinuousLinearMap.id_comp] at h
    exact h
  have hx0 : e.symm (u x) = 0 := by rw [← he0]; exact e.left_inv hzero
  have hn : Continuous (fun w : E => Real.sqrt (B w w)) :=
    (B.continuous₂.comp (continuous_id.prodMk continuous_id)).sqrt
  have hlimit := hn.continuousAt.tendsto.comp (hD.lim w tendsto_norm_atTop_atTop)
  have hray : Tendsto (fun t : ℝ => x + t⁻¹ • w) atTop (𝓝 x) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := x)).add
        ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul
          (tendsto_const_nhds (x := w)))
  have htarget := (hu.continuousAt.tendsto.comp hray).eventually
    (e.open_target.mem_nhds hbase)
  apply hlimit.congr'
  filter_upwards [htarget] with t ht
  have hd := hdist (e.symm (u (x + t⁻¹ • w))) (e.map_target ht)
  change dist (u x) (e (e.symm (u (x + t⁻¹ • w)))) =
    Real.sqrt (B (e.symm (u (x + t⁻¹ • w))) (e.symm (u (x + t⁻¹ • w)))) at hd
  change u (x + t⁻¹ • w) ∈ e.target at ht
  rw [e.right_inv ht] at hd
  simp only [Function.comp_apply, hx0, sub_zero] at hd ⊢
  rw [hd]
  have hscale : B (t • e.symm (u (x + t⁻¹ • w)))
      (t • e.symm (u (x + t⁻¹ • w))) =
      t ^ 2 * B (e.symm (u (x + t⁻¹ • w))) (e.symm (u (x + t⁻¹ • w))) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hscale, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem inner_mfderiv_eq_of_local_dist_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)))
    {u v : V → M} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x)
    (hv : MDifferentiableAt 𝓘(ℝ, V) I v x)
    (hdist : ∀ᶠ y in 𝓝 x, dist (u x) (u y) = dist (v x) (v y)) (w z : V) :
    g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x z) =
      g.inner (v x) (mfderiv 𝓘(ℝ, V) I v x w) (mfderiv 𝓘(ℝ, V) I v x z) := by
  have hsq (q : V) :
      g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x q) (mfderiv 𝓘(ℝ, V) I u x q) =
        g.inner (v x) (mfderiv 𝓘(ℝ, V) I v x q) (mfderiv 𝓘(ℝ, V) I v x q) := by
    have hray : Tendsto (fun t : ℝ => x + t⁻¹ • q) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using
        (tendsto_const_nhds (x := x)).add
          ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul
            (tendsto_const_nhds (x := q)))
    have heq : (fun t : ℝ => |t| * dist (u x) (u (x + t⁻¹ • q))) =ᶠ[atTop]
        (fun t : ℝ => |t| * dist (v x) (v (x + t⁻¹ • q))) := by
      filter_upwards [hray.eventually hdist] with t ht
      rw [ht]
    have h := tendsto_nhds_unique ((tendsto_dist_ray g hr hnorm hu q).congr' heq)
      (tendsto_dist_ray g hr hnorm hv q)
    have hs := congrArg (fun a : ℝ => a ^ 2) h
    rw [Real.sq_sqrt (g.inner_self_nonneg' (u x) _),
      Real.sq_sqrt (g.inner_self_nonneg' (v x) _)] at hs
    exact hs
  let Bu : E →L[ℝ] E →L[ℝ] ℝ := g.inner (u x)
  let Bv : E →L[ℝ] E →L[ℝ] ℝ := g.inner (v x)
  let Lu : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I u x
  let Lv : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I v x
  have hw : Bu (Lu w) (Lu w) = Bv (Lv w) (Lv w) := hsq w
  have hz : Bu (Lu z) (Lu z) = Bv (Lv z) (Lv z) := hsq z
  have hadd : Bu (Lu (w + z)) (Lu (w + z)) = Bv (Lv (w + z)) (Lv (w + z)) := hsq (w + z)
  have hsu : Bu (Lu z) (Lu w) = Bu (Lu w) (Lu z) := g.symm (u x) _ _
  have hsv : Bv (Lv z) (Lv w) = Bv (Lv w) (Lv z) := g.symm (v x) _ _
  simp only [map_add, add_apply, hsu, hsv] at hadd
  change Bu (Lu w) (Lu z) = Bv (Lv w) (Lv z)
  linarith only [hw, hz, hadd]

theorem tendsto_dist_curve
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)))
    {γ : ℝ → M} {τ : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ τ) :
    Tendsto (fun h : ℝ => dist (γ τ) (γ (τ + h)) / h) (𝓝[>] 0)
      (𝓝 (Real.sqrt (g.inner (γ τ)
        (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1)))) := by
  have h := (tendsto_dist_ray g hr hnorm hγ (1 : ℝ)).comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] 0) atTop)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change |s⁻¹| * dist (γ τ) (γ (τ + (s⁻¹)⁻¹ • (1 : ℝ))) =
    dist (γ τ) (γ (τ + s)) / s
  rw [inv_inv, smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr hs)]
  exact mul_comm _ _

theorem real_affine_curve_speed :
    Tendsto (fun h : ℝ => dist (0 : ℝ) h / h) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  let g : ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) 3 ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) :=
    { inner := (riemannianMetricVectorSpace ℝ).inner
      symm := (riemannianMetricVectorSpace ℝ).symm
      pos := (riemannianMetricVectorSpace ℝ).pos
      isVonNBounded := (riemannianMetricVectorSpace ℝ).isVonNBounded
      contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top }
  have hn : ∀ (p : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    intro p v
    change ‖(v : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : ℝ) v))
    rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]
  have h := tendsto_dist_curve (r := 2) g le_rfl hn
    (γ := id) (τ := 0) mdifferentiableAt_id
  simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply, zero_add] at h
  change Tendsto (fun h : ℝ => dist (0 : ℝ) h / h) (𝓝[>] 0) (𝓝 (Real.sqrt (1 * 1))) at h
  convert h using 1
  congr 1
  change (1 : ℝ) = Real.sqrt ((1 : ℝ) * (1 : ℝ))
  norm_num

end DifferentialGeometry.Geometry.FiniteMetricDistance
