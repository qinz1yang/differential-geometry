import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFrozenProduct
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Upper distortion of an actual cusp collar against the frozen product (foundation F-f.U)

For a cusp embedding `e : CuspEmbedding W g K δ X` and two points `p, p'` of the model cusp whose
heights lie in `[z₀ - a, z₀ + a] ⊆ (0, 100)`:
`d_g(e p, e p') ≤ √((1 + δ) e^a ((z' - z)² + e^{-z₀} d_q(t, t')²))`,
where `q` is the flat torus metric of the cusp and `d_q` its length distance
(`CuspEmbedding.riemannianEDistOf_le_frozen_product`). This is the upper half of the distortion
of BCP02's actual splitting map `q ↦ ((z(q) - z₀)/r, t(q))` (blueprint 207B, `B:8234–8321`).

Proof: join `t` to `t'` by a minimizing unit-speed `q`-geodesic `γ` (compact torus) or by the
constant path, move the height affinely, `σ(r) = (γ r, z + r (z' - z)/L)`; along `σ` the cusp
metric is at most `e^a` times the frozen product (`HyperbolicCusp.inner_le_exp_frozen`), the
pulled-back metric is at most `(1 + δ)` times the cusp metric
(`CuspEmbedding.pullback_inner_le_one_add_mul`), and the speed is constant.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The truncated affine height path `r ↦ max (z + r m) 0` in the half line agrees with the affine
map `r ↦ z + r m` near every time where the latter is positive. -/
private theorem eventuallyEq_halfPoint_affine (z m s : ℝ) (hs : 0 < z + s * m) :
    (fun r : ℝ => (halfPoint (max (z + r * m) 0) (le_max_right _ _)).val) =ᶠ[𝓝 s]
      fun r => WithLp.toLp 2 (fun _ : Fin 1 => z) + r • WithLp.toLp 2 (fun _ : Fin 1 => m) := by
  have hev : ∀ᶠ r in 𝓝 s, 0 < z + r * m :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
      (lt_mem_nhds hs)
  filter_upwards [hev] with r hr
  have hmax : max (z + r * m) 0 = z + r * m := max_eq_left hr.le
  ext i
  simp only [halfPoint, hmax]
  simp [mul_comm]

private theorem continuous_halfPoint_affine (z m : ℝ) :
    Continuous fun r : ℝ => halfPoint (max (z + r * m) 0) (le_max_right _ _) := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ =>
    (continuous_const.add (continuous_id.mul continuous_const)).max continuous_const)

/-- The derivative of the truncated affine height path where it is positive. -/
theorem hasMFDerivAt_halfPoint_affine (z m s : ℝ) (hs : 0 < z + s * m) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1)
      (fun r : ℝ => halfPoint (max (z + r * m) 0) (le_max_right _ _)) s
      (ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (fun _ : Fin 1 => m))) := by
  have hlin : HasFDerivAt (fun r : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => z) +
      r • WithLp.toLp 2 (fun _ : Fin 1 => m))
      (ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (fun _ : Fin 1 => m))) s := by
    simpa only [one_smul, id_eq] using
      (((hasDerivAt_id s).smul_const (WithLp.toLp 2 (fun _ : Fin 1 => m))).const_add
        (WithLp.toLp 2 (fun _ : Fin 1 => z))).hasFDerivAt
  refine ⟨(continuous_halfPoint_affine z m).continuousAt, ?_⟩
  simp only [writtenInExtChartAt, mfld_simps]
  exact (hlin.congr_of_eventuallyEq (eventuallyEq_halfPoint_affine z m s hs)).hasFDerivWithinAt

/-- The truncated affine height path is smooth where it is positive. -/
theorem contMDiffAt_halfPoint_affine (z m s : ℝ) (hs : 0 < z + s * m) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞
      (fun r : ℝ => halfPoint (max (z + r * m) 0) (le_max_right _ _)) s := by
  rw [contMDiffAt_iff]
  refine ⟨(continuous_halfPoint_affine z m).continuousAt, ?_⟩
  simp only [mfld_simps]
  have hlin : ContDiff ℝ ∞ (fun r : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => z) +
      r • WithLp.toLp 2 (fun _ : Fin 1 => m)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (hlin.contDiffAt.congr_of_eventuallyEq
    (eventuallyEq_halfPoint_affine z m s hs)).contDiffWithinAt

private theorem halfPoint_max_eq (q : EuclideanHalfSpace 1) {c : ℝ} (hc : c = q.val 0)
    (h : 0 ≤ max c 0) : halfPoint (max c 0) h = q := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  have hmax : max c 0 = q.val 0 := by rw [hc]; exact max_eq_left q.property
  simp only [halfPoint, hmax]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Upper distortion along an explicit torus path: if `γ` joins the torus coordinates of `p` and
`p'` in time `L > 0` with constant `q`-speed `s`, then
`d_g(e p, e p') ≤ √((1 + δ) e^a ((z' - z)² + e^{-z₀} (s L)²))`. -/
theorem CuspEmbedding.riemannianEDistOf_le_of_torus_path {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} {z₀ a : ℝ} (hlow : a < z₀)
    (hup : z₀ + a < 100) (hp : |p.2.val 0 - z₀| ≤ a) (hp' : |p'.2.val 0 - z₀| ≤ a)
    {γ : ℝ → Torus} {L s : ℝ} (hL : 0 < L) (hγ : ContMDiff 𝓘(ℝ, ℝ) torusModel 1 γ)
    (hγ0 : γ 0 = p.1) (hγL : γ L = p'.1)
    (hspeed : ∀ r ∈ Ioo 0 L, e.cusp.torusMetric.inner (γ r)
      (mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1) (mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1) = s ^ 2) :
    riemannianEDistOf g (e.toFun p) (e.toFun p') ≤ ENNReal.ofReal (Real.sqrt
      ((1 + δ) * Real.exp a * ((p'.2.val 0 - p.2.val 0) ^ 2 + Real.exp (-z₀) * (s * L) ^ 2))) := by
  set z := p.2.val 0 with hz
  set z' := p'.2.val 0 with hz'
  set m : ℝ := (z' - z) / L with hm
  set v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => m) with hv
  let ζ : ℝ → EuclideanHalfSpace 1 := fun r => halfPoint (max (z + r * m) 0) (le_max_right _ _)
  let σ : ℝ → CuspHalfSpace := fun r => (γ r, ζ r)
  have hopen : IsOpen cuspDomain := by
    change IsOpen ((fun q : CuspHalfSpace => q.2.val 0) ⁻¹' Iio cuspDepth)
    apply isOpen_Iio.preimage
    fun_prop
  -- the heights along the path
  have hheight : ∀ r ∈ Icc 0 L, |z + r * m - z₀| ≤ a ∧ 0 < z + r * m ∧ z + r * m < 100 := by
    intro r hr
    have hθ0 : 0 ≤ r / L := div_nonneg hr.1 hL.le
    have hθ1 : r / L ≤ 1 := (div_le_one hL).mpr hr.2
    have hrm : z + r * m = (1 - r / L) * z + r / L * z' := by
      rw [hm]; field_simp; ring
    obtain ⟨h1, h2⟩ := abs_le.mp hp
    obtain ⟨h3, h4⟩ := abs_le.mp hp'
    rw [hrm]
    refine ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  have hζval : ∀ r ∈ Icc 0 L, (ζ r).val 0 = z + r * m := by
    intro r hr
    simp [ζ, halfPoint, max_eq_left (hheight r hr).2.1.le]
  have hσdom : ∀ r ∈ Icc 0 L, σ r ∈ cuspDomain := by
    intro r hr
    change (ζ r).val 0 < cuspDepth
    rw [hζval r hr, cuspDepth]
    exact (hheight r hr).2.2
  have hσz : ∀ r ∈ Icc 0 L, |(σ r).2.val 0 - z₀| ≤ a := by
    intro r hr
    change |(ζ r).val 0 - z₀| ≤ a
    rw [hζval r hr]
    exact (hheight r hr).1
  have hζd : ∀ r ∈ Icc 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ζ r
      (ContinuousLinearMap.toSpanSingleton ℝ v) := fun r hr =>
    hasMFDerivAt_halfPoint_affine z m r (hheight r hr).2.1
  have hσmd : ∀ r ∈ Icc 0 L, MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel σ r := fun r hr =>
    (hγ.mdifferentiableAt one_ne_zero).prodMk (hζd r hr).mdifferentiableAt
  have hσsm : ∀ r ∈ Icc 0 L, ContMDiffAt 𝓘(ℝ, ℝ) halfCollarModel 1 σ r := fun r hr =>
    hγ.contMDiffAt.prodMk ((contMDiffAt_halfPoint_affine z m r (hheight r hr).2.1).of_le
      (by exact_mod_cast le_top))
  have he : ∀ r ∈ Icc 0 L, ContMDiffAt halfCollarModel W.model 1 e.toFun (σ r) := fun r hr =>
    (e.contMDiffOn.contMDiffAt (hopen.mem_nhds (hσdom r hr))).of_le le_add_self
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 (e.toFun ∘ σ) (Icc 0 L) := fun r hr =>
    ((he r hr).comp r (hσsm r hr)).contMDiffWithinAt
  -- the speed bound
  set C : ℝ := Real.sqrt ((1 + δ) * Real.exp a * (m ^ 2 + Real.exp (-z₀) * s ^ 2)) with hC
  have hspeedC : ∀ r ∈ Ioo 0 L, Real.sqrt (g.inner ((e.toFun ∘ σ) r)
      (mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1)
      (mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1)) ≤ C := by
    intro r hr
    have hrI : r ∈ Icc 0 L := Ioo_subset_Icc_self hr
    have hchain : mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1 =
        mfderiv halfCollarModel W.model e.toFun (σ r) (mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1) := by
      rw [mfderiv_comp r ((he r hrI).mdifferentiableAt one_ne_zero) (hσmd r hrI)]
      rfl
    set w : TangentSpace halfCollarModel (σ r) := mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1 with hw
    have hw1 : w.1 = mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1 := by
      rw [hw, mfderiv_prodMk (hγ.mdifferentiableAt one_ne_zero) (hζd r hrI).mdifferentiableAt]
      rfl
    have hw2' : w.2 = v := by
      rw [hw, mfderiv_prodMk (hγ.mdifferentiableAt one_ne_zero) (hζd r hrI).mdifferentiableAt]
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) ζ r 1 : EuclideanSpace ℝ (Fin 1)) = v
      rw [(hζd r hrI).mfderiv]
      exact one_smul ℝ v
    have hw2 : w.2 0 = m := by
      rw [hw2', hv]
    have hq : e.cusp.torusMetric.inner (σ r).1 w.1 w.1 = s ^ 2 := by
      rw [hw1]
      exact hspeed r hr
    have hH := (HyperbolicCusp.inner_le_exp_frozen e.cusp (hσz r hrI) w).2
    rw [hq, hw2] at hH
    have hg := e.pullback_inner_le_one_add_mul (hσdom r hrI) w
    rw [hchain]
    change Real.sqrt (g.inner (e.toFun (σ r)) (mfderiv halfCollarModel W.model e.toFun (σ r) w)
      (mfderiv halfCollarModel W.model e.toFun (σ r) w)) ≤ C
    rcases le_or_gt 0 (1 + δ) with hδ | hδ
    · apply Real.sqrt_le_sqrt
      calc _ ≤ (1 + δ) * e.cusp.metric.inner (σ r) w w := hg
        _ ≤ (1 + δ) * (Real.exp a * (m ^ 2 + Real.exp (-z₀) * s ^ 2)) :=
            mul_le_mul_of_nonneg_left hH hδ
        _ = _ := by ring
    · have hH0 : 0 ≤ e.cusp.metric.inner (σ r) w w := metric_inner_self_nonneg _ _ _
      have hneg : g.inner (e.toFun (σ r)) (mfderiv halfCollarModel W.model e.toFun (σ r) w)
          (mfderiv halfCollarModel W.model e.toFun (σ r) w) ≤ 0 := by nlinarith
      rw [Real.sqrt_eq_zero'.mpr hneg]
      exact Real.sqrt_nonneg _
  have hd := riemannianEDistOf_le_of_curve_speed_bound g hL.le hc hspeedC
  have hσ0 : σ 0 = p :=
    Prod.ext hγ0 (halfPoint_max_eq p.2 (by rw [zero_mul, add_zero]) _)
  have hσL : σ L = p' := by
    have hLm : z + L * m = p'.2.val 0 := by rw [hm, ← hz']; field_simp; ring
    exact Prod.ext hγL (halfPoint_max_eq p'.2 hLm _)
  simp only [Function.comp_apply, hσ0, hσL, sub_zero] at hd
  refine hd.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  calc C * L = C * Real.sqrt (L ^ 2) := by rw [Real.sqrt_sq hL.le]
    _ = Real.sqrt ((1 + δ) * Real.exp a * (m ^ 2 + Real.exp (-z₀) * s ^ 2) * L ^ 2) :=
        (Real.sqrt_mul' _ (sq_nonneg L)).symm
    _ = _ := by
        congr 1
        rw [hm]
        field_simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- On a compact connected boundaryless Riemannian manifold, any two points are joined in some time
`L > 0` by a smooth path of constant speed `s` with `s L = d_g(t, t')`: a minimizing unit-speed
geodesic, or the constant path. -/
theorem exists_constant_speed_path_of_compact {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [T2Space (TangentBundle I M)] (g : SmoothRiemannianMetric I M)
    (t t' : M) :
    ∃ (γ : ℝ → M) (L s : ℝ), 0 < L ∧ 0 ≤ s ∧ ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧
      γ 0 = t ∧ γ L = t' ∧
      (∀ r ∈ Ioo 0 L, g.inner (γ r) (mfderiv 𝓘(ℝ, ℝ) I γ r 1) (mfderiv 𝓘(ℝ, ℝ) I γ r 1) = s ^ 2) ∧
      s * L = (riemannianEDistOf g t t').toReal := by
  by_cases htt : t = t'
  · subst htt
    refine ⟨fun _ => t, 1, 0, one_pos, le_rfl, contMDiff_const, rfl, rfl, fun r _ => ?_, ?_⟩
    · rw [mfderiv_const]
      simp
    · simp [riemannianEDistOf_self]
  · let := inducedMetricSpace g
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
    have := hRM
    have := hcont
    have : CompleteSpace M := complete_of_compact
    obtain ⟨γ, L, hL, hγ0, hγL, hγsm, -, hunit, -, hdist⟩ :=
      Riemannian.Exponential.exists_smooth_unit_speed_minimizing_geodesic_between_points_of_ne
        g hEnorm t t' htt
    refine ⟨γ, L, 1, hL, zero_le_one, hγsm.of_le (by simp), hγ0, hγL,
      fun r _ => by rw [one_pow]; exact hunit r, ?_⟩
    change 1 * L = (riemannianEDist I t t').toReal
    rw [hdist, ENNReal.toReal_ofReal hL.le, one_mul]

/-- On the flat torus of a cusp, any two points are joined in some time `L > 0` by a smooth path of
constant `q`-speed `s` with `s L = d_q(t, t')`. -/
theorem HyperbolicCusp.exists_torus_path (Hc : HyperbolicCusp) (t t' : Torus) :
    ∃ (γ : ℝ → Torus) (L s : ℝ), 0 < L ∧ 0 ≤ s ∧ ContMDiff 𝓘(ℝ, ℝ) torusModel 1 γ ∧
      γ 0 = t ∧ γ L = t' ∧
      (∀ r ∈ Ioo 0 L, Hc.torusMetric.inner (γ r) (mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1) = s ^ 2) ∧
      s * L = (riemannianEDistOf Hc.torusMetric t t').toReal := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
    ⟨by simp [Module.finrank_prod]⟩
  exact exists_constant_speed_path_of_compact Hc.torusMetric t t'

/-- F-f.U: upper distortion of an actual cusp collar against the frozen product at height `z₀`:
for heights in `[z₀ - a, z₀ + a] ⊆ (0, 100)`,
`d_g(e p, e p') ≤ √((1 + δ) e^a ((z' - z)² + e^{-z₀} d_q(t, t')²))`. -/
theorem CuspEmbedding.riemannianEDistOf_le_frozen_product {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} {z₀ a : ℝ} (hlow : a < z₀)
    (hup : z₀ + a < 100) (hp : |p.2.val 0 - z₀| ≤ a) (hp' : |p'.2.val 0 - z₀| ≤ a) :
    riemannianEDistOf g (e.toFun p) (e.toFun p') ≤ ENNReal.ofReal (Real.sqrt
      ((1 + δ) * Real.exp a * ((p'.2.val 0 - p.2.val 0) ^ 2 +
        Real.exp (-z₀) * (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) := by
  obtain ⟨γ, L, s, hL, -, hγ, hγ0, hγL, hspeed, hsL⟩ :=
    HyperbolicCusp.exists_torus_path e.cusp p.1 p'.1
  have h := e.riemannianEDistOf_le_of_torus_path hlow hup hp hp' hL hγ hγ0 hγL hspeed
  rwa [hsL] at h

end DifferentialGeometry.Geometry.Collapse
