import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductUpperDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus

/-!
# Upper distance of a cusp collar up to the boundary (heights allowed to be `0`)

For a cusp embedding `e : CuspEmbedding W g K δ X` and two points of the cusp domain with heights
`z, z' ∈ [0, 100)` (boundary allowed):

* `CuspEmbedding.riemannianEDistOf_le_of_min_height`:
  `d_g(e(t, z), e(t', z')) ≤ √((1 + δ)((z' - z)² + e^{-min(z, z')} d_q(t, t')²))`;
* `CuspEmbedding.riemannianEDistOf_le_flat`: the flat form
  `d_g(e(t, z), e(t', z')) ≤ √(1 + δ) √((z' - z)² + d_q(t, t')²)` (lane BDY-V, statement V.2).

Proof: the constant-speed torus path `HyperbolicCusp.exists_torus_path` together with the linear
interpolation of the two non-negative heights, `σ(r) = (γ r, z + r (z' - z)/L)`. The height path is
`C^∞` on `[0, L]` as a map into the half line (`contMDiffOn_halfSpaceOneLift`), so the endpoints
may lie on the boundary; along `σ` the heights are `≥ min(z, z')`, hence
`H ≤ dz² + e^{-min(z,z')} q`, and `e*g ≤ (1 + δ) H` (`CuspEmbedding.pullback_inner_le_one_add_mul`).
This is a new lemma beside F-f.U (`CuspEmbedding.riemannianEDistOf_le_frozen_product`, interior
slab, no change there).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The half-line lift of `t` is the point of height `max t 0`. -/
theorem halfSpaceOneLift_eq_halfPoint_max (t : ℝ) :
    halfSpaceOneLift t = halfPoint (max t 0) (le_max_right _ _) := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change (halfSpaceOneLift t).1 0 = max t 0
  exact halfSpaceOneLift_val_zero t

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Upper distance up to the boundary.** For points of the cusp domain (heights in `[0, 100)`),
`d_g(e p, e p') ≤ √((1 + δ)((z' - z)² + e^{-min(z, z')} d_q(t, t')²))`. -/
theorem CuspEmbedding.riemannianEDistOf_le_of_min_height {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hp' : p' ∈ cuspDomain) :
    riemannianEDistOf g (e.toFun p) (e.toFun p') ≤ ENNReal.ofReal (Real.sqrt
      ((1 + δ) * ((p'.2.val 0 - p.2.val 0) ^ 2 + Real.exp (-min (p.2.val 0) (p'.2.val 0)) *
        (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) := by
  obtain ⟨γ, L, s, hL, -, hγ, hγ0, hγL, hspeed, hsL⟩ :=
    HyperbolicCusp.exists_torus_path e.cusp p.1 p'.1
  set z := p.2.val 0 with hz
  set z' := p'.2.val 0 with hz'
  set κ : ℝ := Real.exp (-min z z') with hκ
  set m : ℝ := (z' - z) / L with hm
  set v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => m) with hv
  let ζ : ℝ → EuclideanHalfSpace 1 := fun r => halfSpaceOneLift (z + r * m)
  let σ : ℝ → CuspHalfSpace := fun r => (γ r, ζ r)
  have hz0 : 0 ≤ z := p.2.2
  have hz'0 : 0 ≤ z' := p'.2.2
  have hz100 : z < 100 := hp
  have hz'100 : z' < 100 := hp'
  -- the heights along the path
  have hheight : ∀ r ∈ Icc 0 L, min z z' ≤ z + r * m ∧ z + r * m < 100 := by
    intro r hr
    have hθ0 : 0 ≤ r / L := div_nonneg hr.1 hL.le
    have hθ1 : r / L ≤ 1 := (div_le_one hL).mpr hr.2
    have hrm : z + r * m = (1 - r / L) * z + r / L * z' := by
      rw [hm]; field_simp; ring
    rw [hrm]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left z z') (sub_nonneg.mpr hθ1)
    have h2 := mul_le_mul_of_nonneg_left (min_le_right z z') hθ0
    have h3 := mul_le_mul_of_nonneg_left (le_max_left z z') (sub_nonneg.mpr hθ1)
    have h4 := mul_le_mul_of_nonneg_left (le_max_right z z') hθ0
    have h5 : max z z' < 100 := max_lt hz100 hz'100
    refine ⟨by linarith, by linarith⟩
  have hmin0 : 0 ≤ min z z' := le_min hz0 hz'0
  have hζval : ∀ r ∈ Icc 0 L, (ζ r).val 0 = z + r * m := by
    intro r hr
    change (halfSpaceOneLift (z + r * m)).1 0 = _
    rw [halfSpaceOneLift_val_zero, max_eq_left (hmin0.trans (hheight r hr).1)]
  have hσdom : ∀ r ∈ Icc 0 L, σ r ∈ cuspDomain := by
    intro r hr
    change (ζ r).val 0 < cuspDepth
    rw [hζval r hr, cuspDepth]
    exact (hheight r hr).2
  -- smoothness of the path on `[0, L]`
  have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun r : ℝ => z + r * m) :=
    (contDiff_const.add (contDiff_id.mul contDiff_const)).contMDiff
  have hζsm : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) 1 ζ (Icc 0 L) :=
    (contMDiffOn_halfSpaceOneLift.comp haff.contMDiffOn
      fun r hr => (show (0 : ℝ) ≤ z + r * m from hmin0.trans (hheight r hr).1)).of_le
      (by exact_mod_cast le_top)
  have hσsm : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 σ (Icc 0 L) :=
    hγ.contMDiffOn.prodMk hζsm
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 (e.toFun ∘ σ) (Icc 0 L) :=
    (e.contMDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 K)).comp hσsm hσdom
  -- the derivative of the height path at interior times
  have hζd : ∀ r ∈ Ioo 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ζ r
      (ContinuousLinearMap.toSpanSingleton ℝ v) := by
    intro r hr
    have hζeq : ζ = fun r : ℝ => halfPoint (max (z + r * m) 0) (le_max_right _ _) :=
      funext fun r => halfSpaceOneLift_eq_halfPoint_max _
    by_cases hpos : 0 < z + r * m
    · rw [hζeq]
      exact hasMFDerivAt_halfPoint_affine z m r hpos
    · -- both heights vanish: the height path is constant
      have hθ0 : 0 < r / L := div_pos hr.1 hL
      have hθ1 : r / L < 1 := (div_lt_one hL).mpr hr.2
      have hrm : z + r * m = (1 - r / L) * z + r / L * z' := by
        rw [hm]; field_simp; ring
      have hzz : z = 0 ∧ z' = 0 := by
        constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hθ1.le) hz0,
          mul_nonneg hθ0.le hz'0]
      have hm0 : m = 0 := by rw [hm, hzz.1, hzz.2]; simp
      have hv0 : v = 0 := by rw [hv, hm0]; rfl
      have hconst : ζ = fun _ => halfSpaceOneLift z := by
        funext r'
        simp only [ζ, hm0, mul_zero, add_zero]
      have h0 : (ContinuousLinearMap.toSpanSingleton ℝ v : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) =
          0 := by
        ext1
        simp [hv0]
      rw [hconst]
      have hc0 := hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡∂ 1) (halfSpaceOneLift z) r
      exact h0 ▸ hc0
  have hσmd : ∀ r ∈ Ioo 0 L, MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel σ r := fun r hr =>
    (hγ.mdifferentiableAt one_ne_zero).prodMk (hζd r hr).mdifferentiableAt
  -- the speed bound
  set C : ℝ := Real.sqrt ((1 + δ) * (m ^ 2 + κ * s ^ 2)) with hC
  have hspeedC : ∀ r ∈ Ioo 0 L, Real.sqrt (g.inner ((e.toFun ∘ σ) r)
      (mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1)
      (mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1)) ≤ C := by
    intro r hr
    have hrI : r ∈ Icc 0 L := Ioo_subset_Icc_self hr
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun (σ r) :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hσdom r hrI))).mdifferentiableAt
        (by simp)
    have hchain : mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ σ) r 1 =
        mfderiv halfCollarModel W.model e.toFun (σ r) (mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1) := by
      rw [mfderiv_comp r hed (hσmd r hr)]
      rfl
    set w : TangentSpace halfCollarModel (σ r) := mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1 with hw
    have hw1 : w.1 = mfderiv 𝓘(ℝ, ℝ) torusModel γ r 1 := by
      rw [hw, mfderiv_prodMk (hγ.mdifferentiableAt one_ne_zero) (hζd r hr).mdifferentiableAt]
      rfl
    have hw2' : w.2 = v := by
      rw [hw, mfderiv_prodMk (hγ.mdifferentiableAt one_ne_zero) (hζd r hr).mdifferentiableAt]
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) ζ r 1 : EuclideanSpace ℝ (Fin 1)) = v
      rw [(hζd r hr).mfderiv]
      exact one_smul ℝ v
    have hw2 : w.2 0 = m := by rw [hw2', hv]
    have hq : e.cusp.torusMetric.inner (σ r).1 w.1 w.1 = s ^ 2 := by
      rw [hw1]
      exact hspeed r hr
    have hH : e.cusp.metric.inner (σ r) w w ≤ m ^ 2 + κ * s ^ 2 := by
      rw [e.cusp.metric_formula, hq, hw2]
      have hexp : Real.exp (-(σ r).2.val 0) ≤ κ := by
        rw [hκ]
        apply Real.exp_le_exp.mpr
        have : min z z' ≤ (σ r).2.val 0 := by
          change min z z' ≤ (ζ r).val 0
          rw [hζval r hrI]
          exact (hheight r hrI).1
        linarith
      have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
      nlinarith
    have hg := e.pullback_inner_le_one_add_mul (hσdom r hrI) w
    rw [hchain]
    change Real.sqrt (g.inner (e.toFun (σ r)) (mfderiv halfCollarModel W.model e.toFun (σ r) w)
      (mfderiv halfCollarModel W.model e.toFun (σ r) w)) ≤ C
    rcases le_or_gt 0 (1 + δ) with hδ | hδ
    · apply Real.sqrt_le_sqrt
      calc _ ≤ (1 + δ) * e.cusp.metric.inner (σ r) w w := hg
        _ ≤ (1 + δ) * (m ^ 2 + κ * s ^ 2) := mul_le_mul_of_nonneg_left hH hδ
    · have hH0 : 0 ≤ e.cusp.metric.inner (σ r) w w := metric_inner_self_nonneg _ _ _
      have hneg : g.inner (e.toFun (σ r)) (mfderiv halfCollarModel W.model e.toFun (σ r) w)
          (mfderiv halfCollarModel W.model e.toFun (σ r) w) ≤ 0 := by nlinarith
      rw [Real.sqrt_eq_zero'.mpr hneg]
      exact Real.sqrt_nonneg _
  have hd := riemannianEDistOf_le_of_curve_speed_bound g hL.le hc hspeedC
  have hσ0 : σ 0 = p := by
    refine Prod.ext hγ0 ?_
    change halfSpaceOneLift (z + 0 * m) = p.2
    rw [zero_mul, add_zero, hz]
    exact halfSpaceOneLift_val_zero_self p.2
  have hσL : σ L = p' := by
    refine Prod.ext hγL ?_
    change halfSpaceOneLift (z + L * m) = p'.2
    have hLm : z + L * m = z' := by rw [hm]; field_simp; ring
    rw [hLm, hz']
    exact halfSpaceOneLift_val_zero_self p'.2
  simp only [Function.comp_apply, hσ0, hσL, sub_zero] at hd
  refine hd.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  calc C * L = C * Real.sqrt (L ^ 2) := by rw [Real.sqrt_sq hL.le]
    _ = Real.sqrt ((1 + δ) * (m ^ 2 + κ * s ^ 2) * L ^ 2) :=
        (Real.sqrt_mul' _ (sq_nonneg L)).symm
    _ = _ := by
        rw [← hsL]
        congr 1
        rw [hm]
        field_simp

/-- **Flat upper distance up to the boundary** (statement V.2 of lane BDY-V): for points of the
cusp domain, `d_g(e(t, z), e(t', z')) ≤ √(1 + δ) √((z - z')² + d_q(t, t')²)`. -/
theorem CuspEmbedding.riemannianEDistOf_le_flat {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hp' : p' ∈ cuspDomain) :
    riemannianEDistOf g (e.toFun p) (e.toFun p') ≤ ENNReal.ofReal (Real.sqrt (1 + δ) *
      Real.sqrt ((p.2.val 0 - p'.2.val 0) ^ 2 +
        (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2)) := by
  refine (e.riemannianEDistOf_le_of_min_height hp hp').trans ?_
  rcases le_or_gt 0 (1 + δ) with hδ | hδ
  · rw [← Real.sqrt_mul hδ]
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    have hexp : Real.exp (-min (p.2.val 0) (p'.2.val 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_min p.2.2 p'.2.2))
    have hd2 := sq_nonneg (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal
    have hsq : (p'.2.val 0 - p.2.val 0) ^ 2 = (p.2.val 0 - p'.2.val 0) ^ 2 := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hδ
  · have h0 : (1 + δ) * ((p'.2.val 0 - p.2.val 0) ^ 2 +
        Real.exp (-min (p.2.val 0) (p'.2.val 0)) *
          (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hδ.le (by positivity)
    rw [Real.sqrt_eq_zero'.mpr h0, ENNReal.ofReal_zero]
    exact bot_le

end DifferentialGeometry.Geometry.Collapse
