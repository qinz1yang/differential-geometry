import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.TorusAreaRatio

/-!
# The reference torus of a nearly cuspidal collar is small (statement G-diam of BSA01)

Blueprint 207B, BSA01 proof `B:7641–7653`. The boundary diameter `≤ δ` of a
`NearlyCuspidalBoundary` is measured in the ambient intrinsic distance of `W` (the weaker
convention). It is NOT taken as the intrinsic diameter of the reference torus: a `C¹` path of
`g`-length `< r ≤ 1/2` between two boundary points of a collar is trapped below height `1` by the
first exit (statement E), lifts to the cusp domain, and its torus projection has `g_T`-length
`< 2r` (`g_T ≤ e^z H ≤ e (1 - δ)^{-1} e*g ≤ 4 e*g` below height `1`). Hence

* `NearlyCuspidalBoundary.torus_riemannianEDistOf_le_two_mul`: `diam(T², g_T) ≤ 2δ`;
* `NearlyCuspidalBoundary.torus_area_le_four_pi_mul_sq`: `Area(T², g_T) ≤ 4πδ²`, by the flat-torus
  area bound of statement M (two-dimensional Bishop–Gromov), with no lattice classification and
  no Dirichlet-cell argument.

Also `CuspEmbedding.delta_nonneg`: the error bound of a cusp embedding is nonnegative.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- The metric error bound of a cusp embedding is nonnegative (it bounds a norm). -/
theorem CuspEmbedding.delta_nonneg (e : CuspEmbedding W g K δ X) : 0 ≤ δ := by
  have hp : (((1 : Circle), (1 : Circle)), halfZero) ∈ cuspDomain := by
    change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
    change (0 : ℝ) < 100
    norm_num
  exact (Real.sqrt_nonneg _).trans (e.metric_error 0 (Nat.zero_le _) _ hp)

/-- Below height `1`, the torus part of a tangent vector is controlled by the actual metric:
`g_T(v_T, v_T) ≤ 4 g(De v, De v)` for `δ ≤ 1/100`. -/
theorem CuspEmbedding.torus_inner_le_four_mul_pullback (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : p.2.val 0 ≤ 1)
    (v : TangentSpace halfCollarModel p) :
    e.cusp.torusMetric.inner p.1 v.1 v.1 ≤
      4 * g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
  have hG := e.one_sub_mul_le_pullback_inner hp v
  have hH := e.cusp.metric_formula p v v
  have hT0 : 0 ≤ e.cusp.torusMetric.inner p.1 v.1 v.1 := metric_inner_self_nonneg _ _ _
  have hexp : Real.exp (p.2.val 0) ≤ 2.7182818286 :=
    (Real.exp_le_exp.mpr hz).trans Real.exp_one_lt_d9.le
  have hprod : Real.exp (p.2.val 0) * Real.exp (-p.2.val 0) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hTH : e.cusp.torusMetric.inner p.1 v.1 v.1 ≤
      Real.exp (p.2.val 0) * e.cusp.metric.inner p v v := by
    rw [hH]
    have hsq := sq_nonneg (v.2 0)
    have hepos := Real.exp_pos (p.2.val 0)
    nlinarith
  have hH0 : 0 ≤ e.cusp.metric.inner p v v := metric_inner_self_nonneg _ _ _
  nlinarith [Real.exp_pos (p.2.val 0)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Torus distance from the ambient distance.** If two boundary points `e(x,0)`, `e(y,0)` of a
collar are at `g`-distance `< r ≤ 1/2`, then `d_{g_T}(x, y) ≤ 2r` (for `δ ≤ 1/100`). -/
theorem CuspEmbedding.torus_riemannianEDistOf_le_of_lt (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 1 / 100) {x y : Torus} {r : ℝ} (hr : r ≤ 1 / 2)
    (hxy : riemannianEDistOf g (e.toFun (x, halfZero)) (e.toFun (y, halfZero)) <
      ENNReal.ofReal r) :
    riemannianEDistOf e.cusp.torusMetric x y ≤ ENNReal.ofReal (2 * r) := by
  let : RiemannianBundle (fun z : W.Carrier => TangentSpace W.model z) := ⟨g.toRiemannianMetric⟩
  have hxy' : Manifold.riemannianEDist W.model (e.toFun (x, halfZero)) (e.toFun (y, halfZero)) <
      ENNReal.ofReal r := hxy
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hxy'
  have hm : (100 / 101 : ℝ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hdom0 : ∀ t : Torus, ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
    intro t
    change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
    change (0 : ℝ) < 100
    norm_num
  -- the short curve stays below height `1`
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 1} := by
    intro t ht
    by_contra hnot
    have h0 : ((x, halfZero) : CuspHalfSpace).2.val 0 = 0 := rfl
    have h1 := e.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt (h := 1)
      (by change (1 : ℝ) < 100; norm_num) (p := (x, halfZero)) (by rw [h0]; norm_num) hnot
    rw [h0, sub_zero, mul_one] at h1
    have h2 : riemannianEDistOf g (e.toFun (x, halfZero)) (γ t) ≤ pathELength W.model γ 0 1 := by
      change Manifold.riemannianEDist W.model _ _ ≤ _
      rw [← hγ0]
      exact (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) rfl rfl
        ht.1).trans (pathELength_mono le_rfl ht.2)
    have h3 := (ENNReal.ofReal_lt_ofReal_iff'.mp ((h1.trans h2).trans_lt hlen)).1
    linarith
  have hmaps : MapsTo γ (Icc 0 1) (e.toFun '' cuspDomain) := by
    intro t ht
    obtain ⟨q, hq, hqt⟩ := hstay t ht
    exact ⟨q, lt_trans (show q.2.val 0 < 1 from hq) (by change (1 : ℝ) < 100; norm_num), hqt⟩
  obtain ⟨c, hc, hcd, hce⟩ := e.exists_lift hγ hmaps
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, (c t).2.val 0 < 1 := by
    intro t ht
    obtain ⟨q, hq, hqt⟩ := hstay t ht
    have hqd : q ∈ cuspDomain := lt_trans (show q.2.val 0 < 1 from hq)
      (by change (1 : ℝ) < 100; norm_num)
    rw [← e.injOn_cuspDomain hqd (hcd ht) (hqt.trans (hce t ht).symm)]
    exact hq
  have hc0 : c 0 = (x, halfZero) :=
    e.injOn_cuspDomain (hcd ⟨le_rfl, zero_le_one⟩) (hdom0 x)
      ((hce 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hc1 : c 1 = (y, halfZero) :=
    e.injOn_cuspDomain (hcd ⟨zero_le_one, le_rfl⟩) (hdom0 y)
      ((hce 1 ⟨zero_le_one, le_rfl⟩).trans hγ1)
  have hlen' : pathELength W.model (e.toFun ∘ c) 0 1 < ENNReal.ofReal r :=
    (pathELength_congr (γ := e.toFun ∘ c) fun t ht => hce t ht).trans_lt hlen
  rw [pathELength_eq_lintegral_mfderiv_Ioo] at hlen'
  -- the torus projection
  let : RiemannianBundle (fun z : Torus => TangentSpace torusModel z) :=
    ⟨e.cusp.torusMetric.toRiemannianMetric⟩
  have hfst : ContMDiffOn 𝓘(ℝ, ℝ) torusModel 1 (Prod.fst ∘ c) (Icc 0 1) :=
    contMDiff_fst.comp_contMDiffOn hc
  have hT := riemannianEDist_le_pathELength hfst (x := x) (y := y)
    (by simp only [comp_apply, hc0]) (by simp only [comp_apply, hc1]) zero_le_one
  change riemannianEDist torusModel x y ≤ _
  refine hT.trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) torusModel (Prod.fst ∘ c) t 1‖ₑ ≤
      ENNReal.ofReal 2 * ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
      (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun (c t) :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hcd htI))).mdifferentiableAt
        (by simp)
    have hfd : mfderiv 𝓘(ℝ, ℝ) torusModel (Prod.fst ∘ c) t 1 =
        (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).1 := by
      rw [mfderiv_comp t mdifferentiableAt_fst hdiff, mfderiv_fst]
      rfl
    rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
      mfderiv_comp t hed hdiff, hfd, ← ENNReal.ofReal_mul (by norm_num)]
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    have h4 := e.torus_inner_le_four_mul_pullback hδ (hcd htI) (hz t htI).le v
    apply ENNReal.ofReal_le_ofReal
    change Real.sqrt (e.cusp.torusMetric.inner (c t).1 v.1 v.1) ≤
      2 * Real.sqrt (g.inner (e.toFun (c t)) (mfderiv halfCollarModel W.model e.toFun (c t) v)
        (mfderiv halfCollarModel W.model e.toFun (c t) v))
    calc Real.sqrt (e.cusp.torusMetric.inner (c t).1 v.1 v.1)
        ≤ Real.sqrt (4 * g.inner (e.toFun (c t))
            (mfderiv halfCollarModel W.model e.toFun (c t) v)
            (mfderiv halfCollarModel W.model e.toFun (c t) v)) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt (g.inner (e.toFun (c t))
            (mfderiv halfCollarModel W.model e.toFun (c t) v)
            (mfderiv halfCollarModel W.model e.toFun (c t) v)) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  calc ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) torusModel (Prod.fst ∘ c) t 1‖ₑ
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal 2 * ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal 2 *
          ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal r := by gcongr
    _ = ENNReal.ofReal (2 * r) := by rw [ENNReal.ofReal_mul (by norm_num)]

/-- **G-diam.** The reference torus of every collar of a nearly cuspidal boundary has
`g_T`-diameter at most `2δ` (for `δ ≤ 1/100`), although the boundary diameter `≤ δ` is only
measured in the ambient distance of `W`. -/
theorem NearlyCuspidalBoundary.torus_riemannianEDistOf_le_two_mul
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) (i : Fin B.count) (x y : Torus) :
    riemannianEDistOf (B.collar i).cusp.torusMetric x y ≤ ENNReal.ofReal (2 * δ) := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  have hmem : ∀ t : Torus, (B.collar i).toFun (t, halfZero) ∈ B.component i := by
    intro t
    exact (B.collar i).boundary_image.subset (mem_range_self t)
  have hd := B.diameter i _ (hmem x) _ (hmem y)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set s : ℝ := min ((ε : ℝ) / 2) (1 / 4) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
  have hs1 : s ≤ (ε : ℝ) / 2 := min_le_left _ _
  have hs2 : s ≤ 1 / 4 := min_le_right _ _
  have hlt : riemannianEDistOf g ((B.collar i).toFun (x, halfZero))
      ((B.collar i).toFun (y, halfZero)) < ENNReal.ofReal (δ + s) :=
    hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  refine ((B.collar i).torus_riemannianEDistOf_le_of_lt hδ (r := δ + s) (by linarith) hlt).trans ?_
  rw [show 2 * (δ + s) = 2 * δ + 2 * s by ring, ENNReal.ofReal_add (by linarith) (by linarith)]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **G-diam, area form.** `Area(T², g_T) ≤ 4πδ²` for the reference torus of every collar
(`δ ≤ 1/100`); no lattice classification is used. -/
theorem NearlyCuspidalBoundary.torus_area_le_four_pi_mul_sq (B : NearlyCuspidalBoundary W g K δ)
    (hδ : δ ≤ 1 / 100) (i : Fin B.count) :
    (Integral.Measure.riemannianVolumeMeasure torusModel Torus
      (B.collar i).cusp.torusMetric univ).toReal ≤ 4 * Real.pi * δ ^ 2 :=
  torus_area_le_four_pi_mul_sq_of_dist_le_two_mul (B.collar i).cusp
    (B.torus_riemannianEDistOf_le_two_mul hδ i)

end DifferentialGeometry.Geometry.Collapse
