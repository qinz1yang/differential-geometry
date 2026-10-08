import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

/-!
# CX-HTUBE2 G1：whole-component witness 与 spatial ε-neck 不交（单一度量，`_CXHB2`）

R-C11-13 D-6 的 whole-component 局部不交，单一度量 `g` 层（下一组在 `g = g(v_n)` 处实例化）：
* **拓扑 / 相交 ⇒ 包含**：`slab_subset_component_CXHB2`——`nk.map '' (S² × (-ε⁻¹, ε⁻¹))` 连通，
  只要它与 `connectedComponent p` 相交就整个含于其中。
* **ambient distance 下界（排除 shortcut）**：`edist_far_lower_CXHB2`——
  `d_g(x, nk.map (center, ¾ε⁻¹)) ≥ (ε⁻¹/2)·√(1-ε)/√R(x)`。证明用 `SpatialNeck.ball_subset_image_slab`
  （树内已证的 first-exit：`g`-球 `B(x, r√(1-ε)/√R(x))` 含于 slab `|z| ≤ r` 的像）+ chart 单射：
  轴向坐标 `¾ε⁻¹ > ½ε⁻¹` 的点不在该 slab 像中，所以不在球里——这是 ambient 距离，不是轴向曲线长。
* **两分支局部 exclusion**：`disjoint_slab_of_wholeComponent_CXHB2`——若 `W` 的 domain 是整个
  `connectedComponent p`（positive / round 两支，`domain_eq_component_of_posOrRound_CXHB2`），
  且 `ε · (10 · C1 · √C2) ≤ 1`，则 `connectedComponent p` 与 neck slab 像不交。
  定量：`R(x) ≤ C2 R(p)`（`scalar_bounds`，`B = 1`）、`diam ≤ 4·radius ≤ 4 C1 / √R(p)`（`inside_ball`），
  下界常数 `a = √(1-ε)/2 ≥ √(10/11)/2`；`c₀ = 1/10 < a/4`（严格余量）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M}

/-- neck 的开 slab 像连通，与 `connectedComponent p` 相交即整个含于其中。 -/
theorem slab_subset_component_CXHB2 {eps : ℝ} {x : M} (nk : SpatialNeck g eps x) {p w : M}
    (hw : w ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) (hwp : w ∈ connectedComponent p) :
    nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ connectedComponent p := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hS : IsPreconnected ((univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹) :=
    isPreconnected_univ.prod isPreconnected_Ioo
  have hA : IsPreconnected (nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :=
    hS.image nk.map (nk.map.contMDiffOn_toFun.continuousOn.mono nk.domain)
  rw [connectedComponent_eq hwp]
  exact hA.subset_connectedComponent hw

variable [T2Space M]

/-- **ambient distance 下界**：中心到轴向坐标 `¾ε⁻¹` 处点的 `g`-距离 `≥ (ε⁻¹/2)√(1-ε)/√R(x)`。 -/
theorem edist_far_lower_CXHB2 {eps : ℝ} {x : M} (nk : SpatialNeck g eps x) :
    ENNReal.ofReal (eps⁻¹ / 2 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)) ≤
      riemannianEDistOf g x (nk.map (nk.center, 3 / 4 * eps⁻¹)) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk.eps_pos
  by_contra hlt
  have hball : nk.map (nk.center, 3 / 4 * eps⁻¹) ∈
      riemannianBallOf g x (eps⁻¹ / 2 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)) :=
    lt_of_not_ge hlt
  obtain ⟨z, hz, hzeq⟩ := nk.ball_subset_image_slab (half_pos hi) (half_lt_self hi) hball
  have hzsrc : z ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hysrc : (nk.center, 3 / 4 * eps⁻¹) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;> linarith⟩
  have he := nk.map.toPartialEquiv.injOn hzsrc hysrc hzeq
  have h2 := congrArg Prod.snd he
  change z.2 = 3 / 4 * eps⁻¹ at h2
  linarith [hz.2.2]

variable [SigmaCompactSpace M]

/-- positive / round 两支的 domain 是整个 `connectedComponent`。 -/
theorem domain_eq_component_of_posOrRound_CXHB2 {η C1 C2 : ℝ} {p : M}
    (W : SpatialCanonicalWitness g η C1 C2 p)
    (h : (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R) :
    W.domain.carrier = connectedComponent p := by
  rcases h with ⟨wh, -, -, -⟩ | ⟨wh, -, -⟩ <;> exact wh

private theorem real_contra_CXHB2 {eps C1 s t a b : ℝ} (heps : 0 < eps) (heps' : eps < 1 / 11)
    (ha : 0 < a) (hb : 0 < b) (hC1 : 1 ≤ C1) (hab : a ≤ s * b)
    (ht : t = Real.sqrt (1 - eps)) (hsmall : eps * (10 * C1 * s) ≤ 1)
    (hlt : eps⁻¹ / 2 * t / a < 4 * (C1 / b)) : False := by
  have ht2 : t ^ 2 = 1 - eps := by rw [ht, Real.sq_sqrt (by linarith)]
  have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
  have h1 : eps⁻¹ / 2 * t * b < 4 * C1 * a := by
    rw [mul_div_assoc', div_lt_div_iff₀ ha hb] at hlt
    linarith
  have h2 : t * b < 8 * C1 * a * eps := by
    have := mul_lt_mul_of_pos_right h1 heps
    have he : eps⁻¹ / 2 * t * b * eps = t * b / 2 := by field_simp
    linarith
  have h3 : 8 * C1 * a * eps ≤ 8 * C1 * (s * b) * eps := by
    have : 0 ≤ 8 * C1 * eps := by positivity
    nlinarith
  have h4 : t < 8 * C1 * s * eps := by
    have : t * b < 8 * C1 * s * eps * b := by nlinarith
    exact lt_of_mul_lt_mul_right this hb.le
  nlinarith

/-- **whole-component 局部 exclusion（单一度量）**：`W` 的 domain 是整个 `connectedComponent p`，
`nk` 是 `g` 的 spatial `ε`-neck（任意中心 `x`），`ε · (10 C1 √C2) ≤ 1` ⇒ 不交。 -/
theorem disjoint_slab_of_wholeComponent_CXHB2 {η C1 C2 eps : ℝ} {p x : M}
    (W : SpatialCanonicalWitness g η C1 C2 p) (hwhole : W.domain.carrier = connectedComponent p)
    (nk : SpatialNeck g eps x) (hsmall : eps * (10 * C1 * Real.sqrt C2) ≤ 1) :
    Disjoint (connectedComponent p) (nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) := by
  rw [Set.disjoint_left]
  intro w hwp hw
  have hsub := slab_subset_component_CXHB2 nk hw hwp
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk.eps_pos
  have hx : x ∈ W.domain.carrier := by
    rw [hwhole]
    refine hsub ⟨(nk.center, 0), ⟨mem_univ _, by constructor <;> linarith⟩, nk.center_eq⟩
  have hy : nk.map (nk.center, 3 / 4 * eps⁻¹) ∈ W.domain.carrier := by
    rw [hwhole]
    exact hsub ⟨_, ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩
  have hRp := W.Q_pos
  have hRx := nk.Q_pos
  have hpdom : p ∈ W.domain.carrier := interior_subset W.center_inside
  have hC2 : 1 ≤ C2 := by
    have h := (W.scalar_bounds p hpdom).2
    nlinarith
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    have hsq := Real.sqrt_pos.mpr hRp
    rw [div_eq_mul_inv] at h
    nlinarith [inv_pos.mpr hsq, mul_inv_cancel₀ hsq.ne']
  have hrad0 : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr hRp)).trans_le W.radius_lower
  have hdx : riemannianEDistOf g p x < ENNReal.ofReal (2 * W.radius) := W.inside_ball hx
  have hdy : riemannianEDistOf g p (nk.map (nk.center, 3 / 4 * eps⁻¹)) <
      ENNReal.ofReal (2 * W.radius) := W.inside_ball hy
  have hxy : riemannianEDistOf g x (nk.map (nk.center, 3 / 4 * eps⁻¹)) <
      ENNReal.ofReal (4 * W.radius) := by
    calc riemannianEDistOf g x (nk.map (nk.center, 3 / 4 * eps⁻¹))
        ≤ riemannianEDistOf g x p + riemannianEDistOf g p (nk.map (nk.center, 3 / 4 * eps⁻¹)) :=
          riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal (2 * W.radius) + ENNReal.ofReal (2 * W.radius) := by
          rw [riemannianEDistOf_comm g x p]
          exact ENNReal.add_lt_add hdx hdy
      _ = ENNReal.ofReal (4 * W.radius) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hlow := (edist_far_lower_CXHB2 nk).trans_lt hxy
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hlow
  have hrad : 4 * W.radius ≤ 4 * (C1 / Real.sqrt (metricScalarAt g p)) := by
    linarith [W.radius_upper]
  have hxs : Real.sqrt (metricScalarAt g x) ≤
      Real.sqrt C2 * Real.sqrt (metricScalarAt g p) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (W.scalar_bounds x hx).2
  exact real_contra_CXHB2 nk.eps_pos nk.eps_small (Real.sqrt_pos.mpr hRx)
    (Real.sqrt_pos.mpr hRp) hC1 hxs rfl hsmall (hlow.trans_le hrad)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
