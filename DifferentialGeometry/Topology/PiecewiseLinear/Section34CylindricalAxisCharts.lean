import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCurveLevels
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def curveCoordinateShear (u : ℝ → ℝ) (hu : Continuous u) (r : ℝ) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 + u p.2, r + p.2)
  invFun p := (p.1 - u (p.2 - r), p.2 - r)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
  continuous_toFun := (continuous_fst.add (hu.comp continuous_snd)).prodMk
    (continuous_const.add continuous_snd)
  continuous_invFun :=
    (continuous_fst.sub (hu.comp (continuous_snd.sub continuous_const))).prodMk
      (continuous_snd.sub continuous_const)

theorem exists_product_axis_chart_of_line_germ
    {P : Set E} (c : OpenPartialHomeomorph ℝ P) {K : Set (E × ℝ)}
    (hKP : K ⊆ P ×ˢ univ) {x v : E × ℝ} (hxP : x.1 ∈ P)
    (hxc : (⟨x.1, hxP⟩ : P) ∈ c.target) (hv : v.2 = 1)
    (hgerm : ∀ᶠ y in 𝓝 x, y ∈ K ↔ ∃ t : ℝ, y = x + t • v) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (P × ℝ)) (ε : ℝ),
      0 < ε ∧ ((e (0, 0)).1 : E) = x.1 ∧ (e (0, 0)).2 = x.2 ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((((e p).1 : E), (e p).2) ∈ K ↔ p.1 = 0) ∧
          ((e p).2 = x.2 ↔ p.2 = 0) := by
  let γ : ℝ → E × ℝ := fun t => x + t • v
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = x := by simp [γ]
  have ht : Filter.Tendsto γ (𝓝 0) (𝓝 x) := by
    have ht0 : Filter.Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγ.continuousAt
    rwa [hγ0] at ht0
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ K := by
    filter_upwards [ht.eventually hgerm] with t htg
    exact htg.mpr ⟨t, rfl⟩
  obtain ⟨U, hU, hcU⟩ := isOpen_induced_iff.mp c.open_target
  have hxU : x.1 ∈ U := by
    rw [← hcU] at hxc
    exact hxc
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ K ∧ (γ t).1 ∈ U := by
    exact hmem.and (((continuous_fst.tendsto x).comp ht).eventually (hU.mem_nhds hxU))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  let d := δ / 2
  have hd : 0 < d := half_pos hδ
  have hdδ : d < δ := by dsimp [d]; linarith
  let τ : ℝ → ℝ := fun t => max (-d) (min d t)
  have hτ (t : ℝ) : τ t ∈ Icc (-d) d := by
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hτnear (t : ℝ) : γ (τ t) ∈ K ∧ (γ (τ t)).1 ∈ U := by
    apply hδnear
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [(hτ t).1], by linarith [(hτ t).2]⟩
  let g : ℝ → P := fun t => ⟨(γ (τ t)).1, (hKP (hτnear t).1).1⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp (hγ.comp
      (continuous_const.max (continuous_const.min continuous_id)))
  have hgc (t : ℝ) : g t ∈ c.target := by
    rw [← hcU]
    exact (hτnear t).2
  let u : ℝ → ℝ := fun t => c.symm (g t)
  have hu : Continuous u := continuousOn_univ.mp
    (c.continuousOn_symm.comp hg.continuousOn (fun t _ => hgc t))
  have hτ0 : τ 0 = 0 := by simp [τ, le_of_lt hd, le_of_lt (neg_neg_of_pos hd)]
  have hg0 : g 0 = (⟨x.1, hxP⟩ : P) := by
    apply Subtype.ext
    simp [g, hτ0, hγ0]
  let H := curveCoordinateShear u hu x.2
  let e := H.transOpenPartialHomeomorph (c.prod (OpenPartialHomeomorph.refl ℝ))
  have he (p : ℝ × ℝ) : e p = (c (p.1 + u p.2), x.2 + p.2) := rfl
  have hes (p : ℝ × ℝ) : p ∈ e.source ↔ p.1 + u p.2 ∈ c.source := by
    simp [e, H, curveCoordinateShear, Homeomorph.transOpenPartialHomeomorph]
  have he0 : e (0, 0) = ((⟨x.1, hxP⟩ : P), x.2) := by
    rw [he]
    simp only [zero_add, add_zero]
    change (c (c.symm (g 0)), x.2) = _
    rw [c.right_inv (hgc 0), hg0]
  have hzero : (0, 0) ∈ e.source := by
    rw [hes, zero_add]
    exact c.map_target (hgc 0)
  have hecont : ContinuousAt (fun p => (((e p).1 : E), (e p).2)) (0, 0) := by
    exact (continuous_subtype_val.continuousAt.comp
      (continuous_fst.continuousAt.comp
        (e.continuousOn.continuousAt (e.open_source.mem_nhds hzero)))).prodMk
      (continuous_snd.continuousAt.comp
        (e.continuousOn.continuousAt (e.open_source.mem_nhds hzero)))
  have heng : ∀ᶠ p in 𝓝 (0, 0),
      ((((e p).1 : E), (e p).2) ∈ K ↔
        ∃ t : ℝ, (((e p).1 : E), (e p).2) = x + t • v) := by
    have hh : Filter.Tendsto (fun p => (((e p).1 : E), (e p).2))
        (𝓝 (0, 0)) (𝓝 x) := by
      have hh := hecont.tendsto
      simpa only [he0, Prod.mk.eta] using hh
    exact hh.eventually hgerm
  have hbox : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      p ∈ e.source ∧ p.2 ∈ Ioo (-d) d ∧
        ((((e p).1 : E), (e p).2) ∈ K ↔
          ∃ t : ℝ, (((e p).1 : E), (e p).2) = x + t • v) := by
    exact Filter.Eventually.and (e.open_source.mem_nhds hzero)
      (((continuous_snd.tendsto (0, 0)).eventually
        (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos hd, hd⟩)).and heng)
  obtain ⟨ε, hε, hεbox⟩ := Metric.mem_nhds_iff.mp hbox
  have hpbox {p : ℝ × ℝ} (hp : p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε) :
      p ∈ e.source ∧ p.2 ∈ Ioo (-d) d ∧
        ((((e p).1 : E), (e p).2) ∈ K ↔
          ∃ t : ℝ, (((e p).1 : E), (e p).2) = x + t • v) := by
    apply hεbox
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt,
      mem_prod, mem_Ioo] using hp
  refine ⟨e, ε, hε, congrArg (fun q : P × ℝ => (q.1 : E)) he0,
    congrArg Prod.snd he0, fun p hp => (hpbox hp).1, ?_⟩
  intro p hp
  obtain ⟨hps, hpd, hpg⟩ := hpbox hp
  have hτp : τ p.2 = p.2 := by
    simp only [τ, min_eq_right hpd.2.le, max_eq_right hpd.1.le]
  have hgval : (g p.2 : E) = x.1 + p.2 • v.1 := by simp [g, hτp, γ]
  constructor
  · rw [hpg]
    constructor
    · rintro ⟨t, ht⟩
      have htime : t = p.2 := by
        have hh := congrArg Prod.snd ht
        rw [he] at hh
        change x.2 + p.2 = x.2 + t * v.2 at hh
        rw [hv, mul_one] at hh
        linarith
      have hbase : c (p.1 + u p.2) = g p.2 := by
        apply Subtype.ext
        have hh := congrArg Prod.fst ht
        rw [he, htime] at hh
        exact hh.trans hgval.symm
      have huinj := c.injOn ((hes p).mp hps) (c.map_target (hgc p.2))
        (hbase.trans (c.right_inv (hgc p.2)).symm)
      change p.1 + u p.2 = u p.2 at huinj
      exact add_eq_right.mp huinj
    · intro hp0
      refine ⟨p.2, ?_⟩
      rw [he]
      ext
      · simp only [hp0, zero_add]
        change (c (c.symm (g p.2)) : E) = _
        rw [c.right_inv (hgc p.2)]
        exact hgval
      · simp [hv]
  · rw [he]
    exact add_eq_left

open Classical in
theorem IsPLSphere.exists_product_axis_chart_of_regular_height [FiniteDimensional ℝ E]
    {P : Set E} (hP : IsPLSphere 1 P)
    (K : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (hKP : K.space ⊆ P ×ˢ univ)
    {r : ℝ} (hr : r ∉ Prod.snd '' K.vertices) {x : E × ℝ}
    (hx : x ∈ K.space ∩ {y | y.2 = r}) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (P × ℝ)) (ε : ℝ),
      0 < ε ∧ ((e (0, 0)).1 : E) = x.1 ∧ (e (0, 0)).2 = r ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((((e p).1 : E), (e p).2) ∈ K.space ↔ p.1 = 0) ∧
          ((e p).2 = r ↔ p.2 = 0) := by
  obtain ⟨B, hBfin, hBP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsCombinatorialManifold 1 B :=
    IsPLSphere.isCombinatorialManifold (hBP.symm ▸ hP)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) B.space := combinatorialChartedSpace B hB
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) P :=
    (Homeomorph.setCongr hBP).chartedSpace
  let a : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let _ : ChartedSpace ℝ (EuclideanSpace ℝ (Fin 1)) := a.toHomeomorph.chartedSpace
  let _ : ChartedSpace ℝ P := ChartedSpace.comp ℝ (EuclideanSpace ℝ (Fin 1)) P
  have hxP : x.1 ∈ P := (hKP hx.1).1
  let c := (chartAt ℝ (⟨x.1, hxP⟩ : P)).symm
  obtain ⟨p, q, -, -, hpq, -, hgerm⟩ :=
    exists_edge_of_mem_fiber_of_notMem_vertex_image K hcard (LinearMap.snd ℝ E ℝ) hr hx
  have hΔ : q.2 - p.2 ≠ 0 := sub_ne_zero.mpr hpq.symm
  let v : E × ℝ := (q.2 - p.2)⁻¹ • (q - p)
  have hv : v.2 = 1 := by
    change (q.2 - p.2)⁻¹ * (q.2 - p.2) = 1
    exact inv_mul_cancel₀ hΔ
  have hnorm : ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ t : ℝ, y = x + t • v := by
    filter_upwards [hgerm] with y hy
    rw [hy]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t * (q.2 - p.2), by simp [v, smul_smul, hΔ]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t * (q.2 - p.2)⁻¹, by simp [v, smul_smul]⟩
  obtain ⟨e, ε, hε, he₁, he₂, hes, he⟩ := exists_product_axis_chart_of_line_germ
    c hKP hxP (mem_chart_source ℝ _) hv hnorm
  have hxr : x.2 = r := hx.2
  exact ⟨e, ε, hε, he₁, he₂.trans hxr, hes, by simpa only [hxr] using he⟩

end DifferentialGeometry.Topology.PiecewiseLinear
