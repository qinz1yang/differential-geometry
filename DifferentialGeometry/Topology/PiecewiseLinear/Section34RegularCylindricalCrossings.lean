import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAxisCharts
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
omit [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.exists_axis_chart_of_regular_slice
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLSphere 1 P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    (L : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite L.faces]
    {a b r : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hrab : r ∈ Ioo a b)
    (hL : L.space = (P ×ˢ Icc a b) ∩ f ⁻¹' J)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) (hr : r ∉ Prod.snd '' L.vertices)
    {x : E} (hx : x ∈ P) (hxJ : f (x, r) ∈ J) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) S) (ε : ℝ),
      0 < ε ∧ (e (0, 0) : F) = f (x, r) ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((e p : F) ∈ J ↔ p.1 = 0) ∧
          ((e p : F) ∈ f '' (P ×ˢ {r}) ↔ p.2 = 0) := by
  have hr01 : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_lt ha hrab.1, lt_of_lt_of_le hrab.2 hb⟩
  have hLP : L.space ⊆ P ×ˢ univ := by
    rw [hL]
    exact fun _ hy => ⟨hy.1.1, mem_univ _⟩
  have hxr : (x, r) ∈ L.space ∩ {y | y.2 = r} := by
    rw [hL]
    exact ⟨⟨⟨hx, hrab.1.le, hrab.2.le⟩, hxJ⟩, rfl⟩
  obtain ⟨e, ε, hε, he₁, he₂, hes, he⟩ :=
    hP.exists_product_axis_chart_of_regular_height L hcard hLP hr hxr
  obtain ⟨H, hH⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends hP.isPolyhedron.isCompact hends
  let q := (OpenPartialHomeomorph.refl P).prod (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0)
  let d := (e.trans q).transHomeomorph H.symm
  have hd (p : ℝ × ℝ) : d p = H.symm ((e p).1, ((e p).2 : loopCircle)) := rfl
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hezero : (0, 0) ∈ e.source := hes ⟨hzero, hzero⟩
  have he0 : e (0, 0) = ((⟨x, hx⟩ : P), r) := Prod.ext (Subtype.ext he₁) he₂
  have hd0 : (0, 0) ∈ d.source := by
    change (0, 0) ∈ e.source ∩ e ⁻¹' q.source
    refine ⟨hes ⟨hzero, hzero⟩, ?_⟩
    change e (0, 0) ∈ univ ×ˢ Ioo (0 : ℝ) (0 + 1)
    simpa only [he0, zero_add, mem_prod, mem_univ, true_and] using hr01
  have hdcenter : (d (0, 0) : F) = f (x, r) := by
    rw [hd, he0]
    exact hH ⟨x, hx⟩ ⟨r, hr01.1.le, hr01.2.le⟩
  have hheight : Filter.Tendsto (fun p => (e p).2) (𝓝 (0, 0)) (𝓝 r) := by
    have ht := (continuous_snd.continuousAt.comp
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hezero))).tendsto
    change Filter.Tendsto (fun p => (e p).2) (𝓝 (0, 0)) (𝓝 ((e (0, 0)).2)) at ht
    rwa [he₂] at ht
  have hnear : ∀ᶠ p in 𝓝 (0, 0), p ∈ d.source ∧ (e p).2 ∈ Ioo a b :=
    Filter.Eventually.and (d.open_source.mem_nhds hd0)
      (hheight.eventually (isOpen_Ioo.mem_nhds hrab))
  obtain ⟨ρ, hρ, hρnear⟩ := Metric.mem_nhds_iff.mp hnear
  let η := min ε ρ
  have hη : 0 < η := lt_min hε hρ
  have hηε : η ≤ ε := min_le_left _ _
  have hηρ : η ≤ ρ := min_le_right _ _
  have hpε {p : ℝ × ℝ} (hp : p ∈ Ioo (-η) η ×ˢ Ioo (-η) η) :
      p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε := by
    exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hηε⟩,
      ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hηε⟩⟩
  have hpnear {p : ℝ × ℝ} (hp : p ∈ Ioo (-η) η ×ˢ Ioo (-η) η) :
      p ∈ d.source ∧ (e p).2 ∈ Ioo a b := by
    apply hρnear
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hηρ⟩,
      ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hηρ⟩⟩
  refine ⟨d, η, hη, hdcenter, fun p hp => (hpnear hp).1, ?_⟩
  intro p hp
  have htp := (hpnear hp).2
  have htp01 : (e p).2 ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_lt ha htp.1, lt_of_lt_of_le htp.2 hb⟩
  have hdval : (d p : F) = f ((e p).1, (e p).2) := by
    rw [hd]
    exact hH (e p).1 ⟨(e p).2, htp01.1.le, htp01.2.le⟩
  have hgraph : f ((e p).1, (e p).2) ∈ J ↔ (((e p).1 : E), (e p).2) ∈ L.space := by
    rw [hL]
    exact ⟨fun hy => ⟨⟨(e p).1.2, htp.1.le, htp.2.le⟩, hy⟩, fun hy => hy.2⟩
  constructor
  · rw [hdval, hgraph]
    exact (he p (hpε hp)).1
  · rw [hdval]
    have hslice : f ((e p).1, (e p).2) ∈ f '' (P ×ˢ {r}) ↔ (e p).2 = r := by
      constructor
      · rintro ⟨y, hy, hyeq⟩
        have hyr : y.2 = r := hy.2
        have hy01 : y ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hy.1, hyr ▸ ⟨hr01.1.le, hr01.2.le⟩⟩
        rcases hf.eq_or_endpoints y hy01 (((e p).1 : E), (e p).2)
          ⟨(e p).1.2, htp01.1.le, htp01.2.le⟩ hyeq with h | h | h
        · exact (congrArg Prod.snd h).symm.trans hyr
        · exact (htp01.2.ne h.2).elim
        · exact (htp01.1.ne' h.2).elim
      · intro hpr
        exact ⟨((e p).1, (e p).2), ⟨(e p).1.2, hpr⟩, rfl⟩
    exact hslice.trans (he p (hpε hp)).2

open Classical in
theorem IsCylindricalDiagram.exists_finite_slice_axis_charts
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLSphere 1 P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hstrip : 0 < a ∨ b < 1) :
    ∃ (r : ℝ) (L : Geometry.SimplicialComplex ℝ (E × ℝ)),
      r ∈ Ioo a b ∧ L.faces.Finite ∧ L.space = (P ×ˢ Icc a b) ∩ f ⁻¹' J ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧ r ∉ Prod.snd '' L.vertices ∧
      (J ∩ f '' (P ×ˢ {r})).Finite ∧
      ∀ y ∈ J ∩ f '' (P ×ˢ {r}),
        ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) S) (ε : ℝ),
          0 < ε ∧ (e (0, 0) : F) = y ∧
          Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
          ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
            ((e p : F) ∈ J ↔ p.1 = 0) ∧
              ((e p : F) ∈ f '' (P ×ˢ {r}) ↔ p.2 = 0) := by
  obtain ⟨r, L, hrab, hLfin, hL, hcard, hr, hfinite, -⟩ :=
    hf.exists_finite_regular_slice hP.isPolyhedron hJ ha hab hb hstrip
  let _ : Finite L.faces := hLfin.to_subtype
  refine ⟨r, L, hrab, hLfin, hL, hcard, hr, hfinite, ?_⟩
  rintro y ⟨hyJ, z, ⟨hzP, hzr⟩, rfl⟩
  have hzeq : z = (z.1, r) := Prod.ext rfl hzr
  rw [hzeq] at hyJ ⊢
  exact hf.exists_axis_chart_of_regular_slice hP hends L ha hb hrab hL hcard hr hzP hyJ

end DifferentialGeometry.Topology.PiecewiseLinear
