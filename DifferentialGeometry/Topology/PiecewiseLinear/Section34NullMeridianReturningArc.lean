import DifferentialGeometry.Topology.PiecewiseLinear.Section34NullMeridianReturningDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_coordinates_of_seam_formula
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {f g : E × ℝ → F} {P : Set E} {S : Set F} {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t))
    (hrot : ∀ z, g z =
      if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1)) :
    ∃ e' : S ≃ₜ (P × loopCircle),
      (∀ (x : P) (t : Icc (0 : ℝ) 1), (e'.symm (x, (t : ℝ)) : F) = g (x, t)) ∧
      ∀ y : S, e' y = ((e y).1, (e y).2 - r) := by
  let e' : S ≃ₜ (P × loopCircle) :=
    e.trans ((Homeomorph.refl P).prodCongr (Homeomorph.subRight (r : loopCircle)))
  refine ⟨e', ?_, fun _ => rfl⟩
  intro x t
  have he' : e'.symm (x, ((t : ℝ) : loopCircle)) =
      e.symm (x, ((t : ℝ) : loopCircle) + (r : loopCircle)) := rfl
  rw [he', hrot]
  by_cases hc : (t : ℝ) ≤ 1 - r
  · rw [ite_eq_left hc, ← AddCircle.coe_add]
    exact he x ⟨t + r, by linarith [t.2.1, hr.1], by linarith⟩
  · rw [ite_eq_right hc]
    have hcoe : ((t : ℝ) : loopCircle) + (r : loopCircle) =
        (((t : ℝ) + r - 1 : ℝ) : loopCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period, sub_zero]
    rw [hcoe]
    exact he x ⟨t + r - 1, by linarith, by linarith [t.2.2, hr.2]⟩

theorem IsCylindricalDiagram.exists_returning_source_arc_of_nullhomotopic_circle
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f f' : E × ℝ → F} {P : Set E} {S J : Set F} {d : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S) (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hJS : J ⊆ S)
    (hnull : (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic)
    {a b r : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hrab : r ∈ Ioo a b)
    (hrot : ∀ z, f' z =
      if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1))
    (hfinite : (J ∩ f '' (P ×ˢ {r})).Finite)
    (hgerms : ∀ x ∈ P, f (x, r) ∈ J →
      (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 < r}) ∧
        (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | r < y.2}))
    (hne : (J ∩ f '' (P ×ˢ {r})).Nonempty) :
    ∃ (c : ℝ) (γ : ℝ → E × ℝ), 0 < c ∧ c < 1 ∧
      IsPLHomeomorphOn γ (Icc 0 1) (γ '' Icc 0 1) ∧
      γ '' Icc 0 1 ⊆ (d '' stdSimplexBoundary 2) ×ˢ Ioc c 1 ∧
      (γ '' Icc 0 1) ∩ ((d '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) = {γ 0, γ 1} ∧
      f' '' (γ '' Icc 0 1) ⊆ J ∧ IsClosed (J \ f' '' (γ '' Ioo 0 1)) := by
  classical
  have hP : IsPLBall 2 P := ⟨d, hd⟩
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hrab.1, hrab.2.trans_le hb⟩
  obtain ⟨e, he⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends hP.isPolyhedron.isCompact hends
  obtain ⟨f₀, hf₀, -, hcarriers, hformula⟩ := hf.exists_seam_rotation hP.isPolyhedron hends hr01
  have hf₀f' : f₀ = f' := funext fun z => (hformula z).trans (hrot z).symm
  subst f₀
  obtain ⟨e', he', he'e⟩ := exists_coordinates_of_seam_formula hr01 e he hrot
  let π : C(S, loopCircle) := ⟨fun y => (e' y).2, continuous_snd.comp e'.continuous⟩
  obtain ⟨l, hl⟩ := exists_real_circle_lift_of_nullhomotopic (hnull.comp_right π)
  let g : F → ℝ := fun y => if hy : y ∈ J then l ⟨y, hy⟩ else 0
  have hg : ContinuousOn g J := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert l.continuous using 1
    ext y
    exact dite_eq_left y.2
  have hgl (y : F) (hy : y ∈ J) :
      (g y : loopCircle) = (e' ⟨y, hJS hy⟩).2 := by
    have hgval : g y = l ⟨y, hy⟩ := dite_eq_left hy
    rw [hgval]
    exact hl ⟨y, hy⟩
  have hgl' (y : F) (hy : y ∈ J) (hyS : y ∈ S) :
      (g y : loopCircle) = (e ⟨y, hyS⟩).2 - r := by
    rw [hgl y hy, he'e]
  let T := J ∩ f '' (P ×ˢ {r})
  have hTfin : T.Finite := hfinite
  let _ : Fintype T := hTfin.fintype
  let ι := Fintype.equivFin T
  let n := Fintype.card T
  let p : Fin n → F := fun i => (ι.symm i).1
  have hp (i : Fin n) : p i ∈ T := (ι.symm i).2
  have hpinj : Function.Injective p := fun i j hij =>
    ι.symm.injective (Subtype.ext hij)
  have hponto {y : F} (hy : y ∈ T) : ∃ i, p i = y := ⟨ι ⟨y, hy⟩, by simp [p]⟩
  have hn : 0 < n := by
    obtain ⟨y, hy⟩ := hne
    let _ : Nonempty T := ⟨⟨y, hy⟩⟩
    exact Fintype.card_pos
  have hmarks : ∀ y ∈ J, (∃ m : ℤ, g y = m) ↔ ∃ i, p i = y := by
    intro y hyJ
    have hzero : (g y : loopCircle) = 0 ↔ y ∈ f '' (P ×ˢ {r}) := by
      rw [hgl' y hyJ (hJS hyJ), sub_eq_zero]
      constructor
      · intro hy
        have hy' := he (e ⟨y, hJS hyJ⟩).1 ⟨r, hr01.1.le, hr01.2.le⟩
        change (e.symm ((e ⟨y, hJS hyJ⟩).1, (r : loopCircle)) : F) =
          f ((e ⟨y, hJS hyJ⟩).1, r) at hy'
        have hpair : ((e ⟨y, hJS hyJ⟩).1, (r : loopCircle)) = e ⟨y, hJS hyJ⟩ :=
          Prod.ext rfl hy.symm
        rw [hpair, e.symm_apply_apply] at hy'
        exact ⟨(_, r), ⟨(e ⟨y, hJS hyJ⟩).1.2, rfl⟩, hy'.symm⟩
      · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, hxy⟩
        have ht' : t = r := ht
        subst t
        have hy' : e.symm (⟨x, hx⟩, (r : loopCircle)) = (⟨y, hJS hyJ⟩ : S) :=
          Subtype.ext ((he ⟨x, hx⟩ ⟨r, hr01.1.le, hr01.2.le⟩).trans hxy)
        rw [← hy', e.apply_symm_apply]
    have hint : (∃ m : ℤ, g y = m) ↔ (g y : loopCircle) = 0 := by
      symm
      simpa only [zsmul_eq_mul, mul_one, eq_comm] using
        (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := g y))
    rw [hint, hzero]
    exact ⟨fun hy => hponto ⟨hyJ, hy⟩, fun ⟨i, hi⟩ => hi ▸ (hp i).2⟩
  have hcross : ∀ i, (∃ y ∈ J, g y < g (p i)) ∧ ∃ y ∈ J, g (p i) < g y := by
    intro i
    obtain ⟨⟨x, t⟩, ⟨hxP, ht⟩, hxt⟩ := (hp i).2
    have ht' : t = r := ht
    subst t
    have hxJ : f (x, r) ∈ J := hxt.symm ▸ (hp i).1
    obtain ⟨hlo, hhi⟩ := hgerms x hxP hxJ
    simpa only [hxt] using hf.exists_lift_height_sides_of_slice_germs e he hg hgl'
      ha hb ⟨⟨⟨hxP, hrab.1.le, hrab.2.le⟩, hxJ⟩, rfl⟩ hlo hhi
  obtain ⟨i, j, m, β, hij, hβ, hβ0, hβ1, hβJ, havoid, hm0, hm1, hheight,
    hclosed, δ, hδ, hδ1, hbound⟩ :=
    hJ.exists_upper_returning_arc_of_integer_height_marks hn p (fun i => (hp i).1)
      hpinj hg hmarks hcross
  have hbase : d '' stdSimplexBoundary 2 ⊆ P :=
    (image_mono fun _ hx => hx.1).trans hd.image_eq.subset
  have hβside : β '' Icc 0 1 ⊆ f' '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1) := by
    rw [hcarriers _ hbase]
    exact hβJ.trans hJside
  obtain ⟨c, γ, hc, hc1, hγ, hγside, hγtop, hγmap, hγimage⟩ :=
    hf₀.exists_upper_returning_arc_in_strip hP.isPolyhedron hbase e' he' hβ hβside
      (fun t ht _ => (hgl (β t) (hβJ ⟨t, ht, rfl⟩)).symm)
      (hβ0 ▸ hm0) (hβ1 ▸ hm1) (fun t ht => (hheight t ht).2) hδ hδ1 hbound
  have hγopen : f' '' (γ '' Ioo 0 1) = β '' Ioo 0 1 := by
    rw [image_image]
    exact image_congr fun t ht => hγmap t (Ioo_subset_Icc_self ht)
  exact ⟨c, γ, hc, hc1, hγ, hγside, hγtop, hγimage ▸ hβJ, hγopen.symm ▸ hclosed⟩

end DifferentialGeometry.Topology.PiecewiseLinear
