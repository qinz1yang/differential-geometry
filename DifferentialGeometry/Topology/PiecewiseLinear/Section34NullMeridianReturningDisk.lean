import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalSeamRotation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianBigonArc
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianLocalHeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianReturningDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_returning_disk_of_nullhomotopic_circle_of_height_germs
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {d : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S) (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hJS : J ⊆ S)
    (hnull : (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic)
    {a b r : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hrab : r ∈ Ioo a b)
    (hfinite : (J ∩ f '' (P ×ˢ {r})).Finite)
    (hgerms : ∀ x ∈ P, f (x, r) ∈ J →
      (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 < r}) ∧
        (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | r < y.2}))
    (hne : (J ∩ f '' (P ×ˢ {r})).Nonempty) :
    ∃ (D A : Set F) (q : (Fin 3 → ℝ) → F) (β : ℝ → F),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ IsPLBall 1 A ∧
      IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧ β 0 ≠ β 1 ∧
      β '' Icc 0 1 ⊆ J ∧ β 0 ∈ f '' (P ×ˢ {r}) ∧ β 1 ∈ f '' (P ×ˢ {r}) ∧
      Disjoint (β '' Ioo 0 1) (f '' (P ×ˢ {r})) ∧ IsClosed (J \ β '' Ioo 0 1) ∧
      D ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1) ∧
      q '' stdSimplexBoundary 2 = (β '' Icc 0 1) ∪ A ∧
      D ∩ (f '' (P ×ˢ {r})) = A := by
  classical
  have hP : IsPLBall 2 P := ⟨d, hd⟩
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hrab.1, hrab.2.trans_le hb⟩
  obtain ⟨e, he⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends hP.isPolyhedron.isCompact hends
  obtain ⟨f', e', hf', hseam, hcarriers, he', he'e⟩ :=
    hf.exists_seam_rotation_with_coordinates hP.isPolyhedron hends hr01 e he
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
  obtain ⟨D, A, q, hq, hA, hDside, hqbd, hDM⟩ :=
    hf'.exists_returning_disk_of_upper_height_arc hd e' he' hβ hβside
      (fun t ht _ => (hgl (β t) (hβJ ⟨t, ht, rfl⟩)).symm)
      (hβ0 ▸ hm0) (hβ1 ▸ hm1) (fun t ht => (hheight t ht).2) hδ hδ1 hbound
  have hslice : f' '' (P ×ˢ ({0} : Set ℝ)) = f '' (P ×ˢ ({r} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hxP, ht⟩, hxy⟩
      have ht' : t = 0 := ht
      subst t
      exact ⟨(x, r), ⟨hxP, rfl⟩, (hseam x hxP).1.symm.trans hxy⟩
    · rintro ⟨⟨x, t⟩, ⟨hxP, ht⟩, hxy⟩
      have ht' : t = r := ht
      subst t
      exact ⟨(x, 0), ⟨hxP, rfl⟩, (hseam x hxP).1.trans hxy⟩
  rw [hslice] at hDM
  rw [hcarriers _ hbase] at hDside
  refine ⟨D, A, q, β, hq, hA, hβ, ?_, hβJ, hβ0 ▸ (hp i).2, hβ1 ▸ (hp j).2,
    ?_, hclosed, hDside, hqbd, hDM⟩
  · rw [hβ0, hβ1]
    exact fun heq => hij (hpinj heq)
  · refine disjoint_left.mpr fun y hy hyslice => ?_
    obtain ⟨k, hk⟩ := hponto ⟨hβJ ((image_mono Ioo_subset_Icc_self) hy), hyslice⟩
    exact havoid k (hk.symm ▸ hy)

theorem IsCylindricalDiagram.exists_returning_disk_of_nullhomotopic_circle
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {d : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S) (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hJS : J ⊆ S)
    (hnull : (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic)
    (K : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) {a b r : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hrab : r ∈ Ioo a b) (hK : K.space = (P ×ˢ Icc a b) ∩ f ⁻¹' J)
    (hr : r ∉ Prod.snd '' K.vertices) (hne : (J ∩ f '' (P ×ˢ {r})).Nonempty) :
    ∃ (D A : Set F) (q : (Fin 3 → ℝ) → F) (β : ℝ → F),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ IsPLBall 1 A ∧
      IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧ β 0 ≠ β 1 ∧
      β '' Icc 0 1 ⊆ J ∧ β 0 ∈ f '' (P ×ˢ {r}) ∧ β 1 ∈ f '' (P ×ˢ {r}) ∧
      Disjoint (β '' Ioo 0 1) (f '' (P ×ˢ {r})) ∧ IsClosed (J \ β '' Ioo 0 1) ∧
      D ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1) ∧
      q '' stdSimplexBoundary 2 = (β '' Icc 0 1) ∪ A ∧
      D ∩ (f '' (P ×ˢ {r})) = A := by
  classical
  have hfinite : (J ∩ f '' (P ×ˢ {r})).Finite := by
    apply ((finite_fiber_of_notMem_vertex_image K hcard (LinearMap.snd ℝ E ℝ) hr).image f).subset
    rintro y ⟨hyJ, z, ⟨hzP, hzr⟩, hzy⟩
    refine ⟨z, ⟨?_, hzr⟩, hzy⟩
    rw [hK]
    exact ⟨⟨hzP, hzr.symm ▸ ⟨hrab.1.le, hrab.2.le⟩⟩,
      by change f z ∈ J; rw [hzy]; exact hyJ⟩
  apply hf.exists_returning_disk_of_nullhomotopic_circle_of_height_germs hd hends hJ
    hJside hJS hnull ha hb hrab hfinite ?_ hne
  intro x hxP hxJ
  have hxK : (x, r) ∈ K.space ∩ {y | y.2 = r} := by
    rw [hK]
    exact ⟨⟨⟨hxP, hrab.1.le, hrab.2.le⟩, hxJ⟩, rfl⟩
  have hh := mem_closure_height_sides_of_notMem_vertex_image K hcard
    (LinearMap.snd ℝ E ℝ) hr hxK
  rw [hK] at hh
  exact hh

end DifferentialGeometry.Topology.PiecewiseLinear
