import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ThreeCrossingModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34SquareShellScalar (c x t : ℝ) : ℝ :=
  max (x - t) ((1 + 2 * c) * x + t - 2 * c)

noncomputable def section34SquareShellFlatten (c : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (section34SquareShellScalar c z.1.1 z.2, section34SquareShellScalar c z.1.2 z.2)

private theorem scalar_zero {c x : ℝ} (hc : 0 ≤ c) (hx : x ∈ Icc (0 : ℝ) 1) :
    section34SquareShellScalar c x 0 = x := by
  unfold section34SquareShellScalar
  rw [sub_zero, add_zero, max_eq_left]
  nlinarith [hx.2]

private theorem scalar_endpoints {c t : ℝ} (ht : t ∈ Icc (0 : ℝ) c) :
    section34SquareShellScalar c 0 t = -t ∧
      section34SquareShellScalar c 1 t = 1 + t := by
  unfold section34SquareShellScalar
  constructor
  · rw [zero_sub, mul_zero, zero_add, max_eq_left (by linarith [ht.2])]
  · rw [mul_one, max_eq_right (by linarith [ht.1])]
    ring

private theorem scalar_strictMono {c t : ℝ} (hc : 0 ≤ c) :
    StrictMono (fun x => section34SquareShellScalar c x t) := by
  intro x y hxy
  unfold section34SquareShellScalar
  exact max_lt_max (by linarith) (by nlinarith)

private theorem scalar_bounds {c t x : ℝ} (hc : 0 ≤ c) (ht : t ∈ Icc (0 : ℝ) c)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    section34SquareShellScalar c x t ∈ Icc (-t) (1 + t) := by
  obtain ⟨hzero, hone⟩ := scalar_endpoints ht
  exact ⟨hzero ▸ (scalar_strictMono hc).monotone hx.1,
    hone ▸ (scalar_strictMono hc).monotone hx.2⟩

private theorem scalar_surj {c t : ℝ} (ht : t ∈ Icc (0 : ℝ) c) :
    SurjOn (fun x => section34SquareShellScalar c x t) (Icc (0 : ℝ) 1)
      (Icc (-t) (1 + t)) := by
  obtain ⟨hzero, hone⟩ := scalar_endpoints ht
  have hcont : Continuous (fun x => section34SquareShellScalar c x t) := by
    unfold section34SquareShellScalar
    fun_prop
  have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
  rw [hzero, hone] at h
  exact fun y hy => h hy

private theorem frontier_square {p : ℝ × ℝ} :
    p ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ↔
      p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) := by
  rw [frontier_prod_eq, closure_Icc, frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc]
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hx | hx, hy⟩) <;>
      simp_all
  · rintro ⟨⟨hx, hy⟩, h | h | h | h⟩
    · exact Or.inr ⟨Or.inl h, hy⟩
    · exact Or.inr ⟨Or.inr h, hy⟩
    · exact Or.inl ⟨hx, Or.inl h⟩
    · exact Or.inl ⟨hx, Or.inr h⟩

theorem isPiecewiseAffineOn_section34SquareShellFlatten (c : ℝ) :
    IsPiecewiseAffineOn (section34SquareShellFlatten c) univ := by
  let X : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Y : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let T : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have h (Z : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ) :
      IsPiecewiseAffineOn (fun z => section34SquareShellScalar c (Z z) z.2) univ := by
    let L : ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ℝ := Z.toAffineMap - T.toAffineMap
    let R : ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ℝ :=
      (1 + 2 * c) • Z.toAffineMap + T.toAffineMap - AffineMap.const ℝ _ (2 * c)
    exact (isPiecewiseAffineOn_of_affine L isOpen_univ).max
      (isPiecewiseAffineOn_of_affine R isOpen_univ)
  exact (h X).prod_mk (h Y)

theorem section34_square_shell_flatten_zero {c : ℝ} (hc : 0 ≤ c) {p : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    section34SquareShellFlatten c (p, 0) = p :=
  Prod.ext (scalar_zero hc hp.1) (scalar_zero hc hp.2)

private theorem boundary_height_le {c t s : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (ht : t ∈ Icc (0 : ℝ) c)
    (hbound : section34SquareShellFlatten c (p, t) ∈ Icc (-s) (1 + s) ×ˢ Icc (-s) (1 + s)) :
    t ≤ s := by
  obtain ⟨hzero, hone⟩ := scalar_endpoints ht
  rcases frontier_square.mp hp with ⟨_, h | h | h | h⟩
  · have hx := hbound.1.1
    change -s ≤ section34SquareShellScalar c p.1 t at hx
    rw [h, hzero] at hx
    linarith
  · have hx := hbound.1.2
    change section34SquareShellScalar c p.1 t ≤ 1 + s at hx
    rw [h, hone] at hx
    linarith
  · have hy := hbound.2.1
    change -s ≤ section34SquareShellScalar c p.2 t at hy
    rw [h, hzero] at hy
    linarith
  · have hy := hbound.2.2
    change section34SquareShellScalar c p.2 t ≤ 1 + s at hy
    rw [h, hone] at hy
    linarith

theorem isPLHomeomorphOn_section34SquareShellFlatten {c : ℝ} (hc : 0 < c) :
    IsPLHomeomorphOn (section34SquareShellFlatten c)
      (((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ {(0 : ℝ)}) ∪
        frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc 0 c)
      (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) := by
  let P := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let D := P ×ˢ {(0 : ℝ)} ∪ frontier P ×ˢ Icc 0 c
  have hD : IsPLBall 2 D :=
    isPLBall_unit_square.isPLBall_bottom_union_frontier (by simp) hc
  have hmem {z : (ℝ × ℝ) × ℝ} (hz : z ∈ D) : z.1 ∈ P ∧ z.2 ∈ Icc (0 : ℝ) c := by
    rcases hz with hz | hz
    · refine ⟨hz.1, ?_⟩
      rw [show z.2 = 0 from hz.2]
      exact ⟨le_rfl, hc.le⟩
    · exact ⟨isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset hz.1, hz.2⟩
  have hbounds {z : (ℝ × ℝ) × ℝ} (hz : z ∈ D) :
      section34SquareShellFlatten c z ∈ Icc (-z.2) (1 + z.2) ×ˢ Icc (-z.2) (1 + z.2) :=
    ⟨scalar_bounds hc.le (hmem hz).2 (hmem hz).1.1,
      scalar_bounds hc.le (hmem hz).2 (hmem hz).1.2⟩
  have hheight {z w : (ℝ × ℝ) × ℝ} (hz : z ∈ D) (hw : w ∈ D)
      (heq : section34SquareShellFlatten c z = section34SquareShellFlatten c w) :
      z.2 ≤ w.2 := by
    rcases hz with hz | hz
    · rw [show z.2 = 0 from hz.2]
      exact (hmem hw).2.1
    · exact boundary_height_le hz.1 hz.2 (heq ▸ hbounds hw)
  have hinj : InjOn (section34SquareShellFlatten c) D := by
    intro z hz w hw heq
    have ht := le_antisymm (hheight hz hw heq) (hheight hw hz heq.symm)
    apply Prod.ext _ ht
    apply Prod.ext
    · apply (scalar_strictMono hc.le (t := z.2)).injective
      simpa only [section34SquareShellFlatten, ht] using congrArg Prod.fst heq
    · apply (scalar_strictMono hc.le (t := z.2)).injective
      simpa only [section34SquareShellFlatten, ht] using congrArg Prod.snd heq
  have hmaps : MapsTo (section34SquareShellFlatten c) D
      (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) := by
    intro z hz
    have hb := hbounds hz
    have ht := (hmem hz).2.2
    exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
      by linarith [hb.2.1], by linarith [hb.2.2]⟩
  have hsurj : SurjOn (section34SquareShellFlatten c) D
      (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) := by
    rintro ⟨x, y⟩ hxy
    by_cases hp : (x, y) ∈ P
    · exact ⟨((x, y), 0), Or.inl ⟨hp, rfl⟩, section34_square_shell_flatten_zero hc.le hp⟩
    · let t := max (max (-x) (x - 1)) (max (-y) (y - 1))
      have hx₀ : -x ≤ t := (le_max_left _ _).trans (le_max_left _ _)
      have hx₁ : x - 1 ≤ t := (le_max_right _ _).trans (le_max_left _ _)
      have hy₀ : -y ≤ t := (le_max_left _ _).trans (le_max_right _ _)
      have hy₁ : y - 1 ≤ t := (le_max_right _ _).trans (le_max_right _ _)
      have ht₀ : 0 ≤ t := by
        by_contra h
        apply hp
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      have ht₁ : t ≤ c := by
        dsimp only [t]
        exact max_le (max_le (by linarith [hxy.1.1]) (by linarith [hxy.1.2]))
          (max_le (by linarith [hxy.2.1]) (by linarith [hxy.2.2]))
      obtain ⟨u, hu, hux⟩ := scalar_surj ⟨ht₀, ht₁⟩
        (show x ∈ Icc (-t) (1 + t) from ⟨by linarith, by linarith⟩)
      obtain ⟨v, hv, hvy⟩ := scalar_surj ⟨ht₀, ht₁⟩
        (show y ∈ Icc (-t) (1 + t) from ⟨by linarith, by linarith⟩)
      have hbd : (u, v) ∈ frontier P := by
        apply frontier_square.mpr
        refine ⟨⟨hu, hv⟩, ?_⟩
        obtain ⟨hzero, hone⟩ := scalar_endpoints ⟨ht₀, ht₁⟩
        have hin := (scalar_strictMono hc.le (t := t)).injective
        rcases max_choice (max (-x) (x - 1)) (max (-y) (y - 1)) with ht | ht
        · rcases max_choice (-x) (x - 1) with hx | hx
          · exact Or.inl (hin (hux.trans (by dsimp only; rw [hzero]; change t = _ at ht; linarith)))
          · exact Or.inr (Or.inl
              (hin (hux.trans (by dsimp only; rw [hone]; change t = _ at ht; linarith))))
        · rcases max_choice (-y) (y - 1) with hy | hy
          · exact Or.inr (Or.inr (Or.inl
              (hin (hvy.trans (by dsimp only; rw [hzero]; change t = _ at ht; linarith)))))
          · exact Or.inr (Or.inr (Or.inr
              (hin (hvy.trans (by dsimp only; rw [hone]; change t = _ at ht; linarith)))))
      exact ⟨((u, v), t), Or.inr ⟨hbd, ht₀, ht₁⟩, Prod.ext hux hvy⟩
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD.isPolyhedron
    ((isPiecewiseAffineOn_section34SquareShellFlatten c).mono_of_isPolyhedron
      hD.isPolyhedron (subset_univ _)) ⟨hmaps, hinj, hsurj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
