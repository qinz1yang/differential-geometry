import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem future_square_pos (z : ℝ × E) (hz : ‖z.2‖ < z.1) :
    0 < z.1 ^ 2 - ‖z.2‖ ^ 2 := by
  nlinarith [norm_nonneg z.2]

private def normalizeFuture (z : ℝ × E) (hz : ‖z.2‖ < z.1) : Hyperboloid E where
  time := (Real.sqrt (z.1 ^ 2 - ‖z.2‖ ^ 2))⁻¹ * z.1
  space := (Real.sqrt (z.1 ^ 2 - ‖z.2‖ ^ 2))⁻¹ • z.2
  time_pos := mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (future_square_pos z hz)))
    (lt_of_le_of_lt (norm_nonneg _) hz)
  time_sq_sub_inner_self := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h := Real.sq_sqrt (future_square_pos z hz).le
    have hn := (Real.sqrt_pos.mpr (future_square_pos z hz)).ne'
    field_simp
    nlinarith

private theorem norm_space_lt_time (x : Hyperboloid E) : ‖x.space‖ < x.time := by
  nlinarith [x.time_sq, x.time_pos, norm_nonneg x.space]

theorem fixedPoints_nonempty_of_finite (G : Type*) [Group G] [Finite G]
    [MulAction G (Hyperboloid E)] [IsIsometricSMul G (Hyperboloid E)] :
    (MulAction.fixedPoints G (Hyperboloid E)).Nonempty := by
  classical
  let _ := Fintype.ofFinite G
  let s : ℝ × E := ∑ g : G, ((g • (origin : Hyperboloid E)).time, (g • origin).space)
  have hs : ‖s.2‖ < s.1 := by
    change ‖(LinearMap.snd ℝ ℝ E) (∑ g : G,
      ((g • (origin : Hyperboloid E)).time, (g • origin).space))‖ <
      (LinearMap.fst ℝ ℝ E) (∑ g : G,
        ((g • (origin : Hyperboloid E)).time, (g • origin).space))
    rw [map_sum, map_sum]
    calc
      _ ≤ ∑ g : G, ‖(g • (origin : Hyperboloid E)).space‖ := norm_sum_le _ _
      _ < ∑ g : G, (g • (origin : Hyperboloid E)).time :=
        Finset.sum_lt_sum_of_nonempty ⟨1, Finset.mem_univ _⟩
          (fun g _ => norm_space_lt_time (g • origin))
  have hfixed (g : G) : lorentzExtension (IsometryEquiv.constSMul g :
      Hyperboloid E ≃ᵢ Hyperboloid E) s = s := by
    dsimp only [s]
    rw [map_sum]
    simp only [lorentzExtension_apply, IsometryEquiv.constSMul_apply, ← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft g)
      (fun h : G => ((h • (origin : Hyperboloid E)).time, (h • (origin : Hyperboloid E)).space))
  let p := normalizeFuture s hs
  refine ⟨p, fun g => ?_⟩
  have hc : (p.time, p.space) = (Real.sqrt (s.1 ^ 2 - ‖s.2‖ ^ 2))⁻¹ • s := rfl
  have h := lorentzExtension_apply (IsometryEquiv.constSMul g :
    Hyperboloid E ≃ᵢ Hyperboloid E) p
  rw [hc, map_smul, hfixed g] at h
  apply ext
  exact congrArg Prod.snd (h.symm.trans hc.symm)

theorem isOfFinOrder_iff_eq_one (G : Type*) [Group G]
    [MulAction G (Hyperboloid E)] [IsIsometricSMul G (Hyperboloid E)]
    [IsCancelSMul G (Hyperboloid E)] (g : G) : IsOfFinOrder g ↔ g = 1 := by
  constructor
  · intro hg
    let _ : Finite (Subgroup.zpowers g) :=
      Finite.of_equiv (Fin (orderOf g)) (finEquivZPowers hg)
    let _ : IsIsometricSMul (Subgroup.zpowers g) (Hyperboloid E) :=
      ⟨fun h => isometry_smul (Hyperboloid E) (h : G)⟩
    obtain ⟨p, hp⟩ := fixedPoints_nonempty_of_finite (E := E) (Subgroup.zpowers g)
    have hgp : g • p = p := hp ⟨g, Subgroup.mem_zpowers g⟩
    exact IsCancelSMul.eq_one_of_smul hgp
  · rintro rfl
    exact IsOfFinOrder.one

end DifferentialGeometry.Hyperboloid
