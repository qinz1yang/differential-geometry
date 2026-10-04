import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypDiscs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCornerWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryDomain

/-!
# The wall patches of a hyperbolic closed triangle fold

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatPatches`). For a fold datum `D` on a
hyperbolic triangle `σ`, with walls `wᵢ = σ.wallSide i`, reflections `rᵢ = σ.refl i` and the
margin `κ = kap D` (at most half of `radOne · cOne`, `radTwo · cTwo`, `radThree · sin θ₃`, the
constants of the cover), the wall patches have the seven conditions of the flat case:
`patchZero`: `z ∈ V₀`, `κ < w₁, w₂` at `z` and at `r₀ z`, `Re f z < -3/2`, and the wedges
`|arg (e^{-iθ₂} rotTwo z)| < θ₂/2`, `|arg z| < θ₃/2` in the discs about `v₂`, `0`; `patchOne`:
`z ∈ V₁`, `κ < w₀, w₂` at `z` and `r₁ z`, `3/2 < Re f z`, wedges `|arg rotOne z| < θ₁/2`,
`|arg (e^{-iθ₃} z)| < θ₃/2`; `patchTwo`: `z ∈ V₂`, `κ < w₀, w₁` at `z` and `r₂ z`,
`-3/2 < Re f z < 3/2`, `|f z|² < 25/4`, wedges `|arg (e^{-iθ₁} rotOne z)| < θ₁/2`,
`|arg rotTwo z| < θ₂/2`. The main set is the open triangle `σ.openTriangle` together with the
three patches. Since `V i ⊆ U ⊆` the unit disc, where the Möbius maps `rotOne`, `rotTwo`, `r₂`
are continuous, all pieces are open (`isOpen_mainSet`); each patch is stable under its
reflection (`refl_mem_patchZero`, …), and a patch point outside the triangle reflects into the
open triangle (`refl_mem_intT_of_patchZero`, …).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

variable {σ : CompactShape} (D : σ.FoldData)

section Margin

variable (σ) in
def cOne : ℝ := min (σ.sideTanTwo * Real.sin σ.θ₂) (Real.sin σ.θ₁) * (1 - σ.sideTanOne) ^ 2

variable (σ) in
def cTwo : ℝ := Real.sin σ.θ₂ * (1 - σ.sideTanTwo) ^ 2

def kap : ℝ :=
  min (min (radOne D * cOne σ) (radTwo D * cTwo σ)) (radThree D * Real.sin σ.θ₃) / 2

variable (hσ : σ.curv = .hyperbolic)
include hσ

omit D in
theorem sideTanOne_lt_one : σ.sideTanOne < 1 := by
  have := σ.eps_sideTanOne_sq_lt
  rw [CompactShape.eps_of_hyp σ hσ, one_mul] at this
  nlinarith [σ.sideTanOne_pos]

omit D in
theorem sideTanTwo_lt_one : σ.sideTanTwo < 1 := by
  have := σ.eps_sideTanTwo_sq_lt
  rw [CompactShape.eps_of_hyp σ hσ, one_mul] at this
  nlinarith [σ.sideTanTwo_pos]

omit D in
theorem cOne_pos : 0 < cOne σ := by
  have := σ.sideTanTwo_pos
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  have := sideTanOne_lt_one hσ
  unfold cOne
  exact mul_pos (lt_min (by positivity) (by positivity)) (by nlinarith)

omit D in
theorem cTwo_pos : 0 < cTwo σ := by
  have := σ.sin_θ₂_pos
  have := sideTanTwo_lt_one hσ
  unfold cTwo
  exact mul_pos (by positivity) (by nlinarith)

theorem kap_pos : 0 < kap D := by
  have := radOne_pos D
  have := radTwo_pos D
  have := radThree_pos D
  have := cOne_pos hσ
  have := cTwo_pos hσ
  have := σ.sin_θ₃_pos
  unfold kap
  exact div_pos (lt_min (lt_min (by positivity) (by positivity)) (by positivity)) (by norm_num)

theorem kap_lt_one : kap D < radOne D * cOne σ := by
  have := radOne_pos D
  have := cOne_pos hσ
  have : min (min (radOne D * cOne σ) (radTwo D * cTwo σ)) (radThree D * Real.sin σ.θ₃) ≤
      radOne D * cOne σ := (min_le_left _ _).trans (min_le_left _ _)
  unfold kap
  nlinarith

theorem kap_lt_two : kap D < radTwo D * cTwo σ := by
  have := radTwo_pos D
  have := cTwo_pos hσ
  have : min (min (radOne D * cOne σ) (radTwo D * cTwo σ)) (radThree D * Real.sin σ.θ₃) ≤
      radTwo D * cTwo σ := (min_le_left _ _).trans (min_le_right _ _)
  unfold kap
  nlinarith

omit hσ in
theorem kap_lt_three : kap D < radThree D * Real.sin σ.θ₃ := by
  have := radThree_pos D
  have := σ.sin_θ₃_pos
  have : min (min (radOne D * cOne σ) (radTwo D * cTwo σ)) (radThree D * Real.sin σ.θ₃) ≤
      radThree D * Real.sin σ.θ₃ := min_le_right _ _
  unfold kap
  nlinarith

end Margin

variable (σ) in
def intT : Set ℂ := σ.openTriangle

def patchZero : Set ℂ :=
  {z | z ∈ D.V 0 ∧ kap D < σ.wallSide 1 z ∧ kap D < σ.wallSide 2 z ∧
    kap D < σ.wallSide 1 (σ.refl 0 z) ∧ kap D < σ.wallSide 2 (σ.refl 0 z) ∧
    (D.f z).re < -(3 / 2) ∧
    (radTwo D < ‖σ.rotTwo z‖ ∨ exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)) ∧
    (radThree D < ‖z‖ ∨ z ∈ wedgeSet (σ.θ₃ / 2))}

def patchOne : Set ℂ :=
  {z | z ∈ D.V 1 ∧ kap D < σ.wallSide 0 z ∧ kap D < σ.wallSide 2 z ∧
    kap D < σ.wallSide 0 (σ.refl 1 z) ∧ kap D < σ.wallSide 2 (σ.refl 1 z) ∧
    3 / 2 < (D.f z).re ∧
    (radOne D < ‖σ.rotOne z‖ ∨ σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)) ∧
    (radThree D < ‖z‖ ∨ exp (-((σ.θ₃ : ℂ) * I)) * z ∈ wedgeSet (σ.θ₃ / 2))}

def patchTwo : Set ℂ :=
  {z | z ∈ D.V 2 ∧ kap D < σ.wallSide 0 z ∧ kap D < σ.wallSide 1 z ∧
    kap D < σ.wallSide 0 (σ.refl 2 z) ∧ kap D < σ.wallSide 1 (σ.refl 2 z) ∧
    -(3 / 2) < (D.f z).re ∧ (D.f z).re < 3 / 2 ∧ normSq (D.f z) < 25 / 4 ∧
    (radOne D < ‖σ.rotOne z‖ ∨
      exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)) ∧
    (radTwo D < ‖σ.rotTwo z‖ ∨ σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2))}

def mainSet : Set ℂ := intT σ ∪ patchZero D ∪ patchOne D ∪ patchTwo D

section Continuity

theorem isOpen_sep_of {V S : Set ℂ} (hV : IsOpen V) (hVB : V ⊆ Metric.ball 0 1)
    (hS : IsOpen (Metric.ball 0 1 ∩ S)) : IsOpen (V ∩ S) := by
  have e : V ∩ S = V ∩ (Metric.ball 0 1 ∩ S) := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hVB h1, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [e]
  exact hV.inter hS

theorem isOpen_ball_inter_inter {S T : Set ℂ} (hS : IsOpen (Metric.ball (0 : ℂ) 1 ∩ S))
    (hT : IsOpen (Metric.ball (0 : ℂ) 1 ∩ T)) : IsOpen (Metric.ball (0 : ℂ) 1 ∩ (S ∩ T)) := by
  have e : Metric.ball (0 : ℂ) 1 ∩ (S ∩ T) =
      (Metric.ball (0 : ℂ) 1 ∩ S) ∩ (Metric.ball (0 : ℂ) 1 ∩ T) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h1, h3⟩
    · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, h2, h3⟩
  rw [e]
  exact hS.inter hT

theorem isOpen_ball_inter_of {S : Set ℂ} (hS : IsOpen S) : IsOpen (Metric.ball (0 : ℂ) 1 ∩ S) :=
  Metric.isOpen_ball.inter hS

theorem isOpen_preimage_f (i : Fin 3) {S : Set ℂ} (hS : IsOpen S) :
    IsOpen (D.V i ∩ {z | D.f z ∈ S}) := by
  have hc : ContinuousOn D.f (D.V i) :=
    D.contDiffOn_f.continuousOn.mono (D.V_subset_U i)
  exact hc.isOpen_inter_preimage (D.isOpen_V i) hS

omit D in
theorem θ_div_two_le_pi (θ : ℝ) (h0 : 0 < θ) (h : θ ≤ Real.pi / 2) : θ / 2 ≤ Real.pi := by
  linarith [Real.pi_pos]

variable {D}
variable (hσ : σ.curv = .hyperbolic)
include hσ

theorem V_subset_ball (i : Fin 3) : D.V i ⊆ Metric.ball 0 1 := by
  intro z hz
  have := D.U_subset_plane (D.V_subset_U i hz)
  rwa [CompactShape.plane_hyp hσ] at this

theorem continuousOn_refl (i : Fin 3) : ContinuousOn (σ.refl i) (Metric.ball 0 1) := by
  fin_cases i
  · exact continuous_conj.continuousOn
  · change ContinuousOn (fun z : ℂ => exp (2 * (σ.θ₃ : ℂ) * I) * conj z) _
    exact (continuous_const.mul continuous_conj).continuousOn
  · intro z hz
    rw [mem_ball_zero_iff] at hz
    have e : σ.refl 2 = fun z => HypFold.mobInv σ.vertexTwo
        (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)) :=
      funext (HypFold.refl_two_eq hσ)
    change ContinuousWithinAt (σ.refl 2) _ z
    rw [e]
    have hne : 1 - conj σ.vertexTwo * z ≠ 0 :=
      HypFold.one_sub_conj_mul_ne_zero (HypFold.norm_vertexTwo_lt_one hσ) hz
    have hm := (HypFold.contDiffAt_mob hne).continuousAt
    have hw : ‖exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)‖ < 1 := by
      rw [norm_mul, HypFold.norm_exp_neg_two, one_mul, Complex.norm_conj]
      exact HypFold.norm_mob_lt_one (HypFold.norm_vertexTwo_lt_one hσ) hz
    have hd := HypFold.one_add_conj_mul_ne_zero (HypFold.norm_vertexTwo_lt_one hσ) hw
    have hg : ContinuousAt (fun z => exp (-(2 * (σ.θ₂ : ℂ) * I)) *
        conj (HypFold.mob σ.vertexTwo z)) z :=
      continuousAt_const.mul (continuous_conj.continuousAt.comp hm)
    have hinv : ContinuousAt (HypFold.mobInv σ.vertexTwo)
        (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)) := by
      unfold HypFold.mobInv
      exact (continuousAt_id.add continuousAt_const).div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hd
    exact (ContinuousAt.comp (g := HypFold.mobInv σ.vertexTwo) (f := fun z =>
      exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)) (x := z) hinv
      hg).continuousWithinAt

omit hσ in
theorem isOpen_wall_cond (i : Fin 3) (r : ℝ) :
    IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z | r < σ.wallSide i z}) :=
  isOpen_ball_inter_of (isOpen_lt continuous_const (σ.continuous_wallSide i))

theorem isOpen_wall_refl_cond (i j : Fin 3) (r : ℝ) :
    IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z | r < σ.wallSide i (σ.refl j z)}) := by
  have hc : ContinuousOn (fun z => σ.wallSide i (σ.refl j z)) (Metric.ball 0 1) :=
    (σ.continuous_wallSide i).comp_continuousOn (continuousOn_refl hσ j)
  exact hc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_lt continuous_const continuous_id)

omit hσ in
theorem isOpen_wedge_cond {g g' : ℂ → ℂ} (hg : ContinuousOn g (Metric.ball 0 1))
    (hg' : ContinuousOn g' (Metric.ball 0 1)) (r a : ℝ) (ha : a ≤ Real.pi) :
    IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z | r < ‖g z‖ ∨ g' z ∈ wedgeSet a}) := by
  have h1 : IsOpen (Metric.ball (0 : ℂ) 1 ∩ g ⁻¹' {w | r < ‖w‖}) :=
    hg.isOpen_inter_preimage Metric.isOpen_ball (isOpen_lt continuous_const continuous_norm)
  have h2 : IsOpen (Metric.ball (0 : ℂ) 1 ∩ g' ⁻¹' wedgeSet a) :=
    hg'.isOpen_inter_preimage Metric.isOpen_ball (isOpen_wedgeSet ha)
  have e : Metric.ball (0 : ℂ) 1 ∩ {z | r < ‖g z‖ ∨ g' z ∈ wedgeSet a} =
      (Metric.ball (0 : ℂ) 1 ∩ g ⁻¹' {w | r < ‖w‖}) ∪
        (Metric.ball (0 : ℂ) 1 ∩ g' ⁻¹' wedgeSet a) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage]
    tauto
  rw [e]
  exact h1.union h2

omit hσ in
theorem isOpen_intT : IsOpen (intT σ) := σ.isOpen_openTriangle

theorem isOpen_patchZero : IsOpen (patchZero D) := by
  have h0 := isOpen_preimage_f D 0 (isOpen_lt continuous_re continuous_const :
    IsOpen {u : ℂ | u.re < -(3 / 2)})
  have hd2 := isOpen_wedge_cond (g' := fun z => exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z)
    (continuousOn_rotTwo hσ) (continuousOn_const.mul (continuousOn_rotTwo hσ)) (radTwo D) _
    (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le)
  have hd3 := isOpen_wedge_cond (g := id) (g' := id) continuousOn_id continuousOn_id
    (radThree D) _ (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le)
  have e : patchZero D = (D.V 0 ∩ {z | D.f z ∈ {u : ℂ | u.re < -(3 / 2)}}) ∩
      ({z | kap D < σ.wallSide 1 z} ∩ ({z | kap D < σ.wallSide 2 z} ∩
      ({z | kap D < σ.wallSide 1 (σ.refl 0 z)} ∩ ({z | kap D < σ.wallSide 2 (σ.refl 0 z)} ∩
      ({z | radTwo D < ‖σ.rotTwo z‖ ∨
        exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)} ∩
      {z | radThree D < ‖id z‖ ∨ id z ∈ wedgeSet (σ.θ₃ / 2)}))))) := by
    ext z
    simp only [patchZero, mem_inter_iff, mem_ofPred_eq, id]
    tauto
  rw [e]
  refine isOpen_sep_of h0 (fun z hz => V_subset_ball hσ 0 hz.1) ?_
  exact isOpen_ball_inter_inter (isOpen_wall_cond 1 _) (isOpen_ball_inter_inter
    (isOpen_wall_cond 2 _) (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 1 0 _)
    (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 2 0 _)
    (isOpen_ball_inter_inter hd2 hd3))))

theorem isOpen_patchOne : IsOpen (patchOne D) := by
  have h0 := isOpen_preimage_f D 1 (isOpen_lt continuous_const continuous_re :
    IsOpen {u : ℂ | 3 / 2 < u.re})
  have hd1 := isOpen_wedge_cond (continuousOn_rotOne hσ) (continuousOn_rotOne hσ) (radOne D) _
    (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le)
  have hd3 := isOpen_wedge_cond (g := id) (g' := fun z => exp (-((σ.θ₃ : ℂ) * I)) * id z)
    continuousOn_id (continuousOn_const.mul continuousOn_id) (radThree D) _
    (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le)
  have e : patchOne D = (D.V 1 ∩ {z | D.f z ∈ {u : ℂ | 3 / 2 < u.re}}) ∩
      ({z | kap D < σ.wallSide 0 z} ∩ ({z | kap D < σ.wallSide 2 z} ∩
      ({z | kap D < σ.wallSide 0 (σ.refl 1 z)} ∩ ({z | kap D < σ.wallSide 2 (σ.refl 1 z)} ∩
      ({z | radOne D < ‖σ.rotOne z‖ ∨ σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} ∩
      {z | radThree D < ‖id z‖ ∨
        exp (-((σ.θ₃ : ℂ) * I)) * id z ∈ wedgeSet (σ.θ₃ / 2)}))))) := by
    ext z
    simp only [patchOne, mem_inter_iff, mem_ofPred_eq, id]
    tauto
  rw [e]
  refine isOpen_sep_of h0 (fun z hz => V_subset_ball hσ 1 hz.1) ?_
  exact isOpen_ball_inter_inter (isOpen_wall_cond 0 _) (isOpen_ball_inter_inter
    (isOpen_wall_cond 2 _) (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 0 1 _)
    (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 2 1 _)
    (isOpen_ball_inter_inter hd1 hd3))))

theorem isOpen_patchTwo : IsOpen (patchTwo D) := by
  have h0 := isOpen_preimage_f D 2 ((isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_normSq continuous_const)) :
    IsOpen {u : ℂ | -(3 / 2) < u.re ∧ u.re < 3 / 2 ∧ normSq u < 25 / 4})
  have hd1 := isOpen_wedge_cond (g' := fun z => exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z)
    (continuousOn_rotOne hσ) (continuousOn_const.mul (continuousOn_rotOne hσ)) (radOne D) _
    (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le)
  have hd2 := isOpen_wedge_cond (continuousOn_rotTwo hσ) (continuousOn_rotTwo hσ) (radTwo D) _
    (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le)
  have e : patchTwo D = (D.V 2 ∩ {z | D.f z ∈
      {u : ℂ | -(3 / 2) < u.re ∧ u.re < 3 / 2 ∧ normSq u < 25 / 4}}) ∩
      ({z | kap D < σ.wallSide 0 z} ∩ ({z | kap D < σ.wallSide 1 z} ∩
      ({z | kap D < σ.wallSide 0 (σ.refl 2 z)} ∩ ({z | kap D < σ.wallSide 1 (σ.refl 2 z)} ∩
      ({z | radOne D < ‖σ.rotOne z‖ ∨
        exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} ∩
      {z | radTwo D < ‖σ.rotTwo z‖ ∨ σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)}))))) := by
    ext z
    simp only [patchTwo, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [e]
  refine isOpen_sep_of h0 (fun z hz => V_subset_ball hσ 2 hz.1) ?_
  exact isOpen_ball_inter_inter (isOpen_wall_cond 0 _) (isOpen_ball_inter_inter
    (isOpen_wall_cond 1 _) (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 0 2 _)
    (isOpen_ball_inter_inter (isOpen_wall_refl_cond hσ 1 2 _)
    (isOpen_ball_inter_inter hd1 hd2))))

theorem isOpen_mainSet : IsOpen (mainSet D) :=
  ((isOpen_intT.union (isOpen_patchZero hσ)).union (isOpen_patchOne hσ)).union
    (isOpen_patchTwo hσ)

end Continuity

section Basic

omit D in
theorem intT_subset_triangle : intT σ ⊆ σ.triangle := σ.openTriangle_subset

omit D in
theorem ne_zero_of_mem_intT {z : ℂ} (hz : z ∈ intT σ) : z ≠ 0 :=
  (σ.ne_of_mem_openTriangle hz).1

theorem intT_subset_U : intT σ ⊆ D.U := fun _ hz =>
  D.triangle_diff_subset_U ⟨intT_subset_triangle hz, ne_zero_of_mem_intT hz⟩

theorem patchZero_subset_V : patchZero D ⊆ D.V 0 := fun _ hz => hz.1

theorem patchOne_subset_V : patchOne D ⊆ D.V 1 := fun _ hz => hz.1

theorem patchTwo_subset_V : patchTwo D ⊆ D.V 2 := fun _ hz => hz.1

theorem mainSet_subset_U : mainSet D ⊆ D.U := by
  rintro z (((h | h) | h) | h)
  · exact intT_subset_U D h
  · exact D.V_subset_U 0 h.1
  · exact D.V_subset_U 1 h.1
  · exact D.V_subset_U 2 h.1

omit D in
theorem arg_conj_of_abs_lt {w : ℂ} {a : ℝ} (ha : a ≤ Real.pi) (h : |arg w| < a) :
    arg (conj w) = -arg w := by
  rw [arg_conj, ite_eq_right]
  intro hπ
  rw [hπ, abs_of_pos Real.pi_pos] at h
  linarith

omit D in
theorem conj_mem_wedgeSet {w : ℂ} {a : ℝ} (ha : a ≤ Real.pi) (h : w ∈ wedgeSet a) :
    conj w ∈ wedgeSet a := by
  refine ⟨(map_ne_zero _).mpr h.1, ?_⟩
  rw [arg_conj_of_abs_lt ha h.2, abs_neg]
  exact h.2

omit D in
theorem norm_exp_two_mul (x : ℝ) : ‖exp (2 * (x : ℂ) * I)‖ = 1 := by
  rw [show 2 * (x : ℂ) * I = ((2 * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

omit D in
theorem exp_neg_mul_exp_two_conj (x : ℝ) (w : ℂ) :
    exp (-((x : ℂ) * I)) * (exp (2 * (x : ℂ) * I) * conj w) =
      conj (exp (-((x : ℂ) * I)) * w) := by
  rw [map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

variable {D}
variable (hσ : σ.curv = .hyperbolic)
include hσ

theorem norm_lt_one_of_mem_V {i : Fin 3} {z : ℂ} (hz : z ∈ D.V i) : ‖z‖ < 1 := by
  have := V_subset_ball hσ i hz
  rwa [mem_ball_zero_iff] at this

theorem refl_mem_plane (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : σ.refl i z ∈ σ.plane := by
  rw [CompactShape.plane_hyp hσ, mem_ball_zero_iff]
  exact HypFold.norm_refl_lt_one hσ i hz

theorem refl_mem_intT_of_patch {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {z : ℂ} (hV : z ∈ D.V i) (hj : 0 < σ.wallSide j z) (hk : 0 < σ.wallSide k z)
    (hj' : 0 < σ.wallSide j (σ.refl i z)) (hk' : 0 < σ.wallSide k (σ.refl i z))
    (hT : z ∉ σ.triangle) : σ.refl i z ∈ intT σ := by
  have hz := norm_lt_one_of_mem_V hσ hV
  have hpl : z ∈ σ.plane := D.U_subset_plane (D.V_subset_U i hV)
  have hi : σ.wallSide i z < 0 := by
    by_contra h
    apply hT
    refine ⟨hpl, fun l => ?_⟩
    by_cases hl : l = i
    · rw [hl]; exact le_of_not_gt h
    by_cases hl' : l = j
    · rw [hl']; exact hj.le
    have : l = k := by omega
    rw [this]; exact hk.le
  obtain ⟨c, hc, hrc⟩ := HypFold.wallSide_refl hσ i hz
  refine ⟨refl_mem_plane hσ i hz, fun l => ?_⟩
  by_cases hl : l = i
  · rw [hl, hrc]; nlinarith
  by_cases hl' : l = j
  · rw [hl']; exact hj'
  have : l = k := by omega
  rw [this]; exact hk'

theorem refl_mem_intT_of_patchZero {z : ℂ} (hz : z ∈ patchZero D) (hT : z ∉ σ.triangle) :
    σ.refl 0 z ∈ intT σ := by
  have hk := kap_pos D hσ
  exact refl_mem_intT_of_patch hσ (j := 1) (k := 2) (by decide) (by decide) (by decide) hz.1
    (hk.trans hz.2.1) (hk.trans hz.2.2.1) (hk.trans hz.2.2.2.1) (hk.trans hz.2.2.2.2.1) hT

theorem refl_mem_intT_of_patchOne {z : ℂ} (hz : z ∈ patchOne D) (hT : z ∉ σ.triangle) :
    σ.refl 1 z ∈ intT σ := by
  have hk := kap_pos D hσ
  exact refl_mem_intT_of_patch hσ (j := 0) (k := 2) (by decide) (by decide) (by decide) hz.1
    (hk.trans hz.2.1) (hk.trans hz.2.2.1) (hk.trans hz.2.2.2.1) (hk.trans hz.2.2.2.2.1) hT

theorem refl_mem_intT_of_patchTwo {z : ℂ} (hz : z ∈ patchTwo D) (hT : z ∉ σ.triangle) :
    σ.refl 2 z ∈ intT σ := by
  have hk := kap_pos D hσ
  exact refl_mem_intT_of_patch hσ (j := 0) (k := 1) (by decide) (by decide) (by decide) hz.1
    (hk.trans hz.2.1) (hk.trans hz.2.2.1) (hk.trans hz.2.2.2.1) (hk.trans hz.2.2.2.2.1) hT

theorem refl_mem_patchZero {z : ℂ} (hz : z ∈ patchZero D) : σ.refl 0 z ∈ patchZero D := by
  obtain ⟨hV, h1, h2, h3, h4, hf, hw2, hw3⟩ := hz
  have hrr : σ.refl 0 (σ.refl 0 z) = z := HypFold.refl_refl hσ 0 (norm_lt_one_of_mem_V hσ hV)
  refine ⟨D.refl_mapsTo_V 0 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_⟩
  · rw [D.f_refl 0 z hV, conj_re]; exact hf
  · rcases hw2 with h | h
    · left
      rw [HypFold.rotTwo_refl_zero hσ, norm_mul, Complex.norm_conj, norm_exp_two_mul, one_mul]
      exact h
    · right
      rw [HypFold.rotTwo_refl_zero hσ, exp_neg_mul_exp_two_conj]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le) h
  · rcases hw3 with h | h
    · left
      change radThree D < ‖conj z‖
      rwa [Complex.norm_conj]
    · right
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le) h

theorem refl_mem_patchOne {z : ℂ} (hz : z ∈ patchOne D) : σ.refl 1 z ∈ patchOne D := by
  obtain ⟨hV, h1, h2, h3, h4, hf, hw1, hw3⟩ := hz
  have hrr : σ.refl 1 (σ.refl 1 z) = z := HypFold.refl_refl hσ 1 (norm_lt_one_of_mem_V hσ hV)
  refine ⟨D.refl_mapsTo_V 1 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_⟩
  · rw [D.f_refl 1 z hV, conj_re]; exact hf
  · rcases hw1 with h | h
    · left
      rwa [HypFold.rotOne_refl_one hσ, Complex.norm_conj]
    · right
      rw [HypFold.rotOne_refl_one hσ]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le) h
  · rcases hw3 with h | h
    · left
      change radThree D < ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖
      rw [norm_mul, Complex.norm_conj, norm_exp_two_mul, one_mul]
      exact h
    · right
      change exp (-((σ.θ₃ : ℂ) * I)) * (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) ∈ _
      rw [exp_neg_mul_exp_two_conj]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le) h

theorem refl_mem_patchTwo {z : ℂ} (hz : z ∈ patchTwo D) : σ.refl 2 z ∈ patchTwo D := by
  obtain ⟨hV, h1, h2, h3, h4, hf1, hf2, hf3, hw1, hw2⟩ := hz
  have hz1 := norm_lt_one_of_mem_V hσ hV
  have hrr : σ.refl 2 (σ.refl 2 z) = z := HypFold.refl_refl hσ 2 hz1
  have hfr : D.f (σ.refl 2 z) = conj (D.f z) := D.f_refl 2 z hV
  refine ⟨D.refl_mapsTo_V 2 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr, conj_re]; exact hf1
  · rw [hfr, conj_re]; exact hf2
  · rw [hfr, normSq_conj]; exact hf3
  · rcases hw1 with h | h
    · left
      rw [HypFold.rotOne_refl_two hσ hz1, norm_mul, Complex.norm_conj, norm_exp_two_mul, one_mul]
      exact h
    · right
      rw [HypFold.rotOne_refl_two hσ hz1, exp_neg_mul_exp_two_conj]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le) h
  · rcases hw2 with h | h
    · left
      rwa [HypFold.rotTwo_refl_two hσ hz1, Complex.norm_conj]
    · right
      rw [HypFold.rotTwo_refl_two hσ hz1]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le) h

end Basic

end Hyp

end ClosedTriangle

end GC.Seifert
