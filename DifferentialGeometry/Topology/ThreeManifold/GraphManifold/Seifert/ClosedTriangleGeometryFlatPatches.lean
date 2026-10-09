import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatDiscs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryDomain

/-!
# The wall patches of a flat closed triangle fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§1, with review 27's certificate: image domains on the patches, angle domains in the discs). For a
fold datum `D` on a flat triangle `σ`, with walls `wᵢ = σ.wallSide i`, reflections `rᵢ = σ.refl i`
and the margin `κ = kap D`, the wall patches are
* `patchZero`: `z ∈ V₀`, `κ < w₁, w₂` at `z` and at `r₀ z`, `Re f z < -3/2`, and in the discs about
  `v₂`, `0` the wedges `|arg (e^{-iθ₂} rotTwo z)| < θ₂/2`, `|arg z| < θ₃/2`;
* `patchOne`: `z ∈ V₁`, `κ < w₀, w₂` at `z` and `r₁ z`, `3/2 < Re f z`, wedges
  `|arg rotOne z| < θ₁/2`, `|arg (e^{-iθ₃} z)| < θ₃/2`;
* `patchTwo`: `z ∈ V₂`, `κ < w₀, w₁` at `z` and `r₂ z`, `-3/2 < Re f z < 3/2`, `|f z|² < 25/4`,
  wedges `|arg (e^{-iθ₁} rotOne z)| < θ₁/2`, `|arg rotTwo z| < θ₂/2`;
and the main set is the open triangle together with the three patches. All pieces are open
(`isOpen_mainSet`), lie in `U`, each patch is stable under its reflection
(`refl_mem_patchZero`, ...), and a patch point outside the triangle reflects into the open
triangle (`refl_mem_intT_of_patchZero`, ...).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

variable (σ) in
def intT : Set ℂ := {z | ∀ i, 0 < σ.wallSide i z}

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

omit D in
theorem continuous_wallSide (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact continuous_im
  · change Continuous fun z : ℂ => (exp ((σ.θ₃ : ℂ) * I) * conj z).im
    fun_prop
  · change Continuous fun z : ℂ => (σ.rotTwo z).im
    unfold EuclidShape.rotTwo
    fun_prop

omit D in
theorem continuous_refl (i : Fin 3) : Continuous (σ.refl i) := by
  fin_cases i
  · exact continuous_conj
  · change Continuous fun z : ℂ => exp (2 * (σ.θ₃ : ℂ) * I) * conj z
    fun_prop
  · change Continuous fun z : ℂ =>
      σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo)
    fun_prop

omit D in
theorem continuous_rotOne : Continuous σ.rotOne := by
  unfold EuclidShape.rotOne
  fun_prop

omit D in
theorem continuous_rotTwo : Continuous σ.rotTwo := by
  unfold EuclidShape.rotTwo
  fun_prop

theorem isOpen_preimage_f (i : Fin 3) {S : Set ℂ} (hS : IsOpen S) :
    IsOpen {z | z ∈ D.V i ∧ D.f z ∈ S} := by
  have hc : ContinuousOn D.f (D.V i) :=
    D.contDiffOn_f.continuousOn.mono (D.V_subset_U i)
  exact hc.isOpen_inter_preimage (D.isOpen_V i) hS

theorem isOpen_disjWedge {g : ℂ → ℂ} (hg : Continuous g) (r a : ℝ) (ha : a ≤ Real.pi)
    {g' : ℂ → ℂ} (hg' : Continuous g') :
    IsOpen {z | r < ‖g z‖ ∨ g' z ∈ wedgeSet a} :=
  (isOpen_lt continuous_const (continuous_norm.comp hg)).union
    ((isOpen_wedgeSet ha).preimage hg')

omit D in
theorem θ_div_two_le_pi (θ : ℝ) (h0 : 0 < θ) (h : θ ≤ Real.pi / 2) : θ / 2 ≤ Real.pi := by
  linarith [Real.pi_pos]

omit D in
theorem isOpen_intT : IsOpen (intT σ) := by
  have : intT σ = ⋂ i, {z | 0 < σ.wallSide i z} := by ext z; simp [intT]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_wallSide i)

theorem isOpen_patchZero : IsOpen (patchZero D) := by
  have h1 := isOpen_preimage_f D 0 (isOpen_lt continuous_re continuous_const :
    IsOpen {u : ℂ | u.re < -(3 / 2)})
  have hw : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i z} := fun i =>
    isOpen_lt continuous_const (continuous_wallSide i)
  have hwr : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i (σ.refl 0 z)} := fun i =>
    isOpen_lt continuous_const ((continuous_wallSide i).comp (continuous_refl 0))
  have hd2 : IsOpen {z : ℂ | radTwo D < ‖σ.rotTwo z‖ ∨
      exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)} :=
    isOpen_disjWedge (continuous_rotTwo (σ := σ)) _ _ (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le)
      (continuous_const.mul (continuous_rotTwo (σ := σ)))
  have hd3 : IsOpen {z : ℂ | radThree D < ‖id z‖ ∨ id z ∈ wedgeSet (σ.θ₃ / 2)} :=
    isOpen_disjWedge continuous_id _ _ (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le) continuous_id
  have e : patchZero D = {z | z ∈ D.V 0 ∧ D.f z ∈ {u : ℂ | u.re < -(3 / 2)}} ∩
      {z | kap D < σ.wallSide 1 z} ∩ {z | kap D < σ.wallSide 2 z} ∩
      {z | kap D < σ.wallSide 1 (σ.refl 0 z)} ∩ {z | kap D < σ.wallSide 2 (σ.refl 0 z)} ∩
      {z | radTwo D < ‖σ.rotTwo z‖ ∨
        exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)} ∩
      {z | radThree D < ‖id z‖ ∨ id z ∈ wedgeSet (σ.θ₃ / 2)} := by
    ext z
    simp only [patchZero, mem_inter_iff, mem_ofPred_eq, id]
    tauto
  rw [e]
  exact ((((((h1.inter (hw 1)).inter (hw 2)).inter (hwr 1)).inter (hwr 2)).inter hd2).inter hd3)

theorem isOpen_patchOne : IsOpen (patchOne D) := by
  have h1 := isOpen_preimage_f D 1 (isOpen_lt continuous_const continuous_re :
    IsOpen {u : ℂ | 3 / 2 < u.re})
  have hw : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i z} := fun i =>
    isOpen_lt continuous_const (continuous_wallSide i)
  have hwr : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i (σ.refl 1 z)} := fun i =>
    isOpen_lt continuous_const ((continuous_wallSide i).comp (continuous_refl 1))
  have hd1 : IsOpen {z : ℂ | radOne D < ‖σ.rotOne z‖ ∨ σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} :=
    isOpen_disjWedge (continuous_rotOne (σ := σ)) _ _ (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le)
      (continuous_rotOne (σ := σ))
  have hd3 : IsOpen {z : ℂ | radThree D < ‖id z‖ ∨
      exp (-((σ.θ₃ : ℂ) * I)) * z ∈ wedgeSet (σ.θ₃ / 2)} :=
    isOpen_disjWedge continuous_id _ _ (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le)
      (continuous_const.mul continuous_id)
  have e : patchOne D = {z | z ∈ D.V 1 ∧ D.f z ∈ {u : ℂ | 3 / 2 < u.re}} ∩
      {z | kap D < σ.wallSide 0 z} ∩ {z | kap D < σ.wallSide 2 z} ∩
      {z | kap D < σ.wallSide 0 (σ.refl 1 z)} ∩ {z | kap D < σ.wallSide 2 (σ.refl 1 z)} ∩
      {z | radOne D < ‖σ.rotOne z‖ ∨ σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} ∩
      {z | radThree D < ‖id z‖ ∨ exp (-((σ.θ₃ : ℂ) * I)) * z ∈ wedgeSet (σ.θ₃ / 2)} := by
    ext z
    simp only [patchOne, mem_inter_iff, mem_ofPred_eq, id]
    tauto
  rw [e]
  exact ((((((h1.inter (hw 0)).inter (hw 2)).inter (hwr 0)).inter (hwr 2)).inter hd1).inter hd3)

theorem isOpen_patchTwo : IsOpen (patchTwo D) := by
  have h1 := isOpen_preimage_f D 2 ((isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_normSq continuous_const)) :
    IsOpen {u : ℂ | -(3 / 2) < u.re ∧ u.re < 3 / 2 ∧ normSq u < 25 / 4})
  have hw : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i z} := fun i =>
    isOpen_lt continuous_const (continuous_wallSide i)
  have hwr : ∀ i : Fin 3, IsOpen {z : ℂ | kap D < σ.wallSide i (σ.refl 2 z)} := fun i =>
    isOpen_lt continuous_const ((continuous_wallSide i).comp (continuous_refl 2))
  have hd1 : IsOpen {z : ℂ | radOne D < ‖σ.rotOne z‖ ∨
      exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} :=
    isOpen_disjWedge (continuous_rotOne (σ := σ)) _ _ (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le)
      (continuous_const.mul (continuous_rotOne (σ := σ)))
  have hd2 : IsOpen {z : ℂ | radTwo D < ‖σ.rotTwo z‖ ∨ σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)} :=
    isOpen_disjWedge (continuous_rotTwo (σ := σ)) _ _ (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le)
      (continuous_rotTwo (σ := σ))
  have e : patchTwo D = {z | z ∈ D.V 2 ∧ D.f z ∈
      {u : ℂ | -(3 / 2) < u.re ∧ u.re < 3 / 2 ∧ normSq u < 25 / 4}} ∩
      {z | kap D < σ.wallSide 0 z} ∩ {z | kap D < σ.wallSide 1 z} ∩
      {z | kap D < σ.wallSide 0 (σ.refl 2 z)} ∩ {z | kap D < σ.wallSide 1 (σ.refl 2 z)} ∩
      {z | radOne D < ‖σ.rotOne z‖ ∨
        exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z ∈ wedgeSet (σ.θ₁ / 2)} ∩
      {z | radTwo D < ‖σ.rotTwo z‖ ∨ σ.rotTwo z ∈ wedgeSet (σ.θ₂ / 2)} := by
    ext z
    simp only [patchTwo, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [e]
  exact ((((((h1.inter (hw 0)).inter (hw 1)).inter (hwr 0)).inter (hwr 1)).inter hd1).inter hd2)

theorem isOpen_mainSet : IsOpen (mainSet D) :=
  ((isOpen_intT.union (isOpen_patchZero D)).union (isOpen_patchOne D)).union (isOpen_patchTwo D)

end Continuity

section Basic

omit D in
theorem intT_subset_triangle : intT σ ⊆ σ.triangle := fun _ hz i => (hz i).le

omit D in
theorem ne_zero_of_mem_intT {z : ℂ} (hz : z ∈ intT σ) : z ≠ 0 := by
  rintro rfl
  have := hz 0
  rw [EuclidShape.wallSide_zero_zero] at this
  exact lt_irrefl _ this

theorem intT_subset_U : intT σ ⊆ D.U := fun _ hz =>
  triangle_diff_subset_U' D ⟨intT_subset_triangle hz, ne_zero_of_mem_intT hz⟩

theorem patchZero_subset_V : patchZero D ⊆ D.V 0 := fun _ hz => hz.1

theorem patchOne_subset_V : patchOne D ⊆ D.V 1 := fun _ hz => hz.1

theorem patchTwo_subset_V : patchTwo D ⊆ D.V 2 := fun _ hz => hz.1

theorem mainSet_subset_U : mainSet D ⊆ D.U := by
  rintro z (((h | h) | h) | h)
  · exact intT_subset_U D h
  · exact D.V_subset_U 0 h.1
  · exact D.V_subset_U 1 h.1
  · exact D.V_subset_U 2 h.1

theorem refl_mem_intT_of_patchZero {z : ℂ} (hz : z ∈ patchZero D) (hT : z ∉ σ.triangle) :
    σ.refl 0 z ∈ intT σ := by
  have hk := kap_pos D
  have h0 : σ.wallSide 0 z < 0 := by
    by_contra h
    apply hT
    intro i
    fin_cases i
    · exact le_of_not_gt h
    · exact (hk.trans hz.2.1).le
    · exact (hk.trans hz.2.2.1).le
  intro i
  fin_cases i
  · change 0 < σ.wallSide 0 (σ.refl 0 z)
    rw [σ.wallSide_refl]
    linarith
  · exact hk.trans hz.2.2.2.1
  · exact hk.trans hz.2.2.2.2.1

theorem refl_mem_intT_of_patchOne {z : ℂ} (hz : z ∈ patchOne D) (hT : z ∉ σ.triangle) :
    σ.refl 1 z ∈ intT σ := by
  have hk := kap_pos D
  have h1 : σ.wallSide 1 z < 0 := by
    by_contra h
    apply hT
    intro i
    fin_cases i
    · exact (hk.trans hz.2.1).le
    · exact le_of_not_gt h
    · exact (hk.trans hz.2.2.1).le
  intro i
  fin_cases i
  · exact hk.trans hz.2.2.2.1
  · change 0 < σ.wallSide 1 (σ.refl 1 z)
    rw [σ.wallSide_refl]
    linarith
  · exact hk.trans hz.2.2.2.2.1

theorem refl_mem_intT_of_patchTwo {z : ℂ} (hz : z ∈ patchTwo D) (hT : z ∉ σ.triangle) :
    σ.refl 2 z ∈ intT σ := by
  have hk := kap_pos D
  have h2 : σ.wallSide 2 z < 0 := by
    by_contra h
    apply hT
    intro i
    fin_cases i
    · exact (hk.trans hz.2.1).le
    · exact (hk.trans hz.2.2.1).le
    · exact le_of_not_gt h
  intro i
  fin_cases i
  · exact hk.trans hz.2.2.2.1
  · exact hk.trans hz.2.2.2.2.1
  · change 0 < σ.wallSide 2 (σ.refl 2 z)
    rw [σ.wallSide_refl]
    linarith

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

theorem refl_mem_patchZero {z : ℂ} (hz : z ∈ patchZero D) : σ.refl 0 z ∈ patchZero D := by
  obtain ⟨hV, h1, h2, h3, h4, hf, hw2, hw3⟩ := hz
  have hrr : σ.refl 0 (σ.refl 0 z) = z := σ.refl_refl 0 z
  refine ⟨refl_mapsTo_V' D 0 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_⟩
  · rw [f_refl' D 0 hV, conj_re]; exact hf
  · rcases hw2 with h | h
    · left
      rw [σ.rotTwo_refl_zero, norm_mul, Complex.norm_conj]
      rw [show 2 * (σ.θ₂ : ℂ) * I = ((2 * σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
        EuclidShape.norm_exp_mul_I, one_mul]
      exact h
    · right
      have e : exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo (σ.refl 0 z) =
          conj (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z) := by
        rw [σ.rotTwo_refl_zero, map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
        congr 2
        simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [e]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le) h
  · rcases hw3 with h | h
    · left
      change radThree D < ‖conj z‖
      rwa [Complex.norm_conj]
    · right
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le) h

theorem refl_mem_patchOne {z : ℂ} (hz : z ∈ patchOne D) : σ.refl 1 z ∈ patchOne D := by
  obtain ⟨hV, h1, h2, h3, h4, hf, hw1, hw3⟩ := hz
  have hrr : σ.refl 1 (σ.refl 1 z) = z := σ.refl_refl 1 z
  refine ⟨refl_mapsTo_V' D 1 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_⟩
  · rw [f_refl' D 1 hV, conj_re]; exact hf
  · rcases hw1 with h | h
    · left
      rwa [σ.rotOne_refl_one, Complex.norm_conj]
    · right
      rw [σ.rotOne_refl_one]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le) h
  · have e : exp (-((σ.θ₃ : ℂ) * I)) * σ.refl 1 z = conj (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
      change exp (-((σ.θ₃ : ℂ) * I)) * (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
      rw [map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rcases hw3 with h | h
    · left
      change radThree D < ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖
      rw [norm_mul, Complex.norm_conj,
        show 2 * (σ.θ₃ : ℂ) * I = ((2 * σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
        EuclidShape.norm_exp_mul_I, one_mul]
      exact h
    · right
      rw [e]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₃_pos σ.θ₃_le) h

theorem refl_mem_patchTwo {z : ℂ} (hz : z ∈ patchTwo D) : σ.refl 2 z ∈ patchTwo D := by
  obtain ⟨hV, h1, h2, h3, h4, hf1, hf2, hf3, hw1, hw2⟩ := hz
  have hrr : σ.refl 2 (σ.refl 2 z) = z := σ.refl_refl 2 z
  have hfr : D.f (σ.refl 2 z) = conj (D.f z) := f_refl' D 2 hV
  refine ⟨refl_mapsTo_V' D 2 hV, h3, h4, by rwa [hrr], by rwa [hrr], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr, conj_re]; exact hf1
  · rw [hfr, conj_re]; exact hf2
  · rw [hfr, normSq_conj]; exact hf3
  · have e : exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne (σ.refl 2 z) =
        conj (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) := by
      rw [σ.rotOne_refl_two, map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rcases hw1 with h | h
    · left
      rw [σ.rotOne_refl_two, norm_mul, Complex.norm_conj,
        show 2 * (σ.θ₁ : ℂ) * I = ((2 * σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring,
        EuclidShape.norm_exp_mul_I, one_mul]
      exact h
    · right
      rw [e]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₁_pos σ.θ₁_le) h
  · rcases hw2 with h | h
    · left
      rwa [σ.rotTwo_refl_two, Complex.norm_conj]
    · right
      rw [σ.rotTwo_refl_two]
      exact conj_mem_wedgeSet (θ_div_two_le_pi _ σ.θ₂_pos σ.θ₂_le) h

end Basic

end ClosedTriangle

end GC.Seifert
