import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# S-W-STAB-2 G2a：三维定向空间里 "正向单位法向" 的唯一性与存在性（纯线性代数）

`T` 三维实向量空间，`B` 正定对称双线性型（取 `g_x`），`a, b` 线性无关，`o` 一个定向。
`n` 是 `B`-单位法向（`B n a = B n b = 0`，`B n n = 1`）。则

* `![a, b, n]` 线性无关（`linearIndependent_frame_WS2`）；
* 单位法向恰为 `±n`（`unit_normal_eq_pm_WS2`）；
* `![a, b, -n]` 的定向 = `-![a, b, n]` 的定向，所以 `n` 与 `-n` 中恰一个与 `o` 同向
  （`posNormal_or_neg_WS2`、`posNormal_unique_WS2`）。
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry

section Linear

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

theorem linearIndependent_frame_WS2 (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ) {a b n : T}
    (hab : LinearIndependent ℝ ![a, b]) (hna : B n a = 0) (hnb : B n b = 0)
    (hnn : B n n = 1) : LinearIndependent ℝ ![a, b, n] := by
  rw [Fintype.linearIndependent_iff] at hab ⊢
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hg
  have h2 : g 2 = 0 := by
    have h := congrArg (B n) hg
    simpa [map_add, map_smul, hna, hnb, hnn] using h
  rw [h2, zero_smul, add_zero] at hg
  have h01 := hab (fun i => g (Fin.castSucc i)) (by
    rw [Fin.sum_univ_two]
    simpa using hg)
  intro i
  fin_cases i
  · exact h01 0
  · exact h01 1
  · exact h2

/-- 三个线性无关向量（`finrank = 3`）给出的基。 -/
def frameBasis_WS2 (hdim : Module.finrank ℝ T = 3) {a b n : T}
    (h : LinearIndependent ℝ ![a, b, n]) : Module.Basis (Fin 3) ℝ T :=
  basisOfLinearIndependentOfCardEqFinrank h (by rw [Fintype.card_fin, hdim])

theorem frameBasis_apply_WS2 (hdim : Module.finrank ℝ T = 3) {a b n : T}
    (h : LinearIndependent ℝ ![a, b, n]) (i : Fin 3) :
    frameBasis_WS2 hdim h i = ![a, b, n] i := by
  simp [frameBasis_WS2]

/-- 单位法向只有 `±n`。 -/
theorem unit_normal_eq_pm_WS2 (hdim : Module.finrank ℝ T = 3) (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u, u ≠ 0 → 0 < B u u) {a b n n' : T}
    (hab : LinearIndependent ℝ ![a, b]) (hna : B n a = 0) (hnb : B n b = 0)
    (hnn : B n n = 1) (hna' : B n' a = 0) (hnb' : B n' b = 0) (hnn' : B n' n' = 1) :
    n' = n ∨ n' = -n := by
  have hfr := linearIndependent_frame_WS2 B hab hna hnb hnn
  let bs := frameBasis_WS2 hdim hfr
  have hrepr : n' = bs.repr n' 0 • a + bs.repr n' 1 • b + bs.repr n' 2 • n := by
    have h := bs.sum_repr n'
    rw [Fin.sum_univ_three] at h
    simpa [bs, frameBasis_apply_WS2] using h.symm
  set g0 := bs.repr n' 0
  set g1 := bs.repr n' 1
  set g2 := bs.repr n' 2
  set p : T := g0 • a + g1 • b with hpdef
  have hpp : B p p = 0 := by
    have h1 : B p n' = 0 := by
      simp [hpdef, map_add, map_smul, hs a n', hs b n', hna', hnb']
    have h2 : B p n = 0 := by
      simp [hpdef, map_add, map_smul, hs a n, hs b n, hna, hnb]
    have h3 : p = n' - g2 • n := by
      rw [eq_sub_iff_add_eq]
      exact hrepr.symm
    calc B p p = B p (n' - g2 • n) := by rw [← h3]
      _ = B p n' - g2 * B p n := by rw [map_sub, map_smul]; rfl
      _ = 0 := by rw [h1, h2]; ring
  have hp0 : p = 0 := by
    by_contra hne
    have := hp p hne
    linarith
  have hn'eq : n' = g2 • n := by
    rw [hrepr, hp0, zero_add]
  have hg2 : g2 * g2 = 1 := by
    have h := hnn'
    rw [hn'eq] at h
    simpa [map_smul, hnn, mul_comm] using h
  rcases mul_self_eq_one_iff.mp hg2 with h | h
  · left
    rw [hn'eq, h, one_smul]
  · right
    rw [hn'eq, h, neg_one_smul]

/-- `![a, b, -n]` 的基的定向是 `![a, b, n]` 的基的定向的相反。 -/
theorem frameBasis_neg_orientation_WS2 (hdim : Module.finrank ℝ T = 3) {a b n : T}
    (h : LinearIndependent ℝ ![a, b, n]) (h' : LinearIndependent ℝ ![a, b, -n]) :
    (frameBasis_WS2 hdim h').orientation = -(frameBasis_WS2 hdim h).orientation := by
  rw [← Module.Basis.orientation_neg_single (frameBasis_WS2 hdim h) 2]
  congr 1
  apply Module.Basis.eq_of_apply_eq
  intro i
  rw [frameBasis_apply_WS2]
  fin_cases i
  · simp [Module.Basis.unitsSMul_apply, frameBasis_apply_WS2]
  · simp [Module.Basis.unitsSMul_apply, frameBasis_apply_WS2]
  · simp [Module.Basis.unitsSMul_apply, frameBasis_apply_WS2]

/-- 与 `o` 同向：`![a, b, m]` 线性无关且其基的定向等于 `o`。 -/
theorem posNormal_or_neg_WS2 (hdim : Module.finrank ℝ T = 3) (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (o : Orientation ℝ T (Fin 3)) {a b n : T}
    (hab : LinearIndependent ℝ ![a, b]) (hna : B n a = 0) (hnb : B n b = 0)
    (hnn : B n n = 1) :
    (∃ h : LinearIndependent ℝ ![a, b, n], (frameBasis_WS2 hdim h).orientation = o) ∨
      ∃ h : LinearIndependent ℝ ![a, b, -n], (frameBasis_WS2 hdim h).orientation = o := by
  have hfr := linearIndependent_frame_WS2 B hab hna hnb hnn
  have hfr' := linearIndependent_frame_WS2 B hab (n := -n) (by simp [hna]) (by simp [hnb])
    (by simp [hnn])
  rcases (frameBasis_WS2 hdim hfr).orientation_eq_or_eq_neg o with h | h
  · exact Or.inl ⟨hfr, h.symm⟩
  · refine Or.inr ⟨hfr', ?_⟩
    rw [frameBasis_neg_orientation_WS2 hdim hfr hfr', h]

/-- 与 `o` 同向的单位法向至多一个。 -/
theorem posNormal_unique_WS2 (hdim : Module.finrank ℝ T = 3) (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u, u ≠ 0 → 0 < B u u)
    (o : Orientation ℝ T (Fin 3)) {a b n n' : T}
    (hab : LinearIndependent ℝ ![a, b]) (hna : B n a = 0) (hnb : B n b = 0)
    (hnn : B n n = 1) (hna' : B n' a = 0) (hnb' : B n' b = 0) (hnn' : B n' n' = 1)
    (hpos : ∃ h : LinearIndependent ℝ ![a, b, n], (frameBasis_WS2 hdim h).orientation = o)
    (hpos' : ∃ h : LinearIndependent ℝ ![a, b, n'], (frameBasis_WS2 hdim h).orientation = o) :
    n' = n := by
  rcases unit_normal_eq_pm_WS2 hdim B hs hp hab hna hnb hnn hna' hnb' hnn' with h | h
  · exact h
  · exfalso
    obtain ⟨h1, e1⟩ := hpos
    obtain ⟨h2, e2⟩ := hpos'
    subst h
    have := frameBasis_neg_orientation_WS2 hdim h1 h2
    rw [e1, e2] at this
    exact Module.Ray.ne_neg_self _ this

end Linear

end DifferentialGeometry.Geometry
