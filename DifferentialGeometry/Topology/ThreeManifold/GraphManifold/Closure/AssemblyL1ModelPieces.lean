import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelCharts

/-!
# Chapter-14 assembly, item L1, group G3a: the pieces of the model cycle

The pieces of the model cycle of combinatorial length `len` at scale `ε`: the ball `k` is the
model ball centred at height `4k`, the handle `k` and the necks `(k, b)` are the zone map of base
`4k` (the neck `(k, true)` read through the flip `(z, τ) ↦ (z, 1 - τ)`), all followed by the model
map into `S³`. This file records where the pieces sit: their heights modulo the period `4 len`
(`zoneSphere_eq_ballSphere`, …), their radii, and the window lemma `eq_of_window` identifying
the indices of two pieces meeting in `S³`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

variable {ε : ℝ}

/-! ## Indices and windows -/

/-- The base height of the zone `k` (and the centre of the ball `k`). -/
def modelBase {len : ℕ} (k : Fin len) : ℝ := 4 * (k : ℕ)

/-- **Window lemma.** Two heights `4a + x` and `4b + y` congruent modulo `4 len` with
`|x - y| < 4` have `a = b` modulo `len`. -/
theorem eq_of_window {len : ℕ} {a b m : ℤ} {x y : ℝ}
    (h : 4 * (a : ℝ) + x = 4 * b + y + 4 * len * m) (hxy : |x - y| < 4) : a = b + len * m := by
  have h1 : (4 : ℝ) * ((a - b - len * m : ℤ) : ℝ) = y - x := by
    push_cast
    linarith
  have h2 : |((a - b - len * m : ℤ) : ℝ)| < 1 := by
    have : |(4 : ℝ) * ((a - b - len * m : ℤ) : ℝ)| < 4 := by
      rw [h1, abs_sub_comm]
      exact hxy
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
    linarith
  have h3 : |a - b - len * m| < 1 := by exact_mod_cast h2
  have := Int.abs_lt_one_iff.mp h3
  linarith

theorem fin_eq_of_int_eq {len : ℕ} {j k : Fin len} {m : ℤ}
    (h : ((j : ℕ) : ℤ) = (k : ℕ) + len * m) : j = k := by
  have hj := j.2
  have hk := k.2
  have hm : m = 0 := by
    by_contra hm0
    rcases lt_or_gt_of_ne hm0 with hlt | hgt
    · have : (len : ℤ) * m ≤ -len := by nlinarith
      omega
    · have : (len : ℤ) ≤ len * m := by nlinarith
      omega
  subst hm
  apply Fin.ext
  omega

/-- The successor index modulo `len`. -/
theorem finRotate_eq_add_one {len : ℕ} (k : Fin len) :
    ∃ m : ℤ, (((finRotate len k : Fin len) : ℕ) : ℤ) = (k : ℕ) + 1 + len * m := by
  obtain ⟨n, rfl⟩ : ∃ n, len = n + 1 := ⟨len - 1, by have := k.2; omega⟩
  by_cases hk : k = Fin.last n
  · subst hk
    refine ⟨-1, ?_⟩
    rw [finRotate_last]
    simp
  · refine ⟨0, ?_⟩
    rw [coe_finRotate_of_ne_last hk]
    simp

theorem eq_finRotate_of_int_eq {len : ℕ} {j k : Fin len} {m : ℤ}
    (h : ((j : ℕ) : ℤ) = (k : ℕ) + 1 + len * m) : j = finRotate len k := by
  obtain ⟨m', hm'⟩ := finRotate_eq_add_one k
  apply fin_eq_of_int_eq (m := m - m')
  rw [h, hm']
  ring

/-! ## The flip -/

/-- The flip `(z, τ) ↦ (z, 1 - τ)` of the model space. -/
def modelFlip : ModelSpace ≃ₘ^∞⟮𝓘(ℝ, ModelSpace), 𝓘(ℝ, ModelSpace)⟯ ModelSpace where
  toFun y := (y.1, 1 - y.2)
  invFun y := (y.1, 1 - y.2)
  left_inv y := by simp
  right_inv y := by simp
  contMDiff_toFun := (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)).contMDiff

theorem modelFlip_apply (y : ModelSpace) : modelFlip y = (y.1, 1 - y.2) := rfl

/-- The identity of the model space as a diffeomorphism. -/
abbrev modelId : ModelSpace ≃ₘ^∞⟮𝓘(ℝ, ModelSpace), 𝓘(ℝ, ModelSpace)⟯ ModelSpace :=
  Diffeomorph.refl 𝓘(ℝ, ModelSpace) ModelSpace ∞

/-- The neck reparametrization of the end `b`. -/
def neckFlip (b : Bool) : ModelSpace ≃ₘ^∞⟮𝓘(ℝ, ModelSpace), 𝓘(ℝ, ModelSpace)⟯ ModelSpace :=
  if b then modelFlip else modelId

theorem neckFlip_false (y : ModelSpace) : neckFlip false y = y := rfl

theorem neckFlip_true (y : ModelSpace) : neckFlip true y = (y.1, 1 - y.2) := rfl

theorem neckFlip_mapsTo (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (b : Bool) :
    MapsTo (neckFlip b) (neckDomain ε) zoneDomain := by
  intro q hq
  obtain ⟨h1, h2⟩ := hq
  have h2' := abs_lt.mp h2
  cases b
  · rw [neckFlip_false]
    exact ⟨by linarith, by linarith, by linarith⟩
  · rw [neckFlip_true]
    change ‖q.1‖ < 13 / 10 ∧ -1 / 4 < 1 - q.2 ∧ 1 - q.2 < 5 / 4
    exact ⟨by linarith, by linarith, by linarith⟩

theorem isOpen_modelNeckDomain (ε : ℝ) : IsOpen (neckDomain ε) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

/-! ## Heights and radii of the necks -/

theorem capCos_neck_bounds {s : ℝ} (hs : 0 ≤ s) (hs' : s < 5 / 4) :
    39 / 89 < capCos s ∧ capCos s ≤ 1 := by
  refine ⟨?_, capCos_le_one s⟩
  have h := capCos_lt_capCos hs hs'
  have h2 : capCos (5 / 4) = 39 / 89 := by norm_num [capCos]
  linarith

/-- The neck `(k, b)` in the model space. -/
theorem zoneChartMap_neckFlip (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (b : Bool) {q : ModelSpace}
    (hq : q ∈ neckDomain ε) :
    zoneChartMap ε c (neckFlip b q) = (neckRatio ε ‖q.1‖ q.2 • q.1,
      if b then c + 4 - (1 + q.2) * capCos ‖q.1‖ else c + (1 + q.2) * capCos ‖q.1‖) := by
  obtain ⟨h1, h2⟩ := hq
  have h2' := abs_lt.mp h2
  cases b
  · rw [neckFlip_false, zoneChartMap_neck hε hε' c (by linarith) (by linarith) (by linarith)]
    rfl
  · rw [neckFlip_true, zoneChartMap_neck_flip hε hε' c (by linarith) (by linarith) (by linarith)]
    rfl

theorem norm_neckRatio_smul (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {z : ModelPlane} {τ : ℝ}
    (hτ : |τ| < 2 * ε) : ‖neckRatio ε ‖z‖ τ • z‖ = neckRadius ε ‖z‖ τ := by
  have hτ' := abs_lt.mp hτ
  have hpos := neckRatio_pos hε hε' (s := ‖z‖) (τ := τ) (by linarith)
  rw [norm_smul, Real.norm_of_nonneg hpos.le]
  by_cases hz : z = 0
  · rw [hz, norm_zero, mul_zero, neckRadius_eq_left hε (by linarith)]
  · rw [neckRatio_mul (norm_ne_zero_iff.mpr hz)]

theorem neck_height_mem (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {q : ModelSpace} (hq : q ∈ neckDomain ε) :
    8 / 25 < (1 + q.2) * capCos ‖q.1‖ ∧ (1 + q.2) * capCos ‖q.1‖ < 5 / 4 := by
  obtain ⟨h1, h2⟩ := hq
  have h2' := abs_lt.mp h2
  have hc := capCos_neck_bounds (norm_nonneg q.1) (by linarith)
  constructor <;> nlinarith

end GC.GraphManifold.Assembly
