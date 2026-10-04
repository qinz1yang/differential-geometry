import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldApex
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOuterProfile

/-!
# The frozen output of the cone-fold packet (interface of tiers T3 and T5)

`ConeShape.FoldData σ` packages the two-dimensional reflection fold of the triangle
`σ.triangle` onto `σ.basePlus`, the upper half of the base of the filled block: an open
`U ⊇ σ.triangle` inside the upper half-plane, a map `f` smooth on `U` with positive Jacobian off
the apices, reflection-stable open neighbourhoods `V i` of the walls on which `f ∘ σ.refl i =
conj ∘ f`, the bijection `σ.triangle → σ.basePlus`, the branched apex germs `coneApexOne` and
`coneApexTwo`, and the cusp control used by the descent: the modulus `‖f z‖` equals the outer
profile `outerProfile σ.constK Y₁ Y₂ (Im z)` high in the cusp `∞`, and `‖f z + 3/2‖` equals
`coneProfile σ.constK (cuspZeroHeight z)` deep in the cusp at `0` (one-cone shapes). The walls
are `foldWall i = {z ∈ σ.triangle | σ.wallSide i z = 0}`. Consequences recorded here: the walls
map into the real axis, every real value of `basePlus` is attained only on a wall, and
`√σ.constK ≤ 1/2`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open scoped ContDiff ComplexConjugate

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def foldWall (i : Fin 3) : Set ℂ := {z | z ∈ σ.triangle ∧ σ.wallSide i z = 0}

def basePlus : Set ℂ :=
  {u | ‖u‖ < 3 ∧ 0 ≤ u.im ∧ (σ.θ₂ = 0 → 1 / 2 < ‖u + 3 / 2‖)}

structure FoldData where
  U : Set ℂ
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  im_pos_of_mem_U : ∀ z ∈ U, 0 < z.im
  triangle_subset_U : σ.triangle ⊆ U
  contDiffOn_f : ContDiffOn ℝ ∞ f U
  det_fderiv_pos : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ f z).det
  V : Fin 3 → Set ℂ
  isOpen_V : ∀ i, IsOpen (V i)
  V_subset_U : ∀ i, V i ⊆ U
  foldWall_subset_V : ∀ i, σ.foldWall i ⊆ V i
  refl_mapsTo_V : ∀ i, MapsTo (σ.refl i) (V i) (V i)
  f_refl : ∀ i, ∀ z ∈ V i, f (σ.refl i z) = conj (f z)
  bijOn_f : BijOn f σ.triangle σ.basePlus
  f_apexOne : ∀ p : ℕ, σ.θ₁ * p = Real.pi → ∀ᶠ z in 𝓝 σ.vertexOne, f z = σ.coneApexOne p z
  f_apexTwo : ∀ q : ℕ, σ.θ₂ * q = Real.pi → ∀ᶠ z in 𝓝 σ.vertexTwo, f z = σ.coneApexTwo q z
  outerY₁ : ℝ
  outerY₂ : ℝ
  outerY₁_pos : 0 < outerY₁
  outerY₁_lt : outerY₁ < outerY₂
  outerY₂_lt : outerY₂ < Real.sqrt σ.constK
  cuspInfHeight : ℝ
  norm_f_cuspInf : ∀ z ∈ U, cuspInfHeight < z.im →
    ‖f z‖ = outerProfile σ.constK outerY₁ outerY₂ z.im
  cuspZeroBound : ℝ
  cuspZeroBound_pos : 0 < cuspZeroBound
  norm_f_cuspZero : σ.θ₂ = 0 → ∀ z ∈ U, cuspZeroHeight z < cuspZeroBound →
    ‖f z + 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z)

theorem sqrt_constK_le : Real.sqrt σ.constK ≤ 1 / 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have h1 := Real.cos_le_one σ.θ₁
  have h2 := Real.cos_le_one σ.θ₂
  have h3 := σ.cos_θ₁_nonneg
  have h4 := σ.cos_θ₂_nonneg
  unfold constK
  nlinarith [mul_le_mul (by linarith : 1 + Real.cos σ.θ₁ ≤ 2) (by linarith : 1 + Real.cos σ.θ₂ ≤ 2)
    (by linarith) (by norm_num)]

theorem foldWall_subset_triangle (i : Fin 3) : σ.foldWall i ⊆ σ.triangle := fun _ hz => hz.1

theorem refl_eq_self_of_mem_foldWall {i : Fin 3} {z : ℂ} (hz : z ∈ σ.foldWall i) :
    σ.refl i z = z :=
  σ.refl_of_wallSide_eq_zero hz.1.1 hz.2

theorem mem_triangle_iff {z : ℂ} : z ∈ σ.triangle ↔ 0 < z.im ∧ ∀ i, 0 ≤ σ.wallSide i z :=
  Iff.rfl

theorem interior_mem_of_wallSide_pos {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) : σ.triangle ∈ 𝓝 z := by
  have hc : ∀ i, Continuous (σ.wallSide i) := by
    intro i
    fin_cases i
    · exact continuous_re
    · exact continuous_const.sub continuous_re
    · change Continuous fun z : ℂ => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16
      fun_prop
  have h0 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz.1
  have h1 : {w : ℂ | ∀ i, 0 < σ.wallSide i w} ∈ 𝓝 z := by
    have : {w : ℂ | ∀ i, 0 < σ.wallSide i w} = ⋂ i, {w | 0 < σ.wallSide i w} := by
      ext w
      simp
    rw [this]
    exact (Filter.iInter_mem).2 fun i => (isOpen_lt continuous_const (hc i)).mem_nhds (hpos i)
  filter_upwards [h0, h1] with w hw0 hw1
  exact ⟨hw0, fun i => (hw1 i).le⟩

namespace FoldData

variable {σ}
variable (D : σ.FoldData)

theorem im_pos_of_mem_V {i : Fin 3} {z : ℂ} (hz : z ∈ D.V i) : 0 < z.im :=
  D.im_pos_of_mem_U z (D.V_subset_U i hz)

theorem f_refl' {i : Fin 3} {z : ℂ} (hz : z ∈ D.V i) : D.f z = conj (D.f (σ.refl i z)) := by
  have h := D.f_refl i (σ.refl i z) (D.refl_mapsTo_V i hz)
  rw [σ.refl_refl (D.im_pos_of_mem_V hz) i] at h
  exact h

theorem f_real_of_mem_foldWall {i : Fin 3} {z : ℂ} (hz : z ∈ σ.foldWall i) :
    (D.f z).im = 0 := by
  have h := D.f_refl i z (D.foldWall_subset_V i hz)
  rw [σ.refl_eq_self_of_mem_foldWall hz] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

end FoldData

end ConeShape

end GC.Seifert
