import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveRelative

/-!
# Torus curves: the first circle inside the cut annulus

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme, stage (ii)
(review 12, §4.2). Let `φ` have matrix `1` and let `φ (α)` miss the level `α_s`, so that in the
lift `γ t = Φ (t, 0)` the height `ζ = γ.2` stays in an open interval `(b, b + 1)`.

Order argument in the lift. Cut along a regular vertical circle `β_θ`. The horizontal coordinate
`ξ = γ.1` satisfies `ξ (t + 1) = ξ t + 1`. Without same-side arcs (consecutive crossings of the
same vertical line) all crossings have the same sign, and `ξ (t + 1) = ξ t + 1` forces exactly one
crossing `t₀` per period, upward, with `ξ ∈ (θ', θ' + 1)` on `(t₀, t₀ + 1)`
(`exists_unique_cross_of_add_one`): the finite cut-arc model consists of the single arc
`γ [t₀, t₀ + 1]`, whose two ends are the two copies of the crossing point, and connectedness of
the curve is built into the lift parametrisation.

Straightening. A periodic reparametrisation `X` of the horizontal coordinate agrees with
`ξ (t₀ + ·)` near the integers and is strictly increasing (`exists_reparam_of_cross`: the
interpolation with the line `θ' + 1/4 + v/2` is monotone because the line lies above `ξ` where
the cutoff rises and below it where the second cutoff rises). The curved square chart
`M (u + i v) = (X v, sqShift b (ζ (t₀ + v)) u)` sends the vertical middle line onto
`v ↦ (X v, ζ (t₀ + v))`, which is `γ (t₀ + v)` near both ends, so the cut arc read in the chart
is the standard segment near its ends. The square-arc isotopy of MC3 moves the graph
`{(X v, ζ (t₀ + v))}` onto `φ (α)`, and the vertical shear `(x, y) ↦ (x, y - ζ (t₀ + X⁻¹ x))`,
isotopic to the identity, moves the graph onto `α`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem monotone_cutoff {s₁ s₂ : ℝ} (hs : s₁ < s₂) : Monotone (cutoff s₁ s₂) := by
  intro x y hxy
  unfold cutoff
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem deriv_cutoff_eq_zero_of_lt {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : r < s₁) :
    deriv (cutoff s₁ s₂) r = 0 := by
  have he : cutoff s₁ s₂ =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact cutoff_of_le hs (le_of_lt hx)
  rw [he.deriv_eq, deriv_const]

theorem deriv_cutoff_eq_zero_of_gt {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : s₂ < r) :
    deriv (cutoff s₁ s₂) r = 0 := by
  have he : cutoff s₁ s₂ =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact cutoff_of_ge hs (le_of_lt hx)
  rw [he.deriv_eq, deriv_const]

def crossCorr (ξ : ℝ → ℝ) (t₀ η u : ℝ) : ℝ :=
  cutoff η (2 * η) u * (1 - cutoff (1 - 2 * η) (1 - η) u) * (ξ t₀ + 1 / 4 + u / 2 - ξ (t₀ + u))

def crossReparam (ξ : ℝ → ℝ) (t₀ η v : ℝ) : ℝ := ξ (t₀ + v) + crossCorr ξ t₀ η (v - ⌊v⌋)

section Reparam

variable {ξ : ℝ → ℝ} {t₀ η : ℝ}

theorem contDiff_crossCorr (hξ : ContDiff ℝ ∞ ξ) : ContDiff ℝ ∞ (crossCorr ξ t₀ η) :=
  ((contDiff_cutoff _ _).mul (contDiff_const.sub (contDiff_cutoff _ _))).mul
    ((contDiff_const.add (contDiff_id.div_const _)).sub
      (hξ.comp (contDiff_const.add contDiff_id)))

theorem crossCorr_of_le (hη : 0 < η) {u : ℝ} (hu : u ≤ η) : crossCorr ξ t₀ η u = 0 := by
  rw [crossCorr, cutoff_of_le (by linarith) hu, zero_mul, zero_mul]

theorem crossCorr_of_ge (hη : 0 < η) {u : ℝ} (hu : 1 - η ≤ u) : crossCorr ξ t₀ η u = 0 := by
  rw [crossCorr, cutoff_of_ge (by linarith) hu, sub_self, mul_zero, zero_mul]

theorem crossReparam_eq_local (hη : 0 < η) (n : ℤ) {v : ℝ}
    (hv : v ∈ Ioo ((n : ℝ) - 1) (n + 1)) :
    crossReparam ξ t₀ η v =
      ξ (t₀ + v) + (crossCorr ξ t₀ η (v - n) + crossCorr ξ t₀ η (v - n + 1)) := by
  rw [crossReparam]
  congr 1
  rcases lt_or_ge v n with hlt | hge
  · have hf : ⌊v⌋ = n - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hv.1]
    rw [hf, crossCorr_of_le hη (u := v - n) (by linarith)]
    push_cast
    ring_nf
  · have hf : ⌊v⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [hv.2]
    rw [hf, crossCorr_of_ge hη (u := v - n + 1) (by linarith)]
    ring

theorem contDiff_crossReparam (hξ : ContDiff ℝ ∞ ξ) (hη : 0 < η) (hη1 : η < 1 / 2) :
    ContDiff ℝ ∞ (crossReparam ξ t₀ η) := by
  refine contDiff_iff_contDiffAt.mpr fun v => ?_
  have hv : v ∈ Ioo ((⌊v⌋ : ℝ) - 1) (⌊v⌋ + 1) :=
    ⟨by linarith [Int.floor_le v], Int.lt_floor_add_one v⟩
  have hsm : ContDiff ℝ ∞ (fun w => ξ (t₀ + w) +
      (crossCorr ξ t₀ η (w - ⌊v⌋) + crossCorr ξ t₀ η (w - ⌊v⌋ + 1))) :=
    (hξ.comp (contDiff_const.add contDiff_id)).add
      (((contDiff_crossCorr hξ).comp (contDiff_id.sub contDiff_const)).add
        ((contDiff_crossCorr hξ).comp ((contDiff_id.sub contDiff_const).add contDiff_const)))
  refine hsm.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
  exact crossReparam_eq_local hη ⌊v⌋ hw

theorem crossReparam_sub_one (hper : ∀ t, ξ (t + 1) = ξ t + 1) (v : ℝ) :
    crossReparam ξ t₀ η v = crossReparam ξ t₀ η (v - 1) + 1 := by
  rw [crossReparam, crossReparam]
  have hf : ⌊v - 1⌋ = ⌊v⌋ - 1 := by
    rw [show v - 1 = v + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.floor_add_intCast]
    ring
  rw [hf, show t₀ + v = t₀ + (v - 1) + 1 by ring, hper]
  push_cast
  ring_nf

theorem crossReparam_add_one (hper : ∀ t, ξ (t + 1) = ξ t + 1) (v : ℝ) :
    crossReparam ξ t₀ η (v + 1) = crossReparam ξ t₀ η v + 1 := by
  rw [crossReparam_sub_one hper (v + 1), add_sub_cancel_right]

theorem crossReparam_sub_int (hper : ∀ t, ξ (t + 1) = ξ t + 1) (n : ℤ) (v : ℝ) :
    crossReparam ξ t₀ η v = crossReparam ξ t₀ η (v - n) + n := by
  have hnat : ∀ (k : ℕ) (w : ℝ), crossReparam ξ t₀ η w = crossReparam ξ t₀ η (w - k) + k := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [ih w, crossReparam_sub_one hper (w - k)]
      push_cast
      ring_nf
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast hnat k v
  · have := hnat k (v + k)
    push_cast
    rw [sub_neg_eq_add]
    rw [add_sub_cancel_right] at this
    linarith

theorem crossReparam_eq_near (hη : 0 < η) (hη1 : η < 1 / 2) {v : ℝ} (hv : v ∈ Ioo (-η) η) :
    crossReparam ξ t₀ η v = ξ (t₀ + v) := by
  rw [crossReparam_eq_local hη 0 ⟨by push_cast; linarith [hv.1], by push_cast; linarith [hv.2]⟩]
  push_cast
  rw [sub_zero, crossCorr_of_ge hη (u := v + 1) (by linarith [hv.1]),
    crossCorr_of_le hη (u := v) (by linarith [hv.2])]
  ring

theorem deriv_crossReparam_pos_of_mem (hξ : ContDiff ℝ ∞ ξ) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hnear : ∀ u ∈ Icc 0 (2 * η), ξ (t₀ + u) ≤ ξ t₀ + 1 / 4 ∧ 0 < deriv ξ (t₀ + u))
    (hfar : ∀ u ∈ Icc (1 - 2 * η) 1, ξ t₀ + 3 / 4 ≤ ξ (t₀ + u) ∧ 0 < deriv ξ (t₀ + u))
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : 0 < deriv (crossReparam ξ t₀ η) u := by
  have h12 : η < 2 * η := by linarith
  have h12' : 1 - 2 * η < 1 - η := by linarith
  have he : crossReparam ξ t₀ η =ᶠ[𝓝 u] fun v => ξ (t₀ + v) + crossCorr ξ t₀ η v := by
    have hu' : u ∈ Ioo (-η) 1 := ⟨by linarith [hu.1], hu.2⟩
    filter_upwards [isOpen_Ioo.mem_nhds hu'] with v hv
    rw [crossReparam_eq_local hη 0
      ⟨by push_cast; linarith [hv.1], by push_cast; linarith [hv.2]⟩]
    push_cast
    rw [sub_zero, crossCorr_of_ge hη (u := v + 1) (by linarith [hv.1])]
    ring_nf
  rw [he.deriv_eq]
  set ρ₁ := cutoff η (2 * η)
  set ρ₂ := cutoff (1 - 2 * η) (1 - η)
  have hρ₁d : HasDerivAt ρ₁ (deriv ρ₁ u) u :=
    ((contDiff_cutoff _ _).differentiable (by simp) u).hasDerivAt
  have hρ₂d : HasDerivAt ρ₂ (deriv ρ₂ u) u :=
    ((contDiff_cutoff _ _).differentiable (by simp) u).hasDerivAt
  have hξu : HasDerivAt (fun v => ξ (t₀ + v)) (deriv ξ (t₀ + u)) u :=
    ((hξ.differentiable (by simp) (t₀ + u)).hasDerivAt).comp_const_add t₀ u
  have hlin : HasDerivAt (fun v : ℝ => ξ t₀ + 1 / 4 + v / 2) (1 / 2) u := by
    simpa using ((hasDerivAt_id u).div_const (2 : ℝ)).const_add (ξ t₀ + 1 / 4)
  have hall : HasDerivAt (fun v => ξ (t₀ + v) + crossCorr ξ t₀ η v)
      (deriv ξ (t₀ + u) + ((deriv ρ₁ u * (1 - ρ₂ u) + ρ₁ u * (0 - deriv ρ₂ u)) *
        (ξ t₀ + 1 / 4 + u / 2 - ξ (t₀ + u)) +
        ρ₁ u * (1 - ρ₂ u) * (1 / 2 - deriv ξ (t₀ + u)))) u :=
    hξu.add ((hρ₁d.mul ((hasDerivAt_const u (1 : ℝ)).sub hρ₂d)).mul (hlin.sub hξu))
  rw [hall.deriv]
  have hρ₁0 : 0 ≤ ρ₁ u := cutoff_nonneg _ _ _
  have hρ₁1 : ρ₁ u ≤ 1 := cutoff_le_one _ _ _
  have hρ₂0 : 0 ≤ ρ₂ u := cutoff_nonneg _ _ _
  have hρ₂1 : ρ₂ u ≤ 1 := cutoff_le_one _ _ _
  have hd₁ : 0 ≤ deriv ρ₁ u := (monotone_cutoff h12).deriv_nonneg
  have hd₂ : 0 ≤ deriv ρ₂ u := (monotone_cutoff h12').deriv_nonneg
  rcases le_or_gt u (2 * η) with hu2 | hu2
  · have hρ₂u : ρ₂ u = 0 := cutoff_of_le h12' (by linarith)
    have hd₂u : deriv ρ₂ u = 0 := deriv_cutoff_eq_zero_of_lt h12' (by linarith)
    obtain ⟨hn1, hn2⟩ := hnear u ⟨hu.1, hu2⟩
    have hgap : 0 ≤ ξ t₀ + 1 / 4 + u / 2 - ξ (t₀ + u) := by linarith [hu.1]
    rw [hρ₂u, hd₂u]
    have h3 : 0 ≤ deriv ρ₁ u * (ξ t₀ + 1 / 4 + u / 2 - ξ (t₀ + u)) := mul_nonneg hd₁ hgap
    rcases eq_or_lt_of_le hρ₁1 with h5 | h5
    · rw [h5]; nlinarith
    · have h6 : 0 < (1 - ρ₁ u) * deriv ξ (t₀ + u) := mul_pos (by linarith) hn2
      nlinarith
  · have hρ₁u : ρ₁ u = 1 := cutoff_of_ge h12 hu2.le
    have hd₁u : deriv ρ₁ u = 0 := deriv_cutoff_eq_zero_of_gt h12 hu2
    rw [hρ₁u, hd₁u]
    rcases lt_or_ge u (1 - 2 * η) with hu3 | hu3
    · have hρ₂u : ρ₂ u = 0 := cutoff_of_le h12' hu3.le
      have hd₂u : deriv ρ₂ u = 0 := deriv_cutoff_eq_zero_of_lt h12' hu3
      rw [hρ₂u, hd₂u]
      norm_num
    · obtain ⟨hf1, hf2⟩ := hfar u ⟨hu3, hu.2.le⟩
      have hgap : 0 ≤ ξ (t₀ + u) - (ξ t₀ + 1 / 4 + u / 2) := by linarith [hu.2]
      have h3 : 0 ≤ deriv ρ₂ u * (ξ (t₀ + u) - (ξ t₀ + 1 / 4 + u / 2)) := mul_nonneg hd₂ hgap
      rcases eq_or_lt_of_le hρ₂0 with h5 | h5
      · rw [← h5]; nlinarith
      · have h6 : 0 < ρ₂ u * deriv ξ (t₀ + u) := mul_pos h5 hf2
        nlinarith

end Reparam

theorem exists_reparam_of_cross {ξ : ℝ → ℝ} (hξ : ContDiff ℝ ∞ ξ)
    (hper : ∀ t, ξ (t + 1) = ξ t + 1) {t₀ : ℝ} (hd : 0 < deriv ξ t₀) :
    ∃ X : ℝ → ℝ, ContDiff ℝ ∞ X ∧ (∀ v, 0 < deriv X v) ∧ (∀ v, X (v + 1) = X v + 1) ∧
      ∃ η > 0, ∀ v ∈ Ioo (-η) η, X v = ξ (t₀ + v) := by
  have hξd : ∀ x, HasDerivAt ξ (deriv ξ x) x := fun x =>
    (hξ.differentiable (by simp) x).hasDerivAt
  have hdc : Continuous (deriv ξ) := hξ.continuous_deriv (by simp)
  have hdper : ∀ t, deriv ξ (t + 1) = deriv ξ t := by
    intro t
    have h1 : HasDerivAt (fun x => ξ (x + 1)) (deriv ξ (t + 1)) t :=
      (hξd (t + 1)).comp_add_const t 1
    have h2 : HasDerivAt (fun x => ξ (x + 1)) (deriv ξ t) t := by
      have : (fun x => ξ (x + 1)) = fun x => ξ x + 1 := funext hper
      rw [this]
      exact (hξd t).add_const 1
    exact h1.unique h2
  have hev : ∀ᶠ t in 𝓝 t₀, |ξ t - ξ t₀| < 1 / 4 ∧ 0 < deriv ξ t := by
    have h1 : ∀ᶠ t in 𝓝 t₀, ξ t ∈ Ioo (ξ t₀ - 1 / 4) (ξ t₀ + 1 / 4) :=
      hξ.continuous.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
    have h2 : ∀ᶠ t in 𝓝 t₀, 0 < deriv ξ t :=
      hdc.continuousAt.eventually (lt_mem_nhds hd)
    filter_upwards [h1, h2] with t ht ht'
    exact ⟨by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2], ht'⟩
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨η, hηpos, hηr, hη8⟩ : ∃ η : ℝ, 0 < η ∧ 2 * η < r ∧ η ≤ 1 / 8 :=
    ⟨min (r / 4) (1 / 8), lt_min (by linarith) (by norm_num),
      by have := min_le_left (r / 4) (1 / 8); linarith, min_le_right _ _⟩
  have hnear' : ∀ u, |u| ≤ 2 * η → |ξ (t₀ + u) - ξ t₀| < 1 / 4 ∧ 0 < deriv ξ (t₀ + u) := by
    intro u hu
    refine hrP ?_
    rw [Real.dist_eq, show t₀ + u - t₀ = u by ring]
    linarith
  have hnear : ∀ u ∈ Icc 0 (2 * η), ξ (t₀ + u) ≤ ξ t₀ + 1 / 4 ∧ 0 < deriv ξ (t₀ + u) := by
    intro u hu
    have h := hnear' u (by rw [abs_of_nonneg hu.1]; exact hu.2)
    rw [abs_lt] at h
    exact ⟨by linarith [h.1.2], h.2⟩
  have hfar : ∀ u ∈ Icc (1 - 2 * η) 1, ξ t₀ + 3 / 4 ≤ ξ (t₀ + u) ∧ 0 < deriv ξ (t₀ + u) := by
    intro u hu
    have h := hnear' (u - 1) (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])
    have e : t₀ + u = t₀ + (u - 1) + 1 := by ring
    rw [e, hper, hdper]
    rw [abs_lt] at h
    exact ⟨by linarith [h.1.1], h.2⟩
  have hη1 : η < 1 / 2 := by linarith
  have hXd := contDiff_crossReparam (t₀ := t₀) hξ hηpos hη1
  refine ⟨crossReparam ξ t₀ η, hXd, fun v => ?_, crossReparam_add_one hper,
    η, hηpos, fun v hv => crossReparam_eq_near hηpos hη1 hv⟩
  have he : crossReparam ξ t₀ η = fun w => crossReparam ξ t₀ η (w - ⌊v⌋) + ⌊v⌋ :=
    funext fun w => crossReparam_sub_int hper ⌊v⌋ w
  have hd' : HasDerivAt (crossReparam ξ t₀ η) (deriv (crossReparam ξ t₀ η) (v - ⌊v⌋))
      (v - ⌊v⌋) := (hXd.differentiable (by simp) _).hasDerivAt
  have h2 : HasDerivAt (fun w => crossReparam ξ t₀ η (w - ⌊v⌋) + ⌊v⌋)
      (deriv (crossReparam ξ t₀ η) (v - ⌊v⌋)) v :=
    (hd'.comp_sub_const v _).add_const _
  rw [← he] at h2
  rw [h2.deriv]
  exact deriv_crossReparam_pos_of_mem hξ hηpos hη8 hnear hfar
    ⟨by linarith [Int.floor_le v], by linarith [Int.lt_floor_add_one v]⟩

theorem add_int_of_add_one {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = f x + 1) (x : ℝ) (n : ℤ) :
    f (x + n) = f x + n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [← add_assoc, h, ih]
    ring
  | pred k ih =>
    have := h (x + ((-(k : ℤ) - 1 : ℤ) : ℝ))
    push_cast at this ih ⊢
    rw [show x + (-(k : ℝ) - 1) + 1 = x + -(k : ℝ) by ring, ih] at this
    linarith

theorem periodic_int_of_add_one {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = f x) (x : ℝ) (n : ℤ) :
    f (x + n) = f x := by
  have hp : Function.Periodic f 1 := h
  simpa using hp.int_mul n x

theorem exists_vertical_shear {C : ℝ → ℝ} (hC : ContDiff ℝ ∞ C)
    (hper : ∀ x (m : ℤ), C (x + m) = C x) :
    ∃ V : TDiff, IsotopicDiffeomorph torusRefl V ∧
      ∀ p, V (torusCover p) = torusCover (p.1, p.2 - C p.1) := by
  set G : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun q => (q.2.1, q.2.2 - q.1 * C q.2.1) with hGdef
  set Gi : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun q => (q.2.1, q.2.2 + q.1 * C q.2.1) with hGidef
  have hG : ContDiff ℝ ∞ G :=
    contDiff_snd.fst.prodMk (contDiff_snd.snd.sub (contDiff_fst.mul (hC.comp contDiff_snd.fst)))
  have hGi : ContDiff ℝ ∞ Gi :=
    contDiff_snd.fst.prodMk (contDiff_snd.snd.add (contDiff_fst.mul (hC.comp contDiff_snd.fst)))
  have hleft : ∀ t p, Gi (t, G (t, p)) = p := fun t p => by
    simp only [G, Gi, sub_add_cancel]
  have hright : ∀ t p, G (t, Gi (t, p)) = p := fun t p => by
    simp only [G, Gi, add_sub_cancel_right]
  have hp : ∀ t p (m n : ℤ), torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p)) := by
    intro t p m n
    simp only [G, hper]
    rw [← torusCover_add_int (p.1, p.2 - t * C p.1) m n]
    congr 1
    ext
    · simp only
    · simp only; ring
  have hpi : ∀ t p (m n : ℤ),
      torusCover (Gi (t, (p.1 + m, p.2 + n))) = torusCover (Gi (t, p)) := by
    intro t p m n
    simp only [Gi, hper]
    rw [← torusCover_add_int (p.1, p.2 + t * C p.1) m n]
    congr 1
    ext
    · simp only
    · simp only; ring
  refine ⟨torusFamily hG hGi hleft hright hp hpi 1,
    isotopicDiffeomorph_of_lift hG hGi hleft hright hp hpi (fun p => ?_)
      (torusFamilyMap_torusCover hp 1), fun p => ?_⟩
  · simp only [G, zero_mul, sub_zero]
    rfl
  · change torusFamilyMap G 1 (torusCover p) = _
    rw [torusFamilyMap_torusCover hp 1]
    simp only [G, one_mul]

theorem contDiffOn_sqShift_prod (b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => sqShift b q.1 q.2)
      {q | q.1 ∈ Ioo b (b + 1) ∧ q.2 ∈ Ioo 0 1} := by
  refine contDiffOn_const.add (contDiff_sqCoordInv'.comp_contDiffOn (ContDiffOn.add ?_ ?_))
  · exact contDiffOn_sqCoord_Ioo.comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_sqCoord_Ioo.comp (contDiff_fst.sub contDiff_const).contDiffOn
      (fun q hq => sub_mem_Ioo_of_mem hq.1)

theorem contDiffOn_sqShiftInv_prod (b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => sqShiftInv b q.1 q.2)
      {q | q.1 ∈ Ioo b (b + 1) ∧ q.2 ∈ Ioo b (b + 1)} := by
  refine contDiff_sqCoordInv'.comp_contDiffOn (ContDiffOn.sub ?_ ?_)
  · exact contDiffOn_sqCoord_Ioo.comp (contDiff_snd.sub contDiff_const).contDiffOn
      (fun q hq => sub_mem_Ioo_of_mem hq.2)
  · exact contDiffOn_sqCoord_Ioo.comp (contDiff_fst.sub contDiff_const).contDiffOn
      (fun q hq => sub_mem_Ioo_of_mem hq.1)

theorem sqShiftInv_injOn {b c : ℝ} {y y' : ℝ} (hy : y ∈ Ioo b (b + 1)) (hy' : y' ∈ Ioo b (b + 1))
    (h : sqShiftInv b c y = sqShiftInv b c y') : y = y' := by
  have := congrArg (sqShift b c) h
  rwa [sqShift_sqShiftInv hy, sqShift_sqShiftInv hy'] at this

theorem alphaCircle_cexp' (t : ℝ) : alphaCircle (cexp t) = torusCover (t, 0) := by
  rw [torusCover_eq]
  exact Prod.ext rfl cexp_zero.symm

def crossChart (X c : ℝ → ℝ) (b : ℝ) (z : ℂ) : ℝ × ℝ := (X z.im, sqShift b (c z.im) z.re)

def crossChartInv (Y c : ℝ → ℝ) (b : ℝ) (p : ℝ × ℝ) : ℂ :=
  (sqShiftInv b (c (Y p.1)) p.2 : ℂ) + ((Y p.1 : ℝ) : ℂ) * Complex.I

theorem crossChartInv_re (Y c : ℝ → ℝ) (b : ℝ) (p : ℝ × ℝ) :
    (crossChartInv Y c b p).re = sqShiftInv b (c (Y p.1)) p.2 := by
  simp [crossChartInv]

theorem crossChartInv_im (Y c : ℝ → ℝ) (b : ℝ) (p : ℝ × ℝ) :
    (crossChartInv Y c b p).im = Y p.1 := by
  simp [crossChartInv]

theorem contDiffOn_crossChart {X c : ℝ → ℝ} {b : ℝ} (hX : ContDiff ℝ ∞ X)
    (hc : ContDiff ℝ ∞ c) (hcb : ∀ v, c v ∈ Ioo b (b + 1)) :
    ContDiffOn ℝ ∞ (crossChart X c b) openSquare := by
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have h3 : ContDiff ℝ ∞ (fun z : ℂ => (c z.im, z.re)) := (hc.comp him).prodMk hre
  have hm : MapsTo (fun z : ℂ => (c z.im, z.re)) openSquare
      {q : ℝ × ℝ | q.1 ∈ Ioo b (b + 1) ∧ q.2 ∈ Ioo 0 1} :=
    fun z hz => ⟨hcb _, (mem_openSquare.mp hz).1⟩
  have h4 : ContDiffOn ℝ ∞
      ((fun q : ℝ × ℝ => sqShift b q.1 q.2) ∘ (fun z : ℂ => (c z.im, z.re))) openSquare :=
    ContDiffOn.comp (contDiffOn_sqShift_prod b) h3.contDiffOn hm
  have h5 : ContDiffOn ℝ ∞ (fun z : ℂ => (X z.im, sqShift b (c z.im) z.re)) openSquare := by
    have h6 := (hX.comp him).contDiffOn.prodMk h4
    simpa only [Function.comp_def] using h6
  exact h5

theorem contDiffOn_crossChartInv {Y c : ℝ → ℝ} {b : ℝ} (hY : ContDiff ℝ ∞ Y)
    (hc : ContDiff ℝ ∞ c) (hcb : ∀ v, c v ∈ Ioo b (b + 1)) (a : ℝ) :
    ContDiffOn ℝ ∞ (crossChartInv Y c b) (Ioo a (a + 1) ×ˢ Ioo b (b + 1)) := by
  have hof : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (c (Y p.1), p.2)) :=
    (hc.comp (hY.comp contDiff_fst)).prodMk contDiff_snd
  have hm : MapsTo (fun p : ℝ × ℝ => (c (Y p.1), p.2)) (Ioo a (a + 1) ×ˢ Ioo b (b + 1))
      {q : ℝ × ℝ | q.1 ∈ Ioo b (b + 1) ∧ q.2 ∈ Ioo b (b + 1)} :=
    fun p hp => ⟨hcb _, hp.2⟩
  have h4 := hof.comp_contDiffOn (ContDiffOn.comp (contDiffOn_sqShiftInv_prod b) h3.contDiffOn hm)
  have h5 := (hof.comp (hY.comp contDiff_fst)).contDiffOn.mul
    (contDiffOn_const (c := Complex.I) (s := Ioo a (a + 1) ×ˢ Ioo b (b + 1)))
  have h6 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (sqShiftInv b (c (Y p.1)) p.2 : ℂ) +
      ((Y p.1 : ℝ) : ℂ) * Complex.I) (Ioo a (a + 1) ×ˢ Ioo b (b + 1)) := by
    have h7 := h4.add h5
    simpa only [Function.comp_def] using h7
  exact h6

theorem exists_isotopic_height_one_of_cross_data (φ : TDiff)
    {Φ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ)}
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p))
    (hper : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    {b : ℝ} (hb : ∀ t, (Φ (t, 0)).2 ∈ Ioo b (b + 1))
    {t₀ : ℝ} (hd : 0 < deriv (fun t => (Φ (t, 0)).1) t₀)
    (hone : ∀ u ∈ Ioo t₀ (t₀ + 1), (Φ (u, 0)).1 ∈ Ioo (Φ (t₀, 0)).1 ((Φ (t₀, 0)).1 + 1)) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
  set ξ : ℝ → ℝ := fun t => (Φ (t, 0)).1 with hξdef
  set ζ : ℝ → ℝ := fun t => (Φ (t, 0)).2 with hζdef
  set θ' : ℝ := ξ t₀ with hθ'
  have hγd : ContDiff ℝ ∞ (fun t => Φ (t, 0)) := Φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hξ : ContDiff ℝ ∞ ξ := hγd.fst
  have hζ : ContDiff ℝ ∞ ζ := hγd.snd
  have hshift : ∀ (t : ℝ) (m : ℤ), Φ (t + m, 0) = (ξ t + m, ζ t) := by
    intro t m
    have := hper (t, 0) m 0
    simp only [Int.cast_zero, add_zero] at this
    exact this
  have hξper : ∀ t, ξ (t + 1) = ξ t + 1 := by
    intro t
    have := hshift t 1
    simp only [Int.cast_one] at this
    exact congrArg Prod.fst this
  have hζint : ∀ (t : ℝ) (m : ℤ), ζ (t + m) = ζ t := by
    intro t m
    have := congrArg Prod.snd (hshift t m)
    exact this
  obtain ⟨X, hX, hXpos, hX1, η, hη, hXη⟩ := exists_reparam_of_cross hξ hξper hd
  have hXint : ∀ (v : ℝ) (m : ℤ), X (v + m) = X v + m := add_int_of_add_one hX1
  obtain ⟨R, hR, hRX, hXR⟩ := exists_contDiff_inverse_of_sign (E := ℝ) (h := fun q => X q.2)
    (h' := fun q => deriv X q.2) (hX.comp contDiff_snd) (ε := 1) (Or.inl rfl)
    (fun _ x => (hX.differentiable (by simp) x).hasDerivAt) (fun _ x => by simpa using hXpos x)
    (fun _ x n => by simpa using hXint x n)
  set Y : ℝ → ℝ := fun y => R (0, y) with hYdef
  have hY : ContDiff ℝ ∞ Y := hR.comp (contDiff_const.prodMk contDiff_id)
  have hYX : ∀ v, Y (X v) = v := fun v => hRX 0 v
  have hXY : ∀ y, X (Y y) = y := fun y => hXR 0 y
  have hXmono : StrictMono X := strictMono_of_deriv_pos hXpos
  have hX0 : X 0 = θ' := by rw [hXη 0 ⟨by linarith, hη⟩, add_zero]
  have hX1' : X 1 = θ' + 1 := by
    have := hX1 0
    rw [zero_add, hX0] at this
    exact this
  have hXmem : ∀ v ∈ Ioo (0 : ℝ) 1, X v ∈ Ioo θ' (θ' + 1) := fun v hv =>
    ⟨hX0 ▸ hXmono hv.1, hX1' ▸ hXmono hv.2⟩
  have hYmem : ∀ y ∈ Ioo θ' (θ' + 1), Y y ∈ Ioo (0 : ℝ) 1 := by
    intro y hy
    refine ⟨hXmono.lt_iff_lt.mp ?_, hXmono.lt_iff_lt.mp ?_⟩
    · rw [hX0, hXY]; exact hy.1
    · rw [hX1', hXY]; exact hy.2
  have hYint : ∀ (y : ℝ) (m : ℤ), Y (y + m) = Y y + m := by
    intro y m
    apply hXmono.injective
    rw [hXY, hXint, hXY]
  set c : ℝ → ℝ := fun v => ζ (t₀ + v) with hcdef
  have hc : ContDiff ℝ ∞ c := hζ.comp (contDiff_const.add contDiff_id)
  have hcb : ∀ v, c v ∈ Ioo b (b + 1) := fun v => hb _
  have hcint : ∀ (v : ℝ) (m : ℤ), c (v + m) = c v := by
    intro v m
    simp only [c, ← add_assoc, hζint]
  set B : Set (ℝ × ℝ) := Ioo θ' (θ' + 1) ×ˢ Ioo b (b + 1) with hB
  obtain ⟨M, hMdef⟩ : ∃ M : ℂ → ℝ × ℝ, M = crossChart X c b := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ × ℝ → ℂ, N = crossChartInv Y c b := ⟨_, rfl⟩
  have hMapp : ∀ z, M z = (X z.im, sqShift b (c z.im) z.re) := by
    intro z; rw [hMdef]; rfl
  have hNre : ∀ p, (N p).re = sqShiftInv b (c (Y p.1)) p.2 := by
    intro p; rw [hNdef]; exact crossChartInv_re Y c b p
  have hNim : ∀ p, (N p).im = Y p.1 := by
    intro p; rw [hNdef]; exact crossChartInv_im Y c b p
  have hBo : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  have hBinj : InjOn torusCover B := injOn_torusCover_box θ' b
  have hMd : ContDiffOn ℝ ∞ M openSquare := hMdef ▸ contDiffOn_crossChart hX hc hcb
  have hNd : ContDiffOn ℝ ∞ N B := hNdef ▸ contDiffOn_crossChartInv hY hc hcb θ'
  have hMB : MapsTo M openSquare B := fun z hz => by
    rw [hMapp]
    exact ⟨hXmem _ (mem_openSquare.mp hz).2, sqShift_mem _⟩
  have hNB : MapsTo N B openSquare := fun p hp => by
    rw [mem_openSquare, hNre, hNim]
    exact ⟨sqShiftInv_mem _, hYmem _ hp.1⟩
  have hNM : ∀ z ∈ openSquare, N (M z) = z := by
    intro z hz
    apply Complex.ext
    · rw [hNre, hMapp]
      simp only [hYX]
      exact sqShiftInv_sqShift (mem_openSquare.mp hz).1
    · rw [hNim, hMapp]
      exact hYX _
  have hMN : ∀ p ∈ B, M (N p) = p := by
    intro p hp
    rw [hMapp, hNre, hNim, hXY]
    exact Prod.ext rfl (sqShift_sqShiftInv hp.2)
  set L : ℝ → ℂ := fun t => (1 / 2 : ℂ) + (t : ℂ) * Complex.I with hLdef
  have hLre : ∀ t, (L t).re = 1 / 2 := fun t => by simp [L]
  have hLim : ∀ t, (L t).im = t := fun t => by simp [L]
  have hML : ∀ t, M (L t) = (X t, c t) := by
    intro t
    rw [hMapp, hLre, hLim, sqShift_half (hcb t)]
  have hNML : ∀ t, N (M (L t)) = L t := by
    intro t
    apply Complex.ext
    · rw [hNre, hML, hLre]
      simp only [hYX]
      exact sqShiftInv_self
    · rw [hNim, hML, hLim]
      simp only [hYX]
  have hγML : ∀ t, |t| < η ∨ |t - 1| < η → Φ (t₀ + t, 0) = M (L t) := by
    intro t ht
    rw [hML]
    refine Prod.ext ?_ rfl
    change ξ (t₀ + t) = X t
    rcases ht with ht | ht
    · rw [hXη t (abs_lt.mp ht)]
    · have h1 := hXη (t - 1) (abs_lt.mp ht)
      have h2 := hX1 (t - 1)
      rw [sub_add_cancel] at h2
      rw [h2, h1, show t₀ + t = t₀ + (t - 1) + 1 by ring, hξper]
  have hNγ : ∀ t, |t| < η ∨ |t - 1| < η → N (Φ (t₀ + t, 0)) = L t := fun t ht => by
    rw [hγML t ht, hNML]
  set ε' : ℝ := min η (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hη (by norm_num)
  have hε'η : ε' ≤ η := min_le_left _ _
  have hε'h : ε' ≤ 1 / 2 := min_le_right _ _
  have hcurveB : ∀ t ∈ Ioo (0 : ℝ) 1, Φ (t₀ + t, 0) ∈ B := fun t ht =>
    ⟨hone _ ⟨by linarith [ht.1], by linarith [ht.2]⟩, hb _⟩
  let γ : ℝ → ℂ := fun t => if t ∈ Ioo (0 : ℝ) 1 then N (Φ (t₀ + t, 0)) else L t
  set W : Set ℝ := Iio ε' ∪ Ioi (1 - ε') with hW
  have hγW : ∀ t ∈ W, γ t = L t := by
    intro t ht
    simp only [γ]
    split_ifs with h01
    · refine hNγ t ?_
      rcases ht with ht | ht
      · exact Or.inl (by rw [abs_of_pos h01.1]; linarith [mem_Iio.mp ht])
      · exact Or.inr (by rw [abs_of_neg (by linarith [h01.2])]; linarith [mem_Ioi.mp ht])
    · rfl
  have hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = N (Φ (t₀ + t, 0)) := by
    intro t ht
    by_cases h01 : t ∈ Ioo (0 : ℝ) 1
    · simp only [γ, h01, ↓reduceIte]
    · have : t = 0 ∨ t = 1 := by
        rcases eq_or_lt_of_le ht.1 with h | h
        · exact Or.inl h.symm
        · rcases eq_or_lt_of_le ht.2 with h' | h'
          · exact Or.inr h'
          · exact absurd ⟨h, h'⟩ h01
      simp only [γ, h01, ↓reduceIte]
      rcases this with rfl | rfl
      · rw [hNγ 0 (Or.inl (by simpa using hη))]
      · rw [hNγ 1 (Or.inr (by simpa using hη))]
  have hWo : IsOpen W := isOpen_Iio.union isOpen_Ioi
  have hcover : ∀ t : ℝ, t ∈ W ∨ t ∈ Ioo (0 : ℝ) 1 := by
    intro t
    by_cases h1 : t < ε'
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : 1 - ε' < t
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨by linarith, by linarith⟩
  have hLd : ContDiff ℝ ∞ L := contDiff_const.add
    (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hcurve : ContDiff ℝ ∞ (fun t => Φ (t₀ + t, 0)) :=
    Φ.contDiff.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const)
  have hγeq : ∀ t ∈ Ioo (0 : ℝ) 1, γ =ᶠ[𝓝 t] fun s => N (Φ (t₀ + s, 0)) := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp only [γ, hs, ↓reduceIte]
  have hγd : ContDiff ℝ ∞ γ := by
    refine contDiff_iff_contDiffAt.mpr fun t => ?_
    rcases hcover t with ht | ht
    · refine hLd.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hγW s hs
    · exact ((hNd.contDiffAt (hBo.mem_nhds (hcurveB t ht))).comp t
        hcurve.contDiffAt).congr_of_eventuallyEq (hγeq t ht)
  have hinj : InjOn γ (Icc 0 1) := by
    intro s hs t ht hst
    rw [hγc s hs, hγc t ht] at hst
    have him := congrArg Complex.im hst
    have hre := congrArg Complex.re hst
    rw [hNim, hNim] at him
    rw [hNre, hNre, him] at hre
    have h1 : (Φ (t₀ + s, 0)).1 = (Φ (t₀ + t, 0)).1 := by
      rw [← hXY (Φ (t₀ + s, 0)).1, ← hXY (Φ (t₀ + t, 0)).1, him]
    have h2 := sqShiftInv_injOn (hb _) (hb _) hre
    have h3 := congrArg Prod.fst (Φ.injective (Prod.ext h1 h2))
    simp only at h3
    linarith
  have himm : ∀ t, deriv γ t ≠ 0 := by
    intro t
    rcases hcover t with ht | ht
    · have he : γ =ᶠ[𝓝 t] L := by
        filter_upwards [hWo.mem_nhds ht] with s hs
        exact hγW s hs
      rw [he.deriv_eq]
      have hLder : HasDerivAt L Complex.I t := by
        have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
          (1 / 2 : ℂ)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
        exact this
      rw [hLder.deriv]
      exact Complex.I_ne_zero
    · intro h0
      have hγt : γ t ∈ openSquare := by
        rw [hγc t (Ioo_subset_Icc_self ht)]
        exact hNB (hcurveB t ht)
      have hMt : DifferentiableAt ℝ M (γ t) :=
        (hMd.contDiffAt (isOpen_openSquare.mem_nhds hγt)).differentiableAt (by simp)
      have hγt' : HasDerivAt γ 0 t := by
        rw [← h0]
        exact (hγd.differentiable (by simp) t).hasDerivAt
      have h1 : HasDerivAt (fun s => M (γ s)) (fderiv ℝ M (γ t) 0) t :=
        hMt.hasFDerivAt.comp_hasDerivAt t hγt'
      rw [map_zero] at h1
      have he : (fun s => M (γ s)) =ᶠ[𝓝 t] fun s => Φ (t₀ + s, 0) := by
        filter_upwards [hγeq t ht, isOpen_Ioo.mem_nhds ht] with s hs hs'
        rw [hs]
        exact hMN _ (hcurveB s hs')
      have h2 : HasDerivAt (fun s => Φ (t₀ + s, 0)) 0 t := h1.congr_of_eventuallyEq he.symm
      have h3 : HasDerivAt (fun s => Φ (t₀ + s, 0)) (fderiv ℝ Φ (t₀ + t, 0) (1, 0)) t := by
        have hΦd : DifferentiableAt ℝ Φ (t₀ + t, 0) :=
          (Φ.contDiff.differentiable (by simp)) (t₀ + t, 0)
        have hl : HasDerivAt (fun s : ℝ => (t₀ + s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) t :=
          ((hasDerivAt_id t).const_add t₀).prodMk (hasDerivAt_const t (0 : ℝ))
        exact hΦd.hasFDerivAt.comp_hasDerivAt t hl
      have h4 := h2.unique h3
      have h5 := injective_fderiv_of_diffeomorph Φ (t₀ + t, 0)
        (show fderiv ℝ Φ (t₀ + t, 0) (1, 0) = fderiv ℝ Φ (t₀ + t, 0) 0 by rw [← h4, map_zero])
      exact one_ne_zero (congrArg Prod.fst h5)
  have hend : ∀ t, t ≤ ε' / 2 ∨ 1 - ε' / 2 ≤ t → γ t = L t := by
    intro t ht
    refine hγW t ?_
    rcases ht with ht | ht
    · exact Or.inl (by change t < ε'; linarith)
    · exact Or.inr (by change 1 - ε' < t; linarith)
  have hin : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ openSquare := by
    intro t ht
    rw [hγc t (Ioo_subset_Icc_self ht)]
    exact hNB (hcurveB t ht)
  obtain ⟨Q, hQ, C, hC, hCB, hQC, hQt⟩ := exists_square_transport hBo hBinj hMd hNd hMB hNB hNM
    hMN hγd hinj himm (half_pos hε'pos) hend hin
  have hQφ : ∀ t ∈ Ioo (0 : ℝ) 1,
      Q (torusCover (X t, c t)) = φ (alphaCircle (cexp (t₀ + t))) := by
    intro t ht
    have h1 := hQt t ht
    rw [hML, hγc t (Ioo_subset_Icc_self ht), hMN _ (hcurveB t ht)] at h1
    rw [h1, alphaCircle_cexp', hlift]
  have hnotC : ∀ y : ℝ, torusCover (θ', y) ∉ C := by
    intro y hy
    obtain ⟨q, hq, hqp⟩ := hCB hy
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp hqp
    have h1 : q.1 = θ' + m := congrArg Prod.fst hmn
    have h2 := hq.1
    rw [h1] at h2
    have h3 : (0 : ℝ) < m := by linarith [h2.1]
    have h4 : (m : ℝ) < 1 := by linarith [h2.2]
    have h3' : 0 < m := by exact_mod_cast h3
    have h4' : m < 1 := by exact_mod_cast h4
    omega
  have hQs : ∀ z, z ∉ C → Q.symm z = z := by
    intro z hz
    conv_lhs => rw [← hQC z hz]
    exact Q.symm_apply_apply z
  have hrefl : (torusRefl : TDiff).symm = torusRefl := Diffeomorph.ext fun _ => rfl
  have hQi : IsotopicDiffeomorph torusRefl Q.symm := by
    have := IsotopicDiffeomorph.inv hQ
    rwa [hrefl] at this
  set ψ : TDiff := φ.trans Q.symm with hψ
  have hφψ : IsotopicDiffeomorph φ ψ := isotopicDiffeomorph_trans_of_refl φ hQi
  have hψα : ∀ v ∈ Ico (0 : ℝ) 1, ψ (alphaCircle (cexp (t₀ + v))) = torusCover (X v, c v) := by
    intro v hv
    change Q.symm (φ (alphaCircle (cexp (t₀ + v)))) = _
    rcases eq_or_lt_of_le hv.1 with h0 | h0
    · rw [← h0, add_zero, alphaCircle_cexp', hlift, hX0]
      have he : Φ (t₀, 0) = (θ', c 0) := by
        refine Prod.ext rfl ?_
        change (Φ (t₀, 0)).2 = ζ (t₀ + 0)
        rw [add_zero]
      rw [he, hQs _ (hnotC _)]
    · rw [← hQφ v ⟨h0, hv.2⟩, Q.symm_apply_apply]
  set Cv : ℝ → ℝ := fun x => c (Y x) with hCv
  have hCvd : ContDiff ℝ ∞ Cv := hc.comp hY
  have hCvint : ∀ (x : ℝ) (m : ℤ), Cv (x + m) = Cv x := by
    intro x m
    simp only [Cv, hYint, hcint]
  obtain ⟨V, hV, hVapp⟩ := exists_vertical_shear hCvd hCvint
  refine ⟨ψ.trans V, hφψ.trans (isotopicDiffeomorph_trans_of_refl ψ hV), fun z => ?_⟩
  set v : ℝ := Int.fract (rep z - t₀) with hv
  have hz : z = cexp (t₀ + v) := by
    rw [hv, Int.fract, show t₀ + (rep z - t₀ - ⌊rep z - t₀⌋) = rep z + ((-⌊rep z - t₀⌋ : ℤ) : ℝ)
      by push_cast; ring, cexp_add_int, cexp_rep]
  have hvI : v ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  change (V (ψ (alphaCircle z))).2 = 1
  rw [hz, hψα v hvI, hVapp]
  simp only [Cv, hYX, sub_self]
  rw [torusCover_eq, cexp_zero]

theorem contMDiff_alphaWidth (φ : TDiff) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z => (φ (alphaCircle z)).1) :=
  contMDiff_fst.comp (φ.contMDiff.comp contMDiff_alphaCircle)

theorem exists_isotopic_height_one_of_not_hasSameSideArc (φ : TDiff) (h : torusMatrix φ = 1)
    {s : Circle} (hs : ∀ z, heightOnCircle φ z ≠ s) {θ : Circle}
    (hθ : ∀ z, (φ (alphaCircle z)).1 = θ →
      mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0)
    (hno : ¬ HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
  obtain ⟨Φ, -, hlift, -, hdeck⟩ := exists_torusLiftDiffeomorph φ
    (torusCover_torusSection (φ (torusCover 0))).symm
  have hper := lift_add_int_of_eq_one h hdeck
  have hγd : ContDiff ℝ ∞ (fun t => Φ (t, 0)) :=
    Φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
  set ξ : ℝ → ℝ := fun t => (Φ (t, 0)).1 with hξdef
  set ζ : ℝ → ℝ := fun t => (Φ (t, 0)).2 with hζdef
  have hξ : ContDiff ℝ ∞ ξ := hγd.fst
  have hζ : ContDiff ℝ ∞ ζ := hγd.snd
  have hfg (t : ℝ) : (φ (alphaCircle (cexp t))).1 = cexp (ξ t) := by
    rw [alphaCircle_cexp', hlift, torusCover_eq]
  obtain ⟨hh, hcross, hreg, hno'⟩ :=
    cross_hypotheses (contMDiff_alphaWidth φ) hξ hfg (cexp_rep θ) hθ hno
  have hper' : ∀ t, (fun x => ξ x - rep θ) (t + 1) = (fun x => ξ x - rep θ) t + 1 := by
    intro t
    have := congrArg Prod.fst (hper (t, 0) 1 0)
    simp only [Int.cast_one, Int.cast_zero, add_zero] at this
    change (Φ (t + 1, 0)).1 - rep θ = (Φ (t, 0)).1 - rep θ + 1
    rw [this]
    ring
  obtain ⟨t₀, k, hk, hpos, hbetween⟩ := exists_unique_cross_of_add_one hh hreg hper'
    (fun t t' htt' hc hc' hnoc => hno' t (mem_univ t) t' (mem_univ t') htt' hc hc' hnoc)
  have hd : 0 < deriv (fun t => (Φ (t, 0)).1) t₀ := by
    have he : deriv (fun x => ξ x - rep θ) t₀ = deriv ξ t₀ := deriv_sub_const _
    rw [he] at hpos
    exact hpos
  have hone : ∀ u ∈ Ioo t₀ (t₀ + 1),
      (Φ (u, 0)).1 ∈ Ioo (Φ (t₀, 0)).1 ((Φ (t₀, 0)).1 + 1) := by
    intro u hu
    have h1 : (k : ℝ) < ξ u - rep θ ∧ ξ u - rep θ < k + 1 := hbetween u hu
    have hk' : ξ t₀ - rep θ = k := hk
    change ξ u ∈ Ioo (ξ t₀) (ξ t₀ + 1)
    constructor <;> linarith [h1.1, h1.2]
  have hζne : ∀ t (j : ℤ), ζ t ≠ rep s + j := by
    intro t j hj
    apply hs (cexp t)
    rw [heightOnCircle_cexp hlift t]
    change cexp (ζ t) = s
    rw [hj, cexp_add_int, cexp_rep]
  set b : ℝ := rep s + ⌊ζ 0 - rep s⌋ with hbdef
  have hb0 : ζ 0 ∈ Ioo b (b + 1) := by
    refine ⟨lt_of_le_of_ne (by linarith [Int.floor_le (ζ 0 - rep s)]) (fun he => hζne 0 _ he.symm),
      by linarith [Int.lt_floor_add_one (ζ 0 - rep s)]⟩
  have hb : ∀ t, (Φ (t, 0)).2 ∈ Ioo b (b + 1) := by
    have hall := mem_Ioo_of_forall_ne (f := ζ) (a := b) (b := b + 1) isPreconnected_univ
      hζ.continuous.continuousOn (fun t _ => ⟨hζne t _, by
        have := hζne t (⌊ζ 0 - rep s⌋ + 1)
        push_cast at this
        rwa [← add_assoc] at this⟩) (mem_univ 0) hb0
    exact fun t => hall t (mem_univ t)
  exact exists_isotopic_height_one_of_cross_data φ hlift hper hb hd hone

theorem exists_isotopic_height_one_of_forall_ne_of_push
    (hann : ∀ φ : TDiff, torusMatrix φ = 1 → ∀ s : Circle, (∀ z, heightOnCircle φ z ≠ s) →
      ∀ θ : Circle, (∀ z, (φ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0) →
      HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ (∀ z, heightOnCircle ψ z ≠ s) ∧
        (∀ z, (ψ (alphaCircle z)).1 = θ →
          mfderiv (𝓡 1) (𝓡 1) (fun z => (ψ (alphaCircle z)).1) z ≠ 0) ∧
        {z | (ψ (alphaCircle z)).1 = θ}.ncard < {z | (φ (alphaCircle z)).1 = θ}.ncard)
    (φ : TDiff) (h : torusMatrix φ = 1) {s : Circle} (hs : ∀ z, heightOnCircle φ z ≠ s) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
  obtain ⟨θ, -, hθ⟩ := circle_exists_regular_mem (contMDiff_alphaWidth φ) isOpen_univ
    univ_nonempty
  have key : ∀ n : ℕ, ∀ φ : TDiff, torusMatrix φ = 1 → (∀ z, heightOnCircle φ z ≠ s) →
      (∀ z, (φ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0) →
      {z | (φ (alphaCircle z)).1 = θ}.ncard = n →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro φ h hs hθ hn
      by_cases hss : HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ
      · obtain ⟨ψ, hφψ, hs', hθ', hlt⟩ := hann φ h s hs θ hθ hss
        obtain ⟨χ, hψχ, hχ⟩ := ih _ (hn ▸ hlt) ψ
          (by rw [← torusMatrix_eq_of_isotopic hφψ, h]) hs' hθ' rfl
        exact ⟨χ, hφψ.trans hψχ, hχ⟩
      · exact exists_isotopic_height_one_of_not_hasSameSideArc φ h hs hθ hss
  exact key _ φ h hs hθ rfl

end GC.Seifert
