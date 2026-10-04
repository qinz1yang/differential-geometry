import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveSquare
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonDescent

/-!
# Torus curves: the second circle relative to the first

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme, stage (iii)
(review 12, §4.6). Let `φ` have matrix `1` and be the identity on an open neighbourhood of `α`.
Its lift `Φ` normalised at the origin is the identity on a band `|y| < ε`, so the arc
`c y = Φ (0, y)`, `y ∈ [0, 1]`, of the lifted second circle is the vertical segment near both
ends and stays in the strip `0 < y < 1` in between.

If `φ (β)` misses a vertical circle `β_θ`, `0 < θ < 1`, the arc stays in the open box
`(θ - 1, θ) × (0, 1)`. A shifted square chart (`sqShift`) sends the vertical middle line of the
unit square onto `{0} × (0, 1)`, so the arc read in that chart is the standard segment near its
ends, and the square-arc isotopy of MC3 (transported by `exists_square_transport`) moves `β` onto
`φ (β)` with support in a compact subset of the box. Composing `φ` with the inverse gives a map
that is still the identity near `α` and maps `β` into `β`; the relative normal form of MC1
finishes (`exists_isotopic_eqOn_nhds_axes_of_forall_ne`).

In general, a regular `θ` is chosen; while `φ (β)` has a same-side arc against `β_θ` (in the
lift, two consecutive crossings of the arc at the same vertical line) a relative empty-bigon push
removes two crossings (hypothesis `hrel` of `exists_isotopic_eqOn_nhds_axes_of_push`, the
relative proper-arc push of lane MC2). Without same-side arcs all crossings of the arc have the
same sign and its two ends lie on the same side, so there are no crossings at all
(`forall_ne_int_of_eq_endpoint`): twist zero alone does not give disjointness.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

section SquareShift

theorem sqCoordInv_mem_Ioo (y : ℝ) : sqCoordInv y ∈ Ioo (0 : ℝ) 1 := by
  have h1 := Real.arctan_lt_pi_div_two y
  have h2 := Real.neg_pi_div_two_lt_arctan y
  have hpi := Real.pi_pos
  constructor
  · unfold sqCoordInv
    have : -(1 / 2) < Real.arctan y / Real.pi := by
      rw [lt_div_iff₀ hpi]; linarith
    linarith
  · unfold sqCoordInv
    have : Real.arctan y / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ hpi]; linarith
    linarith

theorem contDiffOn_sqCoord_Ioo : ContDiffOn ℝ ∞ sqCoord (Ioo 0 1) := by
  intro X hX
  apply ContDiffAt.contDiffWithinAt
  have hpi := Real.pi_pos
  have harg : Real.pi * (X - 1 / 2) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [hX.1, hX.2]
  have h1 : ContDiff ℝ ∞ (fun X : ℝ => Real.pi * (X - 1 / 2)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  exact (Real.contDiffAt_tan.mpr (Real.cos_pos_of_mem_Ioo harg).ne').comp X h1.contDiffAt

theorem contDiff_sqCoordInv' : ContDiff ℝ ∞ sqCoordInv :=
  contDiff_const.add (Real.contDiff_arctan.div_const _)

theorem sqCoord_half' : sqCoord (1 / 2) = 0 := by
  simp [sqCoord]

theorem sqCoordInv_zero : sqCoordInv 0 = 1 / 2 := by
  simp [sqCoordInv]

def sqShift (b c u : ℝ) : ℝ := b + sqCoordInv (sqCoord u + sqCoord (c - b))

def sqShiftInv (b c y : ℝ) : ℝ := sqCoordInv (sqCoord (y - b) - sqCoord (c - b))

variable {b c : ℝ}

theorem sqShift_mem (u : ℝ) : sqShift b c u ∈ Ioo b (b + 1) := by
  have := sqCoordInv_mem_Ioo (sqCoord u + sqCoord (c - b))
  exact ⟨by unfold sqShift; linarith [this.1], by unfold sqShift; linarith [this.2]⟩

theorem sqShiftInv_mem (y : ℝ) : sqShiftInv b c y ∈ Ioo (0 : ℝ) 1 :=
  sqCoordInv_mem_Ioo _

theorem sub_mem_Ioo_of_mem {y : ℝ} (hy : y ∈ Ioo b (b + 1)) : y - b ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem sqShift_half (hc : c ∈ Ioo b (b + 1)) : sqShift b c (1 / 2) = c := by
  unfold sqShift
  rw [sqCoord_half', zero_add, sqCoordInv_sqCoord (sub_mem_Ioo_of_mem hc)]
  ring

theorem sqShiftInv_self : sqShiftInv b c c = 1 / 2 := by
  unfold sqShiftInv
  rw [sub_self, sqCoordInv_zero]

theorem sqShiftInv_sqShift {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    sqShiftInv b c (sqShift b c u) = u := by
  unfold sqShiftInv sqShift
  rw [add_sub_cancel_left, sqCoord_sqCoordInv, add_sub_cancel_right, sqCoordInv_sqCoord hu]

theorem sqShift_sqShiftInv {y : ℝ} (hy : y ∈ Ioo b (b + 1)) :
    sqShift b c (sqShiftInv b c y) = y := by
  unfold sqShiftInv sqShift
  rw [sqCoord_sqCoordInv, sub_add_cancel, sqCoordInv_sqCoord (sub_mem_Ioo_of_mem hy)]
  ring

theorem contDiffOn_sqShift (b c : ℝ) : ContDiffOn ℝ ∞ (sqShift b c) (Ioo 0 1) :=
  contDiffOn_const.add (contDiff_sqCoordInv'.comp_contDiffOn
    (contDiffOn_sqCoord_Ioo.add contDiffOn_const))

theorem contDiffOn_sqShiftInv (b c : ℝ) :
    ContDiffOn ℝ ∞ (sqShiftInv b c) (Ioo b (b + 1)) := by
  refine contDiff_sqCoordInv'.comp_contDiffOn (ContDiffOn.sub ?_ contDiffOn_const)
  exact contDiffOn_sqCoord_Ioo.comp (contDiff_id.sub contDiff_const).contDiffOn
    (fun y hy => sub_mem_Ioo_of_mem hy)

end SquareShift

theorem mem_Ioo_of_forall_ne {f : ℝ → ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (hf : ContinuousOn f I) {a b : ℝ} (hne : ∀ y ∈ I, f y ≠ a ∧ f y ≠ b) {y₀ : ℝ}
    (hy₀ : y₀ ∈ I) (hab : f y₀ ∈ Ioo a b) : ∀ y ∈ I, f y ∈ Ioo a b := by
  have himg : IsPreconnected (f '' I) := hI.image f hf
  intro y hy
  by_contra hn
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn
  rcases hn with hn | hn
  · obtain ⟨x, hx, hxa⟩ := himg.Icc_subset (mem_image_of_mem f hy) (mem_image_of_mem f hy₀)
      ⟨hn, hab.1.le⟩
    exact (hne x hx).1 hxa
  · obtain ⟨x, hx, hxb⟩ := himg.Icc_subset (mem_image_of_mem f hy₀) (mem_image_of_mem f hy)
      ⟨hab.2.le, hn⟩
    exact (hne x hx).2 hxb

theorem lift_add_int_of_eq_one {φ : TDiff} (h : torusMatrix φ = 1) {Φ : ℝ × ℝ → ℝ × ℝ}
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ),
      (Φ (p.1 + m, p.2 + n)).1 =
        (Φ p).1 + ((torusMatrix φ 0 0 * m + torusMatrix φ 0 1 * n : ℤ) : ℝ) ∧
      (Φ (p.1 + m, p.2 + n)).2 =
        (Φ p).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ))
    (p : ℝ × ℝ) (m n : ℤ) : Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n) := by
  obtain ⟨h1, h2⟩ := hdeck p m n
  rw [h] at h1 h2
  refine Prod.ext ?_ ?_
  · rw [h1]; simp
  · rw [h2]; simp

theorem exists_torusLiftDiffeomorph_band (φ : TDiff) {U : Set Torus} (hU : IsOpen U)
    (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) :
    ∃ ε > 0, (∀ p : ℝ × ℝ, |p.2| < ε → torusCover p ∈ U) ∧
      ∃ Φ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
        (∀ p, φ (torusCover p) = torusCover (Φ p)) ∧
        (∀ (p : ℝ × ℝ) (m n : ℤ),
          (Φ (p.1 + m, p.2 + n)).1 =
            (Φ p).1 + ((torusMatrix φ 0 0 * m + torusMatrix φ 0 1 * n : ℤ) : ℝ) ∧
          (Φ (p.1 + m, p.2 + n)).2 =
            (Φ p).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ)) ∧
        ∀ p : ℝ × ℝ, |p.2| < ε → Φ p = p := by
  obtain ⟨ε, hε, hεU⟩ := torusCover_mem_of_band hU hαU
  have h₀ : φ (torusCover 0) = torusCover 0 := hφU _ (hεU 0 (by simpa using hε))
  obtain ⟨Φ, hΦ0, hlift, -, hdeck⟩ := exists_torusLiftDiffeomorph φ h₀
  have hC : Convex ℝ ((univ : Set ℝ) ×ˢ Ioo (-ε) ε) := convex_univ.prod (convex_Ioo _ _)
  have hmem (q : ℝ × ℝ) : q ∈ (univ : Set ℝ) ×ˢ Ioo (-ε) ε ↔ |q.2| < ε := by
    simp [abs_lt]
  have h := lift_eq_self_of_convex Φ.continuous hlift hC
    (fun q hq => hφU _ (hεU q ((hmem q).mp hq))) ((hmem 0).mpr (by simpa using hε)) hΦ0
  exact ⟨ε, hε, hεU, Φ, hlift, hdeck, fun p hp => h p ((hmem p).mpr hp)⟩

theorem betaCircle_cexp' (y : ℝ) : betaCircle (cexp y) = torusCover (0, y) := by
  rw [torusCover_eq]
  exact Prod.ext cexp_zero.symm rfl

theorem torusCover_not_mem_image_of_int {B : Set (ℝ × ℝ)}
    (hB : ∀ q ∈ B, ∀ k : ℤ, q.2 ≠ k) {p : ℝ × ℝ} {k : ℤ} (hp : p.2 = k) :
    torusCover p ∉ torusCover '' B := by
  rintro ⟨q, hq, hqp⟩
  obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp hqp
  apply hB q hq (k + n)
  rw [hmn]
  push_cast
  rw [hp]

theorem exists_isotopic_eqOn_nhds_axes_of_forall_ne (φ : TDiff) (h : torusMatrix φ = 1)
    {U : Set Torus} (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hne : ∀ w, (φ (betaCircle w)).1 ≠ cexp θ) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∃ V : Set Torus, IsOpen V ∧
      range alphaCircle ∪ range betaCircle ⊆ V ∧ ∀ p ∈ V, ψ p = p := by
  obtain ⟨ε, hε, hεU, Φ, hlift, hdeck, hband⟩ := exists_torusLiftDiffeomorph_band φ hU hαU hφU
  have hper := lift_add_int_of_eq_one h hdeck
  set c : ℝ → ℝ × ℝ := fun y => Φ (0, y) with hc
  have hcd : ContDiff ℝ ∞ c := Φ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'h : ε' ≤ 1 / 2 := min_le_right _ _
  have hc0 : ∀ y, |y| < ε → c y = (0, y) := fun y hy => hband (0, y) hy
  have hc1 : ∀ y, |y - 1| < ε → c y = (0, y) := by
    intro y hy
    have h1 := hper (0, y - 1) 0 1
    simp only [Int.cast_zero, add_zero, Int.cast_one, sub_add_cancel] at h1
    change Φ (0, y) = _
    rw [h1, hband (0, y - 1) hy]
    simp
  have hcinj : ∀ s t, c s = c t → s = t := by
    intro s t hst
    have := congrArg Prod.snd (Φ.injective hst)
    exact this
  have hline : ∀ x : ℝ, ∀ k : ℤ, Φ (x, (k : ℝ)) = (x, (k : ℝ)) := by
    intro x k
    have h1 := hper (x, 0) 0 k
    simp only [Int.cast_zero, add_zero, zero_add] at h1
    rw [h1, hband (x, 0) (by simpa using hε)]
    simp
  have hcy : ∀ y ∈ Ioo (0 : ℝ) 1, (c y).2 ∈ Ioo (0 : ℝ) 1 := by
    have hni : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ k : ℤ, (c y).2 ≠ k := by
      intro y hy k hk
      have he : Φ (0, y) = Φ ((c y).1, k) := by
        rw [hline]
        exact Prod.ext rfl hk
      have := congrArg Prod.snd (Φ.injective he)
      simp only at this
      have h1 : (0 : ℝ) < k := this ▸ hy.1
      have h2 : (k : ℝ) < 1 := this ▸ hy.2
      have h1' : 0 < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    have hy₀ : ε' / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine mem_Ioo_of_forall_ne isPreconnected_Ioo
      (continuous_snd.comp hcd.continuous).continuousOn
      (fun y hy => ⟨by exact_mod_cast hni y hy 0, by exact_mod_cast hni y hy 1⟩) hy₀ ?_
    change (c (ε' / 2)).2 ∈ _
    rw [hc0 _ (by rw [abs_of_pos (by linarith)]; linarith)]
    exact hy₀
  have hcx : ∀ y, (c y).1 ∈ Ioo (θ - 1) θ := by
    have hni : ∀ y, ∀ k : ℤ, (c y).1 ≠ θ + k := by
      intro y k hk
      apply hne (cexp y)
      rw [betaCircle_cexp', hlift, torusCover_eq]
      change cexp (c y).1 = cexp θ
      rw [hk, cexp_add_int]
    have hall := mem_Ioo_of_forall_ne (f := fun y => (c y).1) (a := θ - 1) (b := θ)
      isPreconnected_univ (continuous_fst.comp hcd.continuous).continuousOn
      (fun y _ => ⟨by have := hni y (-1); push_cast at this; rwa [← sub_eq_add_neg] at this,
        by simpa using hni y 0⟩) (mem_univ 0) (by
          rw [hc0 0 (by simpa using hε)]
          exact ⟨by linarith [hθ.2], hθ.1⟩)
    exact fun y => hall y (mem_univ y)
  set a : ℝ := θ - 1 with ha
  have ha1 : a + 1 = θ := by rw [ha]; ring
  have h0a : (0 : ℝ) ∈ Ioo a (a + 1) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  set B : Set (ℝ × ℝ) := Ioo a (a + 1) ×ˢ Ioo 0 1 with hB
  let M : ℂ → ℝ × ℝ := fun z => (sqShift a 0 z.re, z.im)
  let N : ℝ × ℝ → ℂ := fun p => (sqShiftInv a 0 p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hNre (p : ℝ × ℝ) : (N p).re = sqShiftInv a 0 p.1 := by simp [N]
  have hNim (p : ℝ × ℝ) : (N p).im = p.2 := by simp [N]
  have hBo : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  have hBinj : InjOn torusCover B := by
    have := injOn_torusCover_box a 0
    rwa [zero_add] at this
  have hMd : ContDiffOn ℝ ∞ M openSquare := by
    refine ContDiffOn.prodMk ?_ Complex.imCLM.contDiff.contDiffOn
    exact (contDiffOn_sqShift a 0).comp Complex.reCLM.contDiff.contDiffOn
      (fun z hz => (mem_openSquare.mp hz).1)
  have hNd : ContDiffOn ℝ ∞ N B := by
    refine ContDiffOn.add ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_sqShiftInv a 0).comp contDiff_fst.contDiffOn (fun p hp => hp.1))
    · exact (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffOn.mul contDiffOn_const
  have hMB : MapsTo M openSquare B := fun z hz => ⟨sqShift_mem _, (mem_openSquare.mp hz).2⟩
  have hNB : MapsTo N B openSquare := fun p hp => by
    rw [mem_openSquare, hNre, hNim]
    exact ⟨sqShiftInv_mem _, hp.2⟩
  have hNM : ∀ z ∈ openSquare, N (M z) = z := by
    intro z hz
    apply Complex.ext
    · rw [hNre]; exact sqShiftInv_sqShift (mem_openSquare.mp hz).1
    · rw [hNim]
  have hMN : ∀ p ∈ B, M (N p) = p := by
    intro p hp
    refine Prod.ext ?_ ?_
    · change sqShift a 0 (N p).re = p.1
      rw [hNre]; exact sqShift_sqShiftInv hp.1
    · change (N p).im = p.2
      rw [hNim]
  let L : ℝ → ℂ := fun t => (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hNL : ∀ t : ℝ, N (0, t) = L t := by
    intro t
    simp only [N, L, sqShiftInv_self]
    push_cast
    ring
  have hML : ∀ t : ℝ, M (L t) = (0, t) := by
    intro t
    refine Prod.ext ?_ ?_
    · change sqShift a 0 (L t).re = 0
      have : (L t).re = 1 / 2 := by simp [L]
      rw [this, sqShift_half h0a]
    · simp [M, L]
  let γ : ℝ → ℂ := fun t => if t ∈ Ioo (0 : ℝ) 1 then N (c t) else L t
  have hcB : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ B := by
    intro t ht
    exact ⟨by rw [ha1]; exact hcx t, hcy t ht⟩
  set W : Set ℝ := Iio ε' ∪ Ioi (1 - ε') with hW
  have hγW : ∀ t ∈ W, γ t = L t := by
    intro t ht
    simp only [γ]
    split_ifs with h01
    · rcases ht with ht | ht
      · rw [hc0 t (by rw [abs_of_pos h01.1]; linarith [mem_Iio.mp ht]), hNL]
      · rw [hc1 t (by
          rw [abs_of_neg (by linarith [h01.2])]; linarith [mem_Ioi.mp ht]), hNL]
    · rfl
  have hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = N (c t) := by
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
      · rw [hc0 0 (by simpa using hε), hNL]
      · rw [hc1 1 (by simpa using hε), hNL]
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
  have hNcd : ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ ∞ (fun s => N (c s)) t := by
    intro t ht
    exact (hNd.contDiffAt (hBo.mem_nhds (hcB t ht))).comp t hcd.contDiffAt
  have hγeq : ∀ t ∈ Ioo (0 : ℝ) 1, γ =ᶠ[𝓝 t] fun s => N (c s) := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp only [γ, hs, ↓reduceIte]
  have hγd : ContDiff ℝ ∞ γ := by
    refine contDiff_iff_contDiffAt.mpr fun t => ?_
    rcases hcover t with ht | ht
    · refine hLd.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hγW s hs
    · exact (hNcd t ht).congr_of_eventuallyEq (hγeq t ht)
  have hinj : InjOn γ (Icc 0 1) := by
    intro s hs t ht hst
    rw [hγc s hs, hγc t ht] at hst
    have him := congrArg Complex.im hst
    have hre := congrArg Complex.re hst
    rw [hNim, hNim] at him
    rw [hNre, hNre] at hre
    have h1 : (c s).1 = (c t).1 := by
      have := congrArg (sqShift a 0) hre
      rwa [sqShift_sqShiftInv (by rw [ha1]; exact hcx s),
        sqShift_sqShiftInv (by rw [ha1]; exact hcx t)] at this
    exact hcinj s t (Prod.ext h1 him)
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
        exact hNB (hcB t ht)
      have hMt : DifferentiableAt ℝ M (γ t) :=
        (hMd.contDiffAt (isOpen_openSquare.mem_nhds hγt)).differentiableAt (by simp)
      have hγt' : HasDerivAt γ 0 t := by
        rw [← h0]
        exact (hγd.differentiable (by simp) t).hasDerivAt
      have h1 : HasDerivAt (fun s => M (γ s)) (fderiv ℝ M (γ t) 0) t :=
        hMt.hasFDerivAt.comp_hasDerivAt t hγt'
      rw [map_zero] at h1
      have he : (fun s => M (γ s)) =ᶠ[𝓝 t] c := by
        filter_upwards [hγeq t ht, isOpen_Ioo.mem_nhds ht] with s hs hs'
        rw [hs]
        exact hMN _ (hcB s hs')
      have h2 : HasDerivAt c 0 t := h1.congr_of_eventuallyEq he.symm
      have h3 : HasDerivAt c (fderiv ℝ Φ (0, t) (0, 1)) t := by
        have hΦd : DifferentiableAt ℝ Φ (0, t) :=
          (Φ.contDiff.differentiable (by simp)) (0, t)
        have hl : HasDerivAt (fun y : ℝ => ((0 : ℝ), y)) ((0 : ℝ), (1 : ℝ)) t :=
          (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
        exact hΦd.hasFDerivAt.comp_hasDerivAt t hl
      have h4 := h2.unique h3
      have h5 := injective_fderiv_of_diffeomorph Φ (0, t)
        (show fderiv ℝ Φ (0, t) (0, 1) = fderiv ℝ Φ (0, t) 0 by rw [← h4, map_zero])
      exact one_ne_zero (congrArg Prod.snd h5)
  have hend : ∀ t, t ≤ ε' / 2 ∨ 1 - ε' / 2 ≤ t → γ t = L t := by
    intro t ht
    refine hγW t ?_
    rcases ht with ht | ht
    · exact Or.inl (by change t < ε'; linarith)
    · exact Or.inr (by change 1 - ε' < t; linarith)
  have hin : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ openSquare := by
    intro t ht
    rw [hγc t (Ioo_subset_Icc_self ht)]
    exact hNB (hcB t ht)
  obtain ⟨Q, hQ, C, hC, hCB, hQC, hQt⟩ := exists_square_transport hBo hBinj hMd hNd hMB hNB hNM
    hMN hγd hinj himm (half_pos hε'pos) hend hin
  have hQφ : ∀ t ∈ Ioo (0 : ℝ) 1, Q (torusCover (0, t)) = φ (torusCover (0, t)) := by
    intro t ht
    have h1 := hQt t ht
    rw [hML, hγc t (Ioo_subset_Icc_self ht), hMN _ (hcB t ht)] at h1
    rw [h1, hlift]
  have hBint : ∀ q ∈ B, ∀ k : ℤ, q.2 ≠ k := by
    intro q hq k hk
    have h1 : (0 : ℝ) < k := hk ▸ hq.2.1
    have h2 : (k : ℝ) < 1 := hk ▸ hq.2.2
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  have hnotC : ∀ p : ℝ × ℝ, ∀ k : ℤ, p.2 = k → torusCover p ∉ C := fun p k hp hpC =>
    torusCover_not_mem_image_of_int hBint hp (hCB hpC)
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
  have hψm : torusMatrix ψ = 1 := by rw [← torusMatrix_eq_of_isotopic hφψ, h]
  have hψβ : ∀ w, (ψ (betaCircle w)).1 = 1 := by
    intro w
    set t : ℝ := Int.fract (rep w) with ht
    have hw : w = cexp t := by
      rw [ht, Int.fract, sub_eq_add_neg, ← Int.cast_neg, cexp_add_int, cexp_rep]
    rw [hw, betaCircle_cexp']
    change (Q.symm (φ (torusCover (0, t)))).1 = 1
    rcases eq_or_lt_of_le (Int.fract_nonneg (rep w)) with h0 | h0
    · rw [← ht] at h0
      rw [← h0]
      have hfix : φ (torusCover (0, 0)) = torusCover (0, 0) :=
        hφU _ (hεU _ (by simpa using hε))
      rw [hfix, hQs _ (hnotC (0, 0) 0 (by simp)), torusCover_eq, cexp_zero]
    · rw [← hQφ t ⟨h0, Int.fract_lt_one _⟩, Q.symm_apply_apply, torusCover_eq, cexp_zero]
  set V₀ : Set Torus := U ∩ Cᶜ with hV₀
  have hV₀o : IsOpen V₀ := hU.inter hC.isClosed.isOpen_compl
  have hαV₀ : range alphaCircle ⊆ V₀ := by
    rintro _ ⟨z, rfl⟩
    have hz : alphaCircle z = torusCover (rep z, 0) := by
      rw [torusCover_eq, cexp_rep, cexp_zero]
      rfl
    refine ⟨hαU ⟨z, rfl⟩, ?_⟩
    rw [hz]
    exact hnotC _ 0 (by simp)
  have hψV₀ : ∀ p ∈ V₀, ψ p = p := by
    rintro p ⟨hpU, hpC⟩
    change Q.symm (φ p) = p
    rw [hφU p hpU, hQs p hpC]
  obtain ⟨χ, hχ, V, hV, hαβV, hχV⟩ :=
    exists_isotopic_eqOn_nhds_axes_of_beta ψ hψm hV₀o hαV₀ hψV₀ hψβ
  exact ⟨χ, hφψ.trans hχ, V, hV, hαβV, hχV⟩

theorem contMDiff_betaCircle : ContMDiff (𝓡 1) torusModel ∞ betaCircle :=
  contMDiff_const.prodMk contMDiff_id

theorem contMDiff_betaHeight (φ : TDiff) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun w => (φ (betaCircle w)).1) :=
  contMDiff_fst.comp (φ.contMDiff.comp contMDiff_betaCircle)

theorem cexp_fract_rep (w : Circle) : cexp (Int.fract (rep w)) = w := by
  rw [Int.fract, sub_eq_add_neg, ← Int.cast_neg, cexp_add_int, cexp_rep]

theorem forall_betaHeight_ne_of_not_hasSameSideArc (φ : TDiff) (h : torusMatrix φ = 1)
    {U : Set Torus} (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p)
    {s : Circle} (hs1 : s ≠ 1)
    (hs : ∀ w, (φ (betaCircle w)).1 = s →
      mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0)
    (hno : ¬ HasSameSideArcIn (fun w => (φ (betaCircle w)).1) s (Icc 0 1)) :
    ∀ w, (φ (betaCircle w)).1 ≠ s := by
  obtain ⟨ε, hε, -, Φ, hlift, hdeck, hband⟩ := exists_torusLiftDiffeomorph_band φ hU hαU hφU
  have hper := lift_add_int_of_eq_one h hdeck
  set g : ℝ → ℝ := fun y => (Φ (0, y)).1 with hgdef
  have hg : ContDiff ℝ ∞ g := Φ.contDiff.fst.comp (contDiff_const.prodMk contDiff_id)
  have hfg (t : ℝ) : (φ (betaCircle (cexp t))).1 = cexp (g t) := by
    rw [betaCircle_cexp', hlift, torusCover_eq]
  set θ : ℝ := Int.fract (rep s) with hθ
  have hσ : cexp θ = s := cexp_fract_rep s
  have hθ0 : θ ≠ 0 := fun h0 => hs1 (by rw [← hσ, h0, cexp_zero])
  have hθ1 : θ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hθ0), Int.fract_lt_one _⟩
  obtain ⟨hh, hcross, hreg, hno'⟩ := cross_hypotheses (contMDiff_betaHeight φ) hg hfg hσ hs hno
  have hg0 : g 0 = 0 := by
    change (Φ (0, 0)).1 = 0
    rw [hband (0, 0) (by simpa using hε)]
  have hg1 : g 1 = 0 := by
    change (Φ (0, 1)).1 = 0
    have h1 := hper (0, 0) 0 1
    simp only [Int.cast_zero, add_zero, Int.cast_one, zero_add] at h1
    rw [h1, hband (0, 0) (by simpa using hε)]
  have hall := forall_ne_int_of_eq_endpoint hh hreg (a := 0) (b := 1)
    (by simp only [hg0, hg1]) (fun k hk => by
      simp only [hg0, zero_sub] at hk
      have h1 : (-1 : ℝ) < k := by rw [← hk]; linarith [hθ1.2]
      have h2 : (k : ℝ) < 0 := by rw [← hk]; linarith [hθ1.1]
      have h1' : -1 < k := by exact_mod_cast h1
      have h2' : k < 0 := by exact_mod_cast h2
      omega) hno'
  intro w hw
  have ht : Int.fract (rep w) ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨k, hk⟩ := (hcross (Int.fract (rep w))).mp (by rw [cexp_fract_rep]; exact hw)
  exact hall _ ht k hk

theorem cexp_half_ne_one : cexp (1 / 2) ≠ 1 := by
  intro h1
  rw [← cexp_zero] at h1
  obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp h1
  have h2 : (2 * n : ℝ) = 1 := by linarith
  have h3 : 2 * n = 1 := by exact_mod_cast h2
  omega

theorem exists_isotopic_eqOn_nhds_axes_of_push
    (hrel : ∀ φ : TDiff, torusMatrix φ = 1 → ∀ U : Set Torus, IsOpen U →
      range alphaCircle ⊆ U → (∀ p ∈ U, φ p = p) → ∀ s : Circle,
      (∀ w, (φ (betaCircle w)).1 = s →
        mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0) →
      HasSameSideArcIn (fun w => (φ (betaCircle w)).1) s (Icc 0 1) →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
        (∃ U' : Set Torus, IsOpen U' ∧ range alphaCircle ⊆ U' ∧ ∀ p ∈ U', ψ p = p) ∧
        (∀ w, (ψ (betaCircle w)).1 = s →
          mfderiv (𝓡 1) (𝓡 1) (fun w => (ψ (betaCircle w)).1) w ≠ 0) ∧
        {w | (ψ (betaCircle w)).1 = s}.ncard < {w | (φ (betaCircle w)).1 = s}.ncard)
    (φ : TDiff) (h : torusMatrix φ = 1) {U : Set Torus} (hU : IsOpen U)
    (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∃ V : Set Torus, IsOpen V ∧
      range alphaCircle ∪ range betaCircle ⊆ V ∧ ∀ p ∈ V, ψ p = p := by
  obtain ⟨s, hs1, hreg⟩ := circle_exists_regular_mem (contMDiff_betaHeight φ)
    (isOpen_compl_singleton (x := (1 : Circle))) ⟨cexp (1 / 2), cexp_half_ne_one⟩
  have hs1' : s ≠ 1 := hs1
  have hθ1 : Int.fract (rep s) ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne (Int.fract_nonneg _) (fun h0 => hs1' ?_), Int.fract_lt_one _⟩
    rw [← cexp_fract_rep s, ← h0, cexp_zero]
  have key : ∀ n : ℕ, ∀ φ : TDiff, torusMatrix φ = 1 →
      (∃ U : Set Torus, IsOpen U ∧ range alphaCircle ⊆ U ∧ ∀ p ∈ U, φ p = p) →
      (∀ w, (φ (betaCircle w)).1 = s →
        mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0) →
      {w | (φ (betaCircle w)).1 = s}.ncard = n →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∃ V : Set Torus, IsOpen V ∧
        range alphaCircle ∪ range betaCircle ⊆ V ∧ ∀ p ∈ V, ψ p = p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro φ h ⟨U, hU, hαU, hφU⟩ hreg hn
      by_cases hss : HasSameSideArcIn (fun w => (φ (betaCircle w)).1) s (Icc 0 1)
      · obtain ⟨ψ, hφψ, hU', hreg', hlt⟩ := hrel φ h U hU hαU hφU s hreg hss
        obtain ⟨χ, hψχ, hrest⟩ := ih _ (hn ▸ hlt) ψ
          (by rw [← torusMatrix_eq_of_isotopic hφψ, h]) hU' hreg' rfl
        exact ⟨χ, hφψ.trans hψχ, hrest⟩
      · refine exists_isotopic_eqOn_nhds_axes_of_forall_ne φ h hU hαU hφU hθ1 ?_
        rw [cexp_fract_rep]
        exact forall_betaHeight_ne_of_not_hasSameSideArc φ h hU hαU hφU hs1' hreg hss
  exact key _ φ h ⟨U, hU, hαU, hφU⟩ hreg rfl

end GC.Seifert
