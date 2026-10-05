import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceSign
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# FC39 GROUP G, global face functions (F4 core): positive combinations of defining functions

Lane FC39-G-GFF(b), external draft 58 §二 F4, disposition D58-3. Generic first-order facts on a
boundaryless surface `M` (model `𝓡 2`) used to glue local defining functions of one face by
NON-NEGATIVE weights (finitely many smooth bumps; no partition of unity, no division):

* `not_pos_of_sublevel_GGFF`, `dirDeriv_neg_of_sublevel_GGFF` — **comparison**: two functions
  vanishing at `z` whose sublevel sets `{· ≤ 0}` both equal a set `K` near `z`, the second one
  regular at `z`: every direction of descent of the first is a direction of descent of the second
  (chart lines of `FC39GTraceSign.lean`);
* `hasMFDerivAt_mul_of_tsupport_GGFF`, `hasMFDerivAt_sum_mul_GGFF` — the derivative of
  `∑ β_j ψ_j` at a common zero of the `ψ_j` (on their domains) is `∑ β_j(z) dψ_j(z)`;
* `mfderiv_sum_mul_sub_ne_zero_GGFF` — **regularity of the glued function** at a common zero: all
  active `ψ_j` regular with the sublevel `K` near `z`, one active weight positive, the remainder
  `G` vanishing near `z`;
* `sum_mul_sub_nonpos_GGFF`, `sum_mul_sub_neg_GGFF`, `sum_mul_sub_eq_zero_GGFF`,
  `sum_mul_pos_GGFF` — the signs of the glued function on and off `K`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-! ## Signs of the glued function -/

section Signs

variable {X : Type*} [TopologicalSpace X]

/-- On `K`, the glued function is non-positive (every `ψ_j ≤ 0` on `K ∩ U j`, `G ≥ 0`). -/
theorem sum_mul_sub_nonpos_GGFF {J : Type*} [Fintype J] {K : Set X} (β ψ : J → X → ℝ)
    (U : J → Set X) (hβU : ∀ j, tsupport (β j) ⊆ U j) (hβnn : ∀ j u, 0 ≤ β j u)
    (hψK : ∀ j, ∀ c ∈ U j, c ∈ K → ψ j c ≤ 0) {G : X → ℝ} (hGnn : ∀ u, 0 ≤ G u) {c : X}
    (hc : c ∈ K) : ∑ j, β j c * ψ j c - G c ≤ 0 := by
  have : ∑ j, β j c * ψ j c ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    by_cases hj : β j c = 0
    · rw [hj, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hβnn j c)
        (hψK j c (hβU j (subset_tsupport _ hj)) hc)
  linarith [hGnn c]

/-- On `K`, the glued function is negative where one weight is positive and its `ψ_j` is negative,
or where `G` is positive. -/
theorem sum_mul_sub_neg_GGFF {J : Type*} [Fintype J] {K : Set X} (β ψ : J → X → ℝ)
    (U : J → Set X) (hβU : ∀ j, tsupport (β j) ⊆ U j) (hβnn : ∀ j u, 0 ≤ β j u)
    (hψK : ∀ j, ∀ c ∈ U j, c ∈ K → ψ j c ≤ 0) {G : X → ℝ} (hGnn : ∀ u, 0 ≤ G u) {c : X}
    (hc : c ∈ K) (hneg : (∃ j, 0 < β j c ∧ ψ j c < 0) ∨ 0 < G c) :
    ∑ j, β j c * ψ j c - G c < 0 := by
  classical
  have hle : ∀ j, β j c * ψ j c ≤ 0 := by
    intro j
    by_cases hj : β j c = 0
    · rw [hj, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hβnn j c)
        (hψK j c (hβU j (subset_tsupport _ hj)) hc)
  rcases hneg with ⟨j₀, hβ₀, hψ₀⟩ | hG
  · have hlt : β j₀ c * ψ j₀ c < 0 := mul_neg_of_pos_of_neg hβ₀ hψ₀
    have : ∑ j, β j c * ψ j c < 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
      have : ∑ j ∈ Finset.univ.erase j₀, β j c * ψ j c ≤ 0 :=
        Finset.sum_nonpos fun j _ => hle j
      linarith
    linarith [hGnn c]
  · have : ∑ j, β j c * ψ j c ≤ 0 := Finset.sum_nonpos fun j _ => hle j
    linarith

/-- The glued function vanishes where every `ψ_j` vanishes (on its domain) and `G` vanishes. -/
theorem sum_mul_sub_eq_zero_GGFF {J : Type*} [Fintype J] (β ψ : J → X → ℝ) (U : J → Set X)
    (hβU : ∀ j, tsupport (β j) ⊆ U j) {G : X → ℝ} {c : X} (hψ0 : ∀ j, c ∈ U j → ψ j c = 0)
    (hG0 : G c = 0) : ∑ j, β j c * ψ j c - G c = 0 := by
  rw [hG0, sub_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : β j c = 0
  · rw [hj, zero_mul]
  · rw [hψ0 j (hβU j (subset_tsupport _ hj)), mul_zero]

omit [TopologicalSpace X] in
/-- The glued function is positive off `K` where every active `ψ_j` is positive and one weight is
positive (`G` vanishing there). -/
theorem sum_mul_pos_GGFF {J : Type*} [Fintype J] (β ψ : J → X → ℝ) (hβnn : ∀ j u, 0 ≤ β j u)
    {c : X} (hpos : ∀ j, 0 < β j c → 0 < ψ j c) {j₀ : J} (hj₀ : 0 < β j₀ c) :
    0 < ∑ j, β j c * ψ j c := by
  classical
  have hle : ∀ j, 0 ≤ β j c * ψ j c := by
    intro j
    rcases (hβnn j c).eq_or_lt with hj | hj
    · rw [← hj, zero_mul]
    · exact (mul_pos hj (hpos j hj)).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have : 0 ≤ ∑ j ∈ Finset.univ.erase j₀, β j c * ψ j c := Finset.sum_nonneg fun j _ => hle j
  linarith [mul_pos hj₀ (hpos j₀ hj₀)]

end Signs

/-! ## Comparison of two defining functions of one sublevel set -/

/-- Along a chart line on which `f` (vanishing at `z`) has positive derivative, `f` is eventually
positive to the right. -/
theorem eventually_pos_chartLine_GGFF {z : M} (v : EuclideanSpace ℝ (Fin 2)) {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f z) (hf0 : f z = 0)
    (hv : 0 < dirDeriv_GTR (𝓡 2) f z v) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f (chartLine_GTR (𝓡 2) z v t) := by
  have hneg : dirDeriv_GTR (𝓡 2) (-f) z v < 0 := by
    unfold dirDeriv_GTR mderivR_GTR
    rw [mfderiv_neg]
    change -(dirDeriv_GTR (𝓡 2) f z v) < 0
    linarith
  have h := eventually_lt_chartLine_GTR (BoundarylessManifold.isInteriorPoint (I := 𝓡 2)) v
    hf.neg hneg
  filter_upwards [h] with t ht
  simp only [Pi.neg_apply, hf0, neg_zero, neg_lt_zero] at ht
  exact ht

/-- **Comparison (weak form).** If `φ`, `ψ` vanish at `z` and both cut out `K` as `{· ≤ 0}` near
`z`, a direction of descent of `φ` is not a direction of ascent of `ψ`. -/
theorem not_pos_of_sublevel_GGFF {K : Set M} {z : M} {φ ψ : M → ℝ}
    (hφd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) φ z) (hψd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) ψ z)
    (hφ0 : φ z = 0) (hψ0 : ψ z = 0) (hφK : ∀ᶠ u in 𝓝 z, u ∈ K ↔ φ u ≤ 0)
    (hψK : ∀ᶠ u in 𝓝 z, u ∈ K ↔ ψ u ≤ 0) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : dirDeriv_GTR (𝓡 2) φ z v < 0) : ¬ 0 < dirDeriv_GTR (𝓡 2) ψ z v := by
  intro hpos
  have h1 := eventually_lt_chartLine_GTR (BoundarylessManifold.isInteriorPoint (I := 𝓡 2)) v
    hφd hv
  have h2 := eventually_pos_chartLine_GGFF v hψd hψ0 hpos
  have hT := (tendsto_chartLine_GTR (I := 𝓡 2) z v).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
    (h1.and (h2.and ((hT.eventually hφK).and (hT.eventually hψK)))).exists
  rw [hφ0] at ht1
  have hK : chartLine_GTR (𝓡 2) z v t ∈ K := ht3.2 ht1.le
  have := ht4.1 hK
  linarith

/-- **Comparison (strict form).** If moreover `ψ` is regular at `z`, every direction of descent of
`φ` is a direction of descent of `ψ`. -/
theorem dirDeriv_neg_of_sublevel_GGFF {K : Set M} {z : M} {φ ψ : M → ℝ}
    (hφd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) φ z) (hψd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) ψ z)
    (hφ0 : φ z = 0) (hψ0 : ψ z = 0) (hψr : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ψ z ≠ 0)
    (hφK : ∀ᶠ u in 𝓝 z, u ∈ K ↔ φ u ≤ 0) (hψK : ∀ᶠ u in 𝓝 z, u ∈ K ↔ ψ u ≤ 0)
    {v : EuclideanSpace ℝ (Fin 2)} (hv : dirDeriv_GTR (𝓡 2) φ z v < 0) :
    dirDeriv_GTR (𝓡 2) ψ z v < 0 := by
  by_contra hge
  push Not at hge
  obtain ⟨u, hu⟩ := exists_dirDeriv_neg_GTR hψr
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), dirDeriv_GTR (𝓡 2) φ z (v + s • (-u)) < 0 := by
    have hc : Continuous fun s : ℝ => dirDeriv_GTR (𝓡 2) φ z (v + s • (-u)) := by
      simp only [dirDeriv_add_smul_GTR]
      exact continuous_const.add (continuous_id.mul continuous_const)
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hv)
  have hev' : ∀ᶠ s in 𝓝[>] (0 : ℝ), dirDeriv_GTR (𝓡 2) φ z (v + s • (-u)) < 0 :=
    nhdsWithin_le_nhds hev
  obtain ⟨s, hs, hspos⟩ := (hev'.and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  apply not_pos_of_sublevel_GGFF hφd hψd hφ0 hψ0 hφK hψK hs
  rw [dirDeriv_add_smul_GTR, dirDeriv_neg_GTR]
  have hs' : (0 : ℝ) < s := hspos
  nlinarith

/-! ## The derivative of a glued function -/

/-- The derivative of `β ψ` at a point where `ψ` vanishes (if the point is in the domain `U` of
`ψ`, which contains the closed support of `β`). -/
theorem hasMFDerivAt_mul_of_tsupport_GGFF {β ψ : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hβU : tsupport β ⊆ U) (hβ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ β)
    (hψ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ ψ U) {z : M} (hz0 : z ∈ U → ψ z = 0) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun u => β u * ψ u) z (β z • mderivR_GTR (𝓡 2) ψ z) := by
  by_cases hzU : z ∈ U
  · have hψd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) ψ z :=
      ((hψ z hzU).contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp)
    have hβd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) β z := (hβ z).mdifferentiableAt (by simp)
    have h := hβd.hasMFDerivAt.mul hψd.hasMFDerivAt
    refine h.congr_mfderiv ?_
    ext w
    rw [hz0 hzU]
    change β z * mderivR_GTR (𝓡 2) ψ z w + 0 * mderivR_GTR (𝓡 2) β z w =
      β z * mderivR_GTR (𝓡 2) ψ z w
    ring
  · have hz : z ∉ tsupport β := fun h => hzU (hβU h)
    have hev : (fun u => β u * ψ u) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with u hu
      simp only [Pi.zero_apply] at hu
      simp [hu]
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
    exact (hasMFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hev

/-- The derivative of `∑ β_j ψ_j` at a common zero of the `ψ_j` (on their domains). -/
theorem hasMFDerivAt_sum_mul_GGFF {J : Type*} [Fintype J] (β ψ : J → M → ℝ) (U : J → Set M)
    (hU : ∀ j, IsOpen (U j)) (hβU : ∀ j, tsupport (β j) ⊆ U j)
    (hβ : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (β j))
    (hψ : ∀ j, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (ψ j) (U j)) {z : M}
    (hz0 : ∀ j, z ∈ U j → ψ j z = 0) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun u => ∑ j, β j u * ψ j u) z
      (∑ j, β j z • mderivR_GTR (𝓡 2) (ψ j) z) := by
  have h := HasMFDerivAt.sum (t := Finset.univ) (f := fun j u => β j u * ψ j u)
    (fun j _ => hasMFDerivAt_mul_of_tsupport_GGFF (hU j) (hβU j) (hβ j) (hψ j) (hz0 j))
  have hfun : (fun u => ∑ j, β j u * ψ j u) = ∑ j, (fun u => β j u * ψ j u) := by
    ext u
    simp [Finset.sum_apply]
  rw [hfun]
  exact h

/-- **Regularity of the glued function** at a common zero `z`: every active `ψ_j` (`z ∈ U j`) is
regular at `z` and cuts out `K` as `{ψ_j ≤ 0}` near `z`; one weight is positive at `z`; the
remainder `G` vanishes near `z`. -/
theorem mfderiv_sum_mul_sub_ne_zero_GGFF {J : Type*} [Fintype J] {K : Set M}
    (β ψ : J → M → ℝ) (U : J → Set M) (hU : ∀ j, IsOpen (U j))
    (hβU : ∀ j, tsupport (β j) ⊆ U j) (hβ : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (β j))
    (hψ : ∀ j, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (ψ j) (U j)) (hβnn : ∀ j u, 0 ≤ β j u)
    {G : M → ℝ} {z : M} (hG : G =ᶠ[𝓝 z] 0) (hz0 : ∀ j, z ∈ U j → ψ j z = 0)
    (hreg : ∀ j, z ∈ U j → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (ψ j) z ≠ 0)
    (hsign : ∀ j, z ∈ U j → ∀ᶠ u in 𝓝 z, u ∈ K ↔ ψ j u ≤ 0) {j₀ : J} (hj₀ : 0 < β j₀ z) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun u => ∑ j, β j u * ψ j u - G u) z ≠ 0 := by
  classical
  have hmemU : ∀ j, 0 < β j z → z ∈ U j := fun j hj =>
    hβU j (subset_tsupport _ (ne_of_gt hj))
  have hψd : ∀ j, z ∈ U j → MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (ψ j) z := fun j hj =>
    ((hψ j z hj).contMDiffAt ((hU j).mem_nhds hj)).mdifferentiableAt (by simp)
  have hj₀U := hmemU j₀ hj₀
  obtain ⟨w, hw⟩ := exists_dirDeriv_neg_GTR (hreg j₀ hj₀U)
  have h1 := hasMFDerivAt_sum_mul_GGFF β ψ U hU hβU hβ hψ hz0
  have h2 : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) G z (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
    (hasMFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hG
  have h3 : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun u => ∑ j, β j u * ψ j u - G u) z
      ((∑ j, β j z • mderivR_GTR (𝓡 2) (ψ j) z) - (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) :=
    h1.sub h2
  rw [h3.mfderiv]
  intro h0
  have happ : ((∑ j, β j z • mderivR_GTR (𝓡 2) (ψ j) z) -
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) w = 0 := by
    rw [h0]
    rfl
  simp only [sub_zero, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at happ
  have hterm : ∀ j, β j z * mderivR_GTR (𝓡 2) (ψ j) z w ≤ 0 := by
    intro j
    rcases (hβnn j z).eq_or_lt with hj | hj
    · rw [← hj, zero_mul]
    · have hjU := hmemU j hj
      have hlt : dirDeriv_GTR (𝓡 2) (ψ j) z w < 0 :=
        dirDeriv_neg_of_sublevel_GGFF (hψd j₀ hj₀U) (hψd j hjU) (hz0 j₀ hj₀U) (hz0 j hjU)
          (hreg j hjU) (hsign j₀ hj₀U) (hsign j hjU) hw
      exact (mul_neg_of_pos_of_neg hj hlt).le
  have hlt₀ : β j₀ z * mderivR_GTR (𝓡 2) (ψ j₀) z w < 0 := mul_neg_of_pos_of_neg hj₀ hw
  have hsum : ∑ j, β j z * mderivR_GTR (𝓡 2) (ψ j) z w < 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have : ∑ j ∈ Finset.univ.erase j₀, β j z * mderivR_GTR (𝓡 2) (ψ j) z w ≤ 0 :=
      Finset.sum_nonpos fun j _ => hterm j
    linarith
  linarith

end GC.GraphManifold.Assembly.FC39P0
