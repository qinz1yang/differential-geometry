import DifferentialGeometry.Topology.Compactness.UniformBounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set Filter Topology

namespace DifferentialGeometry.Analysis

private theorem mul_abs_sub_le_abs_image_sub_of_le_deriv
    {S : Set ℝ} (hS : Convex ℝ S) {f : ℝ → ℝ}
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) {m : ℝ}
    (hm : ∀ x ∈ S, m ≤ deriv f x) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    m * |y - x| ≤ |f y - f x| := by
  have hbound (x : ℝ) (hx : x ∈ S) (y : ℝ) (hy : y ∈ S) (hxy : x ≤ y) :
      m * |y - x| ≤ |f y - f x| := by
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact (hS.mul_sub_le_image_sub_of_le_deriv
      (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hf z (interior_subset hz)).differentiableWithinAt)
      (fun z hz => hm z (interior_subset hz)) x hx y hy hxy).trans (le_abs_self _)
  rcases le_total x y with hxy | hyx
  · exact hbound x hx y hy hxy
  · simpa only [abs_sub_comm] using hbound y hy x hx hyx

theorem injOn_prod_of_fderiv_bounds
    {S T : Set ℝ} (hS : Convex ℝ S) (hT : Convex ℝ T)
    {F : (ℝ × ℝ) → ℝ × ℝ}
    (hF : ∀ z ∈ S ×ˢ T, DifferentiableAt ℝ F z)
    {p q M ε : ℝ} (hq : 0 < q) (hsmall : M * ε < p * q)
    (hPu : ∀ z ∈ S ×ˢ T, p ≤ (fderiv ℝ F z (1, 0)).1)
    (hPt : ∀ z ∈ S ×ˢ T, |(fderiv ℝ F z (0, 1)).1| ≤ M)
    (hHu : ∀ z ∈ S ×ˢ T, |(fderiv ℝ F z (1, 0)).2| ≤ ε)
    (hHt : ∀ z ∈ S ×ˢ T, (fderiv ℝ F z (0, 1)).2 ≤ -q) :
    InjOn F (S ×ˢ T) := by
  have hdu (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun u => F (u, t)) (fderiv ℝ F (u, t) (1, 0)) u := by
    exact (hF (u, t) ⟨hu, ht⟩).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u t))
  have hdt (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun t => F (u, t)) (fderiv ℝ F (u, t) (0, 1)) t := by
    exact (hF (u, t) ⟨hu, ht⟩).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t u).prodMk (hasDerivAt_id t))
  have hdu₁ (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun u => (F (u, t)).1) (fderiv ℝ F (u, t) (1, 0)).1 u :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt u (hdu u t hu ht)
  have hdu₂ (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun u => (F (u, t)).2) (fderiv ℝ F (u, t) (1, 0)).2 u :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt u (hdu u t hu ht)
  have hdt₁ (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun t => (F (u, t)).1) (fderiv ℝ F (u, t) (0, 1)).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hdt u t hu ht)
  have hdt₂ (u t : ℝ) (hu : u ∈ S) (ht : t ∈ T) :
      HasDerivAt (fun t => (F (u, t)).2) (fderiv ℝ F (u, t) (0, 1)).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hdt u t hu ht)
  intro x hx y hy hxy
  have hM : 0 ≤ M := (abs_nonneg _).trans (hPt x hx)
  have hP : p * |y.1 - x.1| ≤ M * |y.2 - x.2| := by
    have hlo := mul_abs_sub_le_abs_image_sub_of_le_deriv hS (m := p)
      (fun u hu => (hdu₁ u x.2 hu hx.2).differentiableAt)
      (fun u hu => by rw [(hdu₁ u x.2 hu hx.2).deriv]; exact hPu (u, x.2) ⟨hu, hx.2⟩)
      hx.1 hy.1
    have hhi := hT.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hdt₁ y.1 t hy.1 ht).differentiableAt)
      (fun t ht => by rw [(hdt₁ y.1 t hy.1 ht).deriv]; exact hPt (y.1, t) ⟨hy.1, ht⟩)
      hx.2 hy.2
    have heq : (F x).1 = (F y).1 := congrArg Prod.fst hxy
    simp only [Real.norm_eq_abs] at hhi
    rw [heq] at hlo
    rw [abs_sub_comm (F (y.1, x.2)).1 (F y).1] at hlo
    exact hlo.trans hhi
  have hH : q * |y.2 - x.2| ≤ ε * |y.1 - x.1| := by
    have hlo := mul_abs_sub_le_abs_image_sub_of_le_deriv hT (m := q)
      (fun t ht => (hdt₂ y.1 t hy.1 ht).neg.differentiableAt)
      (fun t ht => by
        rw [(hdt₂ y.1 t hy.1 ht).neg.deriv]
        have h := hHt (y.1, t) ⟨hy.1, ht⟩
        linarith)
      hx.2 hy.2
    have hhi := hS.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hdu₂ u x.2 hu hx.2).differentiableAt)
      (fun u hu => by rw [(hdu₂ u x.2 hu hx.2).deriv]; exact hHu (u, x.2) ⟨hu, hx.2⟩)
      hx.1 hy.1
    have heq : (F x).2 = (F y).2 := congrArg Prod.snd hxy
    simp only [Real.norm_eq_abs] at hhi
    have hle : |-(F y).2 - -(F (y.1, x.2)).2| =
        |(F (y.1, x.2)).2 - (F x).2| := by rw [heq]; congr 1; ring
    change q * |y.2 - x.2| ≤ |-(F y).2 - -(F (y.1, x.2)).2| at hlo
    rw [hle] at hlo
    exact hlo.trans hhi
  have hmul : p * q * |y.1 - x.1| ≤ M * ε * |y.1 - x.1| := by
    calc
      p * q * |y.1 - x.1| = q * (p * |y.1 - x.1|) := by ring
      _ ≤ q * (M * |y.2 - x.2|) := mul_le_mul_of_nonneg_left hP hq.le
      _ = M * (q * |y.2 - x.2|) := by ring
      _ ≤ M * (ε * |y.1 - x.1|) := mul_le_mul_of_nonneg_left hH hM
      _ = M * ε * |y.1 - x.1| := by ring
  have hu : |y.1 - x.1| = 0 := by
    by_contra h
    exact hsmall.not_ge (le_of_mul_le_mul_right hmul (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)))
  have ht : |y.2 - x.2| = 0 := by
    rw [hu, mul_zero] at hH
    nlinarith [abs_nonneg (y.2 - x.2)]
  exact Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp hu)).symm
    (sub_eq_zero.mp (abs_eq_zero.mp ht)).symm

theorem exists_injOn_prod_reparametrization
    {S : Set ℝ} (hS : IsCompact S) (hconv : Convex ℝ S)
    {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {U : Set (ℝ × (ℝ × ℝ))}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) {a : ℝ}
    (hbase : ∀ u ∈ S, (u, a, a) ∈ U)
    (hdu : ∀ u ∈ S, fderiv ℝ F (u, a, a) (1, 0, 0) = (1, 0))
    (htrans : ∀ u ∈ S, ∀ v ∈ Icc (0 : ℝ) 1,
      (fderiv ℝ F (u, a, a) (0, v, 1)).2 < 0) :
    ∃ δ > 0, ∀ h : ℝ → ℝ,
      (∀ t ∈ Icc (a - δ) (a + δ), DifferentiableAt ℝ h t) →
      MapsTo h (Icc (a - δ) (a + δ)) (Icc (a - δ) (a + δ)) →
      (∀ t ∈ Icc (a - δ) (a + δ), deriv h t ∈ Icc (0 : ℝ) 1) →
      InjOn (fun z : ℝ × ℝ => F (z.1, h z.2, z.2))
        (S ×ˢ Icc (a - δ) (a + δ)) ∧
      ∀ z ∈ S ×ˢ Icc (a - δ) (a + δ),
        (z.1, h z.2, z.2) ∈ U ∧
        Function.Bijective (fderiv ℝ (fun w : ℝ × ℝ => F (w.1, h w.2, w.2)) z) ∧
        (fderiv ℝ (fun w : ℝ × ℝ => F (w.1, h w.2, w.2)) z (0, 1)).2 < 0 := by
  let K := S ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := hS.prod isCompact_Icc
  let A : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ × ℝ :=
    fun z => fderiv ℝ F (z.1.1, z.2)
  let V : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun z => A z (0, z.1.2, 1)
  let W : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun z => A z (1, 0, 0)
  have hA (w : ℝ × ℝ) (hw : w ∈ K) : ContinuousAt A (w, (a, a)) := by
    apply ((hF.contDiffAt (hU.mem_nhds (hbase w.1 hw.1))).continuousAt_fderiv (by norm_num)).comp
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1.1, z.2))
    exact continuousAt_fst.fst.prodMk continuousAt_snd
  have hV (w : ℝ × ℝ) (hw : w ∈ K) : ContinuousAt V (w, (a, a)) :=
    (hA w hw).clm_apply (continuousAt_const.prodMk (continuousAt_fst.snd.prodMk continuousAt_const))
  have hW (w : ℝ × ℝ) (hw : w ∈ K) : ContinuousAt W (w, (a, a)) :=
    (hA w hw).clm_apply continuousAt_const
  obtain ⟨q, hq, N, hN, hnormal⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound hK
      (d := fun z => -(V z).2) (q₀ := (a, a))
      (fun w hw => (hV w hw).snd.neg)
      (fun w hw => neg_pos.mpr (htrans w.1 hw.1 w.2 hw.2))
  have hc : ContinuousOn (fun w : ℝ × ℝ => (V (w, (a, a))).1) K := by
    intro w hw
    exact ((hV w hw).fst.comp (f := fun v : ℝ × ℝ => (v, (a, a)))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hc
  let M := max M₀ 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right M₀ 0]
  let ε := q / (4 * M)
  have hε : 0 < ε := div_pos hq (by positivity)
  have hsmall : M * ε < (1 / 2 : ℝ) * q := by
    dsimp [ε]
    field_simp
    nlinarith
  let Ω : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {z |
    (z.1.1, z.2) ∈ U ∧ (1 / 2 : ℝ) < (W z).1 ∧ |(V z).1| < M ∧ |(W z).2| < ε}
  have hnear : Ω ∈ (𝓝ˢ K) ×ˢ 𝓝 (a, a) := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro w hw
    rw [← nhds_prod_eq]
    have hmem : ∀ᶠ z : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 (w, (a, a)), (z.1.1, z.2) ∈ U :=
      (continuousAt_fst.fst.prodMk continuousAt_snd).preimage_mem_nhds
        (hU.mem_nhds (hbase w.1 hw.1))
    have hw₀ : W (w, (a, a)) = (1, 0) := hdu w.1 hw.1
    have htan : ∀ᶠ z in 𝓝 (w, (a, a)), (1 / 2 : ℝ) < (W z).1 :=
      (hW w hw).fst.eventually (Ioi_mem_nhds (by simpa only [hw₀] using (show (1 / 2 : ℝ) < 1 by norm_num)))
    have hvel : ∀ᶠ z in 𝓝 (w, (a, a)), |(V z).1| < M :=
      (hV w hw).fst.abs.eventually (Iio_mem_nhds (by
        have hb := hM₀ w hw
        rw [Real.norm_eq_abs] at hb
        dsimp [M]
        linarith [le_max_left M₀ 0]))
    have hcross : ∀ᶠ z in 𝓝 (w, (a, a)), |(W z).2| < ε :=
      (hW w hw).snd.abs.eventually (Iio_mem_nhds (by simpa only [hw₀, abs_zero] using hε))
    exact hmem.and (htan.and (hvel.and hcross))
  obtain ⟨Z, hZ, N', hN', hZN⟩ := mem_prod_iff.mp hnear
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hN hN')
  let δ := ρ / 2
  have hδ : 0 < δ := half_pos hρ
  have hin (s t : ℝ) (hs : s ∈ Icc (a - δ) (a + δ))
      (ht : t ∈ Icc (a - δ) (a + δ)) : (s, t) ∈ N ∩ N' := by
    apply hρsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor <;> apply lt_of_le_of_lt _ (half_lt_self hρ)
    · change |s - a| ≤ ρ / 2
      have hs' : a - ρ / 2 ≤ s ∧ s ≤ a + ρ / 2 := hs
      exact abs_le.mpr ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    · change |t - a| ≤ ρ / 2
      have ht' : a - ρ / 2 ≤ t ∧ t ≤ a + ρ / 2 := ht
      exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  refine ⟨δ, hδ, ?_⟩
  intro h hh hmap hder
  let G : ℝ × ℝ → ℝ × ℝ := fun z => F (z.1, h z.2, z.2)
  have hb (u t : ℝ) (hu : u ∈ S) (ht : t ∈ Icc (a - δ) (a + δ)) :
      ((u, deriv h t), (h t, t)) ∈ Ω :=
    hZN ⟨subset_of_mem_nhdsSet hZ ⟨hu, hder t ht⟩, (hin (h t) t (hmap ht) ht).2⟩
  have hG (z : ℝ × ℝ) (hz : z ∈ S ×ˢ Icc (a - δ) (a + δ)) :
      HasFDerivAt G ((fderiv ℝ F (z.1, h z.2, z.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          (((ContinuousLinearMap.toSpanSingleton ℝ (deriv h z.2)).comp
            (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
            (ContinuousLinearMap.snd ℝ ℝ ℝ)))) z := by
    have hloc := (hF.contDiffAt (hU.mem_nhds (hb z.1 z.2 hz.1 hz.2).1)).differentiableAt (by norm_num)
    apply hloc.hasFDerivAt.comp z
    have hd := (hh z.2 hz.2).hasDerivAt.hasFDerivAt.comp z
      (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ z)
    exact hasFDerivAt_fst.prodMk (hd.prodMk hasFDerivAt_snd)
  have hPu (z) (hz : z ∈ S ×ˢ Icc (a - δ) (a + δ)) :
      (1 / 2 : ℝ) ≤ (fderiv ℝ G z (1, 0)).1 := by
    rw [(hG z hz).fderiv]
    simpa [W, A] using (hb z.1 z.2 hz.1 hz.2).2.1.le
  have hPt (z) (hz : z ∈ S ×ˢ Icc (a - δ) (a + δ)) :
      |(fderiv ℝ G z (0, 1)).1| ≤ M := by
    rw [(hG z hz).fderiv]
    simpa [V, A] using (hb z.1 z.2 hz.1 hz.2).2.2.1.le
  have hHu (z) (hz : z ∈ S ×ˢ Icc (a - δ) (a + δ)) :
      |(fderiv ℝ G z (1, 0)).2| ≤ ε := by
    rw [(hG z hz).fderiv]
    simpa [W, A] using (hb z.1 z.2 hz.1 hz.2).2.2.2.le
  have hHt (z) (hz : z ∈ S ×ˢ Icc (a - δ) (a + δ)) :
      (fderiv ℝ G z (0, 1)).2 ≤ -q := by
    rw [(hG z hz).fderiv]
    have hn := hnormal (z.1, deriv h z.2) ⟨hz.1, hder z.2 hz.2⟩
      (h z.2, z.2) (hin (h z.2) z.2 (hmap hz.2) hz.2).1
    simpa [V, A] using (neg_le_neg hn)
  refine ⟨injOn_prod_of_fderiv_bounds hconv (convex_Icc _ _)
    (fun z hz => (hG z hz).differentiableAt) hq hsmall hPu hPt hHu hHt, ?_⟩
  intro z hz
  let L := fderiv ℝ G z
  have hLin : InjOn L ((univ : Set ℝ) ×ˢ univ) := by
    apply injOn_prod_of_fderiv_bounds convex_univ convex_univ
      (fun w _ => L.differentiableAt) hq hsmall
    · intro w _
      simpa only [L.fderiv] using hPu z hz
    · intro w _
      simpa only [L.fderiv] using hPt z hz
    · intro w _
      simpa only [L.fderiv] using hHu z hz
    · intro w _
      simpa only [L.fderiv] using hHt z hz
  have hinj : Function.Injective L := by simpa only [univ_prod_univ, injOn_univ] using hLin
  exact ⟨(hb z.1 z.2 hz.1 hz.2).1,
    ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩,
    (hHt z hz).trans_lt (neg_neg_of_pos hq)⟩


end DifferentialGeometry.Analysis
