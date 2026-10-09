import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonMinimal

/-!
# Lifts of torus diffeomorphisms with matrix one

Plumbing for the bigon pushes of lane MC2. A torus diffeomorphism with matrix one lifts to a
diffeomorphism `Φ` of the plane commuting with the integer translations; its derivative is
injective, so the lifted curves `t ↦ Φ (t, y)` and `w ↦ Φ (x, w)` are immersions. A circle map
with a smooth real lift has nonzero lift derivative wherever its manifold derivative is nonzero.
A real function with nonzero derivative at `t` takes larger values arbitrarily close to `t`, and
with positive derivative it is below `h t` just left of `t` and above it just right of `t`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

section Deriv

variable {h : ℝ → ℝ} {d t : ℝ}

theorem eventually_lt_right_of_hasDerivAt_pos (hd : HasDerivAt h d t) (hpos : 0 < d) :
    ∀ᶠ u in 𝓝[>] t, h t < h u := by
  have hs : Tendsto (slope h t) (𝓝[>] t) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun u hu => ne_of_gt hu)
  filter_upwards [hs.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with u hu hut
  rw [slope_def_field] at hu
  have hut' : 0 < u - t := sub_pos.mpr hut
  have := (div_pos_iff.mp hu).resolve_right fun h' => absurd h'.2 (not_lt.mpr hut'.le)
  linarith [this.1]

theorem eventually_lt_left_of_hasDerivAt_pos (hd : HasDerivAt h d t) (hpos : 0 < d) :
    ∀ᶠ u in 𝓝[<] t, h u < h t := by
  have hs : Tendsto (slope h t) (𝓝[<] t) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun u hu => ne_of_lt hu)
  filter_upwards [hs.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with u hu hut
  rw [slope_def_field] at hu
  have hut' : u - t < 0 := sub_neg.mpr hut
  have := (div_pos_iff.mp hu).resolve_left fun h' => absurd h'.2 (not_lt.mpr hut'.le)
  linarith [this.1]

theorem exists_lt_of_hasDerivAt_ne (hd : HasDerivAt h d t) (hne : d ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) : ∃ u ∈ Ioo (t - δ) (t + δ), h t < h u := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hd' : HasDerivAt (fun u => -h u) (-d) t := hd.neg
    obtain ⟨u, hu, hu'⟩ := ((eventually_lt_left_of_hasDerivAt_pos hd' (by linarith)).and
      (Ioo_mem_nhdsLT (show t - δ < t by linarith))).exists
    exact ⟨u, ⟨hu'.1, by linarith [hu'.2]⟩, by linarith⟩
  · obtain ⟨u, hu, hu'⟩ := ((eventually_lt_right_of_hasDerivAt_pos hd hpos).and
      (Ioo_mem_nhdsGT (show t < t + δ by linarith))).exists
    exact ⟨u, ⟨by linarith [hu'.1], hu'.2⟩, hu⟩

theorem exists_Ioo_of_eventually_nhdsLT {P : ℝ → Prop} (hP : ∀ᶠ u in 𝓝[<] t, P u) :
    ∃ δ > 0, ∀ u ∈ Ioo (t - δ) t, P u := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hP
  exact ⟨t - l, sub_pos.mpr hl, fun u hu => hsub ⟨by linarith [hu.1], hu.2⟩⟩

theorem exists_Ioo_of_eventually_nhdsGT {P : ℝ → Prop} (hP : ∀ᶠ u in 𝓝[>] t, P u) :
    ∃ δ > 0, ∀ u ∈ Ioo t (t + δ), P u := by
  obtain ⟨r, hr, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hP
  exact ⟨r - t, sub_pos.mpr hr, fun u hu => hsub ⟨hu.1, by linarith [hu.2]⟩⟩

end Deriv

theorem hasDerivAt_fst_comp {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun u => (γ u).1) γ'.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_snd_comp {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun u => (γ u).2) γ'.2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem fderiv_injective_of_diffeomorph (Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ Φ p) := by
  have h1 : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have h2 : ContDiff ℝ ∞ Φ.symm := contMDiff_iff_contDiff.mp Φ.symm.contMDiff
  have hd1 := (h1.differentiable (by simp) p).hasFDerivAt
  have hd2 := (h2.differentiable (by simp) (Φ p)).hasFDerivAt
  have hcomp := hd2.comp p hd1
  have hid : (⇑Φ.symm ∘ ⇑Φ) = id := funext fun x => Φ.symm_apply_apply x
  rw [hid] at hcomp
  have huniq := hcomp.unique (hasFDerivAt_id p)
  intro u v huv
  have := DFunLike.congr_fun huniq u
  have := DFunLike.congr_fun huniq v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at *
  rw [← this, ← huv]
  exact (DFunLike.congr_fun huniq u).symm

theorem hasDerivAt_diffeomorph_horizontal (Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) (y t : ℝ) :
    HasDerivAt (fun u => Φ (u, y)) (fderiv ℝ Φ (t, y) (1, 0)) t := by
  have h1 : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hc : HasDerivAt (fun u : ℝ => ((u, y) : ℝ × ℝ)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact (h1.differentiable (by simp) (t, y)).hasFDerivAt.comp_hasDerivAt t hc

theorem hasDerivAt_diffeomorph_vertical (Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) (x w : ℝ) :
    HasDerivAt (fun u => Φ (x, u)) (fderiv ℝ Φ (x, w) (0, 1)) w := by
  have h1 : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hc : HasDerivAt (fun u : ℝ => ((x, u) : ℝ × ℝ)) (0, 1) w :=
    (hasDerivAt_const w x).prodMk (hasDerivAt_id w)
  exact (h1.differentiable (by simp) (x, w)).hasFDerivAt.comp_hasDerivAt w hc

theorem exists_lift_of_torusMatrix_eq_one (φ : TDiff) (h : torusMatrix φ = 1) :
    ∃ Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ), (∀ p, φ (torusCover p) = torusCover (Φ p)) ∧
      ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n) := by
  obtain ⟨Φ, -, hlift, -, hdeck⟩ := exists_torusLiftDiffeomorph φ
    (p₀ := 0) (q₀ := torusSection (φ (torusCover 0))) (torusCover_torusSection _).symm
  refine ⟨Φ, hlift, fun p m n => ?_⟩
  obtain ⟨h1, h2⟩ := hdeck p m n
  simp only [h, Matrix.one_apply_eq, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_mul, zero_mul, add_zero,
    zero_add] at h1 h2
  exact Prod.ext h1 h2

theorem alphaCircle_cexp (t : ℝ) : alphaCircle (cexp t) = torusCover (t, 0) := by
  rw [torusCover_eq]
  exact Prod.ext rfl cexp_zero.symm

theorem betaCircle_cexp (w : ℝ) : betaCircle (cexp w) = torusCover (0, w) := by
  rw [torusCover_eq]
  exact Prod.ext cexp_zero.symm rfl

theorem deriv_lift_ne_zero {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hfg : ∀ t, f (cexp t) = cexp (g t)) {t : ℝ}
    (hd : mfderiv (𝓡 1) (𝓡 1) f (cexp t) ≠ 0) : deriv g t ≠ 0 := by
  intro h0
  apply hd
  have hcomp : f ∘ cexp = cexp ∘ g := funext hfg
  have hL : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (f ∘ cexp) t
      ((mfderiv (𝓡 1) (𝓡 1) f (cexp t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp t)) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (contMDiff_cexp.mdifferentiableAt (by simp)).hasMFDerivAt
  have hR : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (cexp ∘ g) t
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp (g t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g t)) :=
    (contMDiff_cexp.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hg.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL' := hL.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hcomp.symm)
  have huniq := hasMFDerivAt_unique hL' hR
  have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g t = 0 := by
    rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv, h0]
    simp
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_cexp t).isInvertible_mfderiv (by simp)
  ext v
  have hv := DFunLike.congr_fun huniq (e.symm v)
  rw [h3] at hv
  simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero] at hv
  have hev : (e : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace (𝓡 1) (cexp t)) (e.symm v) = v :=
    e.apply_symm_apply v
  rw [← he, hev] at hv
  exact hv

end GC.Seifert
