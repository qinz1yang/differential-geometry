import DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DifferentialGeometry.Topology.Diffeomorph.Translation
import DifferentialGeometry.Topology.Diffeomorph.CompactLocalIsotopy
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

open Set
open scoped ContDiff Manifold

namespace Diffeomorph

theorem exists_compact_isotopy_height_reparametrization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set (E × ℝ)} (hK : IsCompact K)
    {l u c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) :
    ∃ φ : ℝ → ℝ ≃ₘ[ℝ] ℝ,
      ContDiff ℝ ∞ (fun z : ℝ × ℝ => φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × ℝ => (φ z.1).symm z.2) ∧
      φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞ ∧ φ 1 c = d ∧
      (∀ t y, 0 < deriv (φ t) y) ∧
      (∀ t, EqOn (φ t) id (Ioo l u)ᶜ ∧ EqOn (φ t).symm id (Ioo l u)ᶜ) ∧
      ∃ V : Set (E × ℝ), IsOpen V ∧ K ⊆ V ∧
        ∃ H : ℝ → (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
          ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
          H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ V, H t z = (z.1, φ t z.2)) ∧
          (∀ t z, (H t z).1 = z.1) ∧
          (∀ t, EqOn (H t) id {z | z.2 ∉ Ioo l u} ∧
            EqOn (H t).symm id {z | z.2 ∉ Ioo l u}) ∧
          ∃ S : Set (E × ℝ), IsCompact S ∧ ∀ t,
            EqOn (H t) id Sᶜ ∧ EqOn (H t).symm id Sᶜ := by
  obtain ⟨φ, hφ, hφi, hφ0, hmove, _, J, hJ, hJU, hfix⟩ :=
    exists_isotopy_translation_in_open (isCompact_singleton (x := c)) isOpen_Ioo (d - c)
      (by
        intro t ht x hx
        have hx' : x = c := hx
        subst x
        change l < c + t * (d - c) ∧ c + t * (d - c) < u
        have hmem := (convex_Ioo l u) hc hd (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
        have heq : (1 - t) • c + t • d = c + t * (d - c) := by simp only [smul_eq_mul]; ring
        rwa [heq] at hmem)
  have hφ1 : φ 1 c = d := by simpa using hmove 1 (by simp) c (mem_singleton c)
  have hder (t y : ℝ) : 0 < deriv (φ t) y := by
    have hp := (φ t).det_fderiv_pos_of_eqOn_compl_isCompact hJ (hfix t).1 y
    simpa only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, fderiv_eq_smul_deriv,
      one_smul] using hp
  have hφfix (t : ℝ) : EqOn (φ t) id (Ioo l u)ᶜ ∧ EqOn (φ t).symm id (Ioo l u)ᶜ :=
    ⟨(hfix t).1.mono (compl_subset_compl.mpr hJU),
      (hfix t).2.mono (compl_subset_compl.mpr hJU)⟩
  let A (t : ℝ) : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongr (Equiv.refl E) (φ t).toEquiv
      contMDiff_toFun := (contDiff_fst.prodMk ((φ t).contDiff.comp contDiff_snd)).contMDiff
      contMDiff_invFun := (contDiff_fst.prodMk ((φ t).symm.contDiff.comp contDiff_snd)).contMDiff }
  have hA : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => A z.1 z.2) :=
    contDiff_snd.fst.prodMk (hφ.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hAi : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (A z.1).symm z.2) :=
    contDiff_snd.fst.prodMk (hφi.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hA0 (z : E × ℝ) : A 0 z = z := by
    change (z.1, φ 0 z.2) = z
    rw [hφ0]
    rfl
  obtain ⟨V, hV, hKV, H, hH, hHi, hH0, htrack, hfixed, hfirst, S, hS, _, hHfix⟩ :=
    exists_contDiff_compact_isotopy_eqOn_preserving_linear_map A hA hAi
      (ContinuousLinearMap.fst ℝ E ℝ) (fun _ _ => rfl)
      (A := {z : E × ℝ | z.2 ∉ Ioo l u}) (fun t z hz => Prod.ext rfl ((hφfix t).1 hz))
      (a := 0) (b := 1) hK isOpen_univ (fun _ _ _ _ => mem_univ _)
  refine ⟨φ, hφ, hφi, hφ0, hφ1, hder, hφfix, V, hV, hKV,
    H, hH, hHi, hH0, ?_, hfirst, hfixed, S, hS, hHfix⟩
  intro t ht z hz
  have h := htrack t ht z hz
  rwa [hA0] at h


theorem exists_eq_exponential_on_Iic
    {a b m μ : ℝ} (hab : a < b) (hbm : b < m) (hμ : 0 < μ) :
    ∃ ψ : ℝ ≃ₘ[ℝ] ℝ,
      (∀ t, 0 < deriv ψ t) ∧
      (∀ t ≤ a, ψ t = m - (m - a + 1) * Real.exp (-2 * μ * (t - b))) ∧
      ∀ t, b ≤ t → ψ t = t := by
  let C := m - a + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let f : ℝ → ℝ := fun t => m - C * Real.exp (-2 * μ * (t - b))
  let χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - a) / (b - a))
  let g : ℝ → ℝ := fun t => f t + χ t * (t - f t)
  have hf : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hχ : ContDiff ℝ ∞ χ := by dsimp [χ]; fun_prop
  have hg : ContDiff ℝ ∞ g := hf.add (hχ.mul (contDiff_id.sub hf))
  have hfd (t : ℝ) : HasDerivAt f (2 * μ * C * Real.exp (-2 * μ * (t - b))) t := by
    have hd := ((((hasDerivAt_id t).sub_const b).const_mul (-2 * μ)).exp.const_mul C).const_sub m
    convert hd using 1 <;> first | rfl | (dsimp; ring)
  have hfp (t : ℝ) : 0 < deriv f t := by
    rw [(hfd t).deriv]
    positivity
  have hχ01 (t : ℝ) : χ t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hχmono : Monotone χ := Real.smoothTransition.monotone.comp
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_nonneg.mpr hab.le))
  have hχlo (t : ℝ) (ht : t ≤ a) : χ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le))
  have hχhi (t : ℝ) (ht : b ≤ t) : χ t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
  have hglo (t : ℝ) (ht : t ≤ a) : g t = f t := by simp only [g, hχlo t ht, zero_mul, add_zero]
  have hghi (t : ℝ) (ht : b ≤ t) : g t = t := by dsimp only [g]; rw [hχhi t ht]; ring
  have hgap (t : ℝ) (ht : t ∈ Icc a b) : 0 < t - f t := by
    have he : 1 ≤ Real.exp (-2 * μ * (t - b)) := Real.one_le_exp_iff.mpr
      (by nlinarith [ht.2])
    have hm := mul_le_mul_of_nonneg_left he hC.le
    dsimp only [f]
    dsimp only [C] at hm
    nlinarith [ht.1]
  have hgd (t : ℝ) : deriv g t =
      (1 - χ t) * deriv f t + χ t + deriv χ t * (t - f t) := by
    have hd := (hf.differentiable (by simp) t).hasDerivAt.add
      ((hχ.differentiable (by simp) t).hasDerivAt.mul
        ((hasDerivAt_id t).sub (hf.differentiable (by simp) t).hasDerivAt))
    convert hd.deriv using 1 <;> first | rfl | (dsimp; ring)
  have hgp (t : ℝ) : 0 < deriv g t := by
    rw [hgd]
    have hweights := hχ01 t
    have hpositive : 0 < (1 - χ t) * deriv f t + χ t := by
      rcases eq_or_lt_of_le hweights.2 with heq | hlt
      · rw [heq]; norm_num
      · have hp := mul_pos (sub_pos.mpr hlt) (hfp t)
        linarith [hweights.1]
    have hterm : 0 ≤ deriv χ t * (t - f t) := by
      by_cases htlo : t ≤ a
      · have hmin : IsLocalMin χ t := Filter.Eventually.of_forall (fun x => by
          change χ t ≤ χ x
          rw [hχlo t htlo]
          exact (hχ01 x).1)
        rw [hmin.deriv_eq_zero, zero_mul]
      · by_cases hthi : b ≤ t
        · have hmax : IsLocalMax χ t := Filter.Eventually.of_forall (fun x => by
            change χ x ≤ χ t
            rw [hχhi t hthi]
            exact (hχ01 x).2)
          rw [hmax.deriv_eq_zero, zero_mul]
        · exact mul_nonneg hχmono.deriv_nonneg
            (hgap t ⟨(lt_of_not_ge htlo).le, (lt_of_not_ge hthi).le⟩).le
    linarith
  have hmono : StrictMono g := strictMono_of_deriv_pos hgp
  have hsurj : Function.Surjective g := by
    intro y
    let v := min (y - 1) (m - 1)
    have hvm : v < m := by dsimp [v]; linarith [min_le_right (y - 1) (m - 1)]
    have hvy : v < y := by dsimp [v]; linarith [min_le_left (y - 1) (m - 1)]
    let x := b - Real.log ((m - v) / C) / (2 * μ)
    have hratio : 0 < (m - v) / C := div_pos (sub_pos.mpr hvm) hC
    have hfx : f x = v := by
      have he : -2 * μ * (x - b) = Real.log ((m - v) / C) := by
        dsimp [x]
        field_simp
        ring
      dsimp only [f]
      rw [he, Real.exp_log hratio]
      field_simp
      ring
    let l := min a x
    let u := max b y
    have hlu : l ≤ u := (min_le_left a x).trans (hab.le.trans (le_max_left b y))
    have hlo : g l ≤ y := by
      rw [hglo l (min_le_left _ _)]
      exact ((strictMono_of_deriv_pos hfp).monotone (min_le_right a x)).trans
        (hfx.le.trans hvy.le)
    have hhi : y ≤ g u := by rw [hghi u (le_max_left _ _)]; exact le_max_right _ _
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc hlu hg.continuous.continuousOn ⟨hlo, hhi⟩
    exact ⟨t, ht⟩
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ g := by
    intro t
    let L := (ContinuousLinearEquiv.unitsEquivAut ℝ) (Units.mk0 (deriv g t) (hgp t).ne')
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
      g hg.contMDiff t L (((hg.differentiable (by simp) t).hasDerivAt.hasFDerivAt_equiv
        (hgp t).ne').hasMFDerivAt)
  let ψ := hlocal.diffeomorphOfBijective ⟨hmono.injective, hsurj⟩
  have hψ : (ψ : ℝ → ℝ) = g := rfl
  exact ⟨ψ, hψ ▸ hgp, fun t ht => (congrFun hψ t).trans (hglo t ht),
    fun t ht => (congrFun hψ t).trans (hghi t ht)⟩


end Diffeomorph
