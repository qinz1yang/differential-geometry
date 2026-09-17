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

end Diffeomorph
