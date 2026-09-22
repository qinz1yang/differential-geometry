import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cylinder := S2 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private def verticalGraphField (h : S2 → ℝ) (χ : ℝ → ℝ) (p : Cylinder) : TangentSpace IC p :=
  (χ p.2 * h p.1) • DifferentialGeometry.Geometry.Metric.cylinderAxis p

private theorem verticalGraphField_smooth (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContMDiff IC IC.tangent ∞ (fun p => (⟨p, verticalGraphField h χ p⟩ : TangentBundle IC Cylinder)) :=
  ((hχ.contMDiff.comp contMDiff_snd).mul (hh.comp contMDiff_fst)).smul_section
    DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis

private theorem verticalGraphField_hasCompactSupport (h : S2 → ℝ) (χ : ℝ → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (verticalGraphField h χ) := by
  apply HasCompactSupport.intro (isCompact_univ.prod hχ)
  intro p hp
  have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
  simp only [verticalGraphField, image_eq_zero_of_notMem_tsupport hnot, zero_mul, zero_smul]
  rfl

private theorem graph_path_integralCurve
    (h : S2 → ℝ) (χ : ℝ → ℝ) (p : S2) (z : ℝ)
    (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ (z + t * h p) = 1) :
    IsMIntegralCurveOn (fun t => (p, z + t * h p)) (verticalGraphField h χ) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hd : HasDerivAt (fun t : ℝ => z + t * h p) (h p) t := by
    convert (hasDerivAt_const t z).add ((hasDerivAt_id t).mul_const (h p)) using 1 <;> first | rfl | simp
  have hp := (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := (𝓡 2)) p t).prodMk hd.hasFDerivAt.hasMFDerivAt
  apply hp.hasMFDerivWithinAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  simp only [verticalGraphField, hχ t ht, one_mul]
  change ℝ at r
  change ((0 : EuclideanSpace ℝ (Fin 2)), r * h p) = r • (h p • ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)))
  ext <;> simp [smul_eq_mul]

theorem exists_supported_diffeomorph_eq_graph_shear
    (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (K : Set Cylinder) (hK : IsCompact K) (l u : ℝ)
    (htrack : ∀ p ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, l < p.2 + t * h p.1 ∧ p.2 + t * h p.1 < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ p ∈ K, F p = (p.1, p.2 + h p.1)) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ univ ×ˢ Ioo l u ∧
        EqOn F id Sᶜ ∧ EqOn F.symm id Sᶜ := by
  let B := (fun q : ℝ × Cylinder => q.2.2 + q.1 * h q.2.1) '' (Icc (0 : ℝ) 1 ×ˢ K)
  have hB : IsCompact B := (isCompact_Icc.prod hK).image
    (continuous_snd.snd.add (continuous_fst.mul (hh.continuous.comp continuous_snd.fst)))
  have hBU : B ⊆ Ioo l u := by
    rintro y ⟨q, hq, rfl⟩
    exact htrack q.2 hq.2 q.1 hq.1
  obtain ⟨χ, hχ, hcχ, hχone, hχsupp, _⟩ := DifferentialGeometry.Analysis.exists_bump_compact hB isOpen_Ioo hBU
  let V := verticalGraphField h χ
  have hV := verticalGraphField_smooth h hh χ hχ
  have hVc := verticalGraphField_hasCompactSupport h χ hcχ
  let F := Diffeomorph.compactSupportFlow V hV hVc 1
  have hVs : tsupport V ⊆ univ ×ˢ tsupport χ := by
    apply closure_minimal _ (isClosed_univ.prod isClosed_closure)
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    by_contra hn
    apply hp
    simp only [V, verticalGraphField, image_eq_zero_of_notMem_tsupport hn, zero_mul, zero_smul]
    rfl
  refine ⟨F, ?_, tsupport V, hVc, hVs.trans (prod_mono subset_rfl hχsupp),
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hV hVc 1).1,
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hV hVc 1).2⟩
  intro p hp
  have hχtrack : ∀ t ∈ Icc (0 : ℝ) 1, χ (p.2 + t * h p.1) = 1 := by
    intro t ht
    have hmem : p.2 + t * h p.1 ∈ B := ⟨(t, p), ⟨ht, hp⟩, rfl⟩
    exact Filter.EventuallyEq.eq_of_nhds (hχone.filter_mono (nhds_le_nhdsSet hmem))
  have hpath := graph_path_integralCurve h χ p.1 p.2 hχtrack
  have hflow := (Diffeomorph.isMIntegralCurve_compactSupportFlow V hV hVc p).isMIntegralCurveOn (Icc (0 : ℝ) 1)
  have heq := DifferentialGeometry.Analysis.ODE.isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff
    (hV.of_le (by simp)) hflow hpath (by erw [Diffeomorph.compactSupportFlow_zero]; simp)
  simpa only [one_mul] using heq (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)


theorem exists_supported_diffeomorph_eq_graph_collar
    (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (a r l u : ℝ)
    (ha : l < a - r ∧ a + r < u)
    (hhull : ∀ p : S2, l < a - r + h p ∧ a + r + h p < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ (p : S2) (s : ℝ), |s| ≤ r → F (p, a + s) = (p, a + s + h p)) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ univ ×ˢ Ioo l u ∧
        EqOn F id Sᶜ ∧ EqOn F.symm id Sᶜ := by
  obtain ⟨F, hF, S, hS, hSU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_graph_shear h hh (univ ×ˢ Icc (a - r) (a + r))
      (isCompact_univ.prod isCompact_Icc) l u (by
        rintro p ⟨_, hp⟩ t ht
        have hp0 : p.2 ∈ Ioo l u := ⟨ha.1.trans_le hp.1, hp.2.trans_lt ha.2⟩
        have hp1 : p.2 + h p.1 ∈ Ioo l u := by
          constructor <;> linarith [(hhull p.1).1, (hhull p.1).2, hp.1, hp.2]
        have hconv := convex_Ioo l u hp0 hp1 (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
        have heq : (1 - t) • p.2 + t • (p.2 + h p.1) = p.2 + t * h p.1 := by
          simp only [smul_eq_mul]
          ring
        exact heq ▸ hconv)
  refine ⟨F, ?_, S, hS, hSU, hfix, hfixi⟩
  intro p s hs
  exact hF (p, a + s) ⟨mem_univ _, by
    constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]⟩

end DifferentialGeometry.Topology.Manifold
