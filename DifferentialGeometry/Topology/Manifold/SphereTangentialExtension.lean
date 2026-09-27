import DifferentialGeometry.Topology.Manifold.SphereGraphExtension
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree

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

private def sphereAxialSuspension
    (J : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => J q.1 q.2))
    (hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => (J q.1).symm q.2))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder where
  toFun p := (J (χ p.2) p.1, p.2)
  invFun p := ((J (χ p.2)).symm p.1, p.2)
  left_inv p := Prod.ext ((J (χ p.2)).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((J (χ p.2)).apply_symm_apply p.1) rfl
  contMDiff_toFun :=
    (hJ.comp ((hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (hJi.comp ((hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd

theorem exists_supported_diffeomorph_eq_sphere_map_on_strip
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    (a b l u : ℝ) (hla : l < a) (hbu : b < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ (p : S2) (s : ℝ), s ∈ Icc a b → F (p, s) = (η p, s)) ∧
      (∀ p : Cylinder, (F p).2 = p.2) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ univ ×ˢ Ioo l u ∧
        EqOn F id Sᶜ ∧ EqOn F.symm id Sᶜ := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (sphereDiffeomorphDegree_eq_one_iff_isotopy η).mp hη
  obtain ⟨χ, hχ, hcχ, hχone, hχsupp, _⟩ := DifferentialGeometry.Analysis.exists_bump_compact
    isCompact_Icc isOpen_Ioo (show Icc a b ⊆ Ioo l u from fun s hs => ⟨hla.trans_le hs.1, hs.2.trans_lt hbu⟩)
  let A : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 := fun t => J (1 - t)
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × S2 => (1 - q.1, q.2)) := (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  let F := sphereAxialSuspension A (hJ.comp ht) (hJi.comp ht) χ hχ
  have hzero : A 0 = Diffeomorph.refl (𝓡 2) S2 ∞ := by simpa only [A, sub_zero] using hJ1
  refine ⟨F, ?_, fun _ => rfl, univ ×ˢ tsupport χ, isCompact_univ.prod hcχ,
    prod_mono subset_rfl hχsupp, ?_, ?_⟩
  · intro p s hs
    have hone : χ s = 1 := Filter.EventuallyEq.eq_of_nhds (hχone.filter_mono (nhds_le_nhdsSet hs))
    change (A (χ s) p, s) = _
    rw [hone]
    change (J (1 - 1) p, s) = _
    rw [sub_self, hJ0]
  · intro p hp
    have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
    change (A (χ p.2) p.1, p.2) = _
    rw [image_eq_zero_of_notMem_tsupport hnot, hzero]
    rfl
  · intro p hp
    have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
    change ((A (χ p.2)).symm p.1, p.2) = _
    rw [image_eq_zero_of_notMem_tsupport hnot, hzero]
    rfl

end DifferentialGeometry.Topology.Manifold
