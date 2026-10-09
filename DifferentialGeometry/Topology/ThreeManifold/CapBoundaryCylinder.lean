import DifferentialGeometry.Topology.ThreeManifold.CapAttachingOrientation
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import DifferentialGeometry.Topology.Ehresmann.SphereBoundary

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S2 × unitInterval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_cylinder_diffeomorph_attaching (a : T.Index) :
    ∃ Ψ : Cylinder ≃ₘ⟮CI, CI⟯ Cylinder,
      (∀ p, (Ψ p).2 = p.2) ∧
      (∀ t : unitInterval, t.val ≤ 1 / 3 → ∀ z,
        Ψ (z, t) = (C.attaching (a, false) z, t)) ∧
      ∀ t : unitInterval, 2 / 3 ≤ t.val → ∀ z,
        Ψ (z, t) = (C.attaching (a, true) z, t) := by
  let R₀ := C.attaching (a, false)
  let R₁ := C.attaching (a, true)
  let δ := (R₀.trans R₁.symm).symm
  have hδ : δ.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)) :=
    Diffeomorph.preservesOrientation_symm (C.attaching_trans_symm_preservesOrientation a)
  have hdegree := Manifold.sphereDiffeomorphDegree_eq_one_of_preservesOrientation δ hδ
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ :=
    (Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy δ).mp hdegree
  let A (t : unitInterval) (z : S2) := J (1 - t.val) z
  let Ai (t : unitInterval) (z : S2) := (J (1 - t.val)).symm z
  have ht : ContMDiff CI 𝓘(ℝ) ∞ (fun q : Cylinder => 1 - q.2.val) :=
    contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  have hA : ContMDiff CI (𝓡 2) ∞ (fun q : Cylinder => A q.2 q.1) :=
    hJ.comp (ht.prodMk contMDiff_fst)
  have hAi : ContMDiff CI (𝓡 2) ∞ (fun q : Cylinder => Ai q.2 q.1) :=
    hJi.comp (ht.prodMk contMDiff_fst)
  have hzero (z : S2) : A ⟨0, by norm_num⟩ z = z := by
    change J (1 - 0) z = z
    rw [sub_zero, hJ1]
    rfl
  let H := R₀.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)
  obtain ⟨Ψ, hp, hlo, hhi⟩ := Ehresmann.exists_endpoint_flat_corrected_product H A Ai
    (fun t z => (J (1 - t.val)).symm_apply_apply z)
    (fun t z => (J (1 - t.val)).apply_symm_apply z) hA hAi hzero
  refine ⟨Ψ, hp, ?_, ?_⟩
  · intro t ht z
    exact hlo t ht z
  · intro t ht z
    rw [hhi t ht z]
    change (R₀ (J (1 - 1) z), t) = (R₁ z, t)
    rw [sub_self, hJ0]
    exact Prod.ext (R₀.apply_symm_apply (R₁ z)) rfl

end DifferentialGeometry.Topology.SphericalCapping
