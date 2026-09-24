import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.LeftInverse
import DifferentialGeometry.Topology.Morse.RegularLevel.DirectionalField
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem exists_unitSpeedVectorField_on_saddle_band
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    (hdim : Module.finrank ℝ F = 2)
    {e : M → E × ℝ} (he : ContMDiff I 𝓘(ℝ, E × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s : ℝ} (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) I (ℝ × ℝ) M ∞,
      χ.source = U ∧ χ.target = β '' U ∧ (χ : ℝ × ℝ → M) = β ∧
      (χ.symm : M → ℝ × ℝ) = (fun x => B.symm (e x).1) ∧
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M))
        (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}) ∧
      (∀ x ∈ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0},
        mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun x => B.symm (e x).1) x (W x) =
          (0, -((1 - (B.symm (e x).1).1 ^ 2) * (B.symm (e x).1).2)⁻¹)) ∧
      ∀ x ∈ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0},
        (NormedSpace.fromTangentSpace ((e x).2))
          (mfderiv I 𝓘(ℝ, ℝ) (fun x => (e x).2) x (W x)) = -1 := by
  let _ : FiniteDimensional ℝ F := FiniteDimensional.of_finrank_pos (by omega)
  let G : M → ℝ × ℝ := fun x => B.symm (e x).1
  have hG : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ G :=
    B.symm.contMDiff.comp (contDiff_fst.contMDiff.comp he)
  have hleft : LeftInvOn G β U := by
    intro z hz
    change B.symm (e (β z)).1 = z
    rw [hgraph z hz]
    exact B.symm_apply_apply z
  obtain ⟨χ, hsource, htarget, hχ, hχinv⟩ := hleft.exists_partialDiffeomorph hU hβ
    (fun z _ => hG.contMDiffAt (x := β z)) (by simpa using hdim.symm)
  refine ⟨χ, hsource, htarget, hχ, hχinv, ?_⟩
  let q : ℝ × ℝ → ℝ := fun z => c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hqd (z : ℝ × ℝ) : fderiv ℝ q z (0, 1) = (1 - z.1 ^ 2) * z.2 :=
    fderiv_saddle_band_apply_vertical c s z
  have hn (z : ℝ × ℝ) (hz : z ∈ χ.source) : (e (χ z)).2 = q z := by
    rw [hχ, hgraph z (hsource ▸ hz)]
  obtain ⟨W, hW, hcoords, hdf⟩ := exists_unitSpeedVectorField_on_directional_chart
    (f := fun x => (e x).2) χ hq.contDiffOn hn (0, 1)
  have hset : χ '' {z | z ∈ χ.source ∧ fderiv ℝ q z (0, 1) ≠ 0} =
      β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} := by
    simp only [hχ, hsource, hqd]
  refine ⟨W, hset ▸ hW, ?_, hset ▸ hdf⟩
  intro x hx
  have h := hcoords x (hset.symm ▸ hx)
  rw [hχinv, hqd] at h
  simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one] using h

end DifferentialGeometry.Topology.Morse
