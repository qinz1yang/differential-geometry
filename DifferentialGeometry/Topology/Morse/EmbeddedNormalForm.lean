import DifferentialGeometry.Topology.Morse.SmoothNormalForm
import DifferentialGeometry.Topology.Manifold.Projection
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

open Set Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}
  [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_projected_morse_normal_form
    {e : M → MorseModel n × ℝ} (he : ContMDiff I 𝓘(ℝ, MorseModel n × ℝ) ∞ e)
    {p : M} (hinj : Function.Injective (mfderiv I 𝓘(ℝ, MorseModel n × ℝ) e p))
    (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞,
      ∃ A : PartialDiffeomorph 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
          (MorseModel n) (MorseModel n) ∞,
        0 ∈ χ.source ∧ χ 0 = p ∧ A.source = χ.source ∧
        ∀ x ∈ χ.source, e (χ x) = (A x, morseNormalForm hk (e p).2 x) := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).2) :=
    contDiff_snd.contMDiff.comp he
  obtain ⟨χ, hχ0, hχp, hnormal, _⟩ :=
    DifferentialGeometry.Morse.exists_interior_morse_normal_form I (fun x => (e x).2) hf p
      BoundarylessManifold.isInteriorPoint k hk hnd hindex
  have hproj :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero
      he hinj hnd.1 rfl
  obtain ⟨ψ, hpψ, hψ⟩ := hproj
  let A := χ.trans ψ
  have h0A : (0 : MorseModel n) ∈ A.source := by
    refine ⟨hχ0, ?_⟩
    change χ 0 ∈ ψ.source
    rw [hχp]
    exact hpψ
  let χ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ A.source A.open_source
  have hsource : χ'.source = A.source := inter_eq_right.mpr inter_subset_left
  refine ⟨χ', A, hsource ▸ h0A, hχp, hsource.symm, ?_⟩
  intro x hx
  have hxA : x ∈ A.source := hsource ▸ hx
  exact Prod.ext (hψ hxA.2) (hnormal x hxA.1)

theorem exists_height_preserving_morse_normal_form
    {e : M → MorseModel n × ℝ} (he : ContMDiff I 𝓘(ℝ, MorseModel n × ℝ) ∞ e)
    {p : M} (hinj : Function.Injective (mfderiv I 𝓘(ℝ, MorseModel n × ℝ) e p))
    (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞,
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, MorseModel n × ℝ) 𝓘(ℝ, MorseModel n × ℝ)
          (MorseModel n × ℝ) (MorseModel n × ℝ) ∞,
        0 ∈ χ.source ∧ χ 0 = p ∧ Φ.source = χ.source ×ˢ univ ∧
        (∀ z, (Φ z).2 = z.2) ∧
        ∀ x ∈ χ.source,
          (e (χ x)).2 = morseNormalForm hk (e p).2 x ∧
          Φ (x, morseNormalForm hk (e p).2 x) = e (χ x) := by
  obtain ⟨χ, A, hχ0, hχp, hsource, hnormal⟩ :=
    exists_projected_morse_normal_form he hinj k hk hnd hindex
  let Φ : PartialDiffeomorph 𝓘(ℝ, MorseModel n × ℝ) 𝓘(ℝ, MorseModel n × ℝ)
      (MorseModel n × ℝ) (MorseModel n × ℝ) ∞ :=
    { toPartialEquiv := A.toPartialEquiv.prod (PartialEquiv.refl ℝ)
      open_source := A.open_source.prod isOpen_univ
      open_target := A.open_target.prod isOpen_univ
      contMDiffOn_toFun := (A.contMDiffOn.contDiffOn.prodMap contDiffOn_id).contMDiffOn
      contMDiffOn_invFun := (A.symm.contMDiffOn.contDiffOn.prodMap contDiffOn_id).contMDiffOn }
  refine ⟨χ, Φ, hχ0, hχp, ?_, fun _ => rfl, ?_⟩
  · change A.source ×ˢ univ = χ.source ×ˢ univ
    rw [hsource]
  · intro x hx
    exact ⟨congrArg Prod.snd (hnormal x hx), (hnormal x hx).symm⟩

end DifferentialGeometry.Topology.Morse
