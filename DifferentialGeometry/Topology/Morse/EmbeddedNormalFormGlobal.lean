import DifferentialGeometry.Topology.Morse.EmbeddedNormalForm
import DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension

open Set Manifold Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}
  [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_global_height_preserving_morse_normal_form
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    {p : M}
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) e p))
    (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k) :
    ∃ r : ℝ, 0 < r ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        ∃ Φ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
          closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (Φ z).2 = z.2) ∧
          ∀ y ∈ closedBall 0 r,
            Φ (y, morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)) = e (χ y) := by
  let L := EuclideanSpace.equiv (Fin n) ℝ
  let C := L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have he' : ContMDiff I 𝓘(ℝ, MorseModel n × ℝ) ∞ (C ∘ e) :=
    C.contDiff.contMDiff.comp he
  have hinj' : Function.Injective (mfderiv I 𝓘(ℝ, MorseModel n × ℝ) (C ∘ e) p) := by
    rw [mfderiv_comp p C.differentiableAt.mdifferentiableAt
      (he.mdifferentiableAt (by simp)), C.mfderiv_eq]
    exact C.injective.comp hinj
  obtain ⟨χ, A, hχ0, hχp, hsource, hnormal⟩ :=
    exists_projected_morse_normal_form he' hinj' k hk hnd hindex
  let χ' := L.toDiffeomorph.toPartialDiffeomorph.trans χ
  let A' := (L.toDiffeomorph.toPartialDiffeomorph.trans A).trans
    L.symm.toDiffeomorph.toPartialDiffeomorph
  have h0χ' : (0 : EuclideanSpace ℝ (Fin n)) ∈ χ'.source := by
    change 0 ∈ univ ∧ L 0 ∈ χ.source
    simpa only [map_zero, mem_univ, true_and] using hχ0
  have hsource' : A'.source = χ'.source := by
    ext y
    change (y ∈ univ ∧ L y ∈ A.source) ∧ A (L y) ∈ univ ↔
      y ∈ univ ∧ L y ∈ χ.source
    simp only [mem_univ, true_and, and_true, hsource]
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (χ'.open_source.mem_nhds h0χ')
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrs : closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ χ'.source :=
    (closedBall_subset_ball (show r < R by dsimp [r]; linarith)).trans hRsub
  obtain ⟨B, hB⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
      A' hr (hsource'.symm ▸ hrs)
  let Φ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    { toEquiv := B.toEquiv.prodCongr (Equiv.refl ℝ)
      contMDiff_toFun := ((B.contMDiff.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((B.symm.contMDiff.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  refine ⟨r, hr, χ', Φ, hrs, ?_, fun _ => rfl, ?_⟩
  · change χ (L 0) = p
    simpa only [map_zero] using hχp
  · intro y hy
    have hys : L y ∈ χ.source := (hrs hy).2
    have hn : C (e (χ (L y))) = (A (L y), morseNormalForm hk (e p).2 (L y)) :=
      hnormal (L y) hys
    apply C.injective
    change (L (B y), morseNormalForm hk (e p).2 (L y)) = C (e (χ (L y)))
    rw [hn]
    apply Prod.ext
    · rw [hB hy]
      exact L.apply_symm_apply (A (L y))
    · rfl

end DifferentialGeometry.Topology.Morse
