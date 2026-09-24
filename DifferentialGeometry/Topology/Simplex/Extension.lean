import DifferentialGeometry.Topology.Simplex.HomotopyExtension

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

theorem exists_continuous_extension_of_nullhomotopic (n : ℕ)
    (f : C(boundary (Fin (n + 1)), X)) (hf : f.Nullhomotopic) :
    ∃ F : C(stdSimplex ℝ (Fin (n + 1)), X),
      ∀ p : boundary (Fin (n + 1)), F p.val = f p := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  obtain ⟨F, hF, hside⟩ := exists_continuous_homotopy_extension n
    (ContinuousMap.const _ x) H.symm.toContinuousMap (fun p => H.symm.apply_zero p)
  refine ⟨F.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩, ?_⟩
  intro p
  exact (hside 1 p).trans (H.symm.apply_one p)

end DifferentialGeometry.Simplex
