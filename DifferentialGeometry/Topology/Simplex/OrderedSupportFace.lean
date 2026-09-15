import DifferentialGeometry.Topology.Simplex.SupportFace
import DifferentialGeometry.Topology.Simplex.Reindex
import DifferentialGeometry.Topology.Simplex.MapInjectivity
import Mathlib.Data.Finset.Sort

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem reindexHomeomorph_eq_map (e : ι ≃ κ) (p : stdSimplex ℝ ι) :
    reindexHomeomorph e p = stdSimplex.map e p := by
  ext j
  change p.val (e.symm j) = (stdSimplex.map e p).val j
  have h := stdSimplex.map_apply_of_injective e.injective p (e.symm j)
  change p (e.symm j) = (stdSimplex.map e p) j
  rw [e.apply_symm_apply] at h
  exact h.symm

variable [LinearOrder ι]

def orderedSupportFaceHomeomorph (s : Finset ι) {m : ℕ} (hs : s.card = m) :
    stdSimplex ℝ (Fin m) ≃ₜ supportFace s :=
  (reindexHomeomorph (s.orderIsoOfFin hs).toEquiv).trans (supportFaceHomeomorph s)

@[simp]
theorem orderedSupportFaceHomeomorph_apply_val (s : Finset ι) {m : ℕ} (hs : s.card = m)
    (p : stdSimplex ℝ (Fin m)) :
    (orderedSupportFaceHomeomorph s hs p).val = stdSimplex.map (s.orderEmbOfFin hs) p := by
  change stdSimplex.map Subtype.val (reindexHomeomorph (s.orderIsoOfFin hs).toEquiv p) = _
  rw [reindexHomeomorph_eq_map, stdSimplex.map_comp_apply]
  rfl

@[simp]
theorem orderedSupportFaceHomeomorph_symm_apply (s : Finset ι) {m : ℕ} (hs : s.card = m)
    (p : supportFace s) (i : Fin m) :
    (orderedSupportFaceHomeomorph s hs).symm p i = p.val (s.orderEmbOfFin hs i) := rfl

omit [Fintype ι] in
private theorem orderEmbOfFin_erase (s : Finset ι) {m : ℕ} (hs : s.card = m + 1)
    (i : Fin (m + 1))
    (he : (s.erase (s.orderEmbOfFin hs i)).card = m) :
    (s.erase (s.orderEmbOfFin hs i)).orderEmbOfFin he =
      (Fin.succAboveOrderEmb i).trans (s.orderEmbOfFin hs) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro j
  exact Finset.mem_erase.mpr ⟨by
    intro h
    exact Fin.succAbove_ne i j ((s.orderEmbOfFin hs).injective h),
    s.orderEmbOfFin_mem hs _⟩

theorem orderedSupportFaceHomeomorph_erase_apply_val (s : Finset ι) {m : ℕ}
    (hs : s.card = m + 1) (i : Fin (m + 1))
    (he : (s.erase (s.orderEmbOfFin hs i)).card = m) (p : stdSimplex ℝ (Fin m)) :
    (orderedSupportFaceHomeomorph (s.erase (s.orderEmbOfFin hs i)) he p).val =
      (orderedSupportFaceHomeomorph s hs (stdSimplex.map i.succAbove p)).val := by
  rw [orderedSupportFaceHomeomorph_apply_val, orderedSupportFaceHomeomorph_apply_val,
    stdSimplex.map_comp_apply, orderEmbOfFin_erase s hs i he]
  rfl

end DifferentialGeometry.Simplex
