import DifferentialGeometry.Topology.Simplex.HomotopyExtension
import DifferentialGeometry.Topology.Simplex.Reindex
import DifferentialGeometry.Topology.Simplex.Skeleton
import DifferentialGeometry.Topology.Homotopy.ClosedCoverHomotopy

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

private theorem exists_extension_equiv {n : ℕ} (e : ι ≃ Fin (n + 1))
    (f : C(stdSimplex ℝ ι, X)) (H : C(unitInterval × boundary ι, X))
    (hH : ∀ p : boundary ι, H (0, p) = f p.val) :
    ∃ F : C(unitInterval × stdSimplex ℝ ι, X),
      (∀ p, F (0, p) = f p) ∧
      ∀ t (p : boundary ι), F (t, p.val) = H (t, p) := by
  let b := reindexHomeomorph e
  let eB : boundary ι ≃ₜ boundary (Fin (n + 1)) :=
    b.subtype fun p => (reindexHomeomorph_mem_boundary e p).symm
  let g : C(stdSimplex ℝ (Fin (n + 1)), X) := f.comp ⟨b.symm, b.symm.continuous⟩
  let K : C(unitInterval × boundary (Fin (n + 1)), X) :=
    H.comp ⟨fun z => (z.1, eB.symm z.2),
      continuous_fst.prodMk (eB.symm.continuous.comp continuous_snd)⟩
  have hK : ∀ p : boundary (Fin (n + 1)), K (0, p) = g p.val := by
    intro p
    exact hH (eB.symm p)
  obtain ⟨G, hG0, hGb⟩ := exists_continuous_homotopy_extension n g K hK
  refine ⟨G.comp ⟨fun z => (z.1, b z.2),
    continuous_fst.prodMk (b.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro p
    change G (0, b p) = f p
    rw [hG0]
    exact congrArg f (b.symm_apply_apply p)
  · intro t p
    have h := hGb t (eB p)
    change G (t, b p.val) = H (t, eB.symm (eB p)) at h
    change G (t, b p.val) = H (t, p)
    rw [eB.symm_apply_apply] at h
    exact h

private theorem exists_extension_supportFace {k : ℕ} (s : Finset ι) (hs : s.card = k + 2)
    (f : C(stdSimplex ℝ ι, X)) (H : C(unitInterval × skeleton ι k, X))
    (hH : ∀ p : skeleton ι k, H (0, p) = f p.val) :
    ∃ G : C(unitInterval × supportFace s, X),
      (∀ p, G (0, p) = f p.val) ∧
      ∀ t (p : supportFace s) (hp : p.val ∈ skeleton ι k),
        G (t, p) = H (t, ⟨p.val, hp⟩) := by
  let b := supportFaceHomeomorph s
  let j : C(boundary s, skeleton ι k) :=
    ⟨fun p => ⟨(b p.val).val,
        (supportFaceRestrict_mem_boundary_iff_mem_skeleton hs (b p.val)).mp (by
          change supportFaceRestrict s (supportFaceInsert s p.val) ∈ boundary s
          rw [supportFaceRestrict_supportFaceInsert]
          exact p.property)⟩,
      (continuous_subtype_val.comp (b.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let fi : C(stdSimplex ℝ s, X) :=
    f.comp ⟨fun p => (b p).val, continuous_subtype_val.comp b.continuous⟩
  let Hi : C(unitInterval × boundary s, X) :=
    H.comp ⟨fun z => (z.1, j z.2), continuous_fst.prodMk (j.continuous.comp continuous_snd)⟩
  have hHi : ∀ p : boundary s, Hi (0, p) = fi p.val := fun p => hH (j p)
  obtain ⟨K, hK0, hKb⟩ := exists_extension_equiv (Finset.equivFinOfCardEq hs) fi Hi hHi
  refine ⟨K.comp ⟨fun z => (z.1, b.symm z.2),
    continuous_fst.prodMk (b.symm.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro p
    change K (0, b.symm p) = f p.val
    rw [hK0]
    change f (b (b.symm p)).val = f p.val
    rw [b.apply_symm_apply]
  · intro t p hp
    let q : boundary s := ⟨b.symm p,
      (supportFaceRestrict_mem_boundary_iff_mem_skeleton hs p).mpr hp⟩
    have h := hKb t q
    change K (t, b.symm p) = H (t, j q) at h
    change K (t, b.symm p) = H (t, ⟨p.val, hp⟩)
    apply h.trans
    apply congrArg H
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (b (b.symm p)).val = p.val
      exact congrArg Subtype.val (b.apply_symm_apply p)

private theorem exists_extension_skeleton_succ (k : ℕ)
    (f : C(stdSimplex ℝ ι, X)) (H : C(unitInterval × skeleton ι k, X))
    (hH : ∀ p : skeleton ι k, H (0, p) = f p.val) :
    ∃ G : C(unitInterval × skeleton ι (k + 1), X),
      (∀ p, G (0, p) = f p.val) ∧
      ∀ t (p : skeleton ι k),
        G (t, ⟨p.val, skeleton_mono (Nat.le_succ k) p.property⟩) = H (t, p) := by
  classical
  let J := {s : Finset ι // s.card = k + 2}
  have hcell (s : J) := exists_extension_supportFace s.val s.property f H hH
  choose K hK0 hKA using hcell
  obtain ⟨G, hG0, hGA, _⟩ := Topology.exists_continuous_homotopy_gluing
    (skeleton ι k) (fun s : J => supportFace s.val)
    (isClosed_skeleton k) (fun s => isClosed_supportFace s.val)
    (fun s t hst => supportFace_inter_subset_skeleton s.property t.property
      (fun h => hst (Subtype.ext h)))
    f H hH K hK0 (fun s t x hxA hxB => hKA s t ⟨x, hxB⟩ hxA)
  let e : skeleton ι (k + 1) ≃ₜ
      ↥(skeleton ι k ∪ ⋃ s : J, supportFace s.val) :=
    Homeomorph.setCongr (skeleton_succ_eq_union k)
  refine ⟨G.comp ⟨fun z => (z.1, e z.2),
    continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro p
    exact hG0 (e p)
  · intro t p
    exact hGA t p

private theorem exists_extension_skeleton_add (k n : ℕ)
    (f : C(stdSimplex ℝ ι, X)) (H : C(unitInterval × skeleton ι k, X))
    (hH : ∀ p : skeleton ι k, H (0, p) = f p.val) :
    ∃ G : C(unitInterval × skeleton ι (k + n), X),
      (∀ p, G (0, p) = f p.val) ∧
      ∀ t (p : skeleton ι k),
        G (t, ⟨p.val, skeleton_mono (Nat.le_add_right k n) p.property⟩) = H (t, p) := by
  induction n with
  | zero => exact ⟨H, hH, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨G, hG0, hGA⟩ := ih
    obtain ⟨K, hK0, hKA⟩ := exists_extension_skeleton_succ (k + n) f G hG0
    refine ⟨K, hK0, ?_⟩
    intro t p
    exact (hKA t ⟨p.val, skeleton_mono (Nat.le_add_right k n) p.property⟩).trans (hGA t p)

theorem exists_continuous_homotopy_extension_skeleton (k : ℕ)
    (f : C(stdSimplex ℝ ι, X)) (H : C(unitInterval × skeleton ι k, X))
    (hH : ∀ p : skeleton ι k, H (0, p) = f p.val) :
    ∃ F : C(unitInterval × stdSimplex ℝ ι, X),
      (∀ p, F (0, p) = f p) ∧
      ∀ t (p : skeleton ι k), F (t, p.val) = H (t, p) := by
  obtain ⟨G, hG0, hGA⟩ := exists_extension_skeleton_add k (Fintype.card ι) f H hH
  have hfull : skeleton ι (k + Fintype.card ι) = Set.univ := skeleton_eq_univ (by omega)
  have hj (p : stdSimplex ℝ ι) : p ∈ skeleton ι (k + Fintype.card ι) := by
    rw [hfull]
    trivial
  let j : C(stdSimplex ℝ ι, skeleton ι (k + Fintype.card ι)) :=
    ⟨fun p => ⟨p, hj p⟩, continuous_id.subtype_mk hj⟩
  refine ⟨G.comp ⟨fun z => (z.1, j z.2),
    continuous_fst.prodMk (j.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro p
    exact hG0 (j p)
  · intro t p
    exact hGA t p

end DifferentialGeometry.Simplex
