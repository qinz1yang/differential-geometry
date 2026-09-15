import DifferentialGeometry.Topology.Simplex.Skeleton
import DifferentialGeometry.Topology.ClosedCover
import Mathlib.Topology.UnitInterval

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

def skeletonHomotopyDesc {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (G : (s : {s : Finset ι // s.card = k + 1}) → C(unitInterval × supportFace s.val, X))
    (hG : ∀ (s r : {s : Finset ι // s.card = k + 1}) (t : unitInterval)
      (p : stdSimplex ℝ ι) (hs : p ∈ supportFace s.val) (hr : p ∈ supportFace r.val),
      G s (t, ⟨p, hs⟩) = G r (t, ⟨p, hr⟩)) :
    C(unitInterval × skeleton ι k, X) := by
  classical
  let P := unitInterval × skeleton ι k
  let S : {s : Finset ι // s.card = k + 1} → Set P :=
    fun s => {z | z.2.val ∈ supportFace s.val}
  let φ : ∀ s, C(S s, X) := fun s =>
    ⟨fun z => G s (z.val.1, ⟨z.val.2.val, z.property⟩),
      (G s).continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val)).subtype_mk _))⟩
  have hφ : ∀ s r z (hs : z ∈ S s) (hr : z ∈ S r),
      φ s ⟨z, hs⟩ = φ r ⟨z, hr⟩ := fun s r z hs hr => hG s r z.1 z.2.val hs hr
  have hcov : ⋃ s, S s = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨s, hs, hp⟩ := (mem_skeleton_iff_exists_supportFace_card_eq hk).mp z.2.property
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hp⟩
  have hclosed : ∀ s, IsClosed (S s) := fun s =>
    (isClosed_supportFace s.val).preimage (continuous_subtype_val.comp continuous_snd)
  exact ContinuousMap.liftClosedCover S φ hφ hcov hclosed (locallyFinite_of_finite _)

@[simp] theorem skeletonHomotopyDesc_supportFace {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (G : (s : {s : Finset ι // s.card = k + 1}) → C(unitInterval × supportFace s.val, X))
    (hG : ∀ (s r : {s : Finset ι // s.card = k + 1}) (t : unitInterval)
      (p : stdSimplex ℝ ι) (hs : p ∈ supportFace s.val) (hr : p ∈ supportFace r.val),
      G s (t, ⟨p, hs⟩) = G r (t, ⟨p, hr⟩))
    (s : {s : Finset ι // s.card = k + 1}) (t : unitInterval) (p : supportFace s.val) :
    skeletonHomotopyDesc hk G hG
      (t, ⟨p.val, supportFace_subset_skeleton s.property.le p.property⟩) = G s (t, p) := by
  classical
  let P := unitInterval × skeleton ι k
  let S : {s : Finset ι // s.card = k + 1} → Set P :=
    fun s => {z | z.2.val ∈ supportFace s.val}
  let φ : ∀ s, C(S s, X) := fun s =>
    ⟨fun z => G s (z.val.1, ⟨z.val.2.val, z.property⟩),
      (G s).continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val)).subtype_mk _))⟩
  have hφ : ∀ s r z (hs : z ∈ S s) (hr : z ∈ S r),
      φ s ⟨z, hs⟩ = φ r ⟨z, hr⟩ := fun s r z hs hr => hG s r z.1 z.2.val hs hr
  have hcov : ⋃ s, S s = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨s, hs, hp⟩ := (mem_skeleton_iff_exists_supportFace_card_eq hk).mp z.2.property
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hp⟩
  have hclosed : ∀ s, IsClosed (S s) := fun s =>
    (isClosed_supportFace s.val).preimage (continuous_subtype_val.comp continuous_snd)
  exact ContinuousMap.liftClosedCover_coe (S := S) (φ := φ) (hφ := hφ)
    (hcov := hcov) (hclosed := hclosed) (hfinite := locallyFinite_of_finite _) (i := s)
    ⟨(t, ⟨p.val, supportFace_subset_skeleton s.property.le p.property⟩), p.property⟩

theorem skeletonHomotopyDesc_eq {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (G : (s : {s : Finset ι // s.card = k + 1}) → C(unitInterval × supportFace s.val, X))
    (hG : ∀ (s r : {s : Finset ι // s.card = k + 1}) (t : unitInterval)
      (p : stdSimplex ℝ ι) (hs : p ∈ supportFace s.val) (hr : p ∈ supportFace r.val),
      G s (t, ⟨p, hs⟩) = G r (t, ⟨p, hr⟩))
    (t : unitInterval) (f : stdSimplex ℝ ι → X)
    (hf : ∀ (s : {s : Finset ι // s.card = k + 1}) (p : supportFace s.val),
      G s (t, p) = f p.val)
    (p : skeleton ι k) : skeletonHomotopyDesc hk G hG (t, p) = f p.val := by
  obtain ⟨s, hs, hp⟩ := (mem_skeleton_iff_exists_supportFace_card_eq hk).mp p.property
  exact (skeletonHomotopyDesc_supportFace hk G hG ⟨s, hs⟩ t ⟨p.val, hp⟩).trans
    (hf ⟨s, hs⟩ ⟨p.val, hp⟩)

theorem skeletonHomotopyDesc_zero {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (G : (s : {s : Finset ι // s.card = k + 1}) → C(unitInterval × supportFace s.val, X))
    (hG : ∀ (s r : {s : Finset ι // s.card = k + 1}) (t : unitInterval)
      (p : stdSimplex ℝ ι) (hs : p ∈ supportFace s.val) (hr : p ∈ supportFace r.val),
      G s (t, ⟨p, hs⟩) = G r (t, ⟨p, hr⟩))
    (f : stdSimplex ℝ ι → X)
    (hf : ∀ (s : {s : Finset ι // s.card = k + 1}) (p : supportFace s.val),
      G s (0, p) = f p.val)
    (p : skeleton ι k) : skeletonHomotopyDesc hk G hG (0, p) = f p.val :=
  skeletonHomotopyDesc_eq hk G hG 0 f hf p

end DifferentialGeometry.Simplex
