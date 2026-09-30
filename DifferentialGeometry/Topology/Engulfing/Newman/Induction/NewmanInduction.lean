import DifferentialGeometry.Topology.Engulfing.MapEngulfingSequence
import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ColumnPreimage

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M]

def engulfingOutsideDimension (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) (q : ℕ) : Prop :=
  ∃ Q : SimplicialComplex ℝ E, Q.faces ⊆ H.faces ∧
    (∀ s ∈ Q.faces, s.card ≤ q) ∧
    ∀ x : K.space, x.1 ∈ H.space → x.1 ∉ Q.space → f x ∈ U

def engulfingDecomposition (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) (q : ℕ) : Prop :=
  ∃ R Q : SimplicialComplex ℝ E,
    R.faces ⊆ H.faces ∧ Q.faces ⊆ H.faces ∧ H.faces = R.faces ∪ Q.faces ∧
    (∀ s ∈ Q.faces, s.card ≤ q) ∧
    ∀ x : K.space, x.1 ∈ R.space → f x ∈ U

theorem engulfingDecomposition.to_outsideDimension {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q : ℕ}
    (h : engulfingDecomposition K H f U q) : engulfingOutsideDimension K H f U q := by
  obtain ⟨R, Q, _, hQH, hfaces, hdim, hR⟩ := h
  refine ⟨Q, hQH, hdim, ?_⟩
  intro x hx hnot
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  rw [hfaces] at hs
  rcases hs with hs | hs
  · exact hR x (R.convexHull_subset_space hs hxs)
  · exact (hnot (Q.convexHull_subset_space hs hxs)).elim

theorem engulfingDecomposition_of_face_card_le (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) {q : ℕ}
    (hdim : ∀ s ∈ H.faces, s.card ≤ q) : engulfingDecomposition K H f U q := by
  refine ⟨⊥, H, empty_subset _, subset_rfl, ?_, hdim, ?_⟩
  · rw [SimplicialComplex.faces_bot, empty_union]
  · intro x hx
    rw [SimplicialComplex.space_bot] at hx
    exact hx.elim

theorem engulfingDecomposition.principal_of_uncovered {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q : ℕ}
    (h : engulfingDecomposition K H f U q) {s : Finset E} (hcard : q ≤ s.card)
    (huncovered : ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ f x ∉ U) :
    ∀ t ∈ H.faces, s ⊆ t → t = s := by
  obtain ⟨R, Q, _, _, hfaces, hdim, hR⟩ := h
  intro t ht hst
  rw [hfaces] at ht
  rcases ht with ht | ht
  · obtain ⟨x, hxs, hnot⟩ := huncovered
    exact (hnot (hR x (R.convexHull_subset_space ht (convexHull_mono hst hxs)))).elim
  · exact (Finset.eq_of_subset_of_card_le hst ((hdim t ht).trans hcard)).symm

def newmanConclusion (K L H : SimplicialComplex ℝ E) (f : C(K.space, M))
    (X U : Set M) (ε : ℝ) : Prop :=
  ∃ (g : C(K.space, M)) (h : M ≃ₜ M),
    (∀ x : K.space, x.1 ∈ L.space → g x = f x) ∧
    (∀ x, dist (g x) (f x) < ε) ∧
    X ∪ g '' (Subtype.val ⁻¹' H.space) ⊆ h '' U ∧
    IsCompact (closure {x | h x ≠ x})

theorem engulfingOutsideDimension.mono_index {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q r : ℕ}
    (h : engulfingOutsideDimension K H f U q) (hqr : q ≤ r) :
    engulfingOutsideDimension K H f U r := by
  obtain ⟨Q, hQH, hdim, hcover⟩ := h
  exact ⟨Q, hQH, fun s hs => (hdim s hs).trans hqr, hcover⟩

theorem engulfingOutsideDimension.mono_open {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U V : Set M} {q : ℕ}
    (h : engulfingOutsideDimension K H f U q) (hUV : U ⊆ V) :
    engulfingOutsideDimension K H f V q := by
  obtain ⟨Q, hQH, hdim, hcover⟩ := h
  exact ⟨Q, hQH, hdim, fun x hx hnot => hUV (hcover x hx hnot)⟩

theorem engulfingOutsideDimension_of_cover (K H R Q : SimplicialComplex ℝ E)
    (f : C(K.space, M)) {U : Set M} {q : ℕ}
    (hQH : Q.faces ⊆ H.faces) (hdim : ∀ s ∈ Q.faces, s.card ≤ q)
    (hcover : H.space ⊆ R.space ∪ Q.space)
    (hR : ∀ x : K.space, x.1 ∈ R.space → f x ∈ U) :
    engulfingOutsideDimension K H f U q := by
  refine ⟨Q, hQH, hdim, ?_⟩
  intro x hx hnot
  exact hR x ((hcover hx).resolve_right hnot)

theorem engulfingOutsideDimension.zero_covered {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M}
    (h : engulfingOutsideDimension K H f U 0) :
    f '' (Subtype.val ⁻¹' H.space) ⊆ U := by
  obtain ⟨Q, _, hdim, hcover⟩ := h
  have hQempty : Q.space = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hpos := Finset.card_pos.mpr (Q.nonempty_of_mem_faces hs)
    have hz := hdim s hs
    omega
  rintro y ⟨x, hx, rfl⟩
  exact hcover x hx (by rw [hQempty]; simp)

theorem newmanConclusion_of_zero_complexity (K L H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) {X U : Set M} (hX : X ⊆ U)
    (hzero : engulfingOutsideDimension K H f U 0) {ε : ℝ} (hε : 0 < ε) :
    newmanConclusion K L H f X U ε := by
  refine ⟨f, Homeomorph.refl M, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro x
    simpa only [dist_self] using hε
  · intro x hx
    refine ⟨x, ?_, rfl⟩
    exact hx.elim (fun h => hX h) (fun h => hzero.zero_covered h)
  · simp

end DifferentialGeometry.Topology.Engulfing
