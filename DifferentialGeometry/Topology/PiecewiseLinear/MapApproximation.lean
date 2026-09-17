import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem simplicialMap_eqOn_of_affineOn (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    {s : Finset E} (hs : s ∈ K.faces) {A : E →ᵃ[ℝ] F}
    (hA : EqOn φ A (convexHull ℝ (s : Set E))) :
    EqOn (simplicialMap K φ) φ (convexHull ℝ (s : Set E)) := by
  classical
  intro x hx
  rw [simplicialMap_eq_of_mem K φ hs hx, hA hx]
  have hw := sum_weights hx
  have hvals : ∀ v ∈ s, φ v = A v := fun v hv =>
    hA (subset_convexHull ℝ _ hv)
  have hcomb : s.affineCombination ℝ id (weights s x) = x := by
    rw [Finset.affineCombination_eq_linear_combination s id (weights s x) hw]
    simpa using sum_weights_smul hx
  have hmap := s.map_affineCombination id (weights s x) hw (f := A)
  rw [hcomb] at hmap
  rw [hmap, Finset.affineCombination_eq_linear_combination s (A ∘ id) (weights s x) hw]
  exact Finset.sum_congr rfl fun v hv => by rw [hvals v hv]; rfl

open Classical in
theorem exists_isPiecewiseAffineOn_dist_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : Set E} (hP : IsPolyhedron P) (hPc : IsCompact P)
    {f : E → F} (hf : ContinuousOn f P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F,
      IsPiecewiseAffineOn g P ∧ ∀ x ∈ P, dist (g x) (f x) < ε := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := IsPolyhedron.exists_simplicialComplex hP
  let _ : Finite K.faces := hKfin.to_subtype
  have huc : UniformContinuousOn f P := hPc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  obtain ⟨K', hsub, hK'fin, hK'card, hK'diam⟩ :=
    exists_isSubdivision_diam_lt K (N := Module.finrank ℝ E)
      (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hδ
  let _ : Finite K'.faces := hK'fin.to_subtype
  refine ⟨simplicialMap K' f, ?_, ?_⟩
  · have : K'.space = P := by rw [hsub.space_eq, hKspace]
    rw [← this]
    exact isPiecewiseAffineOn_simplicialMap K' f
  · intro x hx
    have hspace' : K'.space = P := by rw [hsub.space_eq, hKspace]
    have hxK : x ∈ K'.space := by rw [hspace']; exact hx
    set s := carrierFace K' x with hsdef
    have hs : s ∈ K'.faces := carrierFace_mem hxK
    have hxs : x ∈ convexHull ℝ (s : Set E) := mem_convexHull_carrierFace hxK
    have hsubP : (s : Set E) ⊆ P := by
      intro v hv
      rw [← hspace']
      exact K'.convexHull_subset_space hs (subset_convexHull ℝ _ hv)
    have hbdd : Bornology.IsBounded (convexHull ℝ (s : Set E)) :=
      isBounded_convexHull.mpr s.finite_toSet.isBounded
    have hclose' : ∀ v ∈ s, dist (f v) (f x) < ε / 2 := by
      intro v hv
      have hvP : v ∈ P := hsubP hv
      have hd : dist v x ≤ diam (convexHull ℝ (s : Set E)) :=
        dist_le_diam_of_mem hbdd (subset_convexHull ℝ _ hv) hxs
      exact hclose v hvP x hx (lt_of_le_of_lt hd (hK'diam s hs))
    have hsum : simplicialMap K' f x - f x = ∑ v ∈ s, weights s x v • (f v - f x) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_weights hxs, one_smul]
      rfl
    have hbound : ‖simplicialMap K' f x - f x‖ ≤ ε / 2 := by
      rw [hsum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ v ∈ s, ‖weights s x v • (f v - f x)‖
          ≤ ∑ v ∈ s, weights s x v * (ε / 2) := by
            refine Finset.sum_le_sum fun v hv => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weights_nonneg hxs hv)]
            exact mul_le_mul_of_nonneg_left
              (le_of_lt (by simpa [dist_eq_norm] using hclose' v hv)) (weights_nonneg hxs hv)
        _ = ε / 2 := by rw [← Finset.sum_mul, sum_weights hxs, one_mul]
    calc dist (simplicialMap K' f x) (f x) = ‖simplicialMap K' f x - f x‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hbound
      _ < ε := by linarith

end DifferentialGeometry.Topology.PiecewiseLinear
