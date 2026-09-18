import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision

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

open Classical in
theorem exists_isPiecewiseAffineOn_dist_lt_eqOn_of_dist_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    (hPc : IsCompact P)
    {f u : E → F} (hf : ContinuousOn f P) (hu : IsPiecewiseAffineOn u Q)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hclose₀ : ∀ x ∈ Q, dist (u x) (f x) ≤ δ) (hε : 0 < ε) :
    ∃ g : E → F, IsPiecewiseAffineOn g P ∧ EqOn g u Q ∧
      ∀ x ∈ P, dist (g x) (f x) < δ + ε := by
  classical
  set φ : E → F := Q.piecewise u f with hφdef
  have hφQ : EqOn φ u Q := fun y hy => Set.piecewise_eq_of_mem _ _ _ hy
  have hφclose : ∀ v ∈ P, dist (φ v) (f v) ≤ δ := by
    intro v hv
    by_cases hvQ : v ∈ Q
    · rw [hφQ hvQ]; exact hclose₀ v hvQ
    · have hv' : φ v = f v := Set.piecewise_eq_of_notMem _ _ _ hvQ
      rw [hv', dist_self]
      exact hδ
  obtain ⟨K, hKfin, hKspace⟩ := IsPolyhedron.exists_simplicialComplex hP
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R₀, hR₀, hR₀fin, hR₀Q⟩ :=
    exists_isSubdivision_restrict_space K hQ (by rw [hKspace]; exact hQP)
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  set L := restrict R₀ Q with hLdef
  have hLfin : L.faces.Finite := hR₀fin.subset (restrict_faces_subset R₀ Q)
  let _ : Finite L.faces := hLfin.to_subtype
  have hLspace : L.space = Q := hR₀Q
  obtain ⟨L', hL', hL'fin, hL'aff⟩ :=
    exists_isSubdivision_affineOn_faces_finite L (fun _ : Unit => u)
      (fun _ => by rw [hLspace]; exact hu)
  let _ : Finite L'.faces := hL'fin.to_subtype
  obtain ⟨R₁, hR₁, hR₁fin, -, hL'R₁, -⟩ :=
    exists_isSubdivision_extension_of_disjoint (K := R₀) (A := ⊥) (B := L)
      (by rw [Geometry.SimplicialComplex.faces_bot]; exact Set.empty_subset _)
      (restrict_faces_subset R₀ Q)
      (by rw [Geometry.SimplicialComplex.space_bot]; exact disjoint_bot_left) hL'
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  have hR₁space : R₁.space = P := by rw [hR₁.space_eq, hR₀.space_eq, hKspace]
  have hL'space : L'.space = Q := by rw [hL'.space_eq, hLspace]
  have huc : UniformContinuousOn f P := hPc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ₀, hδ₀, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  obtain ⟨K'', hK'', hK''fin, -, hK''diam⟩ :=
    exists_isSubdivision_diam_lt R₁ (N := Module.finrank ℝ E)
      (fun s hs => card_le_finrank_succ_of_mem_faces R₁ hs) hδ₀
  let _ : Finite K''.faces := hK''fin.to_subtype
  have hK''space : K''.space = P := by rw [hK''.space_eq, hR₁space]
  refine ⟨simplicialMap K'' φ, by rw [← hK''space]; exact isPiecewiseAffineOn_simplicialMap K'' φ,
    ?_, ?_⟩
  · intro x hx
    have hxK : x ∈ K''.space := by rw [hK''space]; exact hQP hx
    have hres : IsSubdivision (restrict K'' L'.space) L' := hK''.restrict L' hL'R₁
    have hxres : x ∈ (restrict K'' L'.space).space := by
      rw [hres.space_eq, hL'space]; exact hx
    obtain ⟨t, ht, hxt⟩ := (restrict K'' L'.space).mem_space_iff.mp hxres
    have hcar : carrierFace K'' x ⊆ t := carrierFace_subset hxK ht.1 hxt
    have hcarQ : convexHull ℝ ((carrierFace K'' x : Finset E) : Set E) ⊆ L'.space :=
      (convexHull_mono (Finset.coe_subset.mpr hcar)).trans ht.2
    obtain ⟨t', ht', hsu⟩ := hres.2 (carrierFace K'' x) ⟨carrierFace_mem hxK, hcarQ⟩
    obtain ⟨A, hA⟩ := hL'aff () t' ht'
    have hQhull : convexHull ℝ ((carrierFace K'' x : Finset E) : Set E) ⊆ Q := by
      rw [← hL'space]; exact hcarQ
    refine (simplicialMap_eqOn_of_affineOn K'' φ (carrierFace_mem hxK) (A := A)
      (fun y hy => ?_) (mem_convexHull_carrierFace hxK)).trans (hφQ hx)
    rw [hφQ (hQhull hy)]
    exact hA (hsu hy)
  · intro x hx
    have hxK : x ∈ K''.space := by rw [hK''space]; exact hx
    set s := carrierFace K'' x with hsdef
    have hs : s ∈ K''.faces := carrierFace_mem hxK
    have hxs : x ∈ convexHull ℝ (s : Set E) := mem_convexHull_carrierFace hxK
    have hsubP : (s : Set E) ⊆ P := by
      intro v hv
      rw [← hK''space]
      exact K''.convexHull_subset_space hs (subset_convexHull ℝ _ hv)
    have hbdd : Bornology.IsBounded (convexHull ℝ (s : Set E)) :=
      isBounded_convexHull.mpr s.finite_toSet.isBounded
    have hclose' : ∀ v ∈ s, dist (φ v) (f x) ≤ δ + ε / 2 := by
      intro v hv
      refine (dist_triangle (φ v) (f v) (f x)).trans (add_le_add (hφclose v (hsubP hv)) ?_)
      exact le_of_lt (hclose v (hsubP hv) x hx
        (lt_of_le_of_lt (dist_le_diam_of_mem hbdd (subset_convexHull ℝ _ hv) hxs)
          (hK''diam s hs)))
    have hsum : simplicialMap K'' φ x - f x = ∑ v ∈ s, weights s x v • (φ v - f x) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_weights hxs, one_smul]
      rfl
    have hbound : ‖simplicialMap K'' φ x - f x‖ ≤ δ + ε / 2 := by
      rw [hsum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ v ∈ s, ‖weights s x v • (φ v - f x)‖
          ≤ ∑ v ∈ s, weights s x v * (δ + ε / 2) := by
            refine Finset.sum_le_sum fun v hv => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weights_nonneg hxs hv)]
            exact mul_le_mul_of_nonneg_left
              (by simpa [dist_eq_norm] using hclose' v hv) (weights_nonneg hxs hv)
        _ = δ + ε / 2 := by rw [← Finset.sum_mul, sum_weights hxs, one_mul]
    calc dist (simplicialMap K'' φ x) (f x) = ‖simplicialMap K'' φ x - f x‖ := dist_eq_norm _ _
      _ ≤ δ + ε / 2 := hbound
      _ < δ + ε := by linarith

theorem exists_isPiecewiseAffineOn_dist_lt_eqOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    (hPc : IsCompact P)
    {f : E → F} (hf : ContinuousOn f P) (hfQ : IsPiecewiseAffineOn f Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, IsPiecewiseAffineOn g P ∧ EqOn g f Q ∧ ∀ x ∈ P, dist (g x) (f x) < ε := by
  obtain ⟨g, hg, hgQ, hgd⟩ :=
    exists_isPiecewiseAffineOn_dist_lt_eqOn_of_dist_le hP hQ hQP hPc hf hfQ
      (δ := 0) le_rfl (fun x _ => by rw [dist_self]) hε
  exact ⟨g, hg, hgQ, fun x hx => by simpa using hgd x hx⟩


end DifferentialGeometry.Topology.PiecewiseLinear
