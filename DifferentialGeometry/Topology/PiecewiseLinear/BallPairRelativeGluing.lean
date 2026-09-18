import DifferentialGeometry.Topology.PiecewiseLinear.BallPairCutConfig
import DifferentialGeometry.Topology.PiecewiseLinear.ConeDiskPairExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPLSphere.exists_isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ} {S : Set E} {S' : Set F} (hS : IsPLSphere n S) (hS' : IsPLSphere n S') :
    ∃ f : E → F, IsPLHomeomorphOn f S S' := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨a', ha'⟩ := hS'
  exact ⟨a' ∘ Function.invFunOn a (stdSimplexBoundary (n + 1)), ha.symm.trans ha'⟩

theorem pair_inter_coneSet {z y : E} {X : Set E} (hy : y ∉ coneSet z X) :
    ({z, y} : Set E) ∩ coneSet z X = {z} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hxc⟩
    · exact hx
    · rw [hx] at hxc
      exact absurd hxc hy
  · intro hx
    refine ⟨Or.inl hx, ?_⟩
    rw [hx]
    exact apex_mem_coneSet z X

theorem pair_eq_inter_coneSet_union {z y : E} {X : Set E} (hy : y ∉ coneSet z X) :
    ({z, y} : Set E) = ({z, y} : Set E) ∩ coneSet z X ∪ {y} := by
  rw [pair_inter_coneSet hy, Set.singleton_union]

theorem isPLBallPair_union_of_coneSet_disk [FiniteDimensional ℝ E]
    (hn : Module.finrank ℝ E = 3)
    {p₁ p₂ z y₁ y₂ : E} {L₁ L₂ L₀ : Geometry.SimplicialComplex ℝ E}
    (hfin₁ : L₁.faces.Finite) (hfin₂ : L₂.faces.Finite) (hfin₀ : L₀.faces.Finite)
    (hL₁ : IsConeBase p₁ L₁) (hL₂ : IsConeBase p₂ L₂) (hL₀ : IsConeBase z L₀)
    (hS₁ : IsPLSphere 2 L₁.space) (hS₂ : IsPLSphere 2 L₂.space) (hS₀ : IsPLSphere 1 L₀.space)
    (hD₁ : coneSet z L₀.space ⊆ L₁.space) (hD₂ : coneSet z L₀.space ⊆ L₂.space)
    (hy₁ : y₁ ∈ L₁.space) (hy₁D : y₁ ∉ coneSet z L₀.space)
    (hy₂ : y₂ ∈ L₂.space) (hy₂D : y₂ ∉ coneSet z L₀.space)
    (hmeet : coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space = coneSet z L₀.space) :
    IsPLBallPair 2 1 (coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space)
      (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) := by
  classical
  obtain ⟨P₁, P₂, w, u₁, u₂, M₁, M₂, M₀, hfM₁, hfM₂, hfM₀, hcM₁, hcM₂, hcM₀, hsM₁, hsM₂, hsM₀,
    hDM₁, hDM₂, hu₁M, hu₁D, hu₂M, hu₂D, hmeetM, -, -, -, -, -, -, hpairM⟩ :=
    exists_cutModel_data (E := E) hn
  have _ : Finite L₁.faces := hfin₁.to_subtype
  have _ : Finite L₂.faces := hfin₂.to_subtype
  have _ : Finite L₀.faces := hfin₀.to_subtype
  have _ : Finite M₁.faces := hfM₁.to_subtype
  have _ : Finite M₂.faces := hfM₂.to_subtype
  have _ : Finite M₀.faces := hfM₀.to_subtype
  have hzL₁ : z ∈ L₁.space := hD₁ (apex_mem_coneSet z L₀.space)
  have hzL₂ : z ∈ L₂.space := hD₂ (apex_mem_coneSet z L₀.space)
  have hwM₁ : w ∈ M₁.space := hDM₁ (apex_mem_coneSet w M₀.space)
  have hwM₂ : w ∈ M₂.space := hDM₂ (apex_mem_coneSet w M₀.space)
  have hX₁ : ({z, y₁} : Set E) ⊆ L₁.space := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact hzL₁
    · rw [Set.mem_singleton_iff.mp h]
      exact hy₁
  have hX₂ : ({z, y₂} : Set E) ⊆ L₂.space := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact hzL₂
    · rw [Set.mem_singleton_iff.mp h]
      exact hy₂
  have hDball : IsPLBall 2 (coneSet z L₀.space) := by
    rw [← coneComplex_space_eq_coneSet hL₀]
    exact hL₀.isPLBall_of_isPLSphere hS₀
  have hball₁ : IsPLBall 3 (coneSet p₁ L₁.space) := by
    rw [← coneComplex_space_eq_coneSet hL₁]
    exact hL₁.isPLBall_of_isPLSphere hS₁
  have hball₂ : IsPLBall 3 (coneSet p₂ L₂.space) := by
    rw [← coneComplex_space_eq_coneSet hL₂]
    exact hL₂.isPLBall_of_isPLSphere hS₂
  obtain ⟨f₀, hf₀⟩ := hS₀.exists_isPLHomeomorphOn (F := E) hsM₀
  obtain ⟨g, hg, -, hgz, -⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hL₀ (subset_refl L₀.space) hcM₀ hf₀ hf₀.image_eq
  have hgim : g '' (({z, y₁} : Set E) ∩ coneSet z L₀.space) = ({w, u₁} : Set E) ∩ coneSet w M₀.space
      := by
    rw [pair_inter_coneSet hy₁D, pair_inter_coneSet hu₁D, Set.image_singleton, hgz]
  have hgim₂ : g '' (({z, y₂} : Set E) ∩ coneSet z L₀.space) =
      ({w, u₂} : Set E) ∩ coneSet w M₀.space := by
    rw [pair_inter_coneSet hy₂D, pair_inter_coneSet hu₂D, Set.image_singleton, hgz]
  obtain ⟨G₁, hG₁, hG₁eq, -, hG₁X⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hL₁ hX₁ hS₁ hcM₁ hsM₁ hDball hD₁ hDM₁ hg
      ⟨subset_closure ⟨hy₁, hy₁D⟩, hy₁D⟩ ⟨subset_closure ⟨hu₁M, hu₁D⟩, hu₁D⟩
      (pair_eq_inter_coneSet_union hy₁D) (pair_eq_inter_coneSet_union hu₁D) hgim
  obtain ⟨G₂, hG₂, hG₂eq, -, hG₂X⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hL₂ hX₂ hS₂ hcM₂ hsM₂ hDball hD₂ hDM₂ hg
      ⟨subset_closure ⟨hy₂, hy₂D⟩, hy₂D⟩ ⟨subset_closure ⟨hu₂M, hu₂D⟩, hu₂D⟩
      (pair_eq_inter_coneSet_union hy₂D) (pair_eq_inter_coneSet_union hu₂D) hgim₂
  have hEq : EqOn G₁ G₂ (coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space) := by
    rw [hmeet]
    exact (hG₁eq.trans hG₂eq.symm)
  have hmeetim : G₁ '' (coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space) =
      coneSet P₁ M₁.space ∩ coneSet P₂ M₂.space := by
    rw [hmeet, hmeetM, hG₁eq.image_eq, hg.image_eq]
  have hΦ := hG₁.piecewise hG₂ hball₁.isPolyhedron hball₂.isPolyhedron hEq hmeetim
  set Φ := (coneSet p₁ L₁.space).piecewise G₁ G₂ with hΦdef
  have hΦ₁ : EqOn Φ G₁ (coneSet p₁ L₁.space) := (coneSet p₁ L₁.space).piecewise_eqOn G₁ G₂
  have hΦ₂ : EqOn Φ G₂ (coneSet p₂ L₂.space) := by
    intro x hx
    by_cases hx₁ : x ∈ coneSet p₁ L₁.space
    · rw [hΦdef, Set.piecewise_eq_of_mem _ _ _ hx₁, hEq ⟨hx₁, hx⟩]
    · rw [hΦdef, Set.piecewise_eq_of_notMem _ _ _ hx₁]
  have hsub₁ : coneSet p₁ ({z, y₁} : Set E) ⊆ coneSet p₁ L₁.space := coneSet_mono p₁ hX₁
  have hsub₂ : coneSet p₂ ({z, y₂} : Set E) ⊆ coneSet p₂ L₂.space := coneSet_mono p₂ hX₂
  have harcsub : coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E) ⊆
      coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space :=
    Set.union_subset_union hsub₁ hsub₂
  have hΦarc : Φ '' (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) =
      coneSet P₁ ({w, u₁} : Set E) ∪ coneSet P₂ ({w, u₂} : Set E) := by
    rw [Set.image_union, (hΦ₁.mono hsub₁).image_eq, (hΦ₂.mono hsub₂).image_eq, hG₁X, hG₂X]
  have hinv := (hΦ.bijOn.invOn_invFunOn.1.mono harcsub).image_image
  refine hpairM.of_isPLHomeomorphOn hΦ.symm ?_
  rw [← hΦarc, hinv]

end DifferentialGeometry.Topology.PiecewiseLinear
