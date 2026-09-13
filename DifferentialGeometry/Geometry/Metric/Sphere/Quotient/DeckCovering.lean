import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false
noncomputable section

open Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.RoundSphereQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [NeZero n]

noncomputable instance instMulActionDeckGroup (D : RoundSphereQuotient E n) :
    MulAction D.Γ (sphere (0 : E) 1) where
  smul γ q := sphereDiffeo (n := n) (D.ρ γ) q
  one_smul q := by
    apply Subtype.ext
    change (sphereDiffeo (n := n) (D.ρ 1)) q = (q : E)
    simp only [sphereDiffeo_coe]
    rw [map_one]
    rfl
  mul_smul γ δ q := by
    apply Subtype.ext
    change ((sphereDiffeo (n := n) (D.ρ (γ * δ))) q : E)
      = ((sphereDiffeo (n := n) (D.ρ γ)) ((sphereDiffeo (n := n) (D.ρ δ)) q) : E)
    simp only [sphereDiffeo_coe]
    rw [map_mul, LinearIsometryEquiv.coe_mul]
    rfl

noncomputable instance instContinuousConstSMulDeckGroup (D : RoundSphereQuotient E n) :
    ContinuousConstSMul D.Γ (sphere (0 : E) 1) where
  continuous_const_smul γ := (sphereDiffeo (n := n) (D.ρ γ)).contMDiff.continuous

theorem proj_eq_iff_mem_orbit (D : RoundSphereQuotient E n)
    {e₁ e₂ : sphere (0 : E) 1} :
    D.proj e₁ = D.proj e₂ ↔ e₁ ∈ MulAction.orbit D.Γ e₂ := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := D.proj_eq_imp e₁ e₂ h
    refine ⟨γ⁻¹, ?_⟩
    rw [← hγ]
    exact inv_smul_smul γ e₁
  · rintro ⟨γ, hγ⟩
    rw [← hγ]
    exact D.proj_smul γ e₂

theorem exists_nhds_smul_disjoint (D : RoundSphereQuotient E n)
    (e : sphere (0 : E) 1) :
    ∃ U ∈ 𝓝 e, ∀ γ : D.Γ, ((γ • ·) '' U ∩ U).Nonempty → γ = 1 := by
  classical
  have hsep : ∀ γ : D.Γ, γ ≠ 1 → ∃ V : Set (sphere (0 : E) 1),
      IsOpen V ∧ e ∈ V ∧ Disjoint ((γ • ·) '' V) V := by
    intro γ hγ
    have hne : γ • e ≠ e := fun h => hγ (D.action_free γ e h)
    obtain ⟨A, B, hAopen, hBopen, heA, hγeB, hAB⟩ := t2_separation (Ne.symm hne)
    refine ⟨A ∩ (γ • ·) ⁻¹' B,
      hAopen.inter (hBopen.preimage (continuous_const_smul γ)), ⟨heA, hγeB⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro z ⟨y, hyV, rfl⟩ hzV
    exact (Set.disjoint_left.mp hAB) hzV.1 hyV.2
  have hsep' : ∀ γ : D.Γ, ∃ V : Set (sphere (0 : E) 1), IsOpen V ∧ e ∈ V ∧
      (γ = 1 ∨ Disjoint ((γ • ·) '' V) V) := by
    intro γ
    by_cases h : γ = 1
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, Or.inl h⟩
    · obtain ⟨V, h1, h2, h3⟩ := hsep γ h
      exact ⟨V, h1, h2, Or.inr h3⟩
  let W : D.Γ → Set (sphere (0 : E) 1) := fun γ => Classical.choose (hsep' γ)
  have hWopen : ∀ γ, IsOpen (W γ) := fun γ => (Classical.choose_spec (hsep' γ)).1
  have hWmem : ∀ γ, W γ ∈ 𝓝 e := fun γ =>
    (hWopen γ).mem_nhds (Classical.choose_spec (hsep' γ)).2.1
  have hWdisj : ∀ γ, γ ≠ 1 → Disjoint ((γ • ·) '' W γ) (W γ) := by
    intro γ h
    rcases (Classical.choose_spec (hsep' γ)).2.2 with h1 | h1
    · exact absurd h1 h
    · exact h1
  refine ⟨⋂ γ, W γ, Filter.iInter_mem.mpr hWmem, ?_⟩
  intro γ hγ
  by_contra hne
  obtain ⟨z, ⟨⟨y, hyU, hyz⟩, hzU⟩⟩ := hγ
  have hyW : y ∈ W γ := Set.mem_iInter.mp hyU γ
  have hzW : z ∈ W γ := Set.mem_iInter.mp hzU γ
  exact (Set.disjoint_left.mp (hWdisj γ hne)) ⟨y, hyW, hyz⟩ hzW

theorem isOpen_of_isOpen_preimage_proj (D : RoundSphereQuotient E n) {s : Set D.Q}
    (hs : IsOpen (D.proj ⁻¹' s)) : IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let S := D.sectionAt x
  have hxW : x ∈ S.baseNeighborhood := S.mem_baseNeighborhood
  let A : Set S.baseNeighborhood := S.toSphere ⁻¹' (D.proj ⁻¹' s)
  have hAopen : IsOpen A := hs.preimage S.toSphere_contMDiff.continuous
  have hxA : (⟨x, hxW⟩ : S.baseNeighborhood) ∈ A := by
    change D.proj (S.toSphere ⟨x, hxW⟩) ∈ s
    rw [S.toSphere_proj]
    exact hx
  have hnbhd : Subtype.val '' A ∈ 𝓝 x :=
    (S.baseNeighborhood.isOpen.isOpenMap_subtype_val A hAopen).mem_nhds ⟨_, hxA, rfl⟩
  refine Filter.mem_of_superset hnbhd ?_
  rintro y ⟨r, hr, rfl⟩
  change D.proj (S.toSphere r) ∈ s at hr
  rw [S.toSphere_proj r] at hr
  exact hr

theorem isQuotientMap_proj (D : RoundSphereQuotient E n) : Topology.IsQuotientMap D.proj :=
  ⟨Topology.isCoinducing_iff.mpr fun s =>
    ⟨fun hs => D.isOpen_of_isOpen_preimage_proj (s := s) hs, fun hs =>
      hs.preimage D.proj_smooth.continuous⟩, D.proj_surjective⟩

theorem isQuotientCoveringMap_proj (D : RoundSphereQuotient E n) :
    IsQuotientCoveringMap D.proj D.Γ :=
  IsQuotientCoveringMap.mk D.isQuotientMap_proj (instContinuousConstSMulDeckGroup D)
    (fun {_ _} => D.proj_eq_iff_mem_orbit) D.exists_nhds_smul_disjoint

theorem isCoveringMap_proj (D : RoundSphereQuotient E n) : IsCoveringMap D.proj :=
  D.isQuotientCoveringMap_proj.isCoveringMap

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem simplyConnectedSpace_sphere_of_one_lt (hn : 1 < n) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  have hf : Module.finrank ℝ E = n + 1 := Fact.out
  have hpos : 0 < Module.finrank ℝ E := by
    rw [hf]
    omega
  let : Nontrivial E := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one
  have hvnorm : ‖v‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hv
  have hvne : v ≠ 0 := by
    intro h
    rw [h] at hvnorm
    simp at hvnorm
  refine DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one
    v hvnorm ?_
  have hdim : Module.finrank ℝ ((ℝ ∙ v)ᗮ) = n :=
    Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) hvne
  exact Module.one_lt_rank_of_one_lt_finrank (by rw [hdim]; exact hn)

noncomputable def fundamentalGroupEquivDeckGroup (D : RoundSphereQuotient E n) (x₀ : D.Q)
    (hn : 1 < n) : D.Γ ≃* FundamentalGroup D.Q x₀ := by
  letI : SimplyConnectedSpace (sphere (0 : E) 1) :=
    simplyConnectedSpace_sphere_of_one_lt (E := E) (n := n) hn
  exact ((D.isQuotientCoveringMap_proj.fundamentalGroupEquiv
    ⟨(D.sectionAt x₀).toSphere ⟨x₀, (D.sectionAt x₀).mem_baseNeighborhood⟩,
      (D.sectionAt x₀).toSphere_proj _⟩).trans (MulEquiv.inv' D.Γ).symm).symm

theorem subsingleton_deckGroup_iff_subsingleton_fundamentalGroup
    (D : RoundSphereQuotient E n) (x₀ : D.Q) (hn : 1 < n) :
    Subsingleton D.Γ ↔ Subsingleton (FundamentalGroup D.Q x₀) := by
  constructor
  · intro h
    exact ⟨fun a b => (D.fundamentalGroupEquivDeckGroup x₀ hn).symm.injective
      (Subsingleton.elim _ _)⟩
  · intro h
    exact ⟨fun a b => (D.fundamentalGroupEquivDeckGroup x₀ hn).injective
      (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Geometry.RoundSphereQuotient
