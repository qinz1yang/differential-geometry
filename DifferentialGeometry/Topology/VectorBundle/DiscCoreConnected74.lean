import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# Draft 74, G32: connectedness of a disc core

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. A closed disc bundle `{z | ‖z.2‖ ≤ T}` over a
connected base is connected (every point is joined to the zero section by the ray `s ↦ s • z`,
and the zero section is the continuous image of the base); hence so is the disc core
`{x : N // ‖(e.symm x).2‖ ≤ T}` carried by a homeomorphism `e` of the total space onto `N`.
The row `SolidParam74` needs a connected piece for every non-closed branch of LFR54.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle

variable {B : Type*} [TopologicalSpace B] [ConnectedSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, NormedSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **A closed disc bundle over a connected base is preconnected.** -/
theorem isPreconnected_closedDiscBundle_R74 (T : ℝ) :
    IsPreconnected {z : TotalSpace F V | ‖z.2‖ ≤ T} := by
  obtain ⟨b₀⟩ := (inferInstance : Nonempty B)
  rcases lt_or_ge T 0 with hT | hT
  · have h : {z : TotalSpace F V | ‖z.2‖ ≤ T} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hT (norm_nonneg _)
    rw [h]
    exact isPreconnected_empty
  · refine isPreconnected_of_forall (zeroSection F V b₀) fun y hy => ?_
    have hy' : ‖y.2‖ ≤ T := hy
    have hray : Continuous fun s : ℝ => (⟨y.proj, s • y.2⟩ : TotalSpace F V) :=
      (FiberBundle.continuous_totalSpaceMk F V y.proj).comp
        (continuous_id.smul continuous_const)
    refine ⟨zeroSection F V '' univ ∪
      (fun s : ℝ => (⟨y.proj, s • y.2⟩ : TotalSpace F V)) '' Icc 0 1, ?_,
      Or.inl ⟨b₀, mem_univ _, rfl⟩, Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩, ?_⟩
    · rintro _ (⟨b, -, rfl⟩ | ⟨s, hs, rfl⟩)
      · change ‖(0 : V b)‖ ≤ T
        rwa [norm_zero]
      · change ‖s • y.2‖ ≤ T
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        calc s * ‖y.2‖ ≤ 1 * ‖y.2‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
          _ ≤ T := by rwa [one_mul]
    · refine IsPreconnected.union (zeroSection F V y.proj) ⟨y.proj, mem_univ _, rfl⟩
        ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [zeroSection]⟩
        (isPreconnected_univ.image _ (continuous_zeroSection ℝ).continuousOn)
        (isPreconnected_Icc.image _ hray.continuousOn)

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [ChartedSpace HB B]

/-- **A disc core over a connected base is connected** (`0 ≤ T`). -/
theorem connectedSpace_discCore_R74
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) {T : ℝ} (hT : 0 ≤ T) :
    ConnectedSpace {x : N // ‖(e.symm x).2‖ ≤ T} := by
  obtain ⟨b₀⟩ := (inferInstance : Nonempty B)
  have hpre : PreconnectedSpace {z : TotalSpace F V // ‖z.2‖ ≤ T} :=
    Subtype.preconnectedSpace (isPreconnected_closedDiscBundle_R74 T)
  have hne : Nonempty {z : TotalSpace F V // ‖z.2‖ ≤ T} :=
    ⟨⟨zeroSection F V b₀, by
      change ‖(0 : V b₀)‖ ≤ T
      rwa [norm_zero]⟩⟩
  have hc : ConnectedSpace {z : TotalSpace F V // ‖z.2‖ ≤ T} :=
    { toPreconnectedSpace := hpre, toNonempty := hne }
  exact (discCoreHomeomorph e T).connectedSpace_iff.mp hc

end DifferentialGeometry.Topology.VectorBundle
