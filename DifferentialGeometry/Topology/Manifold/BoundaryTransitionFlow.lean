import DifferentialGeometry.Topology.Diffeomorph.BoundaryFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem contMDiff_tangentSection_self_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ContDiff ℝ ∞ v) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x : E => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine hv.contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [trivializationAt_model_space_apply]

private theorem image_eq_self_of_mem_iff {α : Type*} {f : α ≃ α} {S : Set α}
    (h : ∀ x, f x ∈ S ↔ x ∈ S) : f '' S = S := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    exact (h (f.symm y)).mp (by simpa using hy)

omit [NormedSpace ℝ G] in
private theorem frontier_halfSpace :
    frontier {z : ℝ × G | 0 ≤ z.1} = {z : ℝ × G | z.1 = 0} := by
  change frontier (Prod.fst ⁻¹' Ici (0 : ℝ)) = Prod.fst ⁻¹' {(0 : ℝ)}
  rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst (Ici (0 : ℝ)),
    frontier_Ici]

private noncomputable def halfSpaceIdentityPD :
    PartialDiffeomorph 𝓘(ℝ, ℝ × G) 𝓘(ℝ, ℝ × G) (ℝ × G) (ℝ × G) ∞ where
  toFun := id
  invFun := id
  source := univ
  target := univ
  map_source' := by intro x _; trivial
  map_target' := by intro x _; trivial
  left_inv' := by intro x _; rfl
  right_inv' := by intro x _; rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

theorem compactSupportFlow_mem_iff_of_eq_zero_on_frontier
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport X)) (D : Set M)
    (hzero : ∀ p ∈ frontier D, X p = 0) :
    let Φ := compactSupportFlow X hX hsupp
    ∀ (t : ℝ) (x : M),
      (Φ t x ∈ frontier D ↔ x ∈ frontier D) ∧
      (Φ t x ∈ D ↔ x ∈ D) ∧
      ((Φ t).symm x ∈ frontier D ↔ x ∈ frontier D) ∧
      ((Φ t).symm x ∈ D ↔ x ∈ D) := by
  intro Φ t x
  exact compactSupportFlow_mem_iff_of_boundary_tangent (E := F) X hX hsupp D
    (fun p hp hpne => absurd (hzero p hp) hpne) t x

theorem compactSupportFlow_halfSpace_mem_iff
    [FiniteDimensional ℝ G]
    (X : (z : ℝ × G) → TangentSpace 𝓘(ℝ, ℝ × G) z)
    (hX : ContMDiff 𝓘(ℝ, ℝ × G) (𝓘(ℝ, ℝ × G)).tangent ∞
      (fun z : ℝ × G => (⟨z, X z⟩ : TangentBundle (𝓘(ℝ, ℝ × G)) (ℝ × G))))
    (hsupp : IsCompact (tsupport X))
    (htangent : ∀ z : ℝ × G, z.1 = 0 → (X z).1 = 0) :
    let Φ := compactSupportFlow X hX hsupp
    ∀ (t : ℝ) (x : ℝ × G),
      (Φ t x ∈ {z : ℝ × G | z.1 = 0} ↔ x ∈ {z : ℝ × G | z.1 = 0}) ∧
      (Φ t x ∈ {z : ℝ × G | 0 ≤ z.1} ↔ x ∈ {z : ℝ × G | 0 ≤ z.1}) ∧
      ((Φ t).symm x ∈ {z : ℝ × G | z.1 = 0} ↔ x ∈ {z : ℝ × G | z.1 = 0}) ∧
      ((Φ t).symm x ∈ {z : ℝ × G | 0 ≤ z.1} ↔ x ∈ {z : ℝ × G | 0 ≤ z.1}) := by
  intro Φ t x
  have h := compactSupportFlow_mem_iff_of_boundary_tangent X hX hsupp {z : ℝ × G | 0 ≤ z.1}
    (by
      intro p hp _
      refine ⟨halfSpaceIdentityPD, mem_univ p, ?_, ?_⟩
      · intro y _
        change (id y ∈ {z : ℝ × G | 0 ≤ z.1} ↔ y ∈ {z : ℝ × G | 0 ≤ z.1})
        exact Iff.rfl
      · intro y hy
        have hval :
            mfderiv 𝓘(ℝ, ℝ × G) 𝓘(ℝ, ℝ × G) halfSpaceIdentityPD y (X y) = X y := by
          simp only [halfSpaceIdentityPD]
          rw [mfderiv_id]
          rfl
        rw [hval]
        rw [frontier_halfSpace] at hy
        exact htangent y hy.1)
  have h1 := h t x
  rw [frontier_halfSpace] at h1
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem compactSupportFlow_halfSpace_image_eq
    [FiniteDimensional ℝ G]
    (X : (z : ℝ × G) → TangentSpace 𝓘(ℝ, ℝ × G) z)
    (hX : ContMDiff 𝓘(ℝ, ℝ × G) (𝓘(ℝ, ℝ × G)).tangent ∞
      (fun z : ℝ × G => (⟨z, X z⟩ : TangentBundle (𝓘(ℝ, ℝ × G)) (ℝ × G))))
    (hsupp : IsCompact (tsupport X))
    (htangent : ∀ z : ℝ × G, z.1 = 0 → (X z).1 = 0) (t : ℝ) :
    let Φ := compactSupportFlow X hX hsupp
    Φ t '' {z : ℝ × G | 0 ≤ z.1} = {z : ℝ × G | 0 ≤ z.1} ∧
      Φ t '' {z : ℝ × G | z.1 = 0} = {z : ℝ × G | z.1 = 0} ∧
      Φ t '' {z : ℝ × G | 0 < z.1} = {z : ℝ × G | 0 < z.1} ∧
      (Φ t).symm '' {z : ℝ × G | 0 ≤ z.1} = {z : ℝ × G | 0 ≤ z.1} ∧
      (Φ t).symm '' {z : ℝ × G | z.1 = 0} = {z : ℝ × G | z.1 = 0} ∧
      (Φ t).symm '' {z : ℝ × G | 0 < z.1} = {z : ℝ × G | 0 < z.1} := by
  intro Φ
  have hmem := compactSupportFlow_halfSpace_mem_iff X hX hsupp htangent
  dsimp only at hmem
  have hpt := hmem t
  have himage₁ : Φ t '' {z : ℝ × G | 0 ≤ z.1} = {z : ℝ × G | 0 ≤ z.1} :=
    image_eq_self_of_mem_iff (f := (Φ t).toEquiv) (fun x => (hpt x).2.1)
  have himage₂ : Φ t '' {z : ℝ × G | z.1 = 0} = {z : ℝ × G | z.1 = 0} :=
    image_eq_self_of_mem_iff (f := (Φ t).toEquiv) (fun x => (hpt x).1)
  have hsymm₁ : (Φ t).symm '' {z : ℝ × G | 0 ≤ z.1} = {z : ℝ × G | 0 ≤ z.1} :=
    image_eq_self_of_mem_iff (f := (Φ t).symm.toEquiv) (fun x => (hpt x).2.2.2)
  have hsymm₂ : (Φ t).symm '' {z : ℝ × G | z.1 = 0} = {z : ℝ × G | z.1 = 0} :=
    image_eq_self_of_mem_iff (f := (Φ t).symm.toEquiv) (fun x => (hpt x).2.2.1)
  have hinterior : ∀ x : ℝ × G,
      Φ t x ∈ {z : ℝ × G | 0 < z.1} ↔ x ∈ {z : ℝ × G | 0 < z.1} := by
    intro x
    have hD : 0 ≤ (Φ t x).1 ↔ 0 ≤ x.1 := (hpt x).2.1
    have hF : (Φ t x).1 = 0 ↔ x.1 = 0 := (hpt x).1
    have hDinv : 0 ≤ x.1 ↔ 0 ≤ (Φ t x).1 := by
      have h := (hpt (Φ t x)).2.2.2
      rwa [(Φ t).symm_apply_apply x] at h
    have hFinv : x.1 = 0 ↔ (Φ t x).1 = 0 := by
      have h := (hpt (Φ t x)).2.2.1
      rwa [(Φ t).symm_apply_apply x] at h
    constructor
    · intro hx
      have h1 : (0 : ℝ) ≤ x.1 := hD.mp hx.le
      exact lt_of_le_of_ne h1 (fun h0 => absurd (hF.mpr h0.symm) (ne_of_gt hx))
    · intro hx
      have h1 : (0 : ℝ) ≤ (Φ t x).1 := hDinv.mp hx.le
      exact lt_of_le_of_ne h1 (fun h0 => absurd (hFinv.mpr h0.symm) (ne_of_gt hx))
  have hinterior_symm : ∀ x : ℝ × G,
      (Φ t).symm x ∈ {z : ℝ × G | 0 < z.1} ↔ x ∈ {z : ℝ × G | 0 < z.1} := by
    intro x
    have h := hinterior ((Φ t).symm x)
    rw [(Φ t).apply_symm_apply x] at h
    exact h.symm
  have hf₁ : Φ t '' {z : ℝ × G | 0 < z.1} = {z : ℝ × G | 0 < z.1} :=
    image_eq_self_of_mem_iff (f := (Φ t).toEquiv) hinterior
  have hf₂ : (Φ t).symm '' {z : ℝ × G | 0 < z.1} = {z : ℝ × G | 0 < z.1} :=
    image_eq_self_of_mem_iff (f := (Φ t).symm.toEquiv) hinterior_symm
  exact ⟨himage₁, himage₂, hf₁, hsymm₁, hsymm₂, hf₂⟩

theorem compactSupportFlow_eqOn_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) {S : Set M} (hS : tsupport v ⊆ S) (t : ℝ) :
    Set.EqOn (compactSupportFlow v hv hsupp t) id Sᶜ ∧
      Set.EqOn (compactSupportFlow v hv hsupp t).symm id Sᶜ := by
  have h := (compactSupportFlow_eqOn_compl_tsupport v hv hsupp t).imp
    (fun h => h.mono (compl_subset_compl.mpr hS))
    (fun h => h.mono (compl_subset_compl.mpr hS))
  exact h

theorem compactSupportFlow_image_eq_of_subset_compl_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) {A : Set M} (hA : A ⊆ (tsupport v)ᶜ) (t : ℝ) :
    compactSupportFlow v hv hsupp t '' A = A ∧
      (compactSupportFlow v hv hsupp t).symm '' A = A := by
  have h := compactSupportFlow_eqOn_compl_tsupport v hv hsupp t
  refine ⟨?_, ?_⟩
  · rw [(h.1.mono hA).image_eq, Set.image_id]
  · rw [(h.2.mono hA).image_eq, Set.image_id]

theorem exists_nontrivial_halfSpace_transitionFlow :
    ∃ (X : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) z)
      (hX : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ)).tangent ∞
        (fun z : ℝ × ℝ => (⟨z, X z⟩ : TangentBundle (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ))))
      (hsupp : IsCompact (tsupport X)),
      (∀ z : ℝ × ℝ, z.1 = 0 → (X z).1 = 0) ∧
      ∃ t : ℝ, t ≠ 0 ∧ compactSupportFlow X hX hsupp t ≠
        Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ := by
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let b' : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let v : ℝ × ℝ → ℝ × ℝ := fun z => ((0 : ℝ), b z.1 * b' z.2)
  have hv : ContDiff ℝ ∞ v :=
    contDiff_const.prodMk ((b.contDiff.comp contDiff_fst).mul (b'.contDiff.comp contDiff_snd))
  let X : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) z := v
  have hX : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ)).tangent ∞
      (fun z : ℝ × ℝ => (⟨z, X z⟩ : TangentBundle (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ))) :=
    contMDiff_tangentSection_self_of_contDiff hv
  have hsupp : IsCompact (tsupport X) := by
    have hsub : Function.support X ⊆ tsupport b ×ˢ tsupport b' := by
      rintro z hz
      constructor
      · by_contra hcon
        exact hz (by
          change ((0 : ℝ), b z.1 * b' z.2) = ((0 : ℝ), (0 : ℝ))
          rw [image_eq_zero_of_notMem_tsupport hcon, zero_mul])
      · by_contra hcon
        exact hz (by
          change ((0 : ℝ), b z.1 * b' z.2) = ((0 : ℝ), (0 : ℝ))
          rw [image_eq_zero_of_notMem_tsupport hcon, mul_zero])
    have hcl : tsupport X ⊆ tsupport b ×ˢ tsupport b' :=
      closure_minimal hsub ((isClosed_tsupport b).prod (isClosed_tsupport b'))
    exact (b.hasCompactSupport.prod b'.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport X) hcl
  refine ⟨X, hX, hsupp, fun z _ => rfl, ?_⟩
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_pos_compactSupportFlow_height (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) X hX hsupp
      (fun z : ℝ × ℝ => z.2) (B := {(1 / 2, (0 : ℝ))})
      (U := Metric.ball (1 / 2 : ℝ) (1 / 16) ×ˢ Metric.ball (0 : ℝ) (1 / 16))
      isCompact_singleton (Metric.isOpen_ball.prod Metric.isOpen_ball)
      (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨Metric.mem_ball_self (by norm_num), Metric.mem_ball_self (by norm_num)⟩)
      (by
        intro x hx
        have hb1 : b x.1 = 1 := by
          refine b.one_of_mem_closedBall ?_
          have hx1 := hx.1
          rw [Metric.mem_ball, Real.dist_eq] at hx1
          rw [mem_closedBall_iff_norm, Real.norm_eq_abs]
          change |x.1 - 1 / 2| ≤ (1 / 8 : ℝ)
          linarith
        have hb2 : b' x.2 = 1 := by
          refine b'.one_of_mem_closedBall ?_
          have hx2 := hx.2
          rw [Metric.mem_ball, Real.dist_eq] at hx2
          rw [mem_closedBall_iff_norm, Real.norm_eq_abs]
          change |x.2 - 0| ≤ (1 / 8 : ℝ)
          linarith
        have hmf : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (fun z : ℝ × ℝ => z.2) x (X x)
            = (1 : ℝ) := by
          rw [mfderiv_eq_fderiv, fderiv_snd]
          change (X x).2 = (1 : ℝ)
          simp only [X, v, hb1, hb2, mul_one]
        exact hmf)
  refine ⟨δ / 2, by positivity, fun hrefl => ?_⟩
  have hstep := (hlocal (1 / 2, (0 : ℝ)) (by simp) (δ / 2)
    ⟨by linarith, by linarith⟩).2
  have h2 : compactSupportFlow X hX hsupp (δ / 2) (1 / 2, (0 : ℝ)) = (1 / 2, (0 : ℝ)) := by
    rw [hrefl]
    rfl
  rw [h2] at hstep
  have hzero : (((1 / 2, (0 : ℝ)) : ℝ × ℝ)).2 = 0 := rfl
  rw [hzero] at hstep
  linarith

end Diffeomorph
