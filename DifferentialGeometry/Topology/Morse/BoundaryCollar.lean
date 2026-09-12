import DifferentialGeometry.Topology.Manifold.BoundaryVectorField

open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Morse

private theorem eq_collar_velocity_of_inverse_velocity
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (c : PartialDiffeomorph (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) (N × ℝ) E ∞)
    {x v : E} (hx : x ∈ c.target)
    (hv : mfderiv 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) c.symm x v = (0, 1)) :
    v = deriv (fun t => c ((c.symm x).1, t)) (c.symm x).2 := by
  have hq := c.toPartialEquiv.map_target hx
  have hc := c.mdifferentiableAt (by simp) hq
  have hi := c.symm.mdifferentiableAt (by simp) hx
  have hright : (c ∘ c.symm) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact c.toPartialEquiv.right_inv hy
  have hid : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c ∘ c.symm) x v : E) = v := by
    have he := congrArg (fun L : E →L[ℝ] E => L v)
      (hright.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)))
    exact he.trans (by rw [mfderiv_id]; rfl)
  let L : (F × ℝ) →L[ℝ] E := mfderiv (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) c (c.symm x)
  have hcomp : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c ∘ c.symm) x v : E) =
      L (mfderiv 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) c.symm x v) :=
    mfderiv_comp_apply x hc hi v
  have hLv : L (0, 1) = v :=
    (congrArg L hv).symm.trans (hcomp.symm.trans hid)
  have hp : HasMFDerivAt 𝓘(ℝ) (J.prod 𝓘(ℝ))
      (fun t : ℝ => ((c.symm x).1, t)) (c.symm x).2
      ((0 : ℝ →L[ℝ] TangentSpace J (c.symm x).1).prod
        (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const (c.symm x).1 (c.symm x).2).prodMk
      (hasMFDerivAt_id (c.symm x).2)
  have hlinear : L.comp ((0 : ℝ →L[ℝ] F).prod (ContinuousLinearMap.id ℝ ℝ)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight v := by
    apply ContinuousLinearMap.ext
    intro r
    change L (0, r) = r • v
    calc
      L (0, r) = L (r • (0, 1)) := by simp
      _ = r • L (0, 1) := map_smul _ _ _
      _ = r • v := by rw [hLv]
  have hf : HasFDerivAt (fun t => c ((c.symm x).1, t))
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) (c.symm x).2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((hc.hasMFDerivAt.comp (c.symm x).2 hp).congr_mfderiv hlinear)
  have hd : HasDerivAt (fun t => c ((c.symm x).1, t)) v (c.symm x).2 := by
    simpa using hf.hasDerivAt
  exact hd.deriv.symm

theorem exists_contDiff_boundary_tangent_vector_field_eq_collar_velocity
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) (Fin (n + 1) → ℝ))
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {g : (Fin (n + 1) → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {c : ℝ}
    (hheight : ∀ q ∈ Φ.source, g (Φ q) = c + q.2)
    {A : Set N} (hA : IsCompact A) {ε : ℝ}
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source)
    (hplane : ∀ x ∈ Φ '' (A ×ˢ Set.Icc (-ε) ε), x 0 ≠ 0)
    {B W : Set (Fin (n + 1) → ℝ)}
    (hB : IsCompact B) (hW : IsOpen W) (hBW : B ⊆ W)
    (hTW : Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ W)
    (hregular : ∀ x ∈ B, x 0 ≠ 0 → fderiv ℝ g x ≠ 0)
    (hboundary : ∀ x ∈ B, x 0 = 0 →
      fderiv ℝ (fun z : Fin n → ℝ => g (Fin.cons 0 z)) (Fin.tail x) ≠ 0) :
    ∃ Y : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      (∀ x, x 0 = 0 → Y x 0 = 0) ∧
      (∀ x, 0 ≤ fderiv ℝ g x (Y x) ∧ fderiv ℝ g x (Y x) ≤ 1) ∧
      ∃ U P : Set (Fin (n + 1) → ℝ), IsOpen U ∧
        B ∪ Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ U ∧ U ⊆ W ∧
        (∀ x ∈ U, fderiv ℝ g x (Y x) = 1) ∧
        IsOpen P ∧ Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P ∧ P ⊆ U ∩ Φ.target ∧
        Set.EqOn Y
          (fun x => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2) P := by
  let d := (Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ)
    (Fin (n + 1) → ℝ) ∞).toPartialDiffeomorph
  let Ψ : PartialDiffeomorph (J.prod 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ)
      (N × ℝ) (Fin (n + 1) → ℝ) ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := hΦ
      contMDiffOn_invFun := hi }
  let D : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}
  let T := Φ '' (A ×ˢ Set.Icc (-ε) ε)
  have hfrontier : frontier D = {x | x 0 = 0} := by
    change frontier ((fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' Set.Ici 0) =
      (fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' {0}
    rw [← (isOpenMap_eval (0 : Fin (n + 1))).preimage_frontier_eq_frontier_preimage
      (continuous_apply 0) (Set.Ici 0), frontier_Ici]
  have hd : d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} :=
    fun _ _ => Iff.rfl
  have hT : IsCompact T :=
    (hA.prod isCompact_Icc).image_of_continuousOn (hΦ.continuousOn.mono hw)
  have hTt : T ⊆ Ψ.target :=
    Set.image_subset_iff.mpr (fun _ hx => Φ.map_source (hw hx))
  have hTD : Disjoint T (frontier D) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    exact hplane x hx (by simpa only [hfrontier, Set.mem_ofPred_eq] using hb)
  have hreg : ∀ x ∈ B, x ∉ frontier D →
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) g x ≠ 0 := by
    intro x hx hn hz
    have hx0 : x 0 ≠ 0 := by
      simpa only [hfrontier, Set.mem_ofPred_eq] using hn
    apply hregular x hx hx0
    exact mfderiv_eq_fderiv.symm.trans hz
  have hcharts : ∀ x ∈ B ∩ frontier D,
      ∃ d : PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℝ)
        𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ) ∞,
        x ∈ d.source ∧ d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} ∧
        fderiv ℝ (fun u : Fin n → ℝ => g (d.symm (Fin.cons 0 u)))
          (Fin.tail (d x)) ≠ 0 := by
    intro x hx
    refine ⟨d, Set.mem_univ _, hd, ?_⟩
    exact hboundary x hx.1 (by simpa only [hfrontier, Set.mem_ofPred_eq] using hx.2)
  obtain ⟨X, hX, hXc, hXs, hbounds, ⟨U, hU, hBTU, hUW, hunit⟩,
      htangent, P, hP, hTP, hPt, hcoord⟩ :=
    Manifold.exists_contMDiff_boundary_tangent_vector_field_eq_collar_velocity
      Ψ hg.contMDiff hheight hB hT hW hBW hTW hTt hTD hreg hcharts
  let Y : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x => X x
  have hrate (x) : NormedSpace.fromTangentSpace (g x)
      (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) g x (X x)) =
      fderiv ℝ g x (Y x) :=
    congrArg (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => L (Y x)) mfderiv_eq_fderiv
  refine ⟨Y, contMDiff_vectorSpace_iff_contDiff.mp hX, hXc, hXs, ?_, ?_,
    U, P ∩ U, hU, hBTU, hUW, ?_, hP.inter hU,
    Set.subset_inter hTP (Set.subset_union_right.trans hBTU),
    (fun _ hx => ⟨hx.2, hPt hx.1⟩), ?_⟩
  · intro x hx
    have hb : x ∈ frontier D := by simpa only [hfrontier, Set.mem_ofPred_eq] using hx
    have ht := htangent n d hd x hb (Set.mem_univ _)
    change (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ) id x (Y x)) 0 = 0 at ht
    rw [mfderiv_id] at ht
    exact ht
  · intro x
    exact (hrate x) ▸ hbounds x
  · intro x hx
    exact (hrate x).symm.trans (hunit x hx)
  · intro x hx
    exact eq_collar_velocity_of_inverse_velocity Ψ (hPt hx.1) (hcoord x hx.1)

end DifferentialGeometry.Topology.Morse
