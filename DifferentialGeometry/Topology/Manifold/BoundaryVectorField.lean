import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic

open scoped ContDiff Manifold Topology

namespace Manifold

private theorem fderiv_mem_ker_of_eventually_mapsTo_ker
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x v : E} (ℓ : E →L[ℝ] ℝ) (m : F →L[ℝ] ℝ)
    (hf : DifferentiableAt ℝ f x) (hx : ℓ x = 0) (hv : ℓ v = 0)
    (hmap : ∀ᶠ y in 𝓝 x, ℓ y = 0 → m (f y) = 0) :
    m (fderiv ℝ f x v) = 0 := by
  let γ : ℝ → E := fun t => x + t • v
  have hγ : HasDerivAt γ v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp only [γ, zero_smul, add_zero]
  have hγt : Filter.Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using (hγ.continuousAt.tendsto)
  have heq : (fun t => m (f (γ t))) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [hγt.eventually hmap] with t ht
    apply ht
    simp only [γ, map_add, map_smul, hx, hv, smul_zero, add_zero]
  have hcomp := (m.hasFDerivAt.comp x hf.hasFDerivAt).comp_hasDerivAt_of_eq
    0 hγ hγ0.symm
  have hzero : HasDerivAt (fun t => m (f (γ t))) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
  exact hcomp.unique hzero

private theorem fderiv_preserves_boundary_hyperplane
    {n m : ℕ} (Φ : OpenPartialHomeomorph (Fin (n + 1) → ℝ) (Fin (m + 1) → ℝ))
    {x v : Fin (n + 1) → ℝ} (hx : x ∈ Φ.source)
    (hΦ : DifferentiableAt ℝ Φ x) (hx0 : x 0 = 0) (hv0 : v 0 = 0)
    (hboundary : ∀ y ∈ Φ.source, y 0 = 0 → Φ y 0 = 0) :
    (fderiv ℝ Φ x v) 0 = 0 := by
  apply fderiv_mem_ker_of_eventually_mapsTo_ker
    (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 0) hΦ hx0 hv0
  filter_upwards [Φ.open_source.mem_nhds hx] with y hy
  exact hboundary y hy

private theorem frontier_coordinate_halfspace (n : ℕ) :
    frontier {x : Fin (n + 1) → ℝ | 0 ≤ x 0} = {x | x 0 = 0} := by
  change frontier ((fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' Set.Ici 0) =
    (fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' {0}
  rw [← (isOpenMap_eval (0 : Fin (n + 1))).preimage_frontier_eq_frontier_preimage
    (continuous_apply 0) (Set.Ici 0), frontier_Ici]

private theorem fderiv_preserves_boundary_hyperplane_of_isImage
    {n m : ℕ} (Φ : OpenPartialHomeomorph (Fin (n + 1) → ℝ) (Fin (m + 1) → ℝ))
    (hhalf : Φ.IsImage {x | 0 ≤ x 0} {y | 0 ≤ y 0})
    {x v : Fin (n + 1) → ℝ} (hx : x ∈ Φ.source)
    (hΦ : DifferentiableAt ℝ Φ x) (hx0 : x 0 = 0) (hv0 : v 0 = 0) :
    (fderiv ℝ Φ x v) 0 = 0 := by
  apply fderiv_preserves_boundary_hyperplane Φ hx hΦ hx0 hv0
  intro y hy hy0
  have h := hhalf.frontier hy
  rw [frontier_coordinate_halfspace, frontier_coordinate_halfspace] at h
  exact h.mpr hy0

private theorem contMDiff_normalized_chart_vector_field
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (v : E) :
    let a : E → ℝ := fun z => fderiv ℝ (fun w => g (c.symm w)) z v
    let V : E → E := fun z => (a z)⁻¹ • v
    let X := VectorField.mpullback I 𝓘(ℝ, E) c V
    let W := {y | y ∈ c.source ∧ a (c y) ≠ 0}
    IsOpen W ∧
      ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W ∧
      ∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1 ∧
        mfderiv I 𝓘(ℝ, E) c y (X y) = (a (c y))⁻¹ • v := by
  let q : E → ℝ := fun z => g (c.symm z)
  let a : E → ℝ := fun z => fderiv ℝ q z v
  let V : E → E := fun z => (a z)⁻¹ • v
  let X := VectorField.mpullback I 𝓘(ℝ, E) c V
  let W := {y | y ∈ c.source ∧ a (c y) ≠ 0}
  change IsOpen W ∧
    ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W ∧
    ∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1 ∧
      mfderiv I 𝓘(ℝ, E) c y (X y) = (a (c y))⁻¹ • v
  have hc (y) (hy : y ∈ c.source) : ContMDiffAt I 𝓘(ℝ, E) ∞ c y :=
    c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hy)
  have hq (y) (hy : y ∈ c.source) : ContDiffAt ℝ ∞ q (c y) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact hg.contMDiffAt.comp (c y)
      (c.symm.contMDiffOn.contMDiffAt
        (c.open_target.mem_nhds (c.toPartialEquiv.map_source hy)))
  have ha (y) (hy : y ∈ c.source) : ContDiffAt ℝ ∞ a (c y) :=
    ((hq y hy).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hinv (y) (hy : y ∈ c.source) :
      (mfderiv I 𝓘(ℝ, E) c y).IsInvertible :=
    ⟨(c.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ hy).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have ha' : ContinuousAt (fun z => a (c z)) y :=
      (ha y hy.1).continuousAt.comp (hc y hy.1).continuousAt
    exact Filter.inter_mem (c.open_source.mem_nhds hy.1) (ha'.eventually_ne hy.2)
  · intro y hy
    have hV : ContDiffAt ℝ ∞ V (c y) := ((ha y hy.1).inv hy.2).smul contDiffAt_const
    exact ((contMDiffAt_vectorSpace_iff_contDiffAt.mpr hV).mpullback_vectorField_preimage
      (hc y hy.1) (hinv y hy.1) (by simp)).contMDiffWithinAt
  · intro y hy
    have hcoord : mfderiv I 𝓘(ℝ, E) c y (X y) = V (c y) := by
      let L : TangentSpace I y →L[ℝ] E := mfderiv I 𝓘(ℝ, E) c y
      have hL : L.IsInvertible := hinv y hy.1
      have h := hL.inverse_apply_eq (x := X y) (y := V (c y))
      exact (h.mp rfl).symm
    refine ⟨?_, hcoord⟩
    have heq : (q ∘ c) =ᶠ[𝓝 y] g := by
      filter_upwards [c.open_source.mem_nhds hy.1] with z hz
      exact congrArg g (c.toPartialEquiv.left_inv hz)
    have hderiv := mfderiv_comp y
      ((hq y hy.1).contMDiffAt.mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) hy.1)
    rw [heq.mfderiv_eq] at hderiv
    have happly := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L (X y)) hderiv
    change mfderiv I 𝓘(ℝ) g y (X y) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) q (c y) (mfderiv I 𝓘(ℝ, E) c y (X y)) at happly
    rw [happly, hcoord]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ q (c y) ((a (c y))⁻¹ • v) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ hy.2

private theorem exists_contMDiff_boundary_tangent_unit_field_in_chart
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞)
    {D : Set M} (hD : c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0})
    {p : M} (hp : p ∈ c.source) (hp0 : c p 0 = 0)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hboundary : fderiv ℝ (fun u : Fin n → ℝ => g (c.symm (Fin.cons 0 u)))
      (Fin.tail (c p)) ≠ 0) :
    ∃ (W : Set M) (X : (y : M) → TangentSpace I y),
      IsOpen W ∧ p ∈ W ∧ W ⊆ c.source ∧
      ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W ∧
      (∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1) ∧
      ∀ (m : ℕ)
        (d : PartialDiffeomorph I 𝓘(ℝ, Fin (m + 1) → ℝ) M (Fin (m + 1) → ℝ) ∞),
        d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} →
        ∀ y ∈ W ∩ frontier D, y ∈ d.source →
          (mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y (X y)) 0 = 0 := by
  let e : F ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    (c.isLocalDiffeomorphAt I 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ hp).mfderivToContinuousLinearEquiv
      (by simp)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective e.toLinearMap e.injective
  let : CompleteSpace F := inferInstance
  let q : (Fin (n + 1) → ℝ) → ℝ := fun z => g (c.symm z)
  let j : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun u => Fin.cons 0 u
  let L : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    (0 : (Fin n → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin n → ℝ))
  have hpoint : j (Fin.tail (c p)) = c p := by
    dsimp [j]
    rw [← hp0, Fin.cons_self_tail]
  have hq : ContDiffAt ℝ ∞ q (c p) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact hg.contMDiffAt.comp (c p)
      (c.symm.contMDiffOn.contMDiffAt
        (c.open_target.mem_nhds (c.toPartialEquiv.map_source hp)))
  have hj : HasFDerivAt j L (Fin.tail (c p)) :=
    (hasFDerivAt_const (0 : ℝ) (Fin.tail (c p))).finCons
      (hasFDerivAt_id (Fin.tail (c p)))
  have hqj : DifferentiableAt ℝ q (j (Fin.tail (c p))) := by
    rw [hpoint]
    exact hq.differentiableAt (by simp)
  have hder : fderiv ℝ (q ∘ j) (Fin.tail (c p)) = (fderiv ℝ q (c p)).comp L := by
    simpa only [hpoint] using (hqj.hasFDerivAt.comp (Fin.tail (c p)) hj).fderiv
  obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ (q ∘ j) (Fin.tail (c p)) u ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hboundary
    ext u
    exact hn u
  let v : Fin (n + 1) → ℝ := Fin.cons 0 u
  have hv : fderiv ℝ q (c p) v ≠ 0 := by
    have he := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A u) hder
    change fderiv ℝ (q ∘ j) (Fin.tail (c p)) u = fderiv ℝ q (c p) v at he
    rw [← he]
    exact hu
  let a : (Fin (n + 1) → ℝ) → ℝ := fun z => fderiv ℝ q z v
  let V : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun z => (a z)⁻¹ • v
  let X := VectorField.mpullback I 𝓘(ℝ, Fin (n + 1) → ℝ) c V
  let W := {y | y ∈ c.source ∧ a (c y) ≠ 0}
  obtain ⟨hW, hX, hrate⟩ := contMDiff_normalized_chart_vector_field c hg v
  change IsOpen W at hW
  change ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W at hX
  change ∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1 ∧
    mfderiv I 𝓘(ℝ, Fin (n + 1) → ℝ) c y (X y) = (a (c y))⁻¹ • v at hrate
  refine ⟨W, X, hW, ⟨hp, hv⟩, (fun _ hy => hy.1), hX,
    (fun y hy => (hrate y hy).1), ?_⟩
  intro m d hd y hy hyd
  have hyc : y ∈ c.source := hy.1.1
  have hcy0 : c y 0 = 0 := by
    have h := (hD.frontier hyc).mpr hy.2
    rw [frontier_coordinate_halfspace] at h
    exact h
  let T := c.symm.trans d
  have hTy : c y ∈ T.source := by
    refine ⟨c.toPartialEquiv.map_source hyc, ?_⟩
    change c.symm (c y) ∈ d.source
    exact (c.toPartialEquiv.left_inv hyc).symm ▸ hyd
  have hTD : T.toOpenPartialHomeomorph.IsImage {z | 0 ≤ z 0} {z | 0 ≤ z 0} := by
    intro z hz
    change d (c.symm z) 0 ≥ 0 ↔ z 0 ≥ 0
    exact (hd hz.2).trans (hD.symm hz.1)
  have hTd : DifferentiableAt ℝ T (c y) :=
    (contMDiffAt_iff_contDiffAt.mp
      (T.contMDiffOn.contMDiffAt (T.open_source.mem_nhds hTy))).differentiableAt (by simp)
  have htangent : (fderiv ℝ T (c y) ((a (c y))⁻¹ • v)) 0 = 0 := by
    apply fderiv_preserves_boundary_hyperplane_of_isImage T.toOpenPartialHomeomorph hTD
      hTy hTd hcy0
    simp only [v, Pi.smul_apply, Fin.cons_zero, smul_zero]
  have heq : (T ∘ c) =ᶠ[𝓝 y] d := by
    filter_upwards [c.open_source.mem_nhds hyc] with z hz
    exact congrArg d (c.toPartialEquiv.left_inv hz)
  have hchain := mfderiv_comp y
    (T.mdifferentiableAt (by simp) hTy) (c.mdifferentiableAt (by simp) hyc)
  rw [heq.mfderiv_eq] at hchain
  have happly := congrArg
    (fun A : TangentSpace I y →L[ℝ] (Fin (m + 1) → ℝ) => A (X y)) hchain
  change mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y (X y) =
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (m + 1) → ℝ) T (c y)
      (mfderiv I 𝓘(ℝ, Fin (n + 1) → ℝ) c y (X y)) at happly
  rw [mfderiv_eq_fderiv, (hrate y hy.1).2] at happly
  rw [happly]
  exact htangent

private theorem exists_contMDiff_unit_field_away_frontier
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : Set M} {p : M} (hp : p ∉ frontier D)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hregular : mfderiv I 𝓘(ℝ) g p ≠ 0) :
    ∃ (W : Set M) (X : (y : M) → TangentSpace I y),
      IsOpen W ∧ p ∈ W ∧ W ⊆ (frontier D)ᶜ ∧
      ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W ∧
      ∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : TangentSpace I p, mfderiv I 𝓘(ℝ) g p w ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hregular
    ext w
    exact hn w
  let e := trivializationAt F (TangentSpace I : M → Type _) p
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let v : F := (e (⟨p, w⟩ : TangentBundle I M)).2
  let s : (y : M) → TangentSpace I y := fun y => e.symm y v
  have hsp : s p = w := e.symm_apply_apply_mk hpbase w
  have hs : ContMDiffOn I I.tangent ∞ (fun y => (s y : TangentBundle I M)) e.baseSet := by
    apply e.contMDiffOn_section_baseSet_iff.mpr
    apply (contMDiffOn_const (c := v)).congr
    intro y hy
    change (e (⟨y, e.symm y v⟩ : TangentBundle I M)).2 = v
    have he := congrArg Prod.snd (e.apply_mk_symm hy v)
    exact he
  let a : M → ℝ := fun y => mfderiv I 𝓘(ℝ) g y (s y)
  have ha : ContMDiffOn I 𝓘(ℝ) ∞ a e.baseSet := by
    intro y hy
    exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).contMDiffAt.comp_contMDiffWithinAt y
      ((hg.contMDiff_tangentMap (by simp)).contMDiffAt.comp_contMDiffWithinAt y (hs y hy))
  have hap : a p ≠ 0 := by
    dsimp [a]
    rw [hsp]
    exact hw
  let A : Set M := {y | y ∈ e.baseSet ∧ a y ≠ 0}
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact Filter.inter_mem (e.open_baseSet.mem_nhds hy.1)
      ((ha.contMDiffAt (e.open_baseSet.mem_nhds hy.1)).continuousAt.eventually_ne hy.2)
  let W : Set M := A ∩ (frontier D)ᶜ
  let X : (y : M) → TangentSpace I y := fun y => (a y)⁻¹ • s y
  have hWa : W ⊆ e.baseSet := fun _ hy => hy.1.1
  refine ⟨W, X, hA.inter isClosed_frontier.isOpen_compl, ⟨⟨hpbase, hap⟩, hp⟩,
    Set.inter_subset_right, ?_, ?_⟩
  · exact ((ha.mono hWa).inv₀ (fun _ hy => hy.1.2)).smul_section (hs.mono hWa)
  · intro y hy
    let L : TangentSpace I y →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) g y
    change L ((a y)⁻¹ • s y) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ hy.1.2

theorem exists_contMDiff_boundary_tangent_vector_field
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {D B O : Set M} (hB : IsCompact B)
    (hO : IsOpen O) (hBO : B ⊆ O)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hregular : ∀ p ∈ B, p ∉ frontier D → mfderiv I 𝓘(ℝ) g p ≠ 0)
    (hcharts : ∀ p ∈ B ∩ frontier D,
      ∃ c : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞,
        p ∈ c.source ∧ c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} ∧
        fderiv ℝ (fun u : Fin n → ℝ => g (c.symm (Fin.cons 0 u)))
          (Fin.tail (c p)) ≠ 0) :
    ∃ X : (y : M) → TangentSpace I y,
      ContMDiff I I.tangent ∞ (fun y => (X y : TangentBundle I M)) ∧
      HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ y, 0 ≤ NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) ∧
        NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) ≤ 1) ∧
      (∃ U : Set M, IsOpen U ∧ B ⊆ U ∧ U ⊆ O ∧
        ∀ y ∈ U, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1) ∧
      ∀ (m : ℕ)
        (d : PartialDiffeomorph I 𝓘(ℝ, Fin (m + 1) → ℝ) M (Fin (m + 1) → ℝ) ∞),
        d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} →
        ∀ y ∈ frontier D, y ∈ d.source →
          (mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y (X y)) 0 = 0 := by
  classical
  have hlocal (p : B) : ∃ (W : Set M) (X : (y : M) → TangentSpace I y),
      IsOpen W ∧ (p : M) ∈ W ∧
      ContMDiffOn I I.tangent ∞ (fun y => (X y : TangentBundle I M)) W ∧
      (∀ y ∈ W, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1) ∧
      ∀ (m : ℕ)
        (d : PartialDiffeomorph I 𝓘(ℝ, Fin (m + 1) → ℝ) M (Fin (m + 1) → ℝ) ∞),
        d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} →
        ∀ y ∈ W ∩ frontier D, y ∈ d.source →
          (mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y (X y)) 0 = 0 := by
    by_cases hp : (p : M) ∈ frontier D
    · obtain ⟨c, hpc, hcD, hboundary⟩ := hcharts p ⟨p.property, hp⟩
      have hp0 : c p 0 = 0 := by
        have h := (hcD.frontier hpc).mpr hp
        rw [frontier_coordinate_halfspace] at h
        exact h
      obtain ⟨W, X, hW, hpW, _, hX, hrate, htangent⟩ :=
        exists_contMDiff_boundary_tangent_unit_field_in_chart c hcD hpc hp0 hg hboundary
      exact ⟨W, X, hW, hpW, hX, hrate, htangent⟩
    · obtain ⟨W, X, hW, hpW, hWoutside, hX, hrate⟩ :=
        exists_contMDiff_unit_field_away_frontier hp hg (hregular p p.property hp)
      exact ⟨W, X, hW, hpW, hX, hrate,
        fun _ _ _ _ hy _ => False.elim (hWoutside hy.1 hy.2)⟩
  choose W X hW hpW hX hrate htangent using hlocal
  have hbumps (p : B) : ∃ f : SmoothBumpFunction I (p : M), tsupport f ⊆ W p ∩ O := by
    obtain ⟨f, _, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (p : M)).mem_iff.mp
      ((hW p).inter hO |>.mem_nhds ⟨hpW p, hBO p.property⟩)
    exact ⟨f, hf⟩
  choose f hf using hbumps
  let Q : B → Set M := fun p => interior {y | f p y = 1}
  have hpQ (p : B) : (p : M) ∈ Q p := by
    apply mem_interior_iff_mem_nhds.mpr
    change ∀ᶠ y in 𝓝 (p : M), f p y = 1
    exact (f p).eventuallyEq_one
  obtain ⟨s, hs⟩ := hB.elim_finite_subcover Q (fun _ => isOpen_interior)
    (fun p hp => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpQ ⟨p, hp⟩⟩)
  let ι := {p : B // p ∈ s}
  let U : Set M := ⋃ i : ι, Q i.val
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_interior
  have hBU : B ⊆ U := by
    intro p hp
    obtain ⟨q, hqs, hpq⟩ := Set.mem_iUnion₂.mp (hs hp)
    exact Set.mem_iUnion.mpr ⟨⟨q, hqs⟩, hpq⟩
  let fs : SmoothBumpCovering ι I M U :=
    { c := fun i => i.val.val
      toFun := fun i => f i.val
      c_mem' := fun i => Set.mem_iUnion.mpr ⟨i, hpQ i.val⟩
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        refine ⟨i, ?_⟩
        filter_upwards [isOpen_interior.mem_nhds hi] with z hz
        exact (interior_subset (s := {y | f i.val y = 1}) hz) }
  let ρ := fs.toSmoothPartitionOfUnity
  have hρs (i : ι) : tsupport (ρ i) ⊆ W i.val ∩ O :=
    (closure_mono (fs.support_toSmoothPartitionOfUnity_subset i)).trans (hf i.val)
  have hρc (i : ι) : HasCompactSupport (ρ i) :=
    (f i.val).hasCompactSupport.mono (fs.support_toSmoothPartitionOfUnity_subset i)
  have hUO : U ⊆ O := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have hyone : f i.val y = 1 := interior_subset (s := {y | f i.val y = 1}) hi
    exact (hf i.val (subset_tsupport (f i.val) (by change f i.val y ≠ 0; rw [hyone]; exact one_ne_zero))).2
  let Y : (y : M) → TangentSpace I y := fun y => ∑ i : ι, ρ i y • X i.val y
  have hterm (i : ι) : ContMDiff I I.tangent ∞
      (fun y => ((ρ i y • X i.val y : TangentSpace I y) : TangentBundle I M)) := by
    exact (ρ i).contMDiff.contMDiffOn.smul_section_of_tsupport
      (hW i.val) (fun _ hy => (hρs i hy).1) (hX i.val)
  have hY : ContMDiff I I.tangent ∞ (fun y => (Y y : TangentBundle I M)) := by
    exact ContMDiff.sum_section (fun i _ => hterm i)
  let K : Set M := ⋃ i : ι, tsupport (ρ i)
  have hK : IsCompact K := isCompact_iUnion fun i => (hρc i).isCompact
  have hYK : tsupport Y ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hn
    have hz (i : ι) : ρ i y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hn (Set.mem_iUnion.mpr ⟨i, hi⟩))
    exact hy (by change Y y = 0; simp only [Y, hz, zero_smul, Finset.sum_const_zero])
  have hKO : K ⊆ O := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    exact (hρs i hi).2
  have hYrate (y : M) :
      NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (Y y)) = ∑ i : ι, ρ i y := by
    let L : TangentSpace I y →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) g y
    change L (Y y) = ∑ i : ι, ρ i y
    simp only [Y, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hzero : ρ i y = 0
    · simp only [hzero, zero_smul]
    · have hiunit : L (X i.val y) = 1 := hrate i.val y (hρs i (subset_tsupport (ρ i) hzero)).1
      rw [hiunit]
      simp only [smul_eq_mul, mul_one]
  refine ⟨Y, hY, hK.of_isClosed_subset (isClosed_tsupport Y) hYK,
    hYK.trans hKO, ?_, ⟨U, hU, hBU, hUO, ?_⟩, ?_⟩
  · intro y
    rw [hYrate]
    constructor
    · simpa only [finsum_eq_sum_of_fintype] using ρ.sum_nonneg y
    · simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one y
  · intro y hy
    rw [hYrate]
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hy
  · intro m d hd y hyD hyd
    let L : TangentSpace I y →L[ℝ] (Fin (m + 1) → ℝ) :=
      mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y
    change L (Y y) 0 = 0
    simp only [Y, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hzero : ρ i y = 0
    · simp only [hzero, zero_smul]
    · have hi0 : L (X i.val y) 0 = 0 :=
        htangent i.val m d hd y ⟨(hρs i (subset_tsupport (ρ i) hzero)).1, hyD⟩ hyd
      rw [hi0, smul_zero]

end Manifold
