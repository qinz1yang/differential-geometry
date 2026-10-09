import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelSlice
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeDefs
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeLocal
import DifferentialGeometry.Analysis.Calculus.ContDiff.OrthonormalBasis

/-!
# Orthonormal normal frames of a `C^r` slice (lane CMS3-CARRIER, group G2, part 1)

Ingredients of the §10 normal parametrization (`exists_normalParametrization`):
* sections of `TM` ALONG a map `b : X → M`: sums, scalar multiples, finite sums, the zero section,
  and the bump trick (a scalar with closed support inside an open set where the section is `C^m`);
* `eq_sum_bilin_basis`: coefficients in a basis orthonormal for a symmetric form;
* `exists_sliceNormalFrame`: in a slice chart `c` of order `r` onto an affine subspace `A`, a
  `C^{r−1}` family `ν_k`, `k : Fin (dim − d)`, orthonormal for the slice coefficients of `g`,
  orthogonal to `A.direction` and spanning the coefficient-normal space. It is the orthonormalisation
  (tree `ContDiffOn.exists_orthonormal_basis`) of the raise `N = G⁻¹|_{Dᗮ}`;
* `sliceNormalFrame_*`: the vectors `n_k y = d(c⁻¹)(ν_k (c y))` are a `g`-orthonormal frame of the
  normal space `ν_y S` at `y ∈ S ∩ c.source` (frame identity `v = Σ g(v, n_k) n_k`), and `C^{r−1}`
  along any `C^{r−1}` map.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Along

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {m : ℕ∞ω} {b : X → M} {x₀ : X}

/-- Sum of two `C^m` vector fields along a map. -/
theorem contMDiffAt_along_add {v w : ∀ x, TangentSpace I (b x)}
    (hv : ContMDiffAt J I.tangent m (fun x => (⟨b x, v x⟩ : TangentBundle I M)) x₀)
    (hw : ContMDiffAt J I.tangent m (fun x => (⟨b x, w x⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt J I.tangent m (fun x => (⟨b x, v x + w x⟩ : TangentBundle I M)) x₀ := by
  rw [contMDiffAt_totalSpace] at hv hw ⊢
  refine ⟨hv.1, (hv.2.add hw.2).congr_of_eventuallyEq ?_⟩
  set e := trivializationAt E (TangentSpace I) (b x₀)
  filter_upwards [hv.1.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) (b x₀)))] with x hx
  exact (e.linear ℝ hx).map_add (v x) (w x)

/-- A `C^m` scalar multiple of a `C^m` vector field along a map. -/
theorem contMDiffAt_along_smul {f : X → ℝ} {v : ∀ x, TangentSpace I (b x)}
    (hf : ContMDiffAt J 𝓘(ℝ, ℝ) m f x₀)
    (hv : ContMDiffAt J I.tangent m (fun x => (⟨b x, v x⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt J I.tangent m (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) x₀ := by
  rw [contMDiffAt_totalSpace] at hv ⊢
  refine ⟨hv.1, (hf.smul hv.2).congr_of_eventuallyEq ?_⟩
  set e := trivializationAt E (TangentSpace I) (b x₀)
  filter_upwards [hv.1.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) (b x₀)))] with x hx
  exact (e.linear ℝ hx).map_smul (f x) (v x)

/-- The zero vector field along a `C^m` map. -/
theorem contMDiffAt_along_zero (hb : ContMDiffAt J I m b x₀) :
    ContMDiffAt J I.tangent m (fun x => (⟨b x, (0 : TangentSpace I (b x))⟩ : TangentBundle I M))
      x₀ := by
  rw [contMDiffAt_totalSpace]
  refine ⟨hb, (contMDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_⟩
  set e := trivializationAt E (TangentSpace I) (b x₀)
  filter_upwards [hb.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) (b x₀)))] with x hx
  exact (e.linear ℝ hx).map_zero

/-- A finite sum of `C^m` vector fields along a `C^m` map. -/
theorem contMDiffAt_along_sum {ι : Type*} (s : Finset ι) {v : ι → ∀ x, TangentSpace I (b x)}
    (hb : ContMDiffAt J I m b x₀)
    (hv : ∀ i ∈ s, ContMDiffAt J I.tangent m
      (fun x => (⟨b x, v i x⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt J I.tangent m (fun x => (⟨b x, ∑ i ∈ s, v i x⟩ : TangentBundle I M)) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact contMDiffAt_along_zero hb
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact contMDiffAt_along_add (hv a (Finset.mem_insert_self a s))
      (ih fun i hi => hv i (Finset.mem_insert_of_mem hi))

/-- **Bump trick.** A scalar with closed support inside a set `W` times a vector field that is
`C^m` at the points of `W` is `C^m` along a `C^m` map. -/
theorem contMDiffAt_along_smul_of_tsupport {f : X → ℝ} {v : ∀ x, TangentSpace I (b x)}
    {W : Set X} (hfW : tsupport f ⊆ W) (hf : ContMDiffAt J 𝓘(ℝ, ℝ) m f x₀)
    (hb : ContMDiffAt J I m b x₀)
    (hv : x₀ ∈ W → ContMDiffAt J I.tangent m (fun x => (⟨b x, v x⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt J I.tangent m (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) x₀ := by
  by_cases hx : x₀ ∈ W
  · exact contMDiffAt_along_smul hf (hv hx)
  · have hxt : x₀ ∉ tsupport f := fun h => hx (hfW h)
    refine (contMDiffAt_along_zero hb).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxt] with x hx'
    change (⟨b x, f x • v x⟩ : TangentBundle I M) = ⟨b x, 0⟩
    rw [show f x = 0 from hx', zero_smul]

end Along

section Basis

/-- Coefficients in a basis orthonormal for a symmetric bilinear form. -/
theorem eq_sum_bilin_basis {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (β : Module.Basis ι ℝ W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ i j, B (β i) (β j) = if i = j then 1 else 0) (w : W) :
    w = ∑ i, B w (β i) • β i := by
  have hcoef : ∀ j, B w (β j) = β.repr w j := by
    intro j
    conv_lhs => rw [← β.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hcoef]
  exact (β.sum_repr w).symm

end Basis

section SliceFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {r : ℕ∞}

/-- **Normal frame in a slice chart (coefficient form).** In a partial diffeomorphism `c` of order
`r ≥ 1` and for an affine subspace `A` of dimension `d`, there are `C^{r−1}` vectors
`ν_k`, `k : Fin (dim − d)`, orthonormal for the coefficients of `g`, orthogonal to `A.direction`,
and spanning the coefficient-normal space. -/
theorem exists_sliceNormalFrame (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E (r : ℕ∞ω)) (A : AffineSubspace ℝ E) {d : ℕ}
    (hdim : Module.finrank ℝ A.direction = d) :
    ∃ ν : Fin (Module.finrank ℝ E - d) → E → E,
      (∀ k, ContDiffOn ℝ ((r - 1 : ℕ∞) : ℕ∞ω) (ν k) c.target) ∧
      (∀ x ∈ c.target, ∀ k l,
        sliceCoeffFinite g c x (ν k x) (ν l x) = if k = l then 1 else 0) ∧
      (∀ x ∈ c.target, ∀ k, ∀ u ∈ A.direction, sliceCoeffFinite g c x (ν k x) u = 0) ∧
      (∀ x ∈ c.target, ∀ v : E, (∀ u ∈ A.direction, sliceCoeffFinite g c x v u = 0) →
        v = ∑ k, sliceCoeffFinite g c x v (ν k x) • ν k x) := by
  classical
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr
    exact (zero_lt_one.trans_le h').ne'
  set C := sliceCoeffFinite g c with hCdef
  have hC : ContDiffOn ℝ m C c.target :=
    contDiffOn_sliceCoeffFinite g coe_sub_one_le_add_one_tube (coe_sub_one_add_one_le_tube hr) c
  have hco : ∀ x ∈ c.target, IsCoercive (C x) := fun x hx => isCoercive_sliceCoeffFinite hk0 g hx
  have hsymm : ∀ x u v, C x u v = C x v u := fun x u v => sliceCoeffFinite_symm g c x u v
  set Dp : Submodule ℝ E := A.directionᗮ with hDp
  have hdle : d ≤ Module.finrank ℝ E := hdim ▸ Submodule.finrank_le A.direction
  have hDpdim : Module.finrank ℝ Dp = Module.finrank ℝ E - d :=
    Submodule.finrank_add_finrank_orthogonal' (by rw [hdim]; omega)
  set N : E → Dp →L[ℝ] E := fun x => (normalRaiseFinite (C x)).comp Dp.subtypeL with hNdef
  have hNc : ContDiffOn ℝ m N c.target :=
    (contDiffOn_normalRaiseFinite hC hco).clm_comp contDiffOn_const
  set Bf : E → Dp →L[ℝ] Dp →L[ℝ] ℝ := fun x => (((C x).comp (N x)).flip.comp (N x)).flip
    with hBfdef
  have hBf_apply : ∀ x (u u' : Dp), Bf x u u' = C x (N x u) (N x u') := by
    intro x u u'
    simp only [hBfdef, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  have hBfc : ContDiffOn ℝ m Bf c.target := by
    have hA : ContDiffOn ℝ m (fun x => (C x).comp (N x)) c.target := hC.clm_comp hNc
    have hB : ContDiffOn ℝ m (fun x => ((C x).comp (N x)).flip) c.target :=
      (ContinuousLinearMap.flipₗᵢ ℝ Dp E ℝ).contDiff.comp_contDiffOn hA
    have hC' : ContDiffOn ℝ m (fun x => ((C x).comp (N x)).flip.comp (N x)) c.target :=
      hB.clm_comp hNc
    exact (ContinuousLinearMap.flipₗᵢ ℝ Dp Dp ℝ).contDiff.comp_contDiffOn hC'
  have hNinj : ∀ x ∈ c.target, ∀ u : Dp, N x u = 0 → u = 0 := by
    intro x hx u hu
    have h := gramOpFinite_normalRaiseFinite (hco x hx) (u : E)
    have hu' : normalRaiseFinite (C x) (u : E) = 0 := hu
    rw [hu', map_zero] at h
    exact Subtype.ext h.symm
  have hBsym : ∀ x ∈ c.target, ∀ u u' : Dp, Bf x u u' = Bf x u' u := by
    intro x _ u u'
    rw [hBf_apply, hBf_apply, hsymm]
  have hBpos : ∀ x ∈ c.target, ∀ u : Dp, u ≠ 0 → 0 < Bf x u u := by
    intro x hx u hu
    rw [hBf_apply]
    obtain ⟨κ, hκ, hκu⟩ := hco x hx
    have hNu : N x u ≠ 0 := fun h => hu (hNinj x hx u h)
    have hpos : 0 < κ * ‖N x u‖ * ‖N x u‖ :=
      mul_pos (mul_pos hκ (norm_pos_iff.mpr hNu)) (norm_pos_iff.mpr hNu)
    exact lt_of_lt_of_le hpos (hκu _)
  obtain ⟨β, hβc, hβon⟩ := ContDiffOn.exists_orthonormal_basis hBfc
    (Module.finBasisOfFinrankEq ℝ Dp hDpdim) hBsym hBpos
  have hβδ : ∀ x ∈ c.target, ∀ k l, Bf x (β x k) (β x l) = if k = l then 1 else 0 := by
    intro x hx k l
    by_cases hkl : k = l
    · rw [ite_eq_left_iff.mpr (fun h => absurd hkl h), hkl]; exact (hβon x hx).1 l
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hkl)]; exact (hβon x hx).2 k l hkl
  refine ⟨fun k x => N x (β x k), fun k => hNc.clm_apply (hβc k), ?_, ?_, ?_⟩
  · intro x hx k l
    rw [← hBf_apply]
    exact hβδ x hx k l
  · intro x hx k u hu
    change C x (normalRaiseFinite (C x) ((β x k : Dp) : E)) u = 0
    rw [apply_normalRaiseFinite (hco x hx)]
    exact Submodule.inner_left_of_mem_orthogonal hu (β x k).2
  · intro x hx v hv
    set w : E := gramOpFinite (C x) v with hw
    have hwD : w ∈ Dp := by
      rw [hDp, Submodule.mem_orthogonal]
      intro u hu
      rw [real_inner_comm, hw, inner_gramOpFinite]
      exact hv u hu
    have hvN : v = N x ⟨w, hwD⟩ := by
      change v = normalRaiseFinite (C x) w
      rw [hw, normalRaiseFinite_gramOpFinite (hco x hx)]
    have hexp := eq_sum_bilin_basis (β x)
      (Bf x : Dp →L[ℝ] Dp →L[ℝ] ℝ).toLinearMap₁₂ (hβδ x hx) ⟨w, hwD⟩
    calc v = N x ⟨w, hwD⟩ := hvN
      _ = N x (∑ k, Bf x ⟨w, hwD⟩ (β x k) • β x k) := congrArg (N x) hexp
      _ = ∑ k, Bf x ⟨w, hwD⟩ (β x k) • N x (β x k) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
      _ = ∑ k, C x v (N x (β x k)) • N x (β x k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hBf_apply, ← hvN]

omit [FiniteDimensional ℝ E] in
/-- The metric along the frame vector `d(c⁻¹)(a)`, read in the chart. -/
theorem inner_mfderiv_symm_slice (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E (r : ℕ∞ω)} {y : M} (hy : y ∈ c.source) (a : E)
    (w : TangentSpace I y) :
    g.inner y (mfderiv 𝓘(ℝ, E) I c.symm (c y) a) w =
      sliceCoeffFinite g c (c y) a (mfderiv I 𝓘(ℝ, E) c y w) := by
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr
    exact (zero_lt_one.trans_le h').ne'
  refine (inner_eq_sliceCoeffFinite hk0 g hy _ w).trans ?_
  exact congrArg (fun z => sliceCoeffFinite g c (c y) z (mfderiv I 𝓘(ℝ, E) c y w))
    (mfderiv_apply_mfderiv_symm_of_mem_source_ofOrder hk0 hy a)

omit [FiniteDimensional ℝ E] in
/-- **The slice normal frame on `M`.** For `y ∈ S ∩ c.source` (slice chart onto `A`), the vectors
`n_k = d(c⁻¹)(ν_k (c y))` are `g`-orthonormal, normal to `S`, and every normal vector is
`Σ g(v, n_k) n_k`. -/
theorem sliceNormalFrame_spec (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E (r : ℕ∞ω)} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) {S : Set M}
    (himage : c.toPartialEquiv.IsImage S (A : Set E)) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : ι → E → E}
    (hon : ∀ x ∈ c.target, ∀ k l,
      sliceCoeffFinite g c x (ν k x) (ν l x) = if k = l then 1 else 0)
    (hnor : ∀ x ∈ c.target, ∀ k, ∀ u ∈ A.direction, sliceCoeffFinite g c x (ν k x) u = 0)
    (hspan : ∀ x ∈ c.target, ∀ v : E, (∀ u ∈ A.direction, sliceCoeffFinite g c x v u = 0) →
      v = ∑ k, sliceCoeffFinite g c x v (ν k x) • ν k x)
    {y : M} (hyS : y ∈ S) (hyc : y ∈ c.source) :
    (∀ k l, g.inner y (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y)))
        (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν l (c y))) = if k = l then 1 else 0) ∧
      (∀ k, ∀ w ∈ sliceTangent I S y,
        g.inner y (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y))) w = 0) ∧
      ∀ v : TangentSpace I y, (∀ w ∈ sliceTangent I S y, g.inner y v w = 0) →
        v = ∑ k, g.inner y v (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y))) •
          mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y)) := by
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr
    exact (zero_lt_one.trans_le h').ne'
  have hcy : c y ∈ c.target := c.toPartialEquiv.map_source hyc
  have hdc : ∀ a : E, (mfderiv I 𝓘(ℝ, E) c y (mfderiv 𝓘(ℝ, E) I c.symm (c y) a) : E) = a :=
    fun a => mfderiv_apply_mfderiv_symm_of_mem_source_ofOrder hk0 hyc a
  refine ⟨fun k l => ?_, fun k w hw => ?_, fun v hv => ?_⟩
  · refine (inner_mfderiv_symm_slice hr g hyc _ _).trans ?_
    exact (congrArg (fun z => sliceCoeffFinite g c (c y) (ν k (c y)) z) (hdc _)).trans
      (hon _ hcy k l)
  · exact (inner_mfderiv_symm_slice hr g hyc _ w).trans
      (hnor _ hcy k _ ((mem_sliceTangent_chart_iff_ofOrder hk0 hyS hA hyc himage).1 hw))
  · set u : E := mfderiv I 𝓘(ℝ, E) c y v with hu
    have hunor : ∀ u' ∈ A.direction, sliceCoeffFinite g c (c y) u u' = 0 := by
      intro u' hu'
      have hT : mfderiv 𝓘(ℝ, E) I c.symm (c y) u' ∈ sliceTangent I S y :=
        (mem_sliceTangent_chart_iff_ofOrder hk0 hyS hA hyc himage).2 (by rw [hdc]; exact hu')
      have h := (inner_eq_sliceCoeffFinite hk0 g hyc v _).symm.trans (hv _ hT)
      rw [hdc] at h
      exact h
    have hexp := hspan _ hcy u hunor
    have hv' : v = mfderiv 𝓘(ℝ, E) I c.symm (c y) u :=
      (mfderiv_symm_apply_mfderiv_ofOrder hk0 hyc v).symm
    have hcoef : ∀ k, sliceCoeffFinite g c (c y) u (ν k (c y)) =
        g.inner y v (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y))) := fun k =>
      (sliceCoeffFinite_symm g c _ _ _).trans
        ((inner_mfderiv_symm_slice hr g hyc _ v).symm.trans (g.symm _ _ _))
    have h1 : mfderiv 𝓘(ℝ, E) I c.symm (c y) u = mfderiv 𝓘(ℝ, E) I c.symm (c y)
        (∑ k, sliceCoeffFinite g c (c y) u (ν k (c y)) • ν k (c y)) :=
      congrArg (mfderiv 𝓘(ℝ, E) I c.symm (c y)) hexp
    have h2 : mfderiv 𝓘(ℝ, E) I c.symm (c y)
        (∑ k, sliceCoeffFinite g c (c y) u (ν k (c y)) • ν k (c y)) =
        ∑ k, sliceCoeffFinite g c (c y) u (ν k (c y)) •
          mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y)) :=
      (map_sum (mfderiv 𝓘(ℝ, E) I c.symm (c y)) _ _).trans
        (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
    have h3 : (∑ k, sliceCoeffFinite g c (c y) u (ν k (c y)) •
          mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y))) =
        ∑ k, g.inner y v (mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y))) •
          mfderiv 𝓘(ℝ, E) I c.symm (c y) (ν k (c y)) :=
      Finset.sum_congr rfl fun k _ => by rw [hcoef k]
    exact hv'.trans (h1.trans (h2.trans h3))

omit [FiniteDimensional ℝ E] in
/-- **Regularity of the slice frame along a map.** If `b` is `C^{r−1}` at `x₀` with `b x₀` in the
chart source and `ν_k` is `C^{r−1}` on the chart target, then `x ↦ ⟨b x, d(c⁻¹)(ν_k (c (b x)))⟩` is
`C^{r−1}` at `x₀`. -/
theorem contMDiffAt_sliceFrame_along (hr : 1 ≤ r)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E (r : ℕ∞ω)} {ν : E → E}
    (hν : ContDiffOn ℝ ((r - 1 : ℕ∞) : ℕ∞ω) ν c.target)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {b : X → M} {x₀ : X}
    (hb : ContMDiffAt J I ((r - 1 : ℕ∞) : ℕ∞ω) b x₀) (hx₀ : b x₀ ∈ c.source) :
    ContMDiffAt J I.tangent ((r - 1 : ℕ∞) : ℕ∞ω)
      (fun x => (⟨b x, mfderiv 𝓘(ℝ, E) I c.symm (c (b x)) (ν (c (b x)))⟩ :
        TangentBundle I M)) x₀ := by
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hmr : m ≤ (r : ℕ∞ω) :=
    le_trans (le_add_of_nonneg_right zero_le_one) (coe_sub_one_add_one_le_tube hr)
  have hcx : c (b x₀) ∈ c.target := c.toPartialEquiv.map_source hx₀
  have hf : ContMDiffAt 𝓘(ℝ, E) I (r : ℕ∞ω) c.symm (c (b x₀)) :=
    c.symm.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hcx)
  have hcb : ContMDiffAt J 𝓘(ℝ, E) m (fun x => c (b x)) x₀ :=
    ((c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hx₀)).of_le hmr).comp x₀ hb
  have ha : ContMDiffAt J 𝓘(ℝ, E) m (fun x => ν (c (b x))) x₀ :=
    ((hν _ hcx).contDiffAt (c.open_target.mem_nhds hcx)).contMDiffAt.comp x₀ hcb
  have h := contMDiffAt_mk_mfderiv_apply (φ := fun x => c (b x)) (x := x₀) hf
    (coe_sub_one_add_one_le_tube hr) hcb ha
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hb.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with x hx
  exact tangentBundle_mk_eq (c.toPartialEquiv.left_inv hx).symm rfl

end SliceFrame

end DifferentialGeometry.Geometry.FiniteSoul
