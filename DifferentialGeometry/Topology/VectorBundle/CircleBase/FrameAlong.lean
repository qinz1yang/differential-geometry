import DifferentialGeometry.Topology.VectorBundle.FrameTrivialization
import DifferentialGeometry.Topology.VectorBundle.CircleBase.PlaneFrames
import DifferentialGeometry.Topology.Manifold.AddCircle
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Orthonormal frames along the covering line of the circle (P1a, part 1)

For a smooth Riemannian bundle `V` of rank two over `S¹ = AddCircle 1`, a *frame along the line*
on an open set `U ⊆ ℝ` is a pair `u : Fin 2 → (t : ℝ) → V t` of sections along the covering map
`t ↦ (t : S¹)`, smooth on `U` and orthonormal at every `t ∈ U`.

* `exists_orthonormal_along_near`: local frames (Gram–Schmidt of a trivialization frame);
* `exists_blend_along`: two frames agreeing at `c` are joined, by a rotation through a smooth angle
  in a window around `c`, into one frame that is the first left of the window and the second right
  of it;
* `exists_orthonormal_along_Ioo`: a frame on every bounded interval (real induction).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Linear combinations, with smooth coefficients, of sections along the covering line that are
smooth at `t₀` are smooth at `t₀`. -/
theorem contMDiffAt_along_add_smul {σ τ : (t : ℝ) → V t} {a b : ℝ → ℝ} {t₀ : ℝ}
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), σ t⟩ : TotalSpace F V)) t₀)
    (hτ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), τ t⟩ : TotalSpace F V)) t₀)
    (ha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a t₀) (hb : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), a t • σ t + b t • τ t⟩ : TotalSpace F V)) t₀ := by
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨AddCircle.contMDiff_coe t₀, ?_⟩
  let e := trivializationAt F V ((t₀ : ℝ) : AddCircle (1 : ℝ))
  have hσ' := (Bundle.contMDiffAt_totalSpace.mp hσ).2
  have hτ' := (Bundle.contMDiffAt_totalSpace.mp hτ).2
  have hsum : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞
      (fun t => a t • (e (⟨t, σ t⟩ : TotalSpace F V)).2 +
        b t • (e (⟨t, τ t⟩ : TotalSpace F V)).2) t₀ :=
    (ha.smul hσ').add (hb.smul hτ')
  refine hsum.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ t in 𝓝 t₀, ((t : ℝ) : AddCircle (1 : ℝ)) ∈ e.baseSet :=
    AddCircle.contMDiff_coe.continuous.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hbase] with t ht
  have hlin := e.linear ℝ ht
  let L : V t →ₗ[ℝ] F :=
    { toFun := fun v => (e (⟨t, v⟩ : TotalSpace F V)).2
      map_add' := hlin.map_add
      map_smul' := hlin.map_smul }
  change L (a t • σ t + b t • τ t) = a t • L (σ t) + b t • L (τ t)
  rw [map_add, map_smul, map_smul]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Smooth multiples of a section along the covering line. -/
theorem contMDiffAt_along_smul {σ : (t : ℝ) → V t} {a : ℝ → ℝ} {t₀ : ℝ}
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), σ t⟩ : TotalSpace F V)) t₀)
    (ha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), a t • σ t⟩ : TotalSpace F V)) t₀ := by
  have h := contMDiffAt_along_add_smul hσ hσ ha (contMDiffAt_const (c := (0 : ℝ)))
  simpa only [zero_smul, add_zero] using h

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Rotating a pair of smooth sections through a smooth angle keeps it smooth. -/
theorem contMDiffAt_along_planeRot {u : Fin 2 → (t : ℝ) → V t} {θ : ℝ → ℝ} {t₀ : ℝ}
    (hu : ∀ i, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) t₀)
    (hθ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ θ t₀) (j : Fin 2) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), planeRot (θ t) (fun i => u i t) j⟩ : TotalSpace F V)) t₀ := by
  have hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => Real.cos (θ t)) t₀ :=
    Real.contDiff_cos.contMDiff.contMDiffAt.comp t₀ hθ
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => Real.sin (θ t)) t₀ :=
    Real.contDiff_sin.contMDiff.contMDiffAt.comp t₀ hθ
  fin_cases j
  · exact contMDiffAt_along_add_smul (hu 0) (hu 1) hc hs
  · exact contMDiffAt_along_add_smul (hu 0) (hu 1) hs.neg hc

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Reflecting a pair of smooth sections keeps it smooth. -/
theorem contMDiffAt_along_planeFlip {u : Fin 2 → (t : ℝ) → V t} {t₀ : ℝ}
    (hu : ∀ i, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) t₀) (j : Fin 2) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), planeFlip (fun i => u i t) j⟩ : TotalSpace F V)) t₀ := by
  fin_cases j
  · exact hu 0
  · have h := contMDiffAt_along_smul (hu 1) (contMDiffAt_const (c := (-1 : ℝ)))
    simp only [neg_smul, one_smul] at h
    exact h

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] in
/-- The inner product of two sections along the line that are smooth at `t₀` is smooth at `t₀`. -/
theorem contMDiffAt_along_inner {σ τ : (t : ℝ) → V t} {t₀ : ℝ}
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), σ t⟩ : TotalSpace F V)) t₀)
    (hτ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), τ t⟩ : TotalSpace F V)) t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => ⟪σ t, τ t⟫_ℝ) t₀ :=
  ContMDiffAt.inner_bundle (b := fun t : ℝ => ((t : ℝ) : AddCircle (1 : ℝ))) hσ hτ

private theorem contMDiffAt_inv_sqrt {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g t₀) (hpos : 0 < g t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => (√(g t))⁻¹) t₀ := by
  have hsq : ContDiffAt ℝ ∞ (fun x : ℝ => (√x)⁻¹) (g t₀) :=
    (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  exact hsq.contMDiffAt.comp t₀ hg

/-- Unit normalization of a nonvanishing vector. -/
private theorem norm_inv_sqrt_smul {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {v : W} (hv : v ≠ 0) : ⟪(√⟪v, v⟫_ℝ)⁻¹ • v, (√⟪v, v⟫_ℝ)⁻¹ • v⟫_ℝ = 1 := by
  have hpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
  rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Every fibre of a rank-two bundle is a plane. -/
theorem finrank_fiber_eq_two (hF : Module.finrank ℝ F = 2) (b : AddCircle (1 : ℝ)) :
    Module.finrank ℝ (V b) = 2 :=
  (finrank_fiber_eq (F := F) (V := V) b).trans hF

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Every fibre of a rank-two bundle is finite-dimensional. -/
theorem finiteDimensional_fiber_of_two (hF : Module.finrank ℝ F = 2) (b : AddCircle (1 : ℝ)) :
    FiniteDimensional ℝ (V b) :=
  Module.finite_of_finrank_eq_succ (finrank_fiber_eq_two hF b)

/-- **Local frames along the line.** Near every `t₀` there is a smooth orthonormal frame along
the covering line. -/
theorem exists_orthonormal_along_near (hF : Module.finrank ℝ F = 2) (t₀ : ℝ) :
    ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ∃ u : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U) ∧
      ∀ t ∈ U, Orthonormal ℝ (fun i => u i t) := by
  let e := trivializationAt F V ((t₀ : ℝ) : AddCircle (1 : ℝ))
  let φ : Module.Basis (Fin 2) ℝ F := Module.finBasisOfFinrankEq ℝ F hF
  let U : Set ℝ := (fun t : ℝ => ((t : ℝ) : AddCircle (1 : ℝ))) ⁻¹' e.baseSet
  have hU : IsOpen U := e.open_baseSet.preimage AddCircle.contMDiff_coe.continuous
  let v : Fin 2 → (t : ℝ) → V t := fun j t => e.localFrame φ j t
  have hv : ∀ j, ∀ t ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), v j t⟩ : TotalSpace F V)) t := fun j t ht =>
    (contMDiffAt_localFrame_of_mem (n := ∞) e φ j ht).comp t (AddCircle.contMDiff_coe t)
  have hli : ∀ t ∈ U, ∀ s₀ s₁ : ℝ, s₀ • v 0 t + s₁ • v 1 t = 0 → s₀ = 0 ∧ s₁ = 0 := by
    intro t ht
    have hb := (e.basisAt φ ht).linearIndependent
    have hfam : (⇑(e.basisAt φ ht)) = ![v 0 t, v 1 t] := by
      funext j
      fin_cases j
      · exact (e.localFrame_apply_of_mem_baseSet φ ht).symm
      · exact (e.localFrame_apply_of_mem_baseSet φ ht).symm
    rw [hfam] at hb
    exact LinearIndependent.pair_iff.mp hb
  have hv0 : ∀ t ∈ U, v 0 t ≠ 0 := by
    intro t ht h0
    have := (hli t ht 1 0 (by rw [h0, smul_zero, zero_smul, add_zero])).1
    exact one_ne_zero this
  let w₀ : (t : ℝ) → V t := fun t => (√⟪v 0 t, v 0 t⟫_ℝ)⁻¹ • v 0 t
  let w' : (t : ℝ) → V t := fun t => (1 : ℝ) • v 1 t + (-⟪v 1 t, w₀ t⟫_ℝ) • w₀ t
  have hw'0 : ∀ t ∈ U, w' t ≠ 0 := by
    intro t ht h0
    have h := hli t ht (-⟪v 1 t, w₀ t⟫_ℝ * (√⟪v 0 t, v 0 t⟫_ℝ)⁻¹) 1 (by
      rw [← h0]
      simp only [w', w₀, smul_smul]
      abel)
    exact one_ne_zero h.2
  let w₁ : (t : ℝ) → V t := fun t => (√⟪w' t, w' t⟫_ℝ)⁻¹ • w' t
  refine ⟨U, hU, FiberBundle.mem_baseSet_trivializationAt' _, fun i t => ![w₀ t, w₁ t] i,
    ?_, ?_⟩
  · have hw₀ : ∀ t ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w₀ t⟩ : TotalSpace F V)) t := fun t ht =>
      contMDiffAt_along_smul (hv 0 t ht) (contMDiffAt_inv_sqrt
        (contMDiffAt_along_inner (hv 0 t ht) (hv 0 t ht)) (real_inner_self_pos.mpr (hv0 t ht)))
    have hw' : ∀ t ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w' t⟩ : TotalSpace F V)) t := fun t ht =>
      contMDiffAt_along_add_smul (hv 1 t ht) (hw₀ t ht) contMDiffAt_const
        (contMDiffAt_along_inner (hv 1 t ht) (hw₀ t ht)).neg
    have hw₁ : ∀ t ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w₁ t⟩ : TotalSpace F V)) t := fun t ht =>
      contMDiffAt_along_smul (hw' t ht) (contMDiffAt_inv_sqrt
        (contMDiffAt_along_inner (hw' t ht) (hw' t ht)) (real_inner_self_pos.mpr (hw'0 t ht)))
    intro i t ht
    fin_cases i
    · exact (hw₀ t ht).contMDiffWithinAt
    · exact (hw₁ t ht).contMDiffWithinAt
  · intro t ht
    have h00 : ⟪w₀ t, w₀ t⟫_ℝ = 1 := norm_inv_sqrt_smul (hv0 t ht)
    have h11 : ⟪w₁ t, w₁ t⟫_ℝ = 1 := norm_inv_sqrt_smul (hw'0 t ht)
    have h01 : ⟪w₀ t, w₁ t⟫_ℝ = 0 := by
      simp only [w₁, w', inner_smul_right, inner_add_right, h00, one_smul, real_inner_comm (w₀ t)]
      ring
    exact orthonormal_of_inner h00 h11 h01

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] in
/-- **Blending two frames along the line.** Two smooth orthonormal frames along the line that agree
at `c` are joined into one: there are `r > 0` and a frame `w` on
`U ∩ (-∞, c + r) ∪ U' ∩ (c - r, ∞)` with `w = u` on `(-∞, c - r]` and `w = u'` on `[c + r, ∞)`;
in between, `w` is `u` rotated through a smooth angle. -/
theorem exists_blend_along (hF : Module.finrank ℝ F = 2) {U U' : Set ℝ} (hU : IsOpen U)
    (hU' : IsOpen U') {u u' : Fin 2 → (t : ℝ) → V t}
    (hu : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U)
    (hon : ∀ t ∈ U, Orthonormal ℝ (fun i => u i t))
    (hu' : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u' i t⟩ : TotalSpace F V)) U')
    (hon' : ∀ t ∈ U', Orthonormal ℝ (fun i => u' i t))
    {c : ℝ} (hcU : c ∈ U) (hcU' : c ∈ U') (heq : ∀ i, u' i c = u i c) :
    ∃ r : ℝ, 0 < r ∧ ∃ w : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w i t⟩ : TotalSpace F V))
        (U ∩ Iio (c + r) ∪ U' ∩ Ioi (c - r))) ∧
      (∀ t ∈ U ∩ Iio (c + r) ∪ U' ∩ Ioi (c - r), Orthonormal ℝ (fun i => w i t)) ∧
      (∀ t ≤ c - r, ∀ i, w i t = u i t) ∧ (∀ t, c + r ≤ t → ∀ i, w i t = u' i t) ∧
      Ioo (c - 2 * r) (c + 2 * r) ⊆ U ∩ U' := by
  have hsmU : ∀ i, ∀ t ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) t :=
    fun i t ht => (hu i).contMDiffAt (hU.mem_nhds ht)
  have hsmU' : ∀ i, ∀ t ∈ U', ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u' i t⟩ : TotalSpace F V)) t :=
    fun i t ht => (hu' i).contMDiffAt (hU'.mem_nhds ht)
  let f₁ : ℝ → ℝ := fun t => ⟪u' 0 t, u 0 t⟫_ℝ
  let f₂ : ℝ → ℝ := fun t => planeDet (fun i => u' i t) (fun i => u i t)
  have hf₁ : ContinuousAt f₁ c :=
    (contMDiffAt_along_inner (hsmU' 0 c hcU') (hsmU 0 c hcU)).continuousAt
  have hf₂ : ContinuousAt f₂ c := by
    have h00 := contMDiffAt_along_inner (hsmU' 0 c hcU') (hsmU 0 c hcU)
    have h11 := contMDiffAt_along_inner (hsmU' 1 c hcU') (hsmU 1 c hcU)
    have h01 := contMDiffAt_along_inner (hsmU' 0 c hcU') (hsmU 1 c hcU)
    have h10 := contMDiffAt_along_inner (hsmU' 1 c hcU') (hsmU 0 c hcU)
    exact ((h00.mul h11).sub (h01.mul h10)).continuousAt
  have hf₁c : f₁ c = 1 := by
    simp only [f₁, heq]
    exact inner_self_of_orthonormal (hon c hcU) 0
  have hf₂c : f₂ c = 1 := by
    simp only [f₂, heq]
    exact planeDet_self (hon c hcU)
  have hnhds : U ∩ U' ∩ {t | 0 < f₁ t} ∩ {t | 0 < f₂ t} ∈ 𝓝 c := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hcU)
      (hU'.mem_nhds hcU')) ?_) ?_
    · exact continuousAt_const.eventually_lt hf₁ (by rw [hf₁c]; norm_num)
    · exact continuousAt_const.eventually_lt hf₂ (by rw [hf₂c]; norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hwin : ∀ t, c - 2 * r < t → t < c + 2 * r →
      t ∈ U ∧ t ∈ U' ∧ 0 < f₁ t ∧ 0 < f₂ t := by
    intro t h1 h2
    have ht : t ∈ Metric.ball c ε := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hball ht
    exact ⟨h1, h2, h3, h4⟩
  have hfd := finiteDimensional_fiber_of_two (V := V) hF
  let g : ℝ → ℝ := fun t => ⟪u' 0 t, u 1 t⟫_ℝ
  have hsq : ∀ t, c - 2 * r < t → t < c + 2 * r → f₁ t ^ 2 + g t ^ 2 = 1 := by
    intro t h1 h2
    obtain ⟨htU, htU', -, -⟩ := hwin t h1 h2
    have hfdt_LFR54P1 := hfd t
    exact inner_sq_add_inner_sq_eq_one (finrank_fiber_eq_two hF t) (hon' t htU') (hon t htU)
  have hg1 : ∀ t, c - 2 * r < t → t < c + 2 * r → g t ^ 2 < 1 := by
    intro t h1 h2
    have := hsq t h1 h2
    have := (hwin t h1 h2).2.2.1
    nlinarith
  let θ : ℝ → ℝ := fun t => Real.arcsin (g t)
  have hrot : ∀ t, c - 2 * r < t → t < c + 2 * r →
      (fun i => u' i t) = planeRot (θ t) (fun i => u i t) := by
    intro t h1 h2
    obtain ⟨htU, htU', hp1, hp2⟩ := hwin t h1 h2
    have hfdt_LFR54P1 := hfd t
    have hg := hg1 t h1 h2
    have hgm : -1 ≤ g t := by nlinarith
    have hgp : g t ≤ 1 := by nlinarith
    refine eq_planeRot_of_planeDet_pos (finrank_fiber_eq_two hF t) (hon' t htU') (hon t htU)
      hp2 ?_ (Real.sin_arcsin hgm hgp)
    rw [Real.cos_arcsin, show 1 - g t ^ 2 = f₁ t ^ 2 by linarith [hsq t h1 h2],
      Real.sqrt_sq hp1.le]
  let ψ : ℝ → ℝ := fun t => Real.smoothTransition ((t - (c - r)) / (2 * r)) * θ t
  let w : Fin 2 → (t : ℝ) → V t := fun i t =>
    if t < c - r then u i t else if c + r < t then u' i t
    else planeRot (ψ t) (fun j => u j t) i
  have hψleft : ∀ t, t ≤ c - r → ψ t = 0 := by
    intro t ht
    simp only [ψ]
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)), zero_mul]
  have hψright : ∀ t, c + r ≤ t → ψ t = θ t := by
    intro t ht
    simp only [ψ]
    rw [Real.smoothTransition.one_of_one_le ((one_le_div (by positivity)).mpr (by linarith)),
      one_mul]
  have hwwin : ∀ t, c - 2 * r < t → t < c + 2 * r →
      (fun i => w i t) = planeRot (ψ t) (fun j => u j t) := by
    intro t h1 h2
    funext i
    by_cases hl : t < c - r
    · simp only [w, hl, ite_true]
      rw [hψleft t hl.le, planeRot_zero_angle]
    · by_cases hrt : c + r < t
      · simp only [w, hl, hrt, ite_true, ite_false]
        rw [hψright t hrt.le, ← hrot t h1 h2]
      · simp only [w, hl, hrt, ite_false]
  have hψsmooth : ∀ t, c - 2 * r < t → t < c + 2 * r → ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ t := by
    intro t h1 h2
    obtain ⟨htU, htU', -, -⟩ := hwin t h1 h2
    have hg := hg1 t h1 h2
    have hgm : g t ≠ -1 := by intro h; rw [h] at hg; norm_num at hg
    have hgp : g t ≠ 1 := by intro h; rw [h] at hg; norm_num at hg
    have hgs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g t :=
      contMDiffAt_along_inner (hsmU' 0 t htU') (hsmU 1 t htU)
    have hθ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ θ t :=
      (Real.contDiffAt_arcsin hgm hgp).contMDiffAt.comp t hgs
    have hst : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => Real.smoothTransition ((t - (c - r)) / (2 * r))) t :=
      (Real.smoothTransition.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const _)).contMDiff.contMDiffAt
    exact hst.mul hθ
  refine ⟨r, hr0, w, ?_, ?_, ?_, ?_, fun t ht => ⟨(hwin t ht.1 ht.2).1, (hwin t ht.1 ht.2).2.1⟩⟩
  · intro i t ht
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hl : t < c - r
    · have htU : t ∈ U := by
        rcases ht with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd (show c - r < t from h) (not_lt.mpr hl.le)
      refine (hsmU i t htU).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hl] with s hs
      simp only [w, show s < c - r from hs, ite_true]
    · by_cases hrt : c + r < t
      · have htU' : t ∈ U' := by
          rcases ht with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd (show t < c + r from h) (not_lt.mpr hrt.le)
          · exact h
        refine (hsmU' i t htU').congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hrt] with s hs
        have hs' : c + r < s := hs
        have hs'' : ¬ s < c - r := by linarith
        simp only [w, hs'', hs', ite_true, ite_false]
      · have h1 : c - 2 * r < t := by linarith [not_lt.mp hl]
        have h2 : t < c + 2 * r := by linarith [not_lt.mp hrt]
        obtain ⟨htU, -, -, -⟩ := hwin t h1 h2
        have hrt' := contMDiffAt_along_planeRot (fun j => hsmU j t htU) (hψsmooth t h1 h2) i
        refine hrt'.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (c - 2 * r) (c + 2 * r) from ⟨h1, h2⟩)]
          with s hs
        exact congrArg (fun v => (⟨(s : AddCircle (1 : ℝ)), v⟩ : TotalSpace F V))
          (congrFun (hwwin s hs.1 hs.2) i)
  · intro t ht
    by_cases hl : t < c - r
    · have htU : t ∈ U := by
        rcases ht with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd (show c - r < t from h) (not_lt.mpr hl.le)
      have hw : (fun i => w i t) = fun i => u i t := by
        funext i
        simp only [w, hl, ite_true]
      rw [hw]
      exact hon t htU
    · by_cases hrt : c + r < t
      · have htU' : t ∈ U' := by
          rcases ht with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd (show t < c + r from h) (not_lt.mpr hrt.le)
          · exact h
        have hw : (fun i => w i t) = fun i => u' i t := by
          funext i
          simp only [w, hl, hrt, ite_true, ite_false]
        rw [hw]
        exact hon' t htU'
      · have h1 : c - 2 * r < t := by linarith [not_lt.mp hl]
        have h2 : t < c + 2 * r := by linarith [not_lt.mp hrt]
        obtain ⟨htU, -, -, -⟩ := hwin t h1 h2
        rw [hwwin t h1 h2]
        exact orthonormal_planeRot (hon t htU) _
  · intro t ht i
    by_cases hl : t < c - r
    · simp only [w, hl, ite_true]
    · have heq' : t = c - r := le_antisymm ht (not_lt.mp hl)
      have h1 : c - 2 * r < t := by linarith
      have h2 : t < c + 2 * r := by linarith
      rw [show w i t = (fun i => w i t) i from rfl, hwwin t h1 h2, hψleft t ht,
        planeRot_zero_angle]
  · intro t ht i
    by_cases hrt : c + r < t
    · have hl : ¬ t < c - r := by linarith
      simp only [w, hl, hrt, ite_true, ite_false]
    · have heq' : t = c + r := le_antisymm (not_lt.mp hrt) ht
      have h1 : c - 2 * r < t := by linarith
      have h2 : t < c + 2 * r := by linarith
      rw [show w i t = (fun i => w i t) i from rfl, hwwin t h1 h2, hψright t ht,
        ← hrot t h1 h2]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
private theorem exists_align_along_of_pos (hF : Module.finrank ℝ F = 2) {U : Set ℝ}
    (hU : IsOpen U) {v : Fin 2 → (t : ℝ) → V t}
    (hv : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), v i t⟩ : TotalSpace F V)) U)
    (hon : ∀ t ∈ U, Orthonormal ℝ (fun i => v i t)) {c : ℝ} (hc : c ∈ U)
    {y : Fin 2 → V c} (hy : Orthonormal ℝ y) (hpos : 0 < planeDet (fun i => v i c) y) :
    ∃ u : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U) ∧
      (∀ t ∈ U, Orthonormal ℝ (fun i => u i t)) ∧ ∀ i, u i c = y i := by
  have hfd_LFR54P1 := finiteDimensional_fiber_of_two (V := V) hF c
  obtain ⟨α, hα, hβ⟩ := exists_cos_sin_eq
    (inner_sq_add_inner_sq_eq_one (finrank_fiber_eq_two hF c) (hon c hc) hy)
  have hrot := eq_planeRot_of_planeDet_pos (finrank_fiber_eq_two hF c) (hon c hc) hy hpos hα hβ
  refine ⟨fun i t => planeRot (-α) (fun j => v j t) i, fun i t ht => ?_,
    fun t ht => orthonormal_planeRot (hon t ht) _, fun i => ?_⟩
  · exact (contMDiffAt_along_planeRot (θ := fun _ => -α)
      (fun j => (hv j).contMDiffAt (hU.mem_nhds ht)) contMDiffAt_const i).contMDiffWithinAt
  · change planeRot (-α) (fun j => v j c) i = y i
    rw [hrot, planeRot_planeRot, add_neg_cancel, planeRot_zero_angle]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- **Aligning a frame at a point.** A smooth orthonormal frame along the line on an open set can be
rotated and reflected so that it takes a prescribed orthonormal value at a point. -/
theorem exists_align_along (hF : Module.finrank ℝ F = 2) {U : Set ℝ} (hU : IsOpen U)
    {v : Fin 2 → (t : ℝ) → V t}
    (hv : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), v i t⟩ : TotalSpace F V)) U)
    (hon : ∀ t ∈ U, Orthonormal ℝ (fun i => v i t)) {c : ℝ} (hc : c ∈ U)
    {y : Fin 2 → V c} (hy : Orthonormal ℝ y) :
    ∃ u : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U) ∧
      (∀ t ∈ U, Orthonormal ℝ (fun i => u i t)) ∧ ∀ i, u i c = y i := by
  have hfd_LFR54P1 := finiteDimensional_fiber_of_two (V := V) hF c
  by_cases hpos : 0 < planeDet (fun i => v i c) y
  · exact exists_align_along_of_pos hF hU hv hon hc hy hpos
  · have hne := planeDet_ne_zero (finrank_fiber_eq_two hF c) (hon c hc) hy
    have hneg : 0 < planeDet (planeFlip (fun i => v i c)) y := by
      rw [planeDet_planeFlip_left]
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) hne)
    exact exists_align_along_of_pos hF hU (v := fun i t => planeFlip (fun j => v j t) i)
      (fun i t ht => (contMDiffAt_along_planeFlip
        (fun j => (hv j).contMDiffAt (hU.mem_nhds ht)) i).contMDiffWithinAt)
      (fun t ht => orthonormal_planeFlip (hon t ht)) hc hy hneg

/-- **Frames along every interval.** For every `a, T` there is a smooth orthonormal frame along
the covering line on `(a, T)`. -/
theorem exists_orthonormal_along_Ioo (hF : Module.finrank ℝ F = 2) (a T : ℝ) :
    ∃ u : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) (Ioo a T)) ∧
      ∀ t ∈ Ioo a T, Orthonormal ℝ (fun i => u i t) := by
  let A : Set ℝ := {T | ∃ u : Fin 2 → (t : ℝ) → V t,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) (Ioo a T)) ∧
      ∀ t ∈ Ioo a T, Orthonormal ℝ (fun i => u i t)}
  have hmono : ∀ T₁ T₂, T₁ ≤ T₂ → T₂ ∈ A → T₁ ∈ A := by
    rintro T₁ T₂ h ⟨u, hu, hon⟩
    exact ⟨u, fun i => (hu i).mono (Ioo_subset_Ioo_right h),
      fun t ht => hon t (Ioo_subset_Ioo_right h ht)⟩
  by_contra hT
  have hbdd : BddAbove A := ⟨T, fun T' hT' => le_of_lt (lt_of_not_ge fun h => hT (hmono T T' h hT'))⟩
  have haA : a ∈ A := ⟨fun _ _ => 0, fun i => by simp [contMDiffOn_empty],
    fun t ht => absurd ht (by simp)⟩
  have hne : A.Nonempty := ⟨a, haA⟩
  set T₀ := sSup A with hT₀
  obtain ⟨U'', hU'', hT₀U, u'', hu'', hon''⟩ := exists_orthonormal_along_near (V := V) hF T₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU'' T₀ hT₀U
  have hbig : T₀ + ε ∈ A := by
    by_cases hlow : T₀ - ε < a
    · refine ⟨u'', fun i => (hu'' i).mono fun t ht => hball ?_, fun t ht => hon'' t (hball ?_)⟩
      · rw [Real.ball_eq_Ioo]; exact ⟨by linarith [ht.1], ht.2⟩
      · rw [Real.ball_eq_Ioo]; exact ⟨by linarith [ht.1], ht.2⟩
    · obtain ⟨T₁, hT₁A, hT₁⟩ := exists_lt_of_lt_csSup hne (show T₀ - ε < T₀ by linarith)
      have hT₁le : T₁ ≤ T₀ := le_csSup hbdd hT₁A
      obtain ⟨u₁, hu₁, hon₁⟩ := hT₁A
      set c := (T₀ - ε + T₁) / 2 with hc
      have hcU₁ : c ∈ Ioo a T₁ := ⟨by linarith [not_lt.mp hlow], by linarith⟩
      have hcU'' : c ∈ U'' := hball (by rw [Real.ball_eq_Ioo]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨u₂, hu₂, hon₂, hu₂c⟩ := exists_align_along hF hU'' hu'' hon'' hcU''
        (hon₁ c hcU₁)
      obtain ⟨r, hr, w, hw, honw, -, -, hwin⟩ := exists_blend_along hF isOpen_Ioo hU'' hu₁ hon₁
        hu₂ hon₂ hcU₁ hcU'' hu₂c
      have hsub : Ioo a (T₀ + ε) ⊆ Ioo a T₁ ∩ Iio (c + r) ∪ U'' ∩ Ioi (c - r) := by
        intro t ht
        by_cases htc : t < c + r
        · left
          refine ⟨⟨ht.1, ?_⟩, htc⟩
          by_cases htc' : t ≤ c
          · linarith
          · exact (hwin ⟨by linarith [not_le.mp htc'], by linarith⟩).1.2
        · right
          refine ⟨hball ?_, show c - r < t by linarith [not_lt.mp htc]⟩
          rw [Real.ball_eq_Ioo]
          exact ⟨by linarith [not_lt.mp htc], ht.2⟩
      exact ⟨w, fun i => (hw i).mono hsub, fun t ht => honw t (hsub ht)⟩
  have := le_csSup hbdd hbig
  linarith

end DifferentialGeometry.Topology.VectorBundle
