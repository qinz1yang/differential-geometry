import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.IsotopyOrientationModel
import DifferentialGeometry.Topology.FixedPoint.Brouwer
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Chapter-14 assembly, D2S1 input (c): the monodromy of a lift flow preserves orientation

Frozen statement: `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean` (`exists_monodromy_preservesOrientation`).
Data: an oriented connected manifold `M` with boundary (model `𝓡∂ 3`), a smooth `p : M → Circle`, a
jointly smooth flow `Φ` of diffeomorphisms lifting the rotation (`p (Φ t q) = exp(i t) · p q`), and a
smooth embedding `fibre` of the closed disk onto `p⁻¹{1}`.

* The monodromy `μ = fibre⁻¹ ∘ Φ (2π) ∘ fibre` is a diffeomorphism of the disk (inverse from
  `Φ (−2π)`; smoothness by the immersion criterion `ContMDiffAt.iff_comp_isImmersionAt`).
* Orientation, without any continuity-in-the-base argument: by Brouwer (`Topology/FixedPoint/Brouwer.lean`)
  `μ` has a fixed point `x₀`, so `q₀ = fibre x₀` is fixed by `Φ (2π)`. The time-`2π` map preserves
  the orientation of `M` (jointly smooth isotopy from the identity, `IsotopyOrientationModel.lean`), so
  `det dΦ(2π)_{q₀} > 0`. In the basis `(dfibre ·, ∂ₜΦ)` of `T_{q₀} M` the differential is block
  diagonal `dμ_{x₀} ⊕ 1` (the flow direction is fixed, `range dfibre` is invariant; the two are
  separated by the functional `d(coe ∘ p)`), so `det dμ_{x₀} = det dΦ(2π)_{q₀} > 0`, and a
  diffeomorphism of the connected disk that preserves the orientation at one fixed point preserves
  it everywhere.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsMonodromy_D2S1C : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothMonodromy_D2S1C : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

attribute [local instance] finrank_real_complex_fact'

local instance closedCellNonemptyMonodromy_D2S1C : Nonempty (ClosedCell 2) :=
  ⟨closedCellCenter 2⟩

/-! ## Linear algebra: a block-triangular determinant -/

/-- If `T` leaves the image of an injective `i : W → V` invariant (acting there as `A`), fixes a
vector `X` separated from `range i` by a functional vanishing on it, and `dim V = dim W + 1`, then
`det T = det A`. -/
theorem det_eq_det_of_invariant_of_fixed {V W G : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup G] [Module ℝ G]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (i : W →ₗ[ℝ] V) (hi : Injective i) (ℓ : V →ₗ[ℝ] G) (hℓi : ∀ w, ℓ (i w) = 0) (X : V)
    (hX : ℓ X ≠ 0) (T : V →ₗ[ℝ] V) (A : W →ₗ[ℝ] W) (hTA : ∀ w, T (i w) = i (A w))
    (hTX : T X = X) :
    LinearMap.det T = LinearMap.det A := by
  let e₀ : (W × ℝ) →ₗ[ℝ] V := LinearMap.coprod i (LinearMap.toSpanSingleton ℝ V X)
  have he₀ : ∀ w c, e₀ (w, c) = i w + c • X := by
    intro w c
    simp [e₀, LinearMap.toSpanSingleton_apply]
  have hinj : Injective e₀ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨w, c⟩ h
    rw [he₀] at h
    have hc : c = 0 := by
      have h1 := congrArg ℓ h
      rw [map_add, map_smul, hℓi, zero_add, map_zero] at h1
      exact (smul_eq_zero.mp h1).resolve_right hX
    rw [hc, zero_smul, add_zero] at h
    have hw : w = 0 := hi (by rw [h, map_zero])
    rw [hw, hc]
    rfl
  have hdim' : Module.finrank ℝ (W × ℝ) = Module.finrank ℝ V := by
    rw [Module.finrank_prod, Module.finrank_self, hdim]
  let e : (W × ℝ) ≃ₗ[ℝ] V := LinearMap.linearEquivOfInjective e₀ hinj hdim'
  have hconj : (e : (W × ℝ) →ₗ[ℝ] V) ∘ₗ (A.prodMap LinearMap.id) ∘ₗ (e.symm : V →ₗ[ℝ] W × ℝ) =
      T := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨w, c⟩, rfl⟩ := e.surjective v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq]
    change e₀ (A w, c) = T (e₀ (w, c))
    rw [he₀, he₀, map_add, map_smul, hTA, hTX]
  rw [← hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-! ## Orientation at a fixed point -/

/-- A diffeomorphism of a connected manifold with a fixed point `x` preserves an orientation iff its
differential at `x` has positive determinant. -/
theorem preservesOrientation_iff_det_mfderiv_pos_of_apply_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [PreconnectedSpace N] {n : ℕ} (o : ManifoldOrientation I N n)
    {f : N ≃ₘ⟮I, I⟯ N} (x : N) (hx : f x = x) :
    f.preservesOrientation o o ↔
      0 < LinearMap.det (mfderiv I I f x : E →L[ℝ] E).toLinearMap := by
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by
    rw [Fintype.card_fin, o.dimension_eq]
  have key : ∀ (y : N) (_ : y = x) (L : TangentSpace I x ≃ₗ[ℝ] TangentSpace I y),
      (L.toLinearMap : E →ₗ[ℝ] E) = (mfderiv I I f x : E →L[ℝ] E).toLinearMap →
      (Orientation.map (Fin n) L (o.orientation x) = o.orientation y ↔
        0 < LinearMap.det (mfderiv I I f x : E →L[ℝ] E).toLinearMap) := by
    intro y hy L hL
    subst hy
    rw [← hL]
    exact Orientation.map_eq_iff_det_pos _ _ hcard
  rw [Diffeomorph.preservesOrientation_iff_eq_at f o o x]
  exact key (f x) hx _ rfl

/-! ## The return map of the flow on the fibre over `1` -/

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- The return map `x ↦ fibre⁻¹ (Φ s (fibre x))` of the flow on the fibre over `1`. -/
def fibreReturnMap (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)) (fibre : ClosedCell 2 → M) (s : ℝ)
    (x : ClosedCell 2) : ClosedCell 2 :=
  invFun fibre (Φ s (fibre x))

theorem fibre_fibreReturnMap {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hrange : range fibre = p ⁻¹' {1}) {s : ℝ} (hs : Circle.exp s = 1) (x : ClosedCell 2) :
    fibre (fibreReturnMap Φ fibre s x) = Φ s (fibre x) := by
  have hp1 : p (fibre x) = 1 := by
    have h : fibre x ∈ p ⁻¹' {1} := hrange ▸ mem_range_self x
    exact h
  have hmem : Φ s (fibre x) ∈ range fibre := by
    rw [hrange]
    change p (Φ s (fibre x)) = 1
    rw [hΦp, hp1, hs, mul_one]
  exact Function.invFun_eq hmem

theorem fibreReturnMap_neg_apply {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hinj : Injective fibre) (hrange : range fibre = p ⁻¹' {1}) {s : ℝ}
    (hs : Circle.exp s = 1) (x : ClosedCell 2) :
    fibreReturnMap Φ fibre (-s) (fibreReturnMap Φ fibre s x) = x := by
  have hs' : Circle.exp (-s) = 1 := by rw [Circle.exp_neg, hs, inv_one]
  apply hinj
  rw [fibre_fibreReturnMap hΦp hrange hs', fibre_fibreReturnMap hΦp hrange hs, ← hΦadd,
    neg_add_cancel]
  have h0 : Φ 0 (fibre x) = fibre x := (Φ 0).injective (by
    change Φ 0 (Φ 0 (fibre x)) = Φ 0 (fibre x)
    rw [← hΦadd, add_zero])
  exact h0

theorem contMDiff_fibreReturnMap {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) (hrange : range fibre = p ⁻¹' {1})
    {s : ℝ} (hs : Circle.exp s = 1) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fibreReturnMap Φ fibre s) := by
  have hcomp : fibre ∘ fibreReturnMap Φ fibre s = fun x => Φ s (fibre x) := by
    funext x
    exact fibre_fibreReturnMap hΦp hrange hs x
  have hsm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (fun x => Φ s (fibre x)) :=
    hΦ.comp (contMDiff_const.prodMk hfibre.isImmersion.contMDiff)
  intro x
  refine (ContMDiffAt.iff_comp_isImmersionAt
    (hfibre.isImmersion.isImmersionAt (fibreReturnMap Φ fibre s x))).mpr ⟨?_, ?_⟩
  · refine hfibre.isEmbedding.isInducing.continuousAt_iff.mpr ?_
    rw [hcomp]
    exact hsm.continuous.continuousAt
  · rw [hcomp]
    exact hsm x

/-- The monodromy `fibre⁻¹ ∘ Φ (2π) ∘ fibre` as a diffeomorphism of the disk. -/
def monodromyDiffeomorph {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) :
    ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 where
  toFun := fibreReturnMap Φ fibre (2 * Real.pi)
  invFun := fibreReturnMap Φ fibre (-(2 * Real.pi))
  left_inv := fibreReturnMap_neg_apply hΦadd hΦp hfibre.isEmbedding.injective hrange
    Circle.exp_two_pi
  right_inv x := by
    have h := fibreReturnMap_neg_apply hΦadd hΦp hfibre.isEmbedding.injective hrange
      (s := -(2 * Real.pi)) (by rw [Circle.exp_neg, Circle.exp_two_pi, inv_one]) x
    rwa [neg_neg] at h
  contMDiff_toFun := contMDiff_fibreReturnMap hΦ hΦp hfibre hrange Circle.exp_two_pi
  contMDiff_invFun := contMDiff_fibreReturnMap hΦ hΦp hfibre hrange
    (by rw [Circle.exp_neg, Circle.exp_two_pi, inv_one])

theorem fibre_monodromyDiffeomorph {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) (x : ClosedCell 2) :
    fibre (monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange x) = Φ (2 * Real.pi) (fibre x) :=
  fibre_fibreReturnMap hΦp hrange Circle.exp_two_pi x

/-! ## Brouwer on the closed disk and connectedness -/

theorem closedCell_two_preconnectedSpace : PreconnectedSpace (ClosedCell 2) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
  exact Subtype.preconnectedSpace hconv.isPreconnected

theorem exists_fixedPoint_closedCell_two {f : ClosedCell 2 → ClosedCell 2} (hf : Continuous f) :
    ∃ x, f x = x := by
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun y =>
    ⟨(f ⟨y.1, mem_closedBall_zero_iff.mp y.2⟩).1,
      mem_closedBall_zero_iff.mpr (f ⟨y.1, mem_closedBall_zero_iff.mp y.2⟩).2⟩
  have hg : Continuous g :=
    (continuous_subtype_val.comp (hf.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  obtain ⟨y, hy⟩ :=
    DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closedBall_of_continuous g hg
  refine ⟨⟨y.1, mem_closedBall_zero_iff.mp y.2⟩, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hy
  exact h

/-! ## The derivative of the rotation -/

theorem mfderiv_circle_rotation_coe_ne_zero (c : Circle) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t : ℝ => ((Circle.exp t * c : Circle) : ℂ)) 0 1 ≠ 0 := by
  have hfun : (fun t : ℝ => ((Circle.exp t * c : Circle) : ℂ)) =
      fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (c : ℂ) := by
    funext t
    rw [Circle.coe_mul, Circle.coe_exp]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (c : ℂ))
      (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * ((((1 : ℝ) : ℂ)) * Complex.I) * (c : ℂ)) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp).mul_const (c : ℂ)
  rw [hfun, mfderiv_eq_fderiv]
  change fderiv ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (c : ℂ)) 0 1 ≠ 0
  rw [fderiv_apply_one_eq_deriv, hd.deriv]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul, ne_eq,
    mul_eq_zero, Complex.I_ne_zero, false_or]
  exact Circle.coe_ne_zero c

/-! ## The monodromy preserves orientation -/

variable [IsManifold (𝓡∂ 3) ∞ M]

/-- The monodromy preserves every orientation of the disk when the total space is oriented and
connected. -/
theorem monodromyDiffeomorph_preservesOrientation [ConnectedSpace M]
    (oM : ManifoldOrientation (𝓡∂ 3) M 3) {p : M → Circle} (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦ0 : ∀ q, Φ 0 q = q) (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) (hrange : range fibre = p ⁻¹' {1})
    (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) :
    (monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange).preservesOrientation o o := by
  let _ : PreconnectedSpace (ClosedCell 2) := closedCell_two_preconnectedSpace
  set μ := monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange
  obtain ⟨x₀, hx₀⟩ := exists_fixedPoint_closedCell_two μ.continuous
  set q₀ := fibre x₀ with hq₀
  have hfμ : ∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x) :=
    fibre_monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange
  have hq₀fix : Φ (2 * Real.pi) q₀ = q₀ := by
    rw [hq₀, ← hfμ, hx₀]
  -- `Φ (2π)` preserves `oM`, hence has positive determinant at its fixed point `q₀`
  have hΦpres : (Φ (2 * Real.pi)).preservesOrientation oM oM :=
    DifferentialGeometry.Topology.Manifold.preservesOrientation_of_contMDiff_flow oM Φ hΦ0 hΦ
      (2 * Real.pi)
  have hdetΦ := (preservesOrientation_iff_det_mfderiv_pos_of_apply_eq oM q₀
    hq₀fix).mp hΦpres
  rw [preservesOrientation_iff_det_mfderiv_pos_of_apply_eq o x₀ hx₀]
  -- the data of the block decomposition
  have hp1 : ∀ x, p (fibre x) = 1 := by
    intro x
    have h : fibre x ∈ p ⁻¹' {1} := hrange ▸ mem_range_self x
    exact h
  have hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre := hfibre.isImmersion.contMDiff
  have hcp : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun q => (p q : ℂ)) :=
    contMDiff_coe_sphere.comp hp
  let γ : ℝ → M := fun t => Φ t q₀
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ := hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  have hγ0 : γ 0 = q₀ := hΦ0 q₀
  let ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ := mfderiv (𝓡∂ 3) 𝓘(ℝ, ℂ) (fun q => (p q : ℂ)) q₀
  let X : EuclideanSpace ℝ (Fin 3) := mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 1
  let i : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡∂ 2) (𝓡∂ 3) fibre x₀
  let T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡∂ 3) (𝓡∂ 3) (Φ (2 * Real.pi)) q₀
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡∂ 2) (𝓡∂ 2) μ x₀
  have hmd_cp : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ, ℂ) (fun q => (p q : ℂ)) q₀ :=
    hcp.mdifferentiableAt (by simp)
  have hmd_fibre : ∀ x, MDifferentiableAt (𝓡∂ 2) (𝓡∂ 3) fibre x :=
    fun x => hfibre_sm.mdifferentiableAt (by simp)
  have hmd_Φ : ∀ q, MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (Φ (2 * Real.pi)) q :=
    fun q => (Φ (2 * Real.pi)).contMDiff.mdifferentiableAt (by simp)
  have hmd_μ : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) μ x₀ := μ.contMDiff.mdifferentiableAt (by simp)
  have hmd_γ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 := hγ.mdifferentiableAt (by simp)
  -- `ℓ` kills the fibre directions
  have hℓi : ∀ w, ℓ (i w) = 0 := by
    intro w
    have hconst : (fun q => (p q : ℂ)) ∘ fibre = fun _ => (1 : ℂ) := by
      funext x
      simp [hp1 x]
    have h := mfderiv_comp_apply_of_eq x₀ hmd_cp (hmd_fibre x₀) rfl w
    rw [hconst, mfderiv_const] at h
    exact h.symm
  -- `ℓ` does not kill the flow direction
  have hX : ℓ X ≠ 0 := by
    have hcomp : (fun q => (p q : ℂ)) ∘ γ = fun t : ℝ => ((Circle.exp t * p q₀ : Circle) : ℂ) := by
      funext t
      simp only [Function.comp_apply, γ, hΦp]
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) hmd_cp hmd_γ hγ0 (1 : ℝ)
    rw [hcomp] at h
    change _ = ℓ X at h
    rw [← h]
    exact mfderiv_circle_rotation_coe_ne_zero (p q₀)
  -- `T` acts on the fibre directions as `A`
  have hTA : ∀ w, T (i w) = i (A w) := by
    intro w
    have hfun : fibre ∘ μ = (Φ (2 * Real.pi)) ∘ fibre := by
      funext x
      exact hfμ x
    have h1 := mfderiv_comp_apply_of_eq x₀ (hmd_fibre x₀) hmd_μ hx₀ w
    have h2 := mfderiv_comp_apply_of_eq x₀ (hmd_Φ q₀) (hmd_fibre x₀) rfl w
    rw [hfun] at h1
    exact h2.symm.trans h1
  -- `T` fixes the flow direction
  have hTX : T X = X := by
    have hfun : (Φ (2 * Real.pi)) ∘ γ = γ := by
      funext t
      change Φ (2 * Real.pi) (Φ t q₀) = Φ t q₀
      rw [← hΦadd, add_comm, hΦadd, hq₀fix]
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) (hmd_Φ q₀) hmd_γ hγ0 (1 : ℝ)
    rw [hfun] at h
    exact h.symm
  have hi : Injective i := hfibre.isImmersion.mfderiv_injective (by simp) x₀
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    simp
  have hdet := det_eq_det_of_invariant_of_fixed hdim i.toLinearMap hi ℓ.toLinearMap hℓi X hX
    T.toLinearMap A.toLinearMap hTA hTX
  change 0 < LinearMap.det A.toLinearMap
  rw [← hdet]
  exact hdetΦ

/-- **D2S1 input (c)** (frozen statement minus the unused `[CompactSpace M] [T2Space M]`): the
monodromy of a lift flow on the fibre over `1` is a diffeomorphism of the disk, and it preserves
orientation when the total space is oriented. -/
theorem exists_monodromy_preservesOrientation [ConnectedSpace M]
    (oM : ManifoldOrientation (𝓡∂ 3) M 3)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦ0 : ∀ q, Φ 0 q = q) (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) :
    ∃ μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
      (∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x)) ∧ μ.preservesOrientation o o :=
  ⟨monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange,
    fibre_monodromyDiffeomorph hΦ hΦadd hΦp hfibre hrange,
    monodromyDiffeomorph_preservesOrientation oM hp hΦ hΦ0 hΦadd hΦp hfibre hrange o⟩

/-- The frozen text verbatim (with the unused `[CompactSpace M] [T2Space M]`). -/
example {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] (oM : ManifoldOrientation (𝓡∂ 3) M 3)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦ0 : ∀ q, Φ 0 q = q) (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) :
    ∃ μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
      (∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x)) ∧ μ.preservesOrientation o o :=
  exists_monodromy_preservesOrientation oM p hp Φ hΦ hΦ0 hΦadd hΦp fibre hfibre hrange o

end GC.GraphManifold.Assembly
